#!/usr/bin/env python3
"""Tests of the `route` and `ci` jobs of .github/workflows/ci.yml, run as committed.

A route answer of `false` stops a job from running, so a wrong answer hides a real
failure. Each case below makes a commit in a scratch repository, runs the route step's
script on it as GitHub runs a step, and compares the two answers, `build` and `review`.
Then the `ci` job's script runs against each combination of results it must judge.

The route job runs this file first, so a change that breaks a case fails `CI`.

    python3 .github/test_ci.py        from any directory; prints each case.

No network is used. Needs python3, bash, git and yq (mikefarah's, as GitHub's runners have).
"""
import json
import os
import subprocess
import sys
import tempfile

WORKFLOW = os.path.join(os.path.dirname(os.path.abspath(__file__)), "workflows", "ci.yml")


def load():
    r = subprocess.run(["yq", "-o=json", ".", WORKFLOW], capture_output=True, text=True, check=True)
    return json.loads(r.stdout)


WF = load()
ROUTE = next(s for s in WF["jobs"]["route"]["steps"] if s.get("id") == "route")["run"]
CI = WF["jobs"]["ci"]["steps"][0]["run"]

#: name -> (files the head changes, wanted `build`, wanted `review`)
CASES = [
    ("prose", {"README.md": "x"}, "false", "false"),
    ("nested prose", {"theories/README.md": "x"}, "false", "false"),
    ("licence", {"LICENSE": "x"}, "false", "false"),
    ("a Rocq file", {"theories/A.v": "x"}, "true", "false"),
    ("a tool", {"tools/gen_checker.py": "x"}, "true", "false"),
    ("check_assumptions.py", {".github/check_assumptions.py": "x"}, "true", "false"),
    ("test_review.py", {".github/test_review.py": "x"}, "false", "true"),
    ("test_screen.py", {".github/test_screen.py": "x"}, "false", "true"),
    ("screen.py", {".github/screen.py": "x"}, "false", "true"),
    ("review.md", {".github/review.md": "x"}, "false", "true"),
    ("review.yml", {".github/workflows/review.yml": "x"}, "false", "true"),
    ("review file and prose", {".github/screen.py": "x", "README.md": "y"}, "false", "true"),
    ("review file and a Rocq file", {".github/screen.py": "x", "theories/A.v": "y"}, "true", "true"),
    ("this workflow", {".github/workflows/ci.yml": "x"}, "true", "true"),
    ("this test", {".github/test_ci.py": "x"}, "true", "false"),
    ("a new workflow", {".github/workflows/other.yml": "x"}, "true", "false"),
    ("a name ending in md", {"theories/cmd": "x"}, "true", "false"),
    ("a lookalike of a review file", {".github/screen.pyc": "x"}, "true", "false"),
    ("a review file in a subdirectory", {"x/.github/screen.py": "x"}, "true", "false"),
    ("empty diff", {}, "true", "true"),
]


def git(cwd, *args):
    return subprocess.run(["git", "-C", cwd, *args], capture_output=True, text=True,
                          check=True).stdout.strip()


def run_route(work, env):
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "out")
        open(out, "w").close()
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", ROUTE],
                           cwd=work, env=dict(os.environ, GITHUB_OUTPUT=out, RUNNER_TEMP=tmp, **env),
                           capture_output=True, text=True)
        with open(out) as f:
            got = dict(line.split("=", 1) for line in f.read().splitlines() if "=" in line)
        return r.returncode, got, r.stdout + r.stderr


def main():
    failures = 0

    def report(ok, line, log=""):
        nonlocal failures
        failures += not ok
        print(("ok   " if ok else "FAIL ") + line + ("" if ok or not log else "\n" + log))

    with tempfile.TemporaryDirectory() as work:
        git(work, "init", "-q", "-b", "main")
        git(work, "config", "user.email", "test@example.invalid")
        git(work, "config", "user.name", "test")
        with open(os.path.join(work, "seed"), "w") as f:
            f.write("seed\n")
        git(work, "add", ".")
        git(work, "commit", "-q", "-m", "base")
        base = git(work, "rev-parse", "HEAD")
        for name, files, build, review in CASES:
            git(work, "checkout", "-q", "-B", "case", base)
            for path, text in files.items():
                full = os.path.join(work, path)
                os.makedirs(os.path.dirname(full), exist_ok=True)
                with open(full, "w") as f:
                    f.write(text)
            git(work, "add", "-A")
            git(work, "commit", "-q", "--allow-empty", "-m", name)
            rc, got, log = run_route(work, {"EVENT": "pull_request", "PR_BASE": base, "PUSH_BEFORE": ""})
            report(rc == 0 and got.get("build") == build and got.get("review") == review,
                   f"route  {name:32} build={got.get('build')} review={got.get('review')}"
                   f" (wanted {build} {review})", log)
        for name, env in [
            ("a dispatch (no base)", {"EVENT": "workflow_dispatch", "PR_BASE": "", "PUSH_BEFORE": ""}),
            ("a push of a new branch", {"EVENT": "push", "PR_BASE": "", "PUSH_BEFORE": "0" * 40}),
            ("an unknown base", {"EVENT": "pull_request", "PR_BASE": "1" * 40, "PUSH_BEFORE": ""}),
        ]:
            rc, got, log = run_route(work, env)
            report(rc == 0 and got.get("build") == "true" and got.get("review") == "true",
                   f"route  {name:32} build={got.get('build')} review={got.get('review')}"
                   " (wanted true true)", log)
        # A push of two commits counts both.
        git(work, "checkout", "-q", "-B", "case", base)
        for path in ("A.v", "README.md"):
            with open(os.path.join(work, path), "w") as f:
                f.write("x")
            git(work, "add", "-A")
            git(work, "commit", "-q", "-m", path)
        rc, got, log = run_route(work, {"EVENT": "push", "PR_BASE": "", "PUSH_BEFORE": base})
        report(rc == 0 and got.get("build") == "true" and got.get("review") == "false",
               f"route  {'a push of two commits':32} build={got.get('build')} review={got.get('review')}"
               " (wanted true false)", log)

    s, k, f, c = "success", "skipped", "failure", "cancelled"
    #: name -> (CI must pass?, the results it judges)
    aggregates = [
        ("prose only: all skipped", True, (s, "false", "false", k, k, k)),
        ("the lanes ran and passed", True, (s, "true", "false", s, s, k)),
        ("the review tests ran and passed", True, (s, "false", "true", k, k, s)),
        ("everything passed", True, (s, "true", "true", s, s, s)),
        ("review routed, failed", False, (s, "false", "true", k, k, f)),
        ("review routed, skipped", False, (s, "false", "true", k, k, k)),
        ("review routed, cancelled", False, (s, "true", "true", s, s, c)),
        ("review not routed, ran", False, (s, "false", "false", k, k, s)),
        ("lanes routed, build failed", False, (s, "true", "false", f, s, k)),
        ("lanes routed, opam skipped", False, (s, "true", "false", s, k, k)),
        ("lanes not routed, ran", False, (s, "false", "false", s, s, k)),
        ("route failed", False, (f, "", "", k, k, k)),
        ("route passed with no answer", False, (s, "", "", k, k, k)),
    ]
    names = ("ROUTE", "BUILD_ROUTED", "REVIEW_ROUTED", "BUILD", "OPAM", "REVIEW_WORKFLOW")
    for name, passes, results in aggregates:
        rc = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", CI],
                            env=dict(os.environ, **dict(zip(names, results))),
                            capture_output=True, text=True).returncode
        report((rc == 0) == passes, f"ci     {name:32} exit {rc}, wanted {'0' if passes else 'non-zero'}")

    print("\nno failures" if not failures else f"\n{failures} FAILURES")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
