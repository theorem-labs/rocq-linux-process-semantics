#!/usr/bin/env python3
"""Tests of the gate jobs of .github/workflows/ci.yml (`CI`) and .github/workflows/review-tests.yml
(`Review tests`), run as committed.

A gate is the one check to require, so a gate that passes on a failed job hides a real
failure. Each gate must run always, need every job of its workflow, and read their results.
Then its script runs against the results it must judge: it passes when every job it needs
succeeded, and fails when any one of them failed, was cancelled or was skipped.

ci.yml's `checks` job runs this file, so a change that breaks a case fails `CI`.

    python3 .github/test_ci.py        from any directory; prints each case.

No network is used. Needs python3, bash, jq and yq (mikefarah's, as GitHub's runners have).
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    r = subprocess.run(["yq", "-o=json", ".", os.path.join(HERE, "workflows", name)],
                       capture_output=True, text=True, check=True)
    return json.loads(r.stdout)


#: workflow file -> (the workflow, its gate job, the jobs its gate does not need)
WORKFLOWS = {
    # The prune job runs after the lanes, on main and this repository's pull requests, and deletes old caches.
    "ci.yml": (load("ci.yml"), "ci", {"prune"}),
    "review-tests.yml": (load("review-tests.yml"), "gate", set()),
}


def main():
    failures = 0

    def report(ok, line):
        nonlocal failures
        failures += not ok
        print(("ok   " if ok else "FAIL ") + line)

    for name, (wf, gate, aside) in WORKFLOWS.items():
        job = wf["jobs"][gate]
        want = set(wf["jobs"]) - {gate} - aside
        step = job["steps"][0]
        report(set(job["needs"]) == want and job["if"] == "always()"
               and step.get("env") == {"NEEDS": "${{ toJSON(needs) }}"},
               f"gate   {job['name']:14} needs {sorted(job['needs'])} (wanted {sorted(want)}), if {job['if']},"
               f" env {step.get('env')}")

        def judge(results):
            needs = {j: {"result": r, "outputs": {}} for j, r in results.items()}
            return subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]],
                                  env=dict(os.environ, NEEDS=json.dumps(needs)),
                                  capture_output=True, text=True).returncode

        jobs = sorted(job["needs"])
        rc = judge(dict.fromkeys(jobs, "success"))
        report(rc == 0, f"{job['name']:14} every job succeeded{'':24} exit {rc}, wanted 0")
        for other in jobs:
            for result in ("failure", "cancelled", "skipped"):
                rc = judge({j: result if j == other else "success" for j in jobs})
                report(rc != 0, f"{job['name']:14} {other + ' ' + result:43} exit {rc}, wanted non-zero")

    print("\nno failures" if not failures else f"\n{failures} FAILURES")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
