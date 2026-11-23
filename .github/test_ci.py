#!/usr/bin/env python3
"""Tests of the gate jobs of .github/workflows/ci.yml (`CI`) and .github/workflows/review-tests.yml
(`Review tests`), run as committed, and of the step whose result the gate of review-tests.yml reads for test_review.py.

A gate is the one check to require, so a gate that passes on a failed job hides a real
failure. Each gate must run always, need every job of its workflow, and read their results.
Then its script runs against the results it must judge: it passes when every job it needs
succeeded, and fails when any one of them failed, was cancelled or was skipped.

The job of test_review.py runs its tests in parallel processes (.github/parallel_tests.py). Its step runs here with
a test file of four tests in the place of test_review.py. The step must pass when no test fails. When a test fails, the
step must fail and list each test that failed, whichever process ran it, and every other test must still run.

ci.yml's `checks` job runs this file, so a change that breaks a case fails `CI`.

    python3 .github/test_ci.py        from any directory; prints each case.

No network is used. Needs python3, bash, jq and yq (mikefarah's, as GitHub's runners have).
"""
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# A test file of the tests test_a to test_d: each test whose letter the variable FAILING names fails.
SAMPLE = '''import os
import unittest


class T(unittest.TestCase):
    def check(self, letter):
        self.assertNotIn(letter, os.environ["FAILING"].split(","), "named in FAILING")

    def test_a(self):
        self.check("a")

    def test_b(self):
        self.check("b")

    def test_c(self):
        self.check("c")

    def test_d(self):
        self.check("d")


if __name__ == "__main__":
    unittest.main()
'''

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

    # The step of the job of test_review.py, run from the root of the checkout, as GitHub runs it, with SAMPLE in the
    # place of test_review.py.
    run = WORKFLOWS["review-tests.yml"][0]["jobs"]["review-workflow-review"]["steps"][-1]["run"]
    report(run.count(".github/test_review.py") == 1, f"runner the step names .github/test_review.py once: {run!r}")
    with tempfile.TemporaryDirectory(prefix="test-ci-") as folder:
        sample = os.path.join(folder, "test_sample.py")
        with open(sample, "w", encoding="utf-8") as f:
            f.write(SAMPLE)
        script = run.replace(".github/test_review.py", shlex.quote(sample))
        for failing in ("", "a,d", "d"):
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                               cwd=os.path.dirname(HERE), env=dict(os.environ, FAILING=failing),
                               capture_output=True, text=True)
            out = r.stdout + r.stderr
            want = sorted(failing.split(",")) if failing else []
            # The list after the output of the processes: each line ends with the process that ran the test.
            listed = sorted(re.findall(r"^FAIL: test_([a-d]) .*\[process [0-9]+\]$", out, re.M))
            # Each process ends with "Ran <n> tests": together they ran every test, the ones after a failure too.
            ran = sum(int(n) for n in re.findall(r"^Ran ([0-9]+) tests? in ", out, re.M))
            report((r.returncode == 0) == (not want) and listed == want and ran == 4,
                   f"runner {'failing ' + (failing or 'none'):30} exit {r.returncode}, listed {listed} (wanted {want}),"
                   f" ran {ran} of the 4 tests")

    print("\nno failures" if not failures else f"\n{failures} FAILURES")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
