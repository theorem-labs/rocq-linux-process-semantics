#!/usr/bin/env python3
"""Runs the tests of one unittest file in parallel processes, as the job of .github/test_review.py in
.github/workflows/review-tests.yml does:

    python3 .github/parallel_tests.py --processes 4 .github/test_review.py

The tests of the file go to the processes in turn, in the order in which unittest loads them, so the tests of each
class spread over all the processes. Each process runs `python3 <file> <its tests>`, as `python3 <file>` runs all of
them in one process. Each process writes its output to a file of its own, and runs each of its tests whatever the
other processes give. When a process ends, this script prints its output whole. Then it lists each test that failed or
gave an error, in all processes, and each process that ended with no summary of unittest. It exits 0 only when each
process exited 0.

The tests must not share a state: each test of test_review.py has its own temporary directory, its own copy of the
environment and its own servers on port 0, and no test changes the working directory. .github/test_ci.py tests this
script with the command of the job.
"""
import argparse
import importlib.util
import os
import re
import subprocess
import sys
import tempfile
import time
import unittest

# The line that names each test that failed, gave an error or passed against an expected failure, in the summary that
# unittest writes at the end of a run.
FAILED = re.compile(r"^(?:FAIL|ERROR|UNEXPECTED SUCCESS): .*$", re.M)
# The last line of that summary.
SUMMARY = re.compile(r"^(?:OK|FAILED)\b", re.M)


def test_ids(path):
    """The id of each test of the file at path, in the order in which unittest loads them, as `python3 <file>` takes
    an id: <class>.<method>."""
    sys.dont_write_bytecode = True
    name = os.path.splitext(os.path.basename(path))[0]
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    def flat(suite):
        for test in suite:
            if isinstance(test, unittest.TestSuite):
                yield from flat(test)
            else:
                yield test.id().split(".", 1)[1]
    return list(flat(unittest.defaultTestLoader.loadTestsFromModule(module)))


def main(argv=None):
    parser = argparse.ArgumentParser(description="Run the tests of one unittest file in parallel processes.")
    parser.add_argument("--processes", type=int, required=True, metavar="N", help="the number of processes")
    parser.add_argument("file", help="the test file, which runs the tests that its command line names")
    args = parser.parse_args(argv)
    if args.processes < 1:
        parser.error("--processes must be 1 or more")
    ids = test_ids(args.file)
    if not ids:
        print(f"{args.file} has no tests.")
        return 1
    shares = [share for share in (ids[k::args.processes] for k in range(args.processes)) if share]
    start = time.monotonic()
    failed, unfinished = [], []
    with tempfile.TemporaryDirectory(prefix="parallel-tests-") as folder:
        runs = []
        for k, share in enumerate(shares, 1):
            log = open(os.path.join(folder, f"{k}.log"), "w+", encoding="utf-8", errors="replace")
            runs.append((k, share, log, subprocess.Popen([sys.executable, args.file, *share], stdin=subprocess.DEVNULL,
                                                         stdout=log, stderr=subprocess.STDOUT)))
        for k, share, log, process in runs:
            status = process.wait()
            log.seek(0)
            out = log.read()
            log.close()
            print(f"===== Process {k} of {len(runs)}: {len(share)} tests, exit status {status} =====")
            print(out, end="" if out.endswith("\n") else "\n", flush=True)
            failed += [f"{line}   [process {k}]" for line in FAILED.findall(out)]
            if status != 0 and not SUMMARY.search(out):
                unfinished.append(f"Process {k} ended with exit status {status} before the summary of unittest. "
                                  "Its tests after the last one in its output have no result.")
    print(f"\n{len(ids)} tests in {len(runs)} processes, {time.monotonic() - start:.1f} s.")
    for line in failed + unfinished:
        print(line)
    bad = [str(k) for k, _share, _log, process in runs if process.returncode != 0]
    if bad:
        print(f"FAILED: {len(bad)} of {len(runs)} processes exited with a status that is not 0: {', '.join(bad)}.")
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
