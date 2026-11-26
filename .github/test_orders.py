#!/usr/bin/env python3
"""Every order of the jobs of two and three runs of one head, and the end state that each order must reach (OSSV-221's
architect, 2026-11-24 14:36Z and 14:42Z, for round 24 of OSSV-613; the relabel after each order of two runs, 2026-11-25
01:13Z, for round 25; the refused review, OSSV-613's architect, 2026-11-26 12:52Z, round 30, item 4; the refused review
of a writer, left out of the model, and the line that the comment job derives for a post job that died before it wrote
its output owed, 2026-11-26 20:57Z, round 30, item 4).

The jobs of a pull request that write its import check run, its label comment and its review and hold comments share
one concurrency group (write-<n>), so GitHub runs them one at a time, each whole. A run of the review workflow on HEAD
of mallory's #7 has a post job and then a comment job (its review gave a verdict, or the fresh reader refused it) or a
hold job (its screen held HEAD); an answer has a hold job alone (its screen held the author's comment). This file runs
every order of those jobs that keeps each run's post job before its own comment or hold job, each job as GitHub runs
it (test_review.run_job: its own steps against the stand-in gh, with each job seeing the comments, labels and check
runs that the jobs before it left; a later step of a job reads #7 as the steps before it left it). Before the runs, #7
holds an older review comment of HEAD that counts at no time (a pass with no marker of its read), a label comment of
the state change, the label waits-on-author, and no import check run. At the end of each order it checks:

  I1  a success stands (an import check run repo-pairs/import-approved of HEAD with the conclusion success) only when
      the newest word by read time is a pass of a run that read the author as an outsider; at a tie of read times a
      verdict, a refusal or a hold outranks a pass. One exception (OSSV-613's architect, 2026-11-26 07:36Z and 08:46Z,
      B1 of the failure sweep): a success over a pass of a run that read the kind as unknown, whose route was the
      screen, whose screen passed at HEAD and whose post job did not succeed, when the run that recorded the success
      read the author as an outsider (a relabel, or a review or a rescreen that records its own screened pass), and
      each newest word is such a pass or a pass of an outsider's read, so that no blocking, person or refused word
      stands over it. A pass under the kind unknown is no approval, so the post job of such a run withdraws (its word
      access) and records that HEAD is not approved. When that post job did not succeed, that word was never written,
      and a run that reads the author as an outsider finds a screened pass of an outside author's head, which R12 and
      the author-kind table's R approve. Outside that exception, a failure of I1 stays a failure.
  I2  the label comment says that the workflow recorded the check exactly when a success stands.
  I3  the state of the label comment is the state of the newest word (refused-review for a refusal, whoever wrote the
      item), when that word is of a run that read the author's kind (outsider or writer). A run that could not read it
      (kind unknown) changes no label, so I3 does not apply when the newest word is of such a run; I1, I2, I4 and I5
      still do.
  I4  the newest word is on the pull request at the end: its review comment (in place, from its run) or its hold
      comment. A refusal posts no comment, so one of the two carriers of its word is enough (rules.head_words): the
      line <!-- withdraw-owed HEAD refused <run> <read> --> of the label comment, with its run and its read, or an
      import check run of HEAD with the conclusion neutral whose summary names the reason refused of its run from its
      read (rules.withdrawn_by: its own withdrawal or check run of not-approved, or a withdrawal for its line). At a
      tie of two words that are not passes, one of them is enough.
  I5  no run withdraws a success that a run of a newer read recorded (a tie withdraws).
  I0  every job that runs succeeds: no order here has a failure of GitHub but the refusal of refusedline (below).

After the last job of each order of two runs, one relabel run of #7 runs (the task relabel, a run of the rescreen pass
with no screen and no model: its post job, then its comment job), as a change of the variable, a merge conflict that
went away or a person can start one. It reads the author as its true kind. A relabel gives no word of its own, so I0 to
I4 must hold after it as before it, each written R:I0 to R:I4 when it breaks only after it; and R:I5: when the order
broke no invariant before the relabel, the relabel withdraws no success that stood before it (each such success rests
on the newest word, a pass of an outsider's run). An order in which GitHub refused the write of refusedline (below)
gets no relabel: it ends with the retry.

What it runs. A word is a verdict at a read time: pass, blocking, person, held (the screen held HEAD), answer (the
screen of an answer held the author's comment), or a refused review (the fresh reader refused the review: its review
job gives the output refused=review and the verdict refused, as test_review's refused_review fills them in). A refused
review posts no comment: its post job withdraws for the reason refused (a PATCH of each success of a read at or before
its own) or records the check run of not-approved for refused, and its comment job posts no review and gives the label
comment the state refused-review. Two words are such a review. refused: its post job's writes land, so its check run
carries its word. refusedline: GitHub refuses the first write of its post job (that PATCH or that check run) at the
first attempt of its run, a 502 as the sweep's failure of a write gives it (job); its post job fails with the output
owed, and its comment job's step "Record the withdrawal of a refused review whose post job did not finish" writes the
line <!-- withdraw-owed HEAD refused <run> <read> -->, which carries its word. An order in which GitHub refused that
write ends as a hurt order of the sweep ends (below): with the retry, then the checks of a hurt order, as the workflow
leaves a refused write to the retry. A post job that dies before the step that writes its output owed (a cancel of the
sweep at "Run actions/checkout", at "Read the author-kind table" or at "Write the output owed for the withdrawal of the
import check runs") of either word leaves neither that output nor a check run, and a refused review posts no comment.
The comment job derives that output itself: its step "Record the withdrawal of a refused review whose post job did not
finish", for a post job that failed or was cancelled over a review that the fresh reader refused (its review job's
output refused=review), runs the script of the step "Record a withdrawal that the post job owes" (the two never both
run), which takes "HEAD refused" as the output owed when the post job gave none, under the conditions of the post
job's own write (its output key_set, which test_review.post_outputs fills in from the post job's env, and the table's
withdraw). So that step writes the line, and the older answer's hold job gives way to it. When that step fails or is
cancelled (the sweep fails its reads and its writes, and cancels it, after a refusal of refusedline too), the run
recorded no withdrawal that it owes, and the retry below runs the failed jobs of the run again, the post job among
them, in the place of a relabel, which could not read the refusal (held.sh refusal_unrecorded, due_rerun and
due_retry). Run 0 is a CI review (workflow_run), each other run a rescreen (workflow_dispatch), and
an answer is an answer. Each run reads the author as its true kind or as unknown (GitHub did not say), and one author
has one true kind:
  2 runs: the true kind outsider (each run reads outsider or unknown) or writer (each run reads writer or unknown, not
          both unknown, which the first already runs); each word of a run that reads outsider or unknown is one of the
          seven, and a writer's one of pass, blocking and person (a writer's item has no screen); run 1 read before,
          with or after run 0. Every combination.
  3 runs: each run reads outsider, or exactly one run reads unknown; each word one of pass, blocking, held, answer and
          refused, with at least one pass and one other word; the reads of the three in one of the patterns a<b<c,
          a=b<c, a<b=c and a=b=c, and in a group of runs with the same read, one order of their (kind, word) alone.
What it does not run (the architect's pruning of 14:42Z): 3 runs with the word person, with a writer, with two or three
unknown reads, or with no pass or only passes; 3 runs with the word refusedline, whose retry at the end of each order
would cost more than all the rest (266 combinations of 20,820 orders: about 187,000 job runs), and the sweep gives
three runs the line of a refusal (a failure of the write of the post job of refused, or a cancel of it); a refused
review of a writer, which has no carrier and no invariant here (OSSV-613's architect, 2026-11-26 20:57Z, round 30, item
4, ruling (1), choice (b)): the author-kind table gives a writer no state label and no import record, so no approval can
stand on a writer's head, and the missing carrier fails closed. Its post job records no check run of not-approved and
owes no withdrawal, so that neither a check run nor a line carries its word (rules.head_words); test_review's
test_a_writers_refused_review_writes_no_line_and_no_check_run pins that as a rule, so that the exclusion is a stated
one. (A writer's post job that dies before it finishes its withdrawal leaves the output owed, as the post job's step
writes it for each author, and the comment job derives it for each author alike; no order here runs it.) Also not run:
any failure of GitHub but the one of refusedline and the
one of the failure sweep (below); relabels, catch-ups, approvals and runs by hand; more than one head; a run's re-run
attempt but the re-run of the failed jobs of a run that the retry starts. The sweep runs under ORDERS_FAILURES=1
alone.

That is 1,285 combinations: 741 of 2 runs (3,912 orders, 11,550 job runs, and after each order a relabel of 2 job runs,
or for the 972 orders of refusedline the retry, about 6 job runs (RETRY_COST): 23,262 job runs) and 544 of 3 runs
(35,598 orders, 106,551 job runs; the orders of one combination share their first jobs). The 538 combinations with a
refused word (324 of 2 runs, 214 of 3) come after the 747 of before round 30, which keep their indexes. Each
combination is one test method, which runs every order of its jobs. ORDERS_SHARD=<k>/<n> (0 <= k < n) keeps the
methods of shard k of n, for a matrix of review-tests.yml: the shards share the job runs of the plain orders about
equally (shard_of), so that each of the 60 shards of review-tests.yml ends in under 10 minutes (OSSV-613's architect,
2026-11-26 02:25Z; 60 for the 129,813 job runs of the 1,285 combinations, 1.9 times those of the 747). Run it as
python3 .github/parallel_tests.py --processes 4 .github/test_orders.py.

The failure sweep (OSSV-613, round 29, item 3). ORDERS_FAILURES=1 runs it in each test method, in the place of its
plain orders: the walk still runs the jobs of each plain order, but it checks no plain order. review-tests.yml never
sets the switch: the sweep runs on the build cluster. Each order runs again with one failure of GitHub in one of its
jobs, which starts from the state that the plain walk reached before that job. A failure is one of three kinds. In a
read, the n-th read of GitHub that the job makes fails as a 502 does. In a write, the n-th write of the job fails so,
and it does not land. In a cancel, a cancel of the job ends a step that it ran: that step is cancelled, the steps after
it are skipped, and the step whose if is failure() || cancelled() runs. The stand-in gh counts the reads and the
writes of a job across its steps, in the order in which the job makes them (FAKE_GH, $FAKE_GH/inject). Of two runs,
each read, each write and each step that ran of each job of each order fails in turn. Of three runs, each job of each
order gets one failure: at each node of the walk that reaches a job of a run, the next item of the list of that job
(its reads, then its writes, then its steps) fails, so that over the orders each item fails in some order. No failure
falls in the relabel after an order of two runs, and that relabel does not run after a hurt order.

The retry. A failure that ended no job (the job went on after the failed call) gets none. Else, after the last job of
the order, the rescreen pass runs (test_review.schedule), as it runs an hour or more after each run ended. It reads
what GitHub would give then: the open pull request #7 with the labels, the comments and the check runs that the order
left, and mallory's comment 77 that an answer answers; mallory's permission of the true kind (none for an outsider,
write for a writer); one CI run of HEAD that ended, and no held run; and review.yml's runs that ran a job, a lower id
made earlier, each made and ended over an hour ago, with its name, its newest attempt and its jobs. Then the jobs of
what the pass started run, against what the plain jobs read. A relabel runs its post job and its comment job (runs
900, 901 and on). A re-run of the failed jobs of a run runs again each job of that run whose newest result is failure
or cancelled, at the next attempt (the post job of a refused review that did not finish, too). A stop runs its trust
job, which reads what the pass read, and its comment job
(test_review.write_stop). The pass runs again until it starts nothing, REVIEW_TRIES + 2 times at most.

The checks at the end of a hurt order, after its retry: I1, I2, I3 and I5 as above; I4, or the newest label comment
names Sami's step (the step of a state whose label is waits-on-theorem, but refused-review, the state of a refusal
itself, which only its line or its check run carries); and I0 for each job but the one that the failure ended. Four
more findings come from the retry. PASS: a pass fails and starts no stop (each stop fails its pass). RETRY: the last
pass still starts something. START <task>: a pass starts a run that the sweep does not model (a review, a rescreen, an
approval, a catch-up). An answer that a pass starts is modelled: a new answer run of comment 77 whose screen holds it
again, read now, so its word, answer, is the newest one. STOP: the trust job of a stop does not take it. Each finding
fails the test method. With ORDERS_REPORT=<dir>, each test method appends to <dir>/<pid>.jsonl one line for each
finding of a job, a kind of failure and a site, with its count of orders and its first order, and one line of its
counts: the failures of each kind, the hurt orders (leaves; unchanged: those whose failure changed nothing, which are
plain orders and run no further; excepted: those that the one exception to I3 below covers), the passes, the seconds,
and sites, each site that a failure of the sweep hit as
{job, task, kind, site, count}: site is the text where of a finding's line ("<step> | <METHOD endpoint>" of a read or
a write, "no <kind> <n> in the job" when the job made no such call, or the step of a cancel), and count the failures
of the sweep there. Two hurt worlds of one shape (the same text but for the times, of which only the order counts)
share the jobs, the passes and the checks after them. The sweep does not run two failures in one order (but in an
order of refusedline, whose refused write is one of its plain orders), a failure in a job of the retry, in the trust,
gather, screen or review job, or in the pass.

One exception to I3 (OSSV-613's architect, 2026-11-26 22:30Z, round 30, item 4): a hurt order of refusedline whose
refused run's comment job is cancelled at its first step, "Run actions/checkout", so before its step "Record the
withdrawal of a refused review whose post job did not finish" runs (excepted, below). It needs two independent
failures of GitHub, the refused write that the order of refusedline spends and the death of the comment job before
that step, and it fails closed: no line, no check run and no comment carries the refusal, so no App write follows and
no import check run records a success over it, and the label comment sends the item to Sami, though to the wrong step
(after-hold, not the step of a refusal), until the next run of the head. The pass cannot tell that comment job from
one that had no step to run (it cannot read the verdict of a job), so its retry starts a relabel, which cannot read
the refusal. The field excepted of the counts line gives the number of hurt orders that the exception covers, so that
the sweep of record shows no finding outside it. It is that narrow: any other failure of I3, at any other site, in any
other combination, or any other invariant at that site, stays a finding. test_refusedline_with_the_comment_job_
cancelled_at_its_checkout_records_no_success pins the end of those orders (in shard 0 alone).
"""

import copy
import datetime
import itertools
import json
import os
import re
import sys
import time
import unittest

import test_review as T
from test_review import BOT, BRANCH, FORK_ID, HEAD, JOBS, REPO, WF, ago, evaluate, filled, gh_calls, gh_inputs, \
    post_outputs, review_of, rules, run_job, run_name, writes

WORDS = ("pass", "blocking", "person", "held", "answer", "refused", "refusedline")
# A writer's review that the fresh reader refused has no carrier and no invariant here (OSSV-613's architect,
# 2026-11-26 20:57Z, round 30, item 4, ruling (1), choice (b)): the author-kind table gives a writer no state label and
# no import record, so no approval can stand on a writer's head, and the missing carrier fails closed. The post job of a
# writer's run records no check run of not-approved, and no withdrawal of its own stands to be refused, so neither a
# check run nor a line gives its word (rules.head_words); test_review pins that. So a writer's run has no refused word
# here.
WRITER_WORDS = ("pass", "blocking", "person")
THREE_WORDS = ("pass", "blocking", "held", "answer", "refused")
# The words of a review that the fresh reader refused (the verdict refused): refused, whose post job's writes land, so
# that its check run carries its word, and refusedline, whose post job's first write GitHub refuses at the first
# attempt of its run, so that its withdraw-owed line carries it (the module's text).
REFUSED = ("refused", "refusedline")
RECORDED = "The workflow recorded the check `repo-pairs/import-approved`"
# The run of the relabel after each order of two runs.
RELABEL = {"id": "900", "task": "relabel", "kind": "", "word": "", "minutes": 0}
# The state of a label comment by its next step: each state's own step, and the steps that the state decide takes from
# the import (rules.import_steps). The states screen and after-hold share a step.
STEPS = {}
for _state, (_label, _step, _text) in rules.STATES.items():
    STEPS.setdefault(_step, set()).add(_state)
for _step in (rules.APPROVE, rules.COPY, rules.REVIEW_AGAIN):
    STEPS.setdefault(_step, set()).add("decide")
NAME = "repo-pairs/import-approved"
# The failure sweep (the module's text): ORDERS_FAILURES=1 runs it in the place of the plain orders, and ORDERS_REPORT
# names the directory of its report lines.
FAILURES = os.environ.get("ORDERS_FAILURES") == "1"
REPORT = os.environ.get("ORDERS_REPORT")
TRIES = int(WF["env"]["REVIEW_TRIES"])
# The files in which the stand-in gh records its calls and its injection (FAKE_GH): no part of what GitHub serves.
RECORDS = {"calls", "args", "inputs", "tokens", "sleeps", "inject", "inject.read", "inject.write", "injected"}
TIME = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z")


def result_of(outcomes):
    """A job's result as GitHub gives it from the outcomes of its steps: cancelled when a step was cancelled, else
    failure when a step failed, else success."""
    values = set(outcomes.values())
    return "cancelled" if "cancelled" in values else "failure" if "failure" in values else "success"


def run_specs(runs):
    """runs: (kind, word, rank) of each run, rank 0 the oldest read. The runs as dicts: id, task, kind, word, read."""
    found = []
    for i, (kind, word, rank) in enumerate(runs):
        task = "answer" if word == "answer" else "review" if i == 0 else "rescreen"
        found.append({"id": str(100 + 10 * i), "task": task, "kind": kind, "word": word, "minutes": 40 - 10 * rank})
    return found


def combinations():
    """Each combination that this file runs, in a fixed order: a tuple of (kind, word, rank) per run. The combinations
    with a word of REFUSED come after the others, so that each other combination keeps the index (and the name of its
    test method) that it had before the refused words (OSSV-613, round 30, item 4)."""
    found = []
    for true in ("outsider", "writer"):
        for kinds in itertools.product((true, "unknown"), repeat=2):
            if kinds == ("unknown", "unknown") and true == "writer":
                continue
            for words in itertools.product(*[WRITER_WORDS if k == "writer" else WORDS for k in kinds]):
                for ranks in ((0, 0), (0, 1), (1, 0)):
                    found.append(tuple(zip(kinds, words, ranks)))
    patterns = ((0, 1, 2), (0, 0, 1), (0, 1, 1), (0, 0, 0))
    kind_sets = [("outsider",) * 3] + [tuple("unknown" if i == p else "outsider" for i in range(3)) for p in range(3)]
    for kinds in kind_sets:
        for words in itertools.product(THREE_WORDS, repeat=3):
            if "pass" not in words or set(words) == {"pass"}:
                continue
            for ranks in patterns:
                runs = tuple(zip(kinds, words, ranks))
                if any(ranks[i] == ranks[j] and runs[i][:2] > runs[j][:2] for i in range(3) for j in range(i + 1, 3)):
                    continue
                found.append(runs)
    found.sort(key=lambda runs: any(word in REFUSED for _kind, word, _rank in runs))
    return found


def jobs_of(run):
    """The jobs of run, in the order that its own needs keep."""
    if run["word"] == "answer":
        return [("hold", run["id"])]
    return [("post", run["id"]), ("hold" if run["word"] == "held" else "comment", run["id"])]


def interleavings(runs):
    """Each order of the jobs of runs that keeps each run's own jobs in their order, as a tree: a list of
    (job, subtree)."""
    def tree(left):
        return [((left[i][0]), tree(left[:i] + [left[i][1:]] + left[i + 1:] if len(left[i]) > 1
                                    else left[:i] + left[i + 1:]))
                for i in range(len(left))]
    return tree([jobs_of(r) for r in runs])


class OrderTest(T.ReaderRunner):
    """I0 to I5 at the end of every order of the jobs of each combination (the module's text)."""

    RUN_TOKEN = T.ImportCheckTest.RUN_TOKEN
    TOKENS = T.ImportCheckTest.TOKENS
    LPS = T.ImportCheckTest.LPS
    AnyToken = T.ImportCheckTest.AnyToken
    applied_checks = T.ImportCheckTest.applied_checks
    successes = staticmethod(T.ImportCheckTest.successes)
    maxDiff = None

    def setUp(self):
        super().setUp()
        self.live = None
        # The failure sweep's injection (job): whether it is armed, and the script of the step whose call it failed.
        self.armed, self.hit = False, None
        # The rescreen passes that a retry ran (retry): of the sweep, or of a plain order of refusedline.
        self.passes = 0
        self.serve(f"repos/{REPO}/check-runs", {"id": 901})
        self.serve(f"repos/{REPO}/labels", {"name": T.THEOREM_LABEL})
        self.serve(f"repos/{REPO}/issues/7/labels/review-held", [])

    # --- the world: #7 as the API lists it ----------------------------------------------------------------------------

    def world(self):
        """#7 before the runs: an older review comment of HEAD that counts at no time (a pass with no marker of its
        read), a label comment of the state change, the label waits-on-author, and no check run."""
        return {"comments": [review_of(HEAD, at=ago(70), run=60),
                             {"id": 40, "user": {"login": BOT}, "created_at": ago(70), "updated_at": ago(70),
                              "body": rules.label_comment("change")}],
                "labels": ["waits-on-author"], "checks": [], "next": 50, "posts": {}, "withdrawals": [], "failed": [],
                "hurt": [], "jobs": {}, "makers": {}}

    def serve_world(self, w, run, attempt=1):
        """GitHub's answers while #7 is w, for a job of run at its attempt attempt."""
        self.serve(f"repos/{REPO}/pulls/7/files", [{"filename": "README.md", "previous_filename": None}])
        self.serve(f"repos/{REPO}/pulls/7", {"number": 7, "head": {"sha": HEAD}, "changed_files": 1})
        self.serve(f"repos/{REPO}/pulls/7/reviews", [])
        self.serve(f"repos/{REPO}/issues/7", {"number": 7, "pull_request": {}, "user": {"login": "mallory"}})
        self.serve(f"repos/{REPO}/issues/7/comments", copy.deepcopy(w["comments"]))
        for c in w["comments"] + [{"id": w["next"]}]:
            self.serve(f"repos/{REPO}/issues/comments/{c['id']}",
                       {"id": c["id"], "html_url": f"https://github.com/{REPO}/pull/7#c{c['id']}"})
        self.serve(f"repos/{REPO}/issues/7/labels", [{"name": n} for n in w["labels"]])
        self.serve(f"repos/{REPO}/commits/{HEAD}/check-runs", {"check_runs": copy.deepcopy(w["checks"])})
        for check in w["checks"]:
            self.serve(f"repos/{REPO}/check-runs/{check['id']}", {"id": check["id"], "conclusion": check["conclusion"]})
        self.serve(f"repos/{REPO}/check-runs", {"id": 901 + len(w["checks"])})
        # The jobs of each run as GitHub lists them once they ran, each step ended when its job ran (line_written): the
        # newest attempt of each job.
        for rid, jobs in w["jobs"].items():
            newest = {name: (outcomes, at, n) for name, outcomes, at, n in jobs}
            self.serve(f"repos/{REPO}/actions/runs/{rid}/jobs", {"total_count": len(newest), "jobs": [
                {"name": name, "run_id": int(rid), "run_attempt": n, "status": "completed",
                 "conclusion": result_of(outcomes),
                 "steps": [{"name": s, "status": "completed", "conclusion": c, "started_at": at, "completed_at": at}
                           for s, c in outcomes.items()]} for name, (outcomes, at, n) in newest.items()]})
        self.serve(f"repos/{REPO}/actions/runs/{run['id']}/attempts/{attempt}/jobs",
                   {"jobs": [T.attempt_job("trust"), T.attempt_job("gather"),
                             T.attempt_job("screen", name="screen mallory")]})

    def read(self, run):
        """The time when the trust job of run read #7: run's minutes before the start of this combination, so that two
        runs with the same minutes read at the same second."""
        return (self.start - datetime.timedelta(minutes=run["minutes"])).strftime("%Y-%m-%dT%H:%M:%SZ")

    def trust(self, run):
        """The trust job's outputs of run."""
        kind = run["kind"]
        if run["task"] == "relabel":
            return {"task": "relabel", "route": "review", "outsider": "" if kind == "writer" else "mallory",
                    "outside": "true" if kind == "outsider" else "false", "kind": kind, "number": "7", "head": HEAD,
                    "named": HEAD, "started": self.read(run), "account": "", "origin": "", "tries": "0", "comment": ""}
        return {"task": run["task"], "route": "review" if kind == "writer" else "screen",
                "outsider": "" if kind == "writer" else "mallory", "outside": "true" if kind == "outsider" else "false",
                "kind": kind, "number": "7", "head": HEAD, "named": HEAD, "started": self.read(run),
                "account": "mallory", "origin": "", "tries": "0", "comment": "77" if run["task"] == "answer" else ""}

    def contexts(self, run, trust, post, attempt=1):
        """The contexts that GitHub gives each job of run at its attempt attempt: its trust job's outputs, its event,
        and its post job's result and outputs (post; the post job of an answer is skipped). The review job of a word of
        REFUSED gives the outputs that test_review's refused_review fills in: its comment step gives the head and
        refused=review alone, so the job's output verdict is refused and its body is empty."""
        event = "workflow_dispatch" if run["task"] == "rescreen" else "workflow_run"
        ctx = {f"needs.trust.outputs.{k}": v for k, v in trust.items()}
        ctx.update({"github.event_name": event, "github.ref": "refs/heads/main", "github.repository": REPO,
                    "github.token": self.RUN_TOKEN, "github.run_id": run["id"], "github.run_attempt": str(attempt),
                    "vars.REPO_PAIRS_IMPORT_PATHS": self.LPS, "env.POST_REVIEW": WF["env"]["POST_REVIEW"],
                    "needs.trust.result": "success", "needs.gather.result": "success",
                    "needs.gather.outputs.kind": "pr", "needs.gather.outputs.outside": trust["outside"]})
        screened = trust["route"] == "screen"
        held = run["word"] in ("held", "answer")
        if held:
            outputs = {"head": "", "verdict": "", "body": "", "refused": ""}
        elif run["word"] in REFUSED:
            outputs = filled({k: JOBS["review"]["outputs"][k] for k in ("head", "verdict", "body", "refused")},
                             {"steps.result.outputs.head": HEAD, "steps.result.outputs.refused": "review"})
        else:
            review = review_of(HEAD, run["word"], at=ago(0), run=int(run["id"]), read=trust["started"],
                               screened=screened)
            outputs = {"head": HEAD, "verdict": run["word"], "body": review["body"], "refused": ""}
        ctx.update({"needs.screen.result": "success" if screened else "skipped",
                    "needs.screen.outputs.verdict": ("held" if held else "clean") if screened else "",
                    "needs.review.result": "skipped" if held else "success",
                    **{f"needs.review.outputs.{k}": v for k, v in outputs.items()},
                    "needs.review.outputs.will_fix": "false", "needs.review.outputs.fix_stop": "false"})
        if run["task"] == "relabel":
            ctx.update({"github.event_name": "workflow_dispatch", "needs.gather.result": "skipped",
                        "needs.screen.result": "skipped", "needs.review.result": "skipped",
                        "needs.gather.outputs.kind": "", "needs.screen.outputs.verdict": "",
                        "needs.review.outputs.verdict": "", "needs.review.outputs.head": "",
                        "needs.review.outputs.body": ""})
        if post is not None:
            ctx.update({"needs.post.result": post["result"],
                        **{f"needs.post.outputs.{k}": v for k, v in post["post"].items()}})
        return ctx

    def job(self, name, run, w, site=None, attempt=1):
        """w after the job name of run, as GitHub runs it while #7 is w, at the attempt attempt of run
        (github.run_attempt). site is a failure of GitHub in the job (the failure sweep): ("read", n) or ("write", n),
        the n-th read or write of GitHub that the job makes fails (FAKE_GH's injection); ("cancel", <step>), a cancel
        of the job ends that step; ("none", 0) only counts the reads and the writes; None injects and counts nothing.
        The post job of a run of the word refusedline at attempt 1 with no other site fails at its first write, as
        ("write", 1) does (the module's text): that write is the App's withdrawal of a success or its check run of
        not-approved, and the job makes no call after it. A failure or a cancel that ends the job goes to w["hurt"],
        any other failure to w["failed"]. After the job, self.sites is each site of it for ("none", 0): each read, each
        write and each step that ran, in that order; and self.where says where the failure of a site hit: "<step> |
        <METHOD endpoint>", or the step of a cancel."""
        w = copy.deepcopy(w)
        trust = w["posts"].setdefault("trust " + run["id"], self.trust(run))
        post = None if name == "post" else w["posts"].get(run["id"], {"result": "skipped", "post": {}})
        ctx = self.contexts(run, trust, post, attempt)
        self.serve_world(w, run, attempt)
        self.forget()
        self.logs = []
        open(self.summary, "w").close()
        self.env["GITHUB_STEP_SUMMARY"] = self.summary
        self.sites, self.where = [], ""
        if not evaluate(JOBS[name]["if"], ctx):
            if name == "post":
                w["posts"][run["id"]] = {"result": "skipped", "post": {}}
            return w
        tokens = self.TOKENS if name == "post" else self.AnyToken(self.TOKENS)
        kind, n = site or (None, None)
        counting = kind == "none"
        refusal = name == "post" and run["word"] == "refusedline" and attempt == 1 and kind in (None, "none")
        if refusal:
            kind, n = "write", 1
        if kind in ("none", "read", "write"):
            for record in ("inject.read", "inject.write", "injected"):
                if os.path.exists(os.path.join(self.api, record)):
                    os.remove(os.path.join(self.api, record))
            with open(os.path.join(self.api, "inject"), "w") as f:
                f.write(f"{kind} {n}\n")
            self.armed, self.hit = True, None
        known = {c["id"] for c in w["checks"]}
        self.live = (w, run, attempt)
        try:
            outcomes = run_job(self, name, ctx, tokens, cancel=n if kind == "cancel" else None)
        finally:
            self.live = None
            if self.armed:
                os.remove(os.path.join(self.api, "inject"))
                self.armed = False
        if counting:
            reads, wrote = (int(self.stand_in(f"inject.{k}") or 0) for k in ("read", "write"))
            self.sites = ([("read", i) for i in range(1, reads + 1)] + [("write", i) for i in range(1, wrote + 1)]
                          + [("cancel", s) for s, outcome in outcomes.items() if outcome != "skipped"])
        if kind == "cancel":
            self.where = n
        elif kind in ("read", "write"):
            call = self.stand_in("injected").partition(" ")[2].strip() or f"no {kind} {n} in the job"
            hit = next((s.get("name") or "Run " + s["uses"].split("@")[0] for s in JOBS[name]["steps"]
                        if self.hit is not None and s.get("run") == self.hit), "-")
            self.where = f"{hit} | {call}"
            if refusal and self.stand_in("injected") and not re.fullmatch(
                    rf"(PATCH|POST) repos/{re.escape(REPO)}/check-runs(/[1-9][0-9]*)?", call):
                self.fail(f"the first write of the post job of run {run['id']} ({run['word']}) is no App write of a "
                          f"check run: {self.where}")
        self.record(w, name, run, outcomes, ctx, attempt, hurt=kind in ("read", "write", "cancel"))
        # The run that recorded each success, by its task and the kind it read (I1's exception).
        w["makers"].update({str(c["id"]): [run["task"], run["kind"]] for c in w["checks"]
                            if c["id"] not in known and c.get("conclusion") == "success"})
        return w

    def stand_in(self, record):
        """The text of the stand-in gh's file record (RECORDS), empty when there is none."""
        path = os.path.join(self.api, record)
        if not os.path.exists(path):
            return ""
        with open(path, encoding="utf-8") as f:
            return f.read()

    def record(self, w, name, run, outcomes, ctx, attempt, hurt=False):
        """w after the job name of run ran with outcomes at the attempt attempt in the contexts ctx: its jobs, its
        failures (w["hurt"] for the job that the failure of a site ended), and the result and outputs of a post job."""
        w["jobs"].setdefault(run["id"], []).append((name, outcomes, ago(0), attempt))
        result = result_of(outcomes)
        if result != "success":
            w["hurt" if hurt else "failed"].append(
                f"{name} of run {run['id']}: {[k for k, v in outcomes.items() if v in ('failure', 'cancelled')]} "
                f"{self.logs[-1][-300:] if self.logs else ''}")
        if name == "post":
            w["posts"][run["id"]] = {"result": result, "post": post_outputs(ctx)}

    def run_script(self, script, **env):
        """Runner.run_script, and then, in a job (live), GitHub's answers change with the writes of the step: a later
        step of the job reads #7 as this step left it, as it does on GitHub. While the injection is armed (job), the
        script whose call failed is self.hit."""
        found = super().run_script(script, **env)
        if self.armed and self.hit is None and os.path.exists(os.path.join(self.api, "injected")):
            self.hit = script
        if getattr(self, "live", None):
            w, run, attempt = self.live
            self.apply(w, run)
            self.serve_world(w, run, attempt)
            self.forget()
        return found

    def apply(self, w, run):
        """w after the writes that the stand-in gh saw since it last forgot, as GitHub applies them."""
        before = {c["id"]: c for c in w["checks"]}
        for call, body in zip([c for c in gh_calls(self.api) if "--input" in c], gh_inputs(self.api)):
            endpoint = next((a for a in call if a.startswith(f"repos/{REPO}/check-runs/")), "")
            if "PATCH" in call and endpoint and body.get("conclusion") == "neutral":
                w["withdrawals"].append((run["id"], int(endpoint.rsplit("/", 1)[1]), before.get(
                    int(endpoint.rsplit("/", 1)[1]))))
        w["checks"] = self.applied_checks(w["checks"])
        for call in writes(self.api):
            args, method, endpoint, fields = list(call), "", "", []
            while args:
                a = args.pop(0)
                if a == "--method":
                    method = args.pop(0)
                elif a in ("-f", "-F"):
                    fields.append(args.pop(0))
                elif a in ("--jq", "--input", "-H"):
                    args.pop(0)
                elif not a.startswith("--"):
                    endpoint = a.split("?")[0]
            method = method or "POST"
            body = next((f[len("body="):] for f in fields if f.startswith("body=")), None)
            now = ago(0)
            if endpoint == f"repos/{REPO}/issues/7/comments" and method == "POST" and body is not None:
                w["comments"].append({"id": w["next"], "user": {"login": BOT}, "created_at": now, "updated_at": now,
                                      "body": body})
                w["next"] += 1
            elif endpoint.startswith(f"repos/{REPO}/issues/comments/"):
                cid = int(endpoint.rsplit("/", 1)[1])
                if method == "DELETE":
                    w["comments"] = [c for c in w["comments"] if c["id"] != cid]
                elif body is not None:
                    w["comments"] = [dict(c, body=body, updated_at=now) if c["id"] == cid else c for c in w["comments"]]
            elif endpoint == f"repos/{REPO}/issues/7/labels" and method == "POST":
                for f in fields:
                    if f.startswith("labels[]=") and f[len("labels[]="):] not in w["labels"]:
                        w["labels"].append(f[len("labels[]="):])
            elif endpoint.startswith(f"repos/{REPO}/issues/7/labels/") and method == "DELETE":
                w["labels"] = [n for n in w["labels"] if n != endpoint.rsplit("/", 1)[1]]

    # --- the end state ---------------------------------------------------------------------------------------------

    @staticmethod
    def newest(runs):
        """The newest words of runs: the newest read, and at a tie of reads the words that are not passes."""
        top = min(r["minutes"] for r in runs)
        tied = [r for r in runs if r["minutes"] == top]
        return [r for r in tied if r["word"] != "pass"] or tied

    @staticmethod
    def state_of(run, success):
        """The state of the label comment that the word of run gives, for a run that read the author's kind. A refused
        review gives refused-review (rules.label_state reads the fact refused before the verdict)."""
        if run["word"] in REFUSED:
            return "refused-review"
        if run["kind"] == "writer":
            return "reviewed"
        return {"pass": "import" if success else "decide", "blocking": "change", "person": "person",
                "held": "screen", "answer": "screen"}[run["word"]]

    def on_the_item(self, run, w):
        """Whether the word of run is on #7 in w: its review comment, or its hold comment. A refused review posts no
        comment, so its word is on #7 when one of its two carriers is (rules.head_words): the line
        <!-- withdraw-owed HEAD refused <run> <read> --> of a label comment (rules.OWED), or an import check run of HEAD
        with the conclusion neutral whose summary names the reason refused of run from its read (rules.withdrawn_by: a
        withdrawal or a check run of not-approved of run itself, or a withdrawal by another run for run's line)."""
        if run["word"] in REFUSED:
            word = ("refused", run["id"], self.read(run))
            lines = [rules.OWED.fullmatch(line) for c in w["comments"] if c["body"].startswith(rules.FIRST)
                     for line in c["body"].split("\n")]
            return (any(m and m.groups() == (HEAD, *word) for m in lines)
                    or any(c.get("name") == NAME and rules.withdrawn_by(c, HEAD) == word for c in w["checks"]))
        for c in w["comments"]:
            body = c["body"]
            if run["word"] in ("held", "answer"):
                if body.startswith("<!-- review-held -->") and rules.hold_fact(body) == "screen_held":
                    h, r = rules.HELD_HEAD.search(body), rules.HELD_RUN.search(body)
                    if h and r and h.group(1) == HEAD and r.group(1) == run["id"]:
                        return True
            else:
                m = rules.REVIEWED.match(body)
                r = rules.REVIEW_RUN.match(body, m.end()) if m else None
                if m and r and m.group(1) == HEAD and m.group(2) == run["word"] and r.group(1) == run["id"]:
                    return True
        return False

    def broken(self, runs, w):
        """The invariants that w, the end of an order, breaks, each with what breaks it."""
        found = []
        if w["failed"]:
            found.append(("I0", w["failed"]))
        success = [c for c in w["checks"] if c.get("name") == NAME and c.get("conclusion") == "success"]
        newest = self.newest(runs)
        if success and not all(r["word"] == "pass" and r["kind"] == "outsider" for r in newest):
            # The exception of I1 (the module's text): each newest word is a pass of an outsider's read, or of a read
            # of the kind unknown on the route screen with a screen that passed (trust, contexts) and a post job that
            # did not succeed (its word access was never written); and a run that read the author as an outsider
            # recorded each success.
            def lost(r):
                return (r["kind"] == "unknown" and self.trust(r)["route"] == "screen"
                        and w["posts"].get(r["id"], {}).get("result") != "success")
            passes = all(r["word"] == "pass" and (r["kind"] == "outsider" or lost(r)) for r in newest)
            outsiders = all((w["makers"].get(str(c["id"])) or [None, None])[1] == "outsider" for c in success)
            if not (passes and outsiders):
                found.append(("I1", [c["id"] for c in success]))
        labels = [c for c in w["comments"] if c["body"].startswith(rules.FIRST)]
        label = labels[-1]["body"] if labels else ""
        if (RECORDED in label) != bool(success):
            found.append(("I2", (RECORDED in label, [c["id"] for c in success])))
        if all(r["kind"] != "unknown" for r in newest):
            step = next((line[len("**Next step:** "):] for line in label.split("\n")
                         if line.startswith("**Next step:** ")), "")
            states = STEPS.get(step, set())
            want = {self.state_of(r, bool(success)) for r in newest}
            if not states & want:
                found.append(("I3", (sorted(states), sorted(want))))
        if not any(self.on_the_item(r, w) for r in newest):
            found.append(("I4", [r["id"] for r in newest]))
        reads = {r["id"]: self.read(r) for r in runs}
        for run_id, cid, check in w["withdrawals"]:
            record = rules.recorded_by(check) if check else None
            if run_id in reads and record and record[1] and reads[run_id] < record[1]:
                found.append(("I5", (run_id, cid, record)))
        return found

    def check_orders(self, combination):
        """Every order of the jobs of combination, each from the world before the runs: no invariant breaks. An order
        in which GitHub refused the first write of the post job of a run of refusedline (job; w["hurt"]) ends as a hurt
        order of the sweep ends (hurt_end), with no relabel after it, and two such ends of one shape share it."""
        runs = run_specs(combination)
        self.start = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
        by_id = {r["id"]: r for r in runs}
        failures, ends = [], {}

        relabel = dict(RELABEL, kind="writer" if any(r["kind"] == "writer" for r in runs) else "outsider")

        def walk(tree, w, order):
            if not tree and w["hurt"]:
                key = self.shape(w)
                if key not in ends:
                    ends[key] = self.hurt_end(runs, by_id, w)
                done, broke = ends[key]
                failures.extend((order + done, b) for b in broke)
                return
            if not tree:
                before = self.broken(runs, w)
                failures.extend((order, b) for b in before)
                if len(runs) == 2:
                    after = self.job("comment", relabel, self.job("post", relabel, w))
                    names = {b[0] for b in before}
                    failures.extend((order + ["relabel"], ("R:" + b[0], b[1]))
                                    for b in self.broken(runs, after) if b[0] not in names)
                    stood = {c["id"] for c in w["checks"] if c.get("name") == NAME and c.get("conclusion") == "success"}
                    taken = [cid for rid, cid, _check in after["withdrawals"] if rid == relabel["id"] and cid in stood]
                    if not before and taken:
                        failures.append((order + ["relabel"], ("R:I5", taken)))
                return
            for (name, rid), sub in tree:
                walk(sub, self.job(name, by_id[rid], w), order + [f"{name} {rid}"])

        walk(interleavings(runs), self.world(), [])
        names = sorted({b[0] for _o, b in failures})
        self.assertEqual(failures, [], f"{','.join(names)} in {len({tuple(o) for o, _b in failures})} orders of "
                                       f"{describe(runs)}: {failures[:3]}")

    # --- the failure sweep (ORDERS_FAILURES) ------------------------------------------------------------------------

    def sweep(self, combination):
        """The failure sweep of combination (the module's text): each order again with one failure of GitHub in one of
        its jobs, which starts from the plain walk's state before that job, then the rescreen pass's retry and the
        checks at the end of the hurt order. Of two runs, every site of every job of every order fails in turn; of
        three runs, one site of each job of each order, in turn (self.sites). Each broken invariant fails the test,
        and ORDERS_REPORT gets a line of each, and a line of the counts, with each site that failed and its count. The
        walk shares the first jobs of the orders, and two worlds of one shape (shape) share what comes after them. A
        failure changed nothing when it ended no job that the plain job did not end (the refusal of refusedline ends
        its post job in the plain walk too) and the world after it has the shape of the world after the plain job."""
        runs = run_specs(combination)
        self.start = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
        by_id = {r["id"]: r for r in runs}
        began, self.passes = time.monotonic(), 0
        ran, turns, found, memo, failed = {"read": 0, "write": 0, "cancel": 0}, {}, {}, {}, {}
        counts = {"leaves": 0, "unchanged": 0, "excepted": 0}

        def below(tree, w):
            """Each order of the jobs of tree from w, with no failure: (its jobs and its retry, what broke at its
            end)."""
            key = (id(tree) if tree else None, self.shape(w))
            if key not in memo:
                memo[key] = ([self.hurt_end(runs, by_id, w)] if not tree else
                             [([f"{name} {rid}"] + jobs, broke) for (name, rid), sub in tree
                              for jobs, broke in below(sub, self.job(name, by_id[rid], w))])
            return memo[key]

        def walk(tree, w, order):
            for (name, rid), sub in tree:
                run = by_id[rid]
                plain = self.job(name, run, w, site=("none", 0))
                sites, same = self.sites, None
                if len(runs) == 3 and sites:
                    turn = turns.get((name, rid), 0)
                    turns[(name, rid)] = turn + 1
                    sites = [sites[turn % len(sites)]]
                for site in sites:
                    hurt = self.job(name, run, w, site=site)
                    ran[site[0]] += 1
                    where, hurt_order = self.where, order + [f"{name} {rid} {site[0]} {site[1]}"]
                    at = (name, run["task"], site[0], where)
                    failed[at] = failed.get(at, 0) + 1
                    if len(hurt["hurt"]) == len(plain["hurt"]):
                        same = self.shape(plain) if same is None else same
                        if self.shape(hurt) == same:
                            # The failure changed nothing: each order below is a plain one.
                            counts["unchanged"] += leaves_of(sub)
                            continue
                    for jobs, broke in below(sub, hurt):
                        counts["leaves"] += 1
                        for invariant, detail in broke:
                            if excepted(invariant, name, run, site):
                                counts["excepted"] += 1
                                continue
                            entry = found.setdefault((invariant, name, run["task"], site[0], where), {
                                "orders": 0, "first": hurt_order + jobs, "detail": str(detail)[:300]})
                            entry["orders"] += 1
                walk(sub, plain, order + [f"{name} {rid}"])

        walk(interleavings(runs), self.world(), [])
        if REPORT:
            os.makedirs(REPORT, exist_ok=True)
            with open(os.path.join(REPORT, f"{os.getpid()}.jsonl"), "a", encoding="utf-8") as f:
                for (invariant, name, task, kind, site), entry in found.items():
                    f.write(json.dumps({"combination": self._testMethodName, "invariant": invariant, "job": name,
                                        "task": task, "kind": kind, "site": site, **entry}) + "\n")
                f.write(json.dumps({"combination": self._testMethodName, "ran": ran,
                                    "leaves": counts["leaves"] + counts["unchanged"],
                                    "unchanged": counts["unchanged"], "excepted": counts["excepted"],
                                    "passes": self.passes,
                                    "seconds": round(time.monotonic() - began, 1),
                                    "sites": [{"job": name, "task": task, "kind": kind, "site": site, "count": n}
                                              for (name, task, kind, site), n in failed.items()]}) + "\n")
        names = sorted({key[0] for key in found})
        self.assertEqual(len(found), 0, f"{','.join(names)} in {sum(e['orders'] for e in found.values())} hurt orders "
                                        f"of {describe(runs)}: {list(found.items())[:3]}")

    @staticmethod
    def shape(w):
        """w as text, each time in it replaced by its rank among its times, and its failures by their count: two worlds
        of one shape give the same jobs, passes and checks after them."""
        text = json.dumps({k: v for k, v in w.items() if k not in ("failed", "hurt")}, sort_keys=True)
        rank = {t: str(i) for i, t in enumerate(sorted(set(TIME.findall(text))))}
        return f"{TIME.sub(lambda m: rank[m.group(0)], text)} {len(w['failed'])} {len(w['hurt'])}"

    def hurt_end(self, runs, by_id, w):
        """The end of a hurt order, w: the retry when its failure ended a job, then the checks (the module's text).
        (Each pass and each job of the retry, what broke.)"""
        done, broke, made = [], [], []
        if w["hurt"]:
            w = self.retry(runs, by_id, w, done, broke, made)
        sami = self.names_sami(w)
        words = runs + [r for r in made if r["word"]]
        broke += [b for b in self.broken(words, w) if not (b[0] == "I4" and sami)]
        return done, broke

    @staticmethod
    def names_sami(w):
        """Whether the newest label comment of w names Sami's step: the step of a state whose label is
        waits-on-theorem, but refused-review. That state is the state of a refused word itself (I3), which only its
        line or its check run carries: it waives I4 for no word."""
        labels = [c for c in w["comments"] if c["body"].startswith(rules.FIRST)]
        label = labels[-1]["body"] if labels else ""
        step = next((line[len("**Next step:** "):] for line in label.split("\n")
                     if line.startswith("**Next step:** ")), "")
        return any(rules.STATES[state][0] == rules.THEOREM for state in STEPS.get(step, set()) - {"refused-review"})

    def retry(self, runs, by_id, w, done, broke, made):
        """w after the rescreen pass, run as it runs an hour or more after each run ended, and after what it started,
        again until a pass starts nothing, at most TRIES + 2 passes. made gets each run that a pass started; done each
        pass, with its log lines of what it started, and each job that ran after it; broke each finding: PASS, a pass
        that fails and starts no stop; RETRY, the last pass still starts something; START <task>, a start that the
        sweep does not model; STOP, a stop that its own trust job does not take."""
        true = "writer" if any(r["kind"] == "writer" for r in runs) else "outsider"
        for n in range(1, TRIES + 3):
            kept = self.served()
            try:
                self.serve_pass(runs, w, made, true)
                self.forget()
                rc, log, _ = T.schedule(self, variable=self.LPS)
                self.passes += 1
                starts = self.starts()
                said = [line for line in log.split("\n")
                        if line.startswith("#7: ") and ("started" in line or "run again:" in line)]
                done.append(f"pass {n}: {' '.join(said) or 'starts nothing'}")
                stop = next((s for s in starts if s[0] == "stop"), None)
                if rc != 0 and stop is None:
                    broke.append(("PASS", log[-600:]))
                    return w
                if not starts:
                    return w
                if n == TRIES + 2:
                    broke.append(("RETRY", said))
                    return w
                if stop is not None:
                    # The trust job of a stop decides it again from what the pass read.
                    w = self.run_stop(w, stop, made, done, broke)
                    if broke and broke[-1][0] == "STOP":
                        return w
            finally:
                self.restore(kept)
            for start in starts:
                if start[0] == "rerun":
                    run = by_id.get(start[1]) or next((r for r in made if r["id"] == start[1]), None)
                    if run is None or run["task"] == "stop":
                        broke.append(("START rerun", said))
                        return w
                    newest = {name: (result_of(outcomes), k) for name, outcomes, _at, k in w["jobs"][run["id"]]}
                    attempt = max(k for _result, k in newest.values()) + 1
                    for name, _rid in jobs_of(run):
                        if newest.get(name, ("",))[0] in ("failure", "cancelled"):
                            w = self.job(name, run, w, attempt=attempt)
                            done.append(f"{name} {run['id']} attempt {attempt}")
                elif start[0] == "relabel":
                    run = dict(RELABEL, id=str(900 + len(made)), kind=true, account=start[1])
                    made.append(run)
                    w = self.job("comment", run, self.job("post", run, w))
                    done += [f"post {run['id']} relabel", f"comment {run['id']} relabel"]
                elif start[0] == "answer" and true == "outsider":
                    # A new answer of comment 77, whose screen holds it again: the word answer, read now.
                    run = {"id": str(900 + len(made)), "task": "answer", "kind": true, "word": "answer", "minutes": 0}
                    made.append(run)
                    w = self.job("hold", run, w)
                    done.append(f"hold {run['id']} answer")
                elif start[0] != "stop":
                    broke.append((f"START {start[0]}", said))
                    return w
        return w

    def starts(self):
        """What the pass started, in order: ("rerun", <run>), the failed jobs of a run run again, or (<task>,
        <account>, <head>, <comment>), a run of review.yml."""
        found = []
        for call in gh_calls(self.api):
            if call[:2] != ["--method", "POST"] or len(call) < 3:
                continue
            if call[2].endswith("/rerun-failed-jobs"):
                found.append(("rerun", call[2].split("/")[-2]))
            elif call[2] == f"repos/{REPO}/actions/workflows/review.yml/dispatches":
                f = dict(a.split("=", 1) for a in call[3:] if a != "-f")
                found.append(tuple(f[f"inputs[{k}]"] for k in ("task", "account", "head", "comment")))
        return found

    def run_stop(self, w, start, made, done, broke):
        """w after the run of the stop start that the pass started, while what the pass read is still served: its trust
        job, which must take it (else the finding STOP), and its comment job (T.write_stop)."""
        run = {"id": str(900 + len(made)), "task": "stop", "kind": "", "word": "", "minutes": 0, "head": start[2],
               "comment": start[3]}
        made.append(run)
        w = copy.deepcopy(w)
        self.forget()
        self.logs = []
        open(self.summary, "w").close()
        self.env["GITHUB_STEP_SUMMARY"] = self.summary
        self.live = (w, run, 1)
        try:
            _trust, outcomes = T.write_stop(self, start[3], head=start[2], run=run["id"], variable=self.LPS)
        except AssertionError as e:
            broke.append(("STOP", str(e)[-600:]))
            return w
        finally:
            self.live = None
        self.record(w, "comment", run, outcomes, {}, 1)
        done.append(f"stop {run['id']} {start[3]}")
        return w

    def served(self):
        """What the stand-in gh serves now: the bytes of each of its files but its records (RECORDS)."""
        found = {}
        for name in os.listdir(self.api):
            if name not in RECORDS:
                with open(os.path.join(self.api, name), "rb") as f:
                    found[name] = f.read()
        return found

    def restore(self, kept):
        """The stand-in gh serves kept (served) again, and forgets its calls."""
        for name in os.listdir(self.api):
            if name not in RECORDS and name not in kept:
                os.remove(os.path.join(self.api, name))
        for name, data in kept.items():
            with open(os.path.join(self.api, name), "wb") as f:
                f.write(data)
        self.forget()

    def serve_pass(self, runs, w, made, true):
        """What the rescreen pass reads while #7 is w, an hour or more after each run ended (the module's text): the
        open pull request #7 of mallory at HEAD into main, with the labels, the comments and the check runs of w, and
        mallory's comment 77 that an answer of runs answers, made a minute before the first answer read #7; mallory's
        permission as the true kind of the combination gives it; one CI run of HEAD that ended, and no held run; and
        review.yml's runs that ran a job, those of runs and those that the passes started (made), each made and ended
        over an hour ago, a lower id earlier, with its jobs (listed_jobs)."""
        labels = [{"name": n} for n in w["labels"]]
        opened = ago(24 * 60)
        self.serve(f"repos/{REPO}/issues", [{"number": 7, "state": "open", "user": {"login": "mallory"},
                                             "created_at": opened, "labels": labels, "pull_request": {}}])
        self.serve_prs((7, "mallory", HEAD))
        self.serve(f"repos/{REPO}/pulls/7", {
            "number": 7, "state": "open", "user": {"login": "mallory"}, "merged": False, "draft": False,
            "base": {"ref": "main"}, "created_at": opened, "labels": labels,
            "head": {"sha": HEAD, "ref": BRANCH, "repo": {"id": FORK_ID}}, "mergeable": True,
            "mergeable_state": "clean"})
        self.serve(f"repos/{REPO}/pulls/7/reviews", [])
        self.serve(f"repos/{REPO}/pulls/7/comments", [])
        self.serve(f"repos/{REPO}/issues/7", {
            "number": 7, "state": "open", "user": {"login": "mallory"}, "draft": False, "labels": labels,
            "pull_request": {"url": f"https://api.github.com/repos/{REPO}/pulls/7"}})
        comments = list(w["comments"])
        answers = [r for r in runs if r["task"] == "answer"]
        if answers:
            asked = (self.start - datetime.timedelta(minutes=max(r["minutes"] for r in answers) + 1)).strftime(
                "%Y-%m-%dT%H:%M:%SZ")
            comments.append({"id": 77, "user": {"login": "mallory"}, "created_at": asked, "updated_at": asked,
                             "body": "Is it fixed now?"})
            comments.sort(key=lambda c: c["created_at"])
        T.Scheduled.comments(self, 7, *comments)
        self.serve(f"repos/{REPO}/issues/7/labels", labels)
        self.serve(f"repos/{REPO}/commits/{HEAD}/check-runs", {"check_runs": w["checks"]})
        self.permissions(mallory="write" if true == "writer" else "none")
        self.serve("graphql", T.closed_pulls())
        self.serve(f"repos/{REPO}/actions/workflows/review.yml/dispatches", {})
        listed = sorted((r for r in runs + made if r["id"] in w["jobs"]), key=lambda r: int(r["id"]))
        rows = []
        for i, run in enumerate(listed):
            made_at = 70 + 10 * (len(listed) - 1 - i)
            jobs = self.listed_jobs(run, w)
            event, title, actor = self.titled(run)
            rows.append({"id": int(run["id"]), "event": event, "display_title": title, "status": "completed",
                         "conclusion": "failure" if any(j["conclusion"] in ("failure", "cancelled") for j in jobs)
                         else "success", "created_at": ago(made_at), "updated_at": ago(made_at - 5),
                         "actor": {"login": actor}, "run_attempt": max(k for *_job, k in w["jobs"][run["id"]])})
            self.serve(f"repos/{REPO}/actions/runs/{run['id']}/jobs", {"total_count": len(jobs), "jobs": jobs})
            self.serve(f"repos/{REPO}/actions/runs/{run['id']}/rerun-failed-jobs", {})
        self.serve(f"repos/{REPO}/actions/workflows/review.yml/runs",
                   {"total_count": len(rows), "workflow_runs": rows[::-1]})
        ended = 70 + 10 * len(listed) + 5
        self.serve(f"repos/{REPO}/actions/runs", {"total_count": 1, "workflow_runs": [{
            "id": 70, "status": "completed", "conclusion": "success", "event": "pull_request", "head_sha": HEAD,
            "path": ".github/workflows/ci.yml", "head_branch": BRANCH, "head_repository": {"id": FORK_ID},
            "created_at": ago(ended + 40), "updated_at": ago(ended), "actor": {"login": "mallory"}}]})

    def titled(self, run):
        """(event, name, actor) of run as GitHub lists it, its name as run-name gives it: a CI review, an answer, or a
        run that the pass started (a rescreen of the account mallory but for a writer, a relabel, a stop)."""
        if run["task"] == "review":
            ctx = {"github.event_name": "workflow_run", "github.event.workflow_run.head_sha": HEAD,
                   "github.actor": "mallory"}
        elif run["task"] == "answer":
            ctx = {"github.event_name": "issue_comment", "github.event.issue.number": 7, "github.event.comment.id": 77,
                   "github.event.comment.user.login": "mallory"}
        else:
            account = run.get("account", "")
            if run["task"] == "rescreen":
                account = "" if run["kind"] == "writer" else "mallory"
            ctx = {"github.event_name": "workflow_dispatch", "inputs.task": run["task"], "inputs.number": 7,
                   "inputs.head": run.get("head", HEAD), "inputs.comment": run.get("comment", ""),
                   "inputs.account": account}
        event = ctx["github.event_name"]
        return event, run_name(**ctx), BOT if event == "workflow_dispatch" else "mallory"

    def listed_jobs(self, run, w):
        """The jobs of run as GitHub lists them for its newest attempt: trust; gather, screen and review, each with its
        result for run (contexts); then post, comment and hold with the outcomes of the steps of their newest run, or
        skipped. A stop's trust job alone ran before its comment job."""
        def skipped(name):
            return {"name": name, "status": "completed", "conclusion": "skipped", "steps": []}

        found = [T.attempt_job("trust")]
        if run["task"] == "stop":
            found += [skipped(name) for name in ("gather", "screen mallory", "review")]
        else:
            ctx = self.contexts(run, w["posts"]["trust " + run["id"]], None)
            review = "review (screened)" if ctx["needs.trust.outputs.route"] == "screen" else "review"
            for job, name in (("gather", "gather"), ("screen", "screen mallory"), ("review", review)):
                ran = ctx[f"needs.{job}.result"] == "success"
                found.append(T.attempt_job(job, name=name) if ran else skipped(name))
        newest = {name: outcomes for name, outcomes, _at, _n in w["jobs"].get(run["id"], [])}
        for name in ("post", "comment", "hold"):
            found.append({"name": name, "status": "completed", "conclusion": result_of(newest[name]),
                          "steps": [{"name": s, "status": "completed", "conclusion": c}
                                    for s, c in newest[name].items()]} if name in newest else skipped(name))
        return found


def describe(runs):
    return "; ".join(f"run {r['id']} {r['task']} {r['kind']} {r['word']} read {r['minutes']} min ago" for r in runs)


# The comment job's step that the cancel of the exception to I3 comes before (the module's text), and the site of that
# cancel: the first step of the job.
CHECKOUT = ("cancel", "Run actions/checkout")


def excepted(invariant, name, run, site):
    """Whether the failure of the sweep at site of the job name of run that broke the invariant is the one exception to
    I3 (the module's text): the comment job of a run of refusedline cancelled at its first step. Nothing else is."""
    return invariant == "I3" and name == "comment" and run["word"] == "refusedline" and site == CHECKOUT



def leaves_of(tree):
    """The count of the orders of a tree (interleavings)."""
    return sum(leaves_of(sub) for _job, sub in tree) if tree else 1


# The cost of the end of a plain order of refusedline (check_orders: the retry, of two passes and the jobs that the
# first one starts, in the place of the relabel), in job runs. Measured on one core of the build pod, 2026-11-26: the 6
# orders of OrderTest.test_0748_2_runs_opass0_orefused1 (18 job runs and a relabel of 2 after each order: cost 30) took
# 26.0 s, 0.87 s a job run; the 6 orders of OrderTest.test_0751_2_runs_opass0_orefusedline1 (the same 18 job runs and
# the retry after each order) took 45.6 s, so each retry about 5 s, 6 job runs.
RETRY_COST = 6


def cost(combination):
    """The job runs of the plain orders of combination: one for each node of its tree of orders (interleavings), and
    at the end of each order the two of the relabel after an order of two runs, or RETRY_COST for an order of a
    combination of refusedline, whose end is the retry (check_orders), in the place of the relabel."""
    runs = run_specs(combination)
    tree = interleavings(runs)
    end = RETRY_COST if any(r["word"] == "refusedline" for r in runs) else 2 if len(runs) == 2 else 0

    def nodes(subtree):
        return sum(1 + nodes(sub) for _job, sub in subtree)
    return nodes(tree) + end * leaves_of(tree)


def shard_of(found, n):
    """The shard of each combination of found, by its index, of n shards: the dearest combination first (cost), each
    to the shard with the least cost so far, the lower shard at a tie. So each shard gets about the same cost, and the
    same combination always gets the same shard."""
    costs = [cost(c) for c in found]
    load, shards = [0] * n, {}
    for i in sorted(range(len(costs)), key=lambda i: (-costs[i], i)):
        k = min(range(n), key=lambda k: (load[k], k))
        load[k] += costs[i]
        shards[i] = k
    return shards


def method(combination):
    def test(self):
        if FAILURES:
            self.sweep(combination)
        else:
            self.check_orders(combination)
    test.__doc__ = describe(run_specs(combination))
    return test


def refusedline_with_the_comment_job_cancelled_at_its_checkout_records_no_success(self):
    """The end of the orders that the exception to I3 covers (the module's text; OSSV-613's architect, 2026-11-26
    22:30Z). Run 100 of refusedline (read 30 minutes ago) spends its refused write in its post job, and its comment job
    is cancelled at its first step, so that its step "Record the withdrawal of a refused review whose post job did not
    finish" never runs; answer run 110 (read 40 minutes ago) holds HEAD, whatever the order of the jobs. After the
    retry of the pass (a relabel, which cannot read the refusal): no import check run with the conclusion success
    stands, and no run recorded one, the relabel included (the exception fails closed); the label comment names Sami's
    step; and I3 is the only invariant that breaks. The exception is that narrow: it covers no other invariant, no
    other job, no run of another word, and no other site."""
    combination = (("outsider", "refusedline", 1), ("outsider", "answer", 0))
    runs = run_specs(combination)
    self.start = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
    by_id = {r["id"]: r for r in runs}
    ends = []

    def walk(tree, w, order):
        if not tree:
            done, broke, made = [], [], []
            end = self.retry(runs, by_id, w, done, broke, made)
            sami = self.names_sami(end)
            broke += [b for b in self.broken(runs + [r for r in made if r["word"]], end)
                      if not (b[0] == "I4" and sami)]
            ends.append((order, end, done, broke, sami))
            return
        for (name, rid), sub in tree:
            site = CHECKOUT if (name, rid) == ("comment", "100") else None
            walk(sub, self.job(name, by_id[rid], w, site=site), order + [f"{name} {rid}"])

    walk(interleavings(runs), self.world(), [])
    self.assertEqual(len(ends), 3)
    for order, end, done, broke, sami in ends:
        with self.subTest(order=order):
            success = [c["id"] for c in end["checks"] if c.get("name") == NAME and c.get("conclusion") == "success"]
            self.assertEqual((success, end["makers"], sami, [b[0] for b in broke]), ([], {}, True, ["I3"]),
                             (done, broke))
            self.assertTrue(any("relabel" in d for d in done), done)
            self.assertTrue(excepted("I3", "comment", by_id["100"], CHECKOUT))
    first = by_id["100"]
    for case, args in (("another invariant", ("I4", "comment", first, CHECKOUT)),
                       ("the post job", ("I3", "post", first, CHECKOUT)),
                       ("a run of another word", ("I3", "comment", by_id["110"], CHECKOUT)),
                       ("another step", ("I3", "comment", first, ("cancel", "Record the withdrawal of a refused review "
                                                                     "whose post job did not finish"))),
                       ("a failed read", ("I3", "comment", first, ("read", 1))),
                       ("another run of refused", ("I3", "comment", dict(first, word="refused"), CHECKOUT))):
        with self.subTest(case=case):
            self.assertFalse(excepted(*args))



SHARD = os.environ.get("ORDERS_SHARD", "0/1")
_k, _n = (int(x) for x in SHARD.split("/"))
_all = combinations()
_shards = shard_of(_all, _n) if _n > 1 else {}
for _i, _c in enumerate(_all):
    if _shards.get(_i, 0) == _k:
        _name = "_".join(f"{k[0]}{w}{r}" for k, w, r in _c)
        setattr(OrderTest, f"test_{_i:04d}_{len(_c)}_runs_{_name}", method(_c))

if _k == 0:
    # The pin of the exception to I3 runs once, in shard 0.
    OrderTest.test_refusedline_with_the_comment_job_cancelled_at_its_checkout_records_no_success = \
        refusedline_with_the_comment_job_cancelled_at_its_checkout_records_no_success


if __name__ == "__main__":
    sys.exit(0 if unittest.main(exit=False, verbosity=2).result.wasSuccessful() else 1)
