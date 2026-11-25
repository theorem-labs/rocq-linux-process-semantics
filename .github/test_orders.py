#!/usr/bin/env python3
"""Every order of the jobs of two and three runs of one head, and the end state that each order must reach (OSSV-221's
architect, 2026-11-24 14:36Z and 14:42Z, for round 24 of OSSV-613; the relabel after each order of two runs, 2026-11-25
01:13Z, for round 25).

The jobs of a pull request that write its import check run, its label comment and its review and hold comments share
one concurrency group (write-<n>), so GitHub runs them one at a time, each whole. A run of the review workflow on HEAD
of mallory's #7 has a post job and then a comment job (its review gave a verdict) or a hold job (its screen held
HEAD); an answer has a hold job alone (its screen held the author's comment). This file runs every order of those jobs
that keeps each run's post job before its own comment or hold job, each job as GitHub runs it (test_review.run_job:
its own steps against the stand-in gh, with each job seeing the comments, labels and check runs that the jobs before it
left; a later step of a job reads #7 as the steps before it left it). Before the runs, #7 holds an older review comment
of HEAD that counts at no time (a pass with no marker of its read), a label comment of the state change, the label
waits-on-author, and no import check run. At the end of each order it checks:

  I1  a success stands (an import check run repo-pairs/import-approved of HEAD with the conclusion success) only when
      the newest word by read time is a pass of a run that read the author as an outsider; at a tie of read times a
      verdict or a hold outranks a pass.
  I2  the label comment says that the workflow recorded the check exactly when a success stands.
  I3  the state of the label comment is the state of the newest word, when that word is of a run that read the
      author's kind (outsider or writer). A run that could not read it (kind unknown) changes no label, so I3 does
      not apply when the newest word is of such a run; I1, I2, I4 and I5 still do.
  I4  the newest word is on the pull request at the end: its review comment (in place, from its run) or its hold
      comment. At a tie of two words that are not passes, one of them is enough.
  I5  no run withdraws a success that a run of a newer read recorded (a tie withdraws).
  I0  every job that runs succeeds: no order here has a failure of GitHub.

After the last job of each order of two runs, one relabel run of #7 runs (the task relabel, a run of the rescreen pass
with no screen and no model: its post job, then its comment job), as a change of the variable, a merge conflict that
went away or a person can start one. It reads the author as its true kind. A relabel gives no word of its own, so I0 to
I4 must hold after it as before it, each written R:I0 to R:I4 when it breaks only after it; and R:I5: when the order
broke no invariant before the relabel, the relabel withdraws no success that stood before it (each such success rests
on the newest word, a pass of an outsider's run).

What it runs. A word is a verdict at a read time: pass, blocking, person, held (the screen held HEAD) or answer (the
screen of an answer held the author's comment). Run 0 is a CI review (workflow_run), each other run a rescreen
(workflow_dispatch), and an answer is an answer. Each run reads the author as its true kind or as unknown (GitHub did
not say), and one author has one true kind:
  2 runs: the true kind outsider (each run reads outsider or unknown) or writer (each run reads writer or unknown, not
          both unknown, which the first already runs); each word of a run that reads outsider or unknown is one of the
          five, and a writer's one of pass, blocking and person (a writer's item has no screen); run 1 read before,
          with or after run 0. Every combination.
  3 runs: each run reads outsider, or exactly one run reads unknown; each word one of pass, blocking, held and answer,
          with at least one pass and one other word; the reads of the three in one of the patterns a<b<c, a=b<c,
          a<b=c and a=b=c, and in a group of runs with the same read, one order of their (kind, word) alone.
What it does not run (the architect's pruning of 14:42Z): 3 runs with the word person, with a writer, with two or three
unknown reads, or with no pass or only passes; any failure of GitHub; relabels, catch-ups, approvals and runs by hand;
more than one head; a run's re-run attempt.

That is 747 combinations: 417 of 2 runs (2,112 orders, 6,198 job runs, and a relabel of 2 job runs after each order:
10,422 job runs) and 330 of 3 runs (19,458 orders, 58,183 job runs; the orders of one combination share their first
jobs). Each combination is one test method, which runs every
order of its jobs; ORDERS_SHARD=<k>/<n> (0 <= k < n) keeps the
methods whose index is k modulo n, for a matrix of review-tests.yml. Run it as python3 .github/parallel_tests.py
--processes 4 .github/test_orders.py.
"""

import copy
import datetime
import itertools
import os
import sys
import unittest

import test_review as T
from test_review import BOT, HEAD, JOBS, REPO, WF, ago, evaluate, filled, gh_calls, gh_inputs, review_of, rules, \
    run_job, writes

WORDS = ("pass", "blocking", "person", "held", "answer")
WRITER_WORDS = ("pass", "blocking", "person")
THREE_WORDS = ("pass", "blocking", "held", "answer")
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


def run_specs(runs):
    """runs: (kind, word, rank) of each run, rank 0 the oldest read. The runs as dicts: id, task, kind, word, read."""
    found = []
    for i, (kind, word, rank) in enumerate(runs):
        task = "answer" if word == "answer" else "review" if i == 0 else "rescreen"
        found.append({"id": str(100 + 10 * i), "task": task, "kind": kind, "word": word, "minutes": 40 - 10 * rank})
    return found


def combinations():
    """Each combination that this file runs, in a fixed order: a tuple of (kind, word, rank) per run."""
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
                "jobs": {}}

    def serve_world(self, w, run):
        """GitHub's answers while #7 is w, for a job of run."""
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
        # The jobs of each run as GitHub lists them once they ran, each step ended when its job ran (line_written).
        for rid, jobs in w["jobs"].items():
            self.serve(f"repos/{REPO}/actions/runs/{rid}/jobs", {"total_count": len(jobs), "jobs": [
                {"name": name, "run_id": int(rid), "run_attempt": 1, "status": "completed",
                 "conclusion": "failure" if "failure" in outcomes.values() else "success",
                 "steps": [{"name": n, "status": "completed", "conclusion": c, "started_at": at, "completed_at": at}
                           for n, c in outcomes.items()]} for name, outcomes, at in jobs]})
        self.serve(f"repos/{REPO}/actions/runs/{run['id']}/attempts/1/jobs",
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

    def contexts(self, run, trust, post):
        """The contexts that GitHub gives each job of run: its trust job's outputs, its event, and its post job's result
        and outputs (post; the post job of an answer is skipped)."""
        event = "workflow_dispatch" if run["task"] == "rescreen" else "workflow_run"
        ctx = {f"needs.trust.outputs.{k}": v for k, v in trust.items()}
        ctx.update({"github.event_name": event, "github.ref": "refs/heads/main", "github.repository": REPO,
                    "github.token": self.RUN_TOKEN, "github.run_id": run["id"], "github.run_attempt": "1",
                    "vars.REPO_PAIRS_IMPORT_PATHS": self.LPS, "env.POST_REVIEW": WF["env"]["POST_REVIEW"],
                    "needs.trust.result": "success", "needs.gather.result": "success",
                    "needs.gather.outputs.kind": "pr", "needs.gather.outputs.outside": trust["outside"]})
        screened = trust["route"] == "screen"
        held = run["word"] in ("held", "answer")
        review = review_of(HEAD, run["word"], at=ago(0), run=int(run["id"]), read=trust["started"], screened=screened)
        ctx.update({"needs.screen.result": "success" if screened else "skipped",
                    "needs.screen.outputs.verdict": ("held" if held else "clean") if screened else "",
                    "needs.review.result": "skipped" if held else "success",
                    "needs.review.outputs.head": "" if held else HEAD,
                    "needs.review.outputs.verdict": "" if held else run["word"],
                    "needs.review.outputs.body": "" if held else review["body"],
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

    def job(self, name, run, w):
        """w after the job name of run, as GitHub runs it while #7 is w."""
        w = copy.deepcopy(w)
        trust = w["posts"].setdefault("trust " + run["id"], self.trust(run))
        post = None if name == "post" else w["posts"].get(run["id"], {"result": "skipped", "post": {}})
        ctx = self.contexts(run, trust, post)
        self.serve_world(w, run)
        self.forget()
        self.logs = []
        open(self.summary, "w").close()
        self.env["GITHUB_STEP_SUMMARY"] = self.summary
        if not evaluate(JOBS[name]["if"], ctx):
            if name == "post":
                w["posts"][run["id"]] = {"result": "skipped", "post": {}}
            return w
        tokens = self.TOKENS if name == "post" else self.AnyToken(self.TOKENS)
        self.live = (w, run)
        try:
            outcomes = run_job(self, name, ctx, tokens)
        finally:
            self.live = None
        w["jobs"].setdefault(run["id"], []).append((name, outcomes, ago(0)))
        if "failure" in outcomes.values():
            w["failed"].append(f"{name} of run {run['id']}: {[k for k, v in outcomes.items() if v == 'failure']} "
                               f"{self.logs[-1][-300:] if self.logs else ''}")
        if name == "post":
            w["posts"][run["id"]] = {"result": "failure" if "failure" in outcomes.values() else "success",
                                     "post": filled(JOBS["post"]["outputs"], ctx)}
        return w

    def run_script(self, script, **env):
        """Runner.run_script, and then, in a job (live), GitHub's answers change with the writes of the step: a later
        step of the job reads #7 as this step left it, as it does on GitHub."""
        found = super().run_script(script, **env)
        if getattr(self, "live", None):
            w, run = self.live
            self.apply(w, run)
            self.serve_world(w, run)
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
        """The state of the label comment that the word of run gives, for a run that read the author's kind."""
        if run["kind"] == "writer":
            return "reviewed"
        return {"pass": "import" if success else "decide", "blocking": "change", "person": "person",
                "held": "screen", "answer": "screen"}[run["word"]]

    @staticmethod
    def on_the_item(run, comments):
        """Whether the word of run is on #7: its review comment, or its hold comment."""
        for c in comments:
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
        if not any(self.on_the_item(r, w["comments"]) for r in newest):
            found.append(("I4", [r["id"] for r in newest]))
        reads = {r["id"]: self.read(r) for r in runs}
        for run_id, cid, check in w["withdrawals"]:
            record = rules.recorded_by(check) if check else None
            if run_id in reads and record and record[1] and reads[run_id] < record[1]:
                found.append(("I5", (run_id, cid, record)))
        return found

    def check_orders(self, combination):
        """Every order of the jobs of combination, each from the world before the runs: no invariant breaks."""
        runs = run_specs(combination)
        self.start = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
        by_id = {r["id"]: r for r in runs}
        failures = []

        relabel = dict(RELABEL, kind="writer" if any(r["kind"] == "writer" for r in runs) else "outsider")

        def walk(tree, w, order):
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


def describe(runs):
    return "; ".join(f"run {r['id']} {r['task']} {r['kind']} {r['word']} read {r['minutes']} min ago" for r in runs)


def method(combination):
    def test(self):
        self.check_orders(combination)
    test.__doc__ = describe(run_specs(combination))
    return test


SHARD = os.environ.get("ORDERS_SHARD", "0/1")
_k, _n = (int(x) for x in SHARD.split("/"))
for _i, _c in enumerate(combinations()):
    if _i % _n == _k:
        _name = "_".join(f"{k[0]}{w}{r}" for k, w, r in _c)
        setattr(OrderTest, f"test_{_i:04d}_{len(_c)}_runs_{_name}", method(_c))


if __name__ == "__main__":
    sys.exit(0 if unittest.main(exit=False, verbosity=2).result.wasSuccessful() else 1)
