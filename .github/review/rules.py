#!/usr/bin/env python3
"""The rules of the review workflow that code applies, whatever the model wrote (.github/review.md, "Outside items and
labels").

    python3 .github/review/rules.py label <number> [<fact>=<value> ...] [head=<commit>] [marker=<line> ...]
    python3 .github/review/rules.py make-label <name>

label: the state of the pull request or issue <number> after the event of this run (label_state, from the facts of
FACTS that the job gives), and on GitHub its one state label and its label comment (apply). The state label is
waits-on-author when the next step is the author's, waits-on-theorem when it is Sami's, and none while the workflow
works on the item. Setting one label takes the other off. review-held, the mark of a hold, stays beside them. The
label comment is one comment of github-actions[bot] on the item, edited in place (label_comment). Its first line is
<!-- review-label -->, its text names the next step and who takes it, and with a state label its last line is the
marker <!-- waits-on-author --> or <!-- waits-on-theorem: Sami -->. It keeps each marker line of KEPT that it holds,
and a marker=<line> of the same kind takes the place of that line. It holds <!-- review-conflict-state <head> -->
while it gives the head waits-on-author for a merge conflict, and loses that line with any other state. With no state
label, an item that has a label comment gets the text that the workflow works on the item, and an item that has none
gets none. GH_TOKEN and REPO come from the job's environment, as for gh in the workflow.

make-label: makes the label <name> of LABELS with its colour and description. When it is there (HTTP 422), it sets the
description. A failure only warns: adding a label that does not exist makes it, with no description.

The standard library of Python 3 alone.
"""

import json
import os
import re
import subprocess
import sys

AUTHOR = "waits-on-author"
THEOREM = "waits-on-theorem"
# Who takes a step at Theorem: one person here, as this repository has no code owners.
WHO = "Sami"

# The labels that the workflow makes, with their colours and descriptions (at most 100 characters each).
LABELS = {
    AUTHOR: ("fbca04", "The next step is the author's. A comment of the review workflow names the step."),
    THEOREM: ("5319e7", "The next step is at Theorem. A comment of the review workflow names the step and who takes it."),
    "review-held": ("d93f0b", "The review workflow held this item. Its hold comment tells what happens next."),
}

# The facts of a run that the rule reads, with their values when a job does not give them.
FACTS = {
    # pr or issue.
    "kind": "",
    # The run took an outsider's path (the trust job's outsider): it screened the item first, so its review ran only
    # after the screen passed.
    "outsider": False,
    # The review's verdict at the head: pass, blocking or person.
    "verdict": "",
    # A fix review posted for a blocking finding: suggested changes (R2).
    "fix_posted": False,
    # The author said that they will make the change (the will_fix of the review or of an answer).
    "will_fix": False,
    # 2 fix reviews since the author's last own push, and a blocking finding at the head: no fix runs again.
    "fix_stop": False,
    # A merge conflict at the head.
    "conflict": False,
    # The draft of the reply to an issue is stored.
    "draft_stored": False,
    # A reply that Sami approved posted.
    "reply_posted": False,
    # The screen held the item.
    "screen_held": False,
    # A hold that the workflow tries again: at the hourly limit of an account, at the hourly cap, or of a review that
    # did not finish. Its hold comment gives the time.
    "held": False,
    # A step whose name starts with "Sign in" failed: the run judged nothing, and the schedule takes the item again.
    "sign_in_failed": False,
    # The workflow does not try the work again: the hold job's last try, the schedule's last try of a head, or the
    # rescreens of a hold that settled nothing.
    "tries_used_up": False,
    # A catch-up closed the pull request and could not reopen it.
    "left_closed": False,
    # The post job recorded the import check run at the head (R12).
    "recorded": False,
}
VERDICTS = ("", "pass", "blocking", "person")

# Each state: its label (None for no state label), the next step, which names who takes it, and the text after it.
# {head} is the first 12 characters of the head commit.
STATES = {
    "conflict": (
        AUTHOR, "You resolve the merge conflict with `main`, and push the branch.",
        "This pull request has a merge conflict with `main` at commit {head}. After your push, the checks and the "
        "automated review run again."),
    "fix": (
        AUTHOR, "You apply the suggested changes of the automated review, or push your own change.",
        "The automated review gave a blocking finding, and it posted a fix as suggested changes. When the branch gets "
        "a new commit, the automated review runs again."),
    "change": (
        AUTHOR, "You make the change that the automated review names, and push it.",
        "The automated review gave a blocking finding that no suggested change can fix. After your push, the "
        "automated review runs again."),
    "replied": (
        AUTHOR, "You read the reply to this issue.",
        "If a question stays open, write it in a comment on this issue."),
    "draft": (
        THEOREM, "Sami approves the text of a reply.",
        "The workflow wrote a draft of a reply to this issue, and keeps it private. The workflow posts no reply "
        "before Sami approves its text. You do not need to do anything now."),
    "person": (
        THEOREM, "Sami examines the points of the automated review that need a person.",
        "You do not need to do anything now."),
    "screen": (
        THEOREM, "Sami reads the item and starts its review or its checks by hand.",
        "The automated screen held this item. You do not need to do anything."),
    "will-fix": (
        THEOREM, "Sami reads the automated review and your comment.",
        "You wrote that you will make the change, so no automated fix runs. After your push, the automated review "
        "runs again."),
    "fix-stop": (
        THEOREM, "Sami reads the automated review and its fixes.",
        "The automated review posted 2 fixes since your last push, and it still gives a blocking finding. No "
        "automated fix runs again. You do not need to do anything now."),
    "stopped": (
        THEOREM, "Sami reads the runs and starts the work again.",
        "The automated work on this item did not finish, and the workflow does not try it again. You do not need "
        "to do anything."),
    "reopen": (
        THEOREM, "Sami reopens the pull request.",
        "The automated catch-up closed this pull request and could not reopen it. You do not need to do anything."),
    "decide": (
        THEOREM, "Sami takes one of the steps below.",
        "The automated screen and the automated review passed this pull request. You do not need to do anything. "
        "The step is one of these:\n\n"
        "- Sami merges the pull request on this repository, while the rules of this repository allow a merge.\n"
        "- Else, once the import into the internal repository runs, Sami approves the head commit for the import.\n"
        "- Else, once the import runs, Sami copies the change into the internal repository by hand, if the pull "
        "request changes a path that the import does not take."),
    "working": (
        None, "The automated workflow works on this item.",
        "You do not need to do anything now. When a hold comment gives a time, the workflow tries the item again "
        "from that time."),
}

FIRST = "<!-- review-label -->"
HEAD = re.compile(r"[0-9a-f]{40}")
NUMBER = re.compile(r"[1-9][0-9]*")
# The marker lines of other kinds that a label comment keeps: the import's paths that a decision on a head read
# (R12), the stored draft of an issue's reply, and the approved reply that posted.
KEPT = re.compile(r"<!-- (repo-pairs-import-paths) [0-9a-f]{40}: .* -->|<!-- (issue-draft) [0-9]+-[0-9]+ -->"
                  r"|<!-- (issue-reply-posted) [0-9]+ -->")


def label_state(kind="", outsider=False, verdict="", fix_posted=False, will_fix=False, fix_stop=False,
                conflict=False, draft_stored=False, reply_posted=False, screen_held=False, held=False,
                sign_in_failed=False, tries_used_up=False, left_closed=False, recorded=False):
    """The state of an item after the event of a run, a key of STATES, from the facts of FACTS. The first rule that
    holds gives it."""
    if kind not in ("", "pr", "issue"):
        raise ValueError(f"not a kind of item: {kind!r}")
    if verdict not in VERDICTS:
        raise ValueError(f"not a verdict: {verdict!r}")
    # The run judged nothing, and the schedule takes the item again.
    if sign_in_failed:
        return "working"
    if left_closed:
        return "reopen"
    # GitHub runs no checks on a pull request with a merge conflict: the author resolves it first.
    if conflict:
        return "conflict"
    if tries_used_up:
        return "stopped"
    if screen_held:
        return "screen"
    if held:
        return "working"
    if reply_posted:
        return "replied"
    if draft_stored:
        return "draft"
    # The review's outcome, for an item whose review followed a screen that passed.
    if outsider:
        if kind == "pr":
            if will_fix:
                return "will-fix"
            if fix_stop:
                return "fix-stop"
            if fix_posted:
                return "fix"
            if verdict == "blocking":
                return "change"
        if verdict == "person":
            return "person"
        # R12: a pull request that the screen and the review passed waits on Sami, unless the post job recorded the
        # import check run at its head.
        if kind == "pr" and verdict == "pass" and not recorded:
            return "decide"
    return "working"


def label_of(state):
    """The state label of state: waits-on-author, waits-on-theorem, or None."""
    return STATES[state][0]


def marker_kind(line):
    """The kind of a marker line of KEPT: repo-pairs-import-paths, issue-draft or issue-reply-posted."""
    m = KEPT.fullmatch(line)
    if not m:
        raise ValueError(f"not a marker line that the label comment keeps: {line!r}")
    return next(g for g in m.groups() if g)


def label_comment(state, old="", markers=(), head=""):
    """The text of the label comment of an item in state, which takes the place of old (its label comment, or "" when
    it has none): FIRST, the next step, the text, then each marker line of KEPT that old holds or markers gives (a
    marker of markers takes the place of old's line of its kind), the conflict-state line of head for a conflict, and
    the marker of the state label."""
    label, step, text = STATES[state]
    if state == "conflict" and not HEAD.fullmatch(head):
        raise ValueError(f"a conflict needs its head commit, not {head!r}")
    kept = {}
    for line in old.split("\n"):
        if KEPT.fullmatch(line):
            kept[marker_kind(line)] = line
    for line in markers:
        kind = marker_kind(line)
        kept.pop(kind, None)
        kept[kind] = line
    lines = list(kept.values())
    if state == "conflict":
        lines.append(f"<!-- review-conflict-state {head} -->")
    if label == AUTHOR:
        lines.append(f"<!-- {AUTHOR} -->")
    elif label == THEOREM:
        lines.append(f"<!-- {THEOREM}: {WHO} -->")
    body = f"{FIRST}\n**Next step:** {step}\n\n{text.format(head=head[:12])}"
    if lines:
        body += "\n\n" + "\n".join(lines)
    return body


class GhError(Exception):
    """A call of gh api that failed; status is the HTTP status that gh names, or None."""

    def __init__(self, text):
        super().__init__(text)
        m = re.search(r"\(HTTP ([0-9]{3})\)", text)
        self.status = int(m.group(1)) if m else None


def gh(*args):
    """gh api with args: its standard output, or GhError."""
    r = subprocess.run(["gh", "api", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise GhError((r.stderr or r.stdout).strip() or f"gh api {' '.join(args[:3])} failed")
    return r.stdout


def make_label(name):
    """Makes the label name of LABELS, or sets its description when it is there. A failure only warns."""
    repo = os.environ["REPO"]
    color, description = LABELS[name]
    try:
        gh("--method", "POST", f"repos/{repo}/labels", "-f", f"name={name}", "-f", f"color={color}",
           "-f", f"description={description}", "--jq", ".name")
        return
    except GhError as e:
        if e.status == 422:
            try:
                gh("--method", "PATCH", f"repos/{repo}/labels/{name}", "-f", f"description={description}",
                   "--jq", ".name")
                return
            except GhError:
                pass
    print(f"::warning::the label {name} could not be made or described; adding it makes it, with no description.")


def apply(number, state, markers=(), head=""):
    """Gives the item number the state label of state, takes the other one off, and writes its label comment."""
    repo = os.environ["REPO"]
    want = label_of(state)
    have = set(gh("--paginate", f"repos/{repo}/issues/{number}/labels", "--jq", ".[].name").split("\n"))
    for other in (AUTHOR, THEOREM):
        if other != want and other in have:
            try:
                gh("--method", "DELETE", f"repos/{repo}/issues/{number}/labels/{other}")
            except GhError as e:
                if e.status != 404:
                    raise
    if want and want not in have:
        make_label(want)
        gh("--method", "POST", f"repos/{repo}/issues/{number}/labels", "-f", f"labels[]={want}", "--jq", ".[].name")
    found = gh("--paginate", f"repos/{repo}/issues/{number}/comments", "--jq",
               '.[] | select(.user.login == "github-actions[bot]" and (.body | startswith("<!-- review-label -->")))'
               ' | {id, body} | @json')
    comments = [json.loads(line) for line in found.split("\n") if line.strip()]
    old = comments[-1] if comments else None
    shown = f"#{number}: {want or 'no state label'} ({state})"
    if old is None and want is None:
        print(f"{shown}, and no label comment to change.")
        return
    body = label_comment(state, old["body"] if old else "", markers, head)
    if old is not None and body == old["body"]:
        print(f"{shown}, as its label comment says already.")
        return
    if old is not None:
        if not re.fullmatch(r"[1-9][0-9]*", str(old["id"])):
            raise GhError(f"the label comment of #{number} has no id")
        gh("--method", "PATCH", f"repos/{repo}/issues/comments/{old['id']}", "-f", f"body={body}", "--jq", ".html_url")
    else:
        gh("--method", "POST", f"repos/{repo}/issues/{number}/comments", "-f", f"body={body}", "--jq", ".html_url")
    print(f"{shown}.")


def parse(args):
    """The facts, the marker lines and the head of label's arguments: <fact>=<value> for each fact of FACTS (true or
    false, or empty for false, for each fact that is one or the other), head=<commit>, and marker=<line>."""
    facts, markers, head = {}, [], ""
    for arg in args:
        name, eq, value = arg.partition("=")
        if not eq:
            raise ValueError(f"not <name>=<value>: {arg!r}")
        if name == "marker":
            marker_kind(value)
            markers.append(value)
        elif name == "head":
            if value and not HEAD.fullmatch(value):
                raise ValueError(f"not a head commit: {value!r}")
            head = value
        elif name not in FACTS or name in facts:
            raise ValueError(f"not a fact of the label rule, or given twice: {name!r}")
        elif isinstance(FACTS[name], bool):
            if value not in ("", "true", "false"):
                raise ValueError(f"{name} is true or false, not {value!r}")
            facts[name] = value == "true"
        else:
            facts[name] = value
    return facts, markers, head


def main(argv):
    try:
        if len(argv) == 2 and argv[0] == "make-label" and argv[1] in LABELS:
            make_label(argv[1])
            return 0
        if len(argv) >= 2 and argv[0] == "label" and NUMBER.fullmatch(argv[1]):
            facts, markers, head = parse(argv[2:])
            state = label_state(**facts)
            label_comment(state, "", markers, head)
            apply(argv[1], state, markers, head)
            return 0
    except ValueError as e:
        print(f"::error::rules.py: {e}", file=sys.stderr)
        return 2
    except GhError as e:
        print(f"::error::rules.py: {e}", file=sys.stderr)
        return 1
    print(__doc__.split("\n\n")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
