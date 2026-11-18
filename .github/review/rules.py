#!/usr/bin/env python3
"""The rules of the review workflow that code applies, whatever the model wrote (.github/review.md, "Outside items and
labels").

    python3 .github/review/rules.py label <number> [<fact>=<value> ...] [head=<commit>] [marker=<line> ...]
    python3 .github/review/rules.py mark <number> <line>
    python3 .github/review/rules.py make-label <name>
    python3 .github/review/rules.py proofs <head> <files.jsonl> <changed files>
    python3 .github/review/rules.py soundness <the .review directory> <output.json> <hold> <outside> <section> <all>
    python3 .github/review/rules.py fixes <commits.jsonl> <reviews.jsonl> <head>
    python3 .github/review/rules.py suggestions <fix.json> <pr.diff>
    python3 .github/review/rules.py import-check <files.jsonl> <changed files> <head> <screen> <verdict> <hold>
        <request.json> [<import paths>]
    python3 .github/review/rules.py import-marker <head> [<import paths>]
    python3 .github/review/rules.py verdict <number> <head>
    python3 .github/review/rules.py relabel <number> <head> [<fact>=<value> ...] [marker=<line> ...]

label: the state of the pull request or issue <number> after the event of this run (label_state, from the facts of
FACTS that the job gives), and on GitHub its one state label and its label comment (apply). The state label is
waits-on-author when the next step is the author's, waits-on-theorem when it is Sami's, and none while the workflow
works on the item. Setting one label takes the other off. review-held, the mark of a hold, stays beside them. The
label comment is one comment of github-actions[bot] on the item, edited in place (label_comment). Its first line is
<!-- review-label -->, its text names the next step and who takes it, and with a state label its last line is the
marker <!-- waits-on-author --> or <!-- waits-on-theorem: Sami -->. It keeps each marker line of KEPT that it holds,
and a marker=<line> of the same kind takes the place of that line. It holds <!-- review-conflict-state <head> -->
while it gives the head waits-on-author for a merge conflict, and loses that line with any other state. In a state
with no state label (working, or import), an item that has a label comment gets the text of its state, and an item
that has none gets none. For an outside pull request (the facts kind=pr and outsider=true) in the state decide or
person, the text also names the step of R12 for the import into the internal repository (import_steps), from the
facts import_paths, the text of the variable REPO_PAIRS_IMPORT_PATHS, given only when it is set, and decision, the
post job's decision (import_decision). GH_TOKEN and REPO come from the job's environment, as for gh in the workflow.

mark: records the marker line <line> of KEPT in the label comment of <number>, and changes nothing else
(with_marker): the state label, the text and the other lines stay as they are, as label would keep them for the same
state. <line> takes the place of the line of its kind. An item with no label comment gets one, of the state working.
The comment job of a catch-up records the line <!-- review-catchup <head> --> with it. The rescreen pass reads that
line, so that each head gets one catch-up.

make-label: makes the label <name> of LABELS with its colour and description, or sets its description when the label
is there with another one. It reads the label first, and writes only what differs. A failure only warns: adding a
label that does not exist makes it, with no description.

proofs: the facts of the soundness rule at the head <head> of a pull request, as JSON on standard output, which the
gather job writes into .review/ as soundness.json (proofs): each changed path that can change a Rocq proof, with why,
whether the list of the changed paths is whole, and each file of the build that it could not read. <files.jsonl> holds
the files of the pull request as the API lists them on every page of pulls/<n>/files, one {filename, previous_filename}
on each line, and <changed files> is the pull request's changed_files, or empty when a read did not finish or read
another head: then the list is not whole. A changed path counts when it is a .v file, a dune, dune-project or
dune-workspace file anywhere in the tree, a file that a dune file of <head> names (dune_names), or the file that a link
of <head> points to when the link's own path counts. The dune files come from git objects of <head>, in the
repository of the working directory, never from a checkout.

soundness: the soundness rule of R8 (.github/review.md, "Soundness of a Rocq proof"), which code applies whatever the
model wrote. Stock Rocq accepts three public proofs of False (ISSUES), and this repository's CI lanes check the proofs
on stock Rocq, as the checks that the import's copy must pass do. So a pass of the checks does not show a proof sound.
The rule holds while <hold> (SOUNDNESS_HOLD) is true, for an outside pull request (<outside>, the gather job's outside,
is not false) that changes a path that soundness.json counts or a .v file under head/, whose list of changed paths is
not whole, or for which a file of the build could not be read: the job cannot show then that no proof changed. Then
<output.json>, the review's output {comment, verdict, will_fix, items}, gets the verdict person whatever the model
gave, and QUESTION when its list has no question on soundness (forced). <section> gets the fixed section on soundness,
which trim.py puts after the trimmed text, where the reader never sees it: it says why the rule holds, and lists, as
facts for Sami, each changed file of the build, each line of the changed .v files at the head that uses one of USES, an
array literal or make of the array module (uses), and each changed .v file at the head that the gather job did not
keep whole. None of them is a fail: honest proofs use the same constructs. A proof with no such line gets the section
too: a proof reaches the VM through a tactic such as lia, and a primitive array through make with no array literal, so
a search of the text cannot rule a forgery out. The section lists at most LISTED lines in at most LISTED_CHARACTERS
characters, and says how many more there are. <all> gets the section with every line, for the run's summary. When the
rule does not hold, <output.json> stays as it is and the two files are empty.

fixes: the count of the fix reviews since the author's last own push (.github/review-answer.md, "The two stops"), on
standard output. <commits.jsonl> is the history of <head> as the API gives it (repos/<repo>/commits?sha=<head>), and
<reviews.jsonl> the reviews of the pull request, one JSON object on each line. A fix review is a review of BOT whose
body holds the marker <!-- review-fix <commit> -->. It counts when <commit> is <head>, or a commit before <head> back
to the author's last own push: GitHub made each commit between them from a suggested change (committer web-flow, and
a message that starts with "Apply suggestion"), and such a commit is not a push of the author. So a fix review of an
older push does not count. The status is 2 when <head> is not in <commits.jsonl>.

suggestions: the fix of <fix.json> ({summary, suggestions}, .github/review-answer.md, "The fix") as {summary,
suggestions[, off]}, as JSON on standard output: suggestions holds only the suggestions whose lines are right-side
lines of one hunk of <pr.diff>, and off, there only when a suggestion is off the diff, each other suggestion as the
sentence that names its file and lines, with its why: a suggested change can change only a line that the diff shows.
trim.py fix puts these sentences after the trimmed summary, where the reader never sees them. The status is 2 when
<fix.json> is not such a fix.

import-check: the decision of R12 on the head <head> of an outside pull request (import_decision), on standard output:
record, or the first rule that does not hold. <files.jsonl> holds the files of the pull request at <head> as the API
lists them on every page of pulls/<n>/files, one {filename, previous_filename} on each line, and <changed files> is
the pull request's changed_files. <screen> is true when the screen passed the head, <verdict> is the review's verdict
after the soundness rule, and <hold> is SOUNDNESS_HOLD. <import paths> is the text of the variable
REPO_PAIRS_IMPORT_PATHS, one glob of the import on each line, given only when the variable is set: with none, the
import is not live. The check run repo-pairs/import-approved is recorded only when the screen passed, the verdict is
pass, no changed path (of a file, or the path it had before a rename) is a steering file (under .github/), with the
variable each changed path matches one of its globs by the import's glob rules (glob_match), the list holds each
changed file (GitHub lists at most 3,000), and, while the hold lasts, each changed path ends with .md. Then
<request.json> gets the body of the request that records it (check_run, for POST repos/<repo>/check-runs), whose
output text is the marker line of import-marker. The status is 2 when an argument is not one of these, or when the
import's glob rules refuse a glob of the variable.

import-marker: the marker line <!-- repo-pairs-import-paths <head>: <value> --> of R12, which the output text of the
check run and each label comment of an outside pull request hold (import_marker): <value> is <import paths> as one
JSON string, or null when it is not given. The JSON writes each character outside ASCII, <, > and & as a \\u escape,
so that the line holds no line break and no --> before its end.

verdict: the review's verdict at <head> of the pull request <number>, from the marker
<!-- review-verdict <head> <verdict>[ will-fix] --> of the review comment of github-actions[bot] that names <head>
(review_verdict): <verdict> on standard output, and an empty line when no review comment names <head>.

relabel: label (above) for the head <head> of the pull request <number>, with the facts that the workflow wrote of
that head (relabel_facts) beside the facts and the marker lines of the job: the verdict and will-fix of the review
comment that names <head>, an answer at <head> whose author said they will make the change, the fix reviews of
<head> and the count of fix reviews since the author's last own push, or the hold comment that names <head> when it
is newer than all of those. When the workflow wrote nothing of <head> but the conflict-state line of its label
comment, the item gets no state label and the line goes. When it wrote nothing of <head>, nothing changes.

The standard library of Python 3 alone.
"""

import json
import os
import posixpath
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
    # The draft of the reply to an issue is stored, as an artifact of its run.
    "draft_stored": False,
    # A reply that Sami approved posted.
    "reply_posted": False,
    # The text that the fresh reader refused, so that nothing of it posted: review, answer or fix (REFUSALS).
    "refused": "",
    # The screen held the item.
    "screen_held": False,
    # A hold that the workflow tries again: at the hourly limit of an account, at the hourly cap, or of a review that
    # did not finish. Its hold comment gives the time.
    "held": False,
    # The workflow does not try the work again: the hold job's last try, the rescreen pass's last try of a head, or
    # the rescreens of a hold that settled nothing.
    "tries_used_up": False,
    # A catch-up closed the pull request and could not reopen it.
    "left_closed": False,
    # The post job recorded the import check run at the head (R12).
    "recorded": False,
    # The text of the variable REPO_PAIRS_IMPORT_PATHS, the import's globs, one on each line (R12). None when the
    # variable is not set: then the import is not live.
    "import_paths": None,
    # The post job's decision on the import check run at the head, one of DECISIONS.
    "decision": "",
}
VERDICTS = ("", "pass", "blocking", "person")
# The texts that the fresh reader can refuse, each with its state (STATES), and "" for none.
REFUSALS = ("", "review", "answer", "fix")
# The post job's decisions on the import check run at a head (import_decision): record, or the first rule of R12 that
# does not hold, or moved when the pull request moved on from the head. Empty when the job gave none.
DECISIONS = ("", "record", "screen", "verdict", "steering", "outside", "unread", "person", "markdown", "moved")

# The texts of R12 for an outside pull request that the screen and the review passed (import_steps). With no variable
# REPO_PAIRS_IMPORT_PATHS, the workflow cannot tell whether the import does not run yet, a move is under way or the
# import is paused, so the comment names each step that can come next. With the variable, it names the step for the
# paths that the pull request changes.
PASSED = "The automated screen and the automated review passed this pull request."
MERGE_STEPS = (
    "- If the rules of this repository allow a merge, Sami merges the pull request in this repository.\n"
    "- Else, when the import into the internal repository runs and copies each changed path, Sami approves the "
    "head commit for the import.\n"
    "- Else, when the import runs, Sami copies the change into the internal repository by hand.")
APPROVE = "Sami approves the head commit for the import into the internal repository."
COPY = "Sami copies the change into the internal repository by hand."
IMPORT_STEPS = (f"- {APPROVE.removesuffix('.')}, if the import copies each path that the pull request changes.\n"
                f"- Else, {COPY}")
UNREAD = ("GitHub did not give the full list of the files that this pull request changes, so the workflow cannot "
          "tell which step comes next.")
# Why the import does not take the pull request, for each decision whose step is COPY.
NOT_TAKEN = {
    "steering": ("This pull request changes a file under `.github/`. The workflow never records the check "
                 "`repo-pairs/import-approved` for such a change."),
    "outside": "This pull request changes a path that the import does not copy.",
}

# Each state: its label (None for no state label), the next step, which names who takes it, and the text after it
# ("" for none, and None when import_steps writes it).
STATES = {
    # The comment on the merge conflict, which the same run posts, says why and how to resolve it.
    "conflict": (AUTHOR, "You resolve the merge conflict with `main`. Then you push the branch.", ""),
    "fix": (
        AUTHOR, "You apply the suggested changes of the automated fix, or push your own change.",
        "The automated review gave a blocking finding. The automated fix posted suggested changes for it. When the "
        "branch gets a new commit, the automated review runs again."),
    "change": (
        AUTHOR, "You make the change that the automated review names. Then you push the change.",
        "The automated review gave a blocking finding, and the automated fix posted no suggested change for it. "
        "After your push, the automated review runs again."),
    "replied": (
        AUTHOR, "You read the reply to this issue.",
        "If a question stays open, write it in a comment on this issue."),
    "draft": (THEOREM, "Sami approves the text of a reply.", "You do not need to do anything."),
    # The fresh reader refused the text (the fact refused): nothing of it posted.
    "refused-review": (
        THEOREM, "Sami writes the review by hand.",
        "A second Claude session read the automated review and stopped it, so the review did not post. You do not "
        "need to do anything."),
    "refused-answer": (
        THEOREM, "Sami answers your comment by hand.",
        "A second Claude session read the automated answer to your comment and stopped it, so the answer did not "
        "post. You do not need to do anything."),
    "refused-fix": (
        THEOREM, "Sami writes the fix by hand.",
        "The automated review gave a blocking finding. A second Claude session read the automated fix for the "
        "finding and stopped it, so no suggested change posted. You can push your own change."),
    "person": (THEOREM, "Sami answers the questions of the automated review.", "You do not need to do anything."),
    "screen": (
        THEOREM, "Sami starts the review or the checks of this item by hand.", "You do not need to do anything."),
    "will-fix": (
        THEOREM, "Sami replies to your comment.",
        "You wrote that you will make the change, so no automated fix runs. After your push, the automated review "
        "runs again."),
    "fix-stop": (
        THEOREM, "Sami writes a comment on the blocking finding that the automated fixes did not fix.",
        "The workflow posted 2 automated fixes since your last push, and the automated review still gives a blocking "
        "finding. No automated fix runs again. You do not need to do anything."),
    # The hold comment says what did not finish, after how many tries, and that the workflow does not try it again.
    "stopped": (
        THEOREM, "Sami starts the automated work on this item again by hand.", "You do not need to do anything."),
    "reopen": (
        THEOREM, "Sami reopens the pull request.",
        "The workflow closed this pull request to start its checks. It could not reopen the pull request. You do not "
        "need to do anything."),
    # An outside pull request that the screen and the review passed (R12). Its text is import_steps' own, for the
    # variable REPO_PAIRS_IMPORT_PATHS and the post job's decision.
    "decide": (THEOREM, "Sami takes one of the steps below.", None),
    # An outside pull request whose head has the import check run, while the variable gives the import's paths.
    "import": (
        None, "The automated import copies the head commit into the internal repository.",
        f"{PASSED} The workflow recorded the check `repo-pairs/import-approved` on its head commit. You do not need "
        "to do anything."),
    "working": (
        None, "The workflow continues the automated work on this item.",
        "You do not need to do anything. When a hold comment gives a time, the workflow tries the item again from "
        "that time."),
}

FIRST = "<!-- review-label -->"
HEAD = re.compile(r"[0-9a-f]{40}")
NUMBER = re.compile(r"[1-9][0-9]*")
# The marker lines of other kinds that a label comment keeps: the import's paths that a decision on a head read
# (R12), the stored draft of an issue's reply, the approved reply that posted, and the head that a catch-up closed and
# reopened the pull request at (D16 (a): once for each head).
KEPT = re.compile(r"<!-- (repo-pairs-import-paths) [0-9a-f]{40}: .* -->|<!-- (issue-draft) [0-9]+-[0-9]+ -->"
                  r"|<!-- (issue-reply-posted) [0-9]+ -->|<!-- (review-catchup) [0-9a-f]{40} -->")


def marker_line(line):
    """Whether line is a marker line, as the last part of a label comment holds them: <!-- and a space, then any
    text with no line break, then a space and -->."""
    return len(line) >= 9 and line.startswith("<!-- ") and line.endswith(" -->") and "\n" not in line


def label_state(kind="", outsider=False, verdict="", fix_posted=False, will_fix=False, fix_stop=False,
                conflict=False, draft_stored=False, reply_posted=False, refused="", screen_held=False, held=False,
                tries_used_up=False, left_closed=False, recorded=False, import_paths=None, decision=""):
    """The state of an item after the event of a run, a key of STATES, from the facts of FACTS. The first rule that
    holds gives it."""
    if kind not in ("", "pr", "issue"):
        raise ValueError(f"not a kind of item: {kind!r}")
    if verdict not in VERDICTS:
        raise ValueError(f"not a verdict: {verdict!r}")
    if decision not in DECISIONS:
        raise ValueError(f"not a decision of the post job: {decision!r}")
    if refused not in REFUSALS:
        raise ValueError(f"not a text that the fresh reader refuses: {refused!r}")
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
    # A text that the fresh reader refused never posts: Sami writes it, whoever wrote the item.
    if refused:
        return f"refused-{refused}"
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
        # R12: a pull request that the screen and the review passed waits on Sami, unless the import is live and the
        # post job recorded the import check run at its head, which it does only when the import takes each path.
        if kind == "pr" and verdict == "pass":
            return "import" if recorded and import_paths is not None else "decide"
    return "working"


def label_of(state):
    """The state label of state: waits-on-author, waits-on-theorem, or None."""
    return STATES[state][0]


def marker_kind(line):
    """The kind of a marker line of KEPT: repo-pairs-import-paths, issue-draft, issue-reply-posted or review-catchup."""
    m = KEPT.fullmatch(line)
    if not m:
        raise ValueError(f"not a marker line that the label comment keeps: {line!r}")
    return next(g for g in m.groups() if g)


def import_steps(state, value, decision):
    """(step, text) of the label comment of an outside pull request in the state decide or person (R12), for value, the
    text of the variable REPO_PAIRS_IMPORT_PATHS (None when it is not set), and the post job's decision. With the
    variable, the step is Sami's approval of the head commit when the import takes each changed path, and a copy by
    hand when it does not take one or a file is under .github/. A decision that does not say which, as when the list of
    changed files is not whole or the post job did not succeed, gives both. With no variable, each step of
    MERGE_STEPS."""
    if state not in ("decide", "person"):
        raise ValueError(f"no step of the import for the state {state!r}")
    if decision not in DECISIONS:
        raise ValueError(f"not a decision of the post job: {decision!r}")
    live = value is not None
    steps = IMPORT_STEPS if live else MERGE_STEPS
    unread = f"{UNREAD} " if decision == "unread" else ""
    if state == "decide":
        if live and decision in ("person", "markdown"):
            return APPROVE, (f"{PASSED} The import copies each path that this pull request changes. You do not need "
                             "to do anything.")
        if live and decision in NOT_TAKEN:
            return COPY, f"{PASSED} {NOT_TAKEN[decision]} You do not need to do anything."
        return STATES[state][1], f"{PASSED} {unread}You do not need to do anything.\n\n{steps}"
    _label, step, text = STATES[state]
    # No text promises a merge or an import before the questions have their answers.
    answered = "If the answers to the questions leave no blocking finding,"
    if live and decision in ("person", "markdown"):
        after = f"{answered} {APPROVE}"
    elif live and decision in NOT_TAKEN:
        after = f"{answered} {COPY} {NOT_TAKEN[decision]}"
    else:
        after = f"{unread}{answered} the next step is one of these:\n\n{steps}"
    return step, f"{text}\n\n{after}"


def conflict_state(head):
    """The marker line of the label comment while it gives head waits-on-author for a merge conflict."""
    return f"<!-- review-conflict-state {head} -->"


def label_comment(state, old="", markers=(), head="", imports=None):
    """The text of the label comment of an item in state, which takes the place of old (its label comment, or "" when
    it has none): FIRST, the next step, the text when the state has one, then each marker line of KEPT that old holds
    or markers gives (a marker of markers takes the place of old's line of its kind), the conflict-state line of head
    for a conflict, and the marker of the state label. imports is (value, decision) of import_steps for an outside
    pull request, and None for any other item. The state decide is an outside pull request's alone, so there None
    reads as no variable and no decision."""
    label, step, text = STATES[state]
    if state == "decide" or (state == "person" and imports is not None):
        step, text = import_steps(state, *(imports or (None, "")))
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
        lines.append(conflict_state(head))
    if label == AUTHOR:
        lines.append(f"<!-- {AUTHOR} -->")
    elif label == THEOREM:
        lines.append(f"<!-- {THEOREM}: {WHO} -->")
    body = f"{FIRST}\n**Next step:** {step}"
    for part in (text, "\n".join(lines)):
        if part:
            body += "\n\n" + part
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


def gh_objects(*args):
    """The JSON objects that gh api with args gives, one on each line (its --jq ends with @json)."""
    return [json.loads(line) for line in gh(*args).split("\n") if line.strip()]


def make_label(name):
    """Makes the label name of LABELS, or sets its description when the label is there with another one: one read,
    and a write only when one is needed. A failure only warns."""
    repo = os.environ["REPO"]
    color, description = LABELS[name]
    try:
        try:
            label = json.loads(gh(f"repos/{repo}/labels/{name}"))
            if isinstance(label, dict) and label.get("description") == description:
                return
        except GhError as e:
            if e.status != 404:
                raise
            try:
                gh("--method", "POST", f"repos/{repo}/labels", "-f", f"name={name}", "-f", f"color={color}",
                   "-f", f"description={description}", "--jq", ".name")
                return
            except GhError as made:
                # Made in between, by another run.
                if made.status != 422:
                    raise
        gh("--method", "PATCH", f"repos/{repo}/labels/{name}", "-f", f"description={description}", "--jq", ".name")
        return
    except (GhError, ValueError):
        pass
    print(f"::warning::the label {name} could not be made or described; adding it makes it, with no description.")


def apply(number, state, markers=(), head="", imports=None, labels=None):
    """Gives the item number the state label of state, takes the other one off, and writes its label comment
    (label_comment, with imports). labels are the item's label comments of BOT, each {id, body}, when the caller read
    them already; else this reads them."""
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
    if labels is None:
        labels = read_labels(number)
    old = labels[-1] if labels else None
    shown = f"#{number}: {want or 'no state label'} ({state})"
    if old is None and want is None:
        print(f"{shown}, and no label comment to change.")
        return
    body = label_comment(state, old["body"] if old else "", markers, head, imports)
    if old is not None and body == old["body"]:
        print(f"{shown}, as its label comment says already.")
        return
    write_label(number, old, body)
    print(f"{shown}.")


def read_labels(number):
    """The label comments of BOT on the item number, each {id, body}, in the order that GitHub lists them."""
    mine = f"select(.user.login == {json.dumps(BOT)} and (.body | startswith({json.dumps(FIRST)})))"
    return gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{number}/comments", "--jq",
                      f".[] | {mine} | {{id, body}} | @json")


def write_label(number, old, body):
    """Writes body as the label comment of the item number: in the place of old, a label comment {id, body}, or as a
    new comment when old is None."""
    repo = os.environ["REPO"]
    if old is not None:
        if not NUMBER.fullmatch(str(old["id"])):
            raise GhError(f"the label comment of #{number} has no id")
        gh("--method", "PATCH", f"repos/{repo}/issues/comments/{old['id']}", "-f", f"body={body}", "--jq", ".html_url")
    else:
        gh("--method", "POST", f"repos/{repo}/issues/{number}/comments", "-f", f"body={body}", "--jq", ".html_url")


def with_marker(body, line):
    """The label comment body with line, a marker line of KEPT, as label_comment gives it for the same state with line
    among its markers: in the last part of body, which holds the marker lines, line takes the place of the line of its
    kind, after the other kept lines and before the conflict-state line and the marker of the state label. A body with
    no marker line gets line as a new last part. The rest of body stays as it is."""
    kind = marker_kind(line)
    text, gap, last = body.rpartition("\n\n")
    lines = last.split("\n")
    if not gap or not all(marker_line(m) for m in lines):
        return f"{body}\n\n{line}"
    kept = [m for m in lines if KEPT.fullmatch(m) and marker_kind(m) != kind]
    rest = [m for m in lines if not KEPT.fullmatch(m)]
    return text + gap + "\n".join(kept + [line] + rest)


def mark(number, line):
    """Records line, a marker line of KEPT, in the label comment of the item number (with_marker), and writes nothing
    else: the state label and the text of the label comment stay as they are. An item with no label comment gets one
    of the state working, which has no state label, with line."""
    marker_kind(line)
    labels = read_labels(number)
    old = labels[-1] if labels else None
    body = label_comment("working", "", [line]) if old is None else with_marker(old["body"], line)
    if old is not None and body == old["body"]:
        print(f"#{number}: its label comment holds {line} already.")
        return
    write_label(number, old, body)
    print(f"#{number}: its label comment holds {line}.")


def set_state(number, facts, markers=(), head="", labels=None):
    """Gives the item number the state that facts give (label_state), with its state label and its label comment
    (apply, with labels): for an outside pull request, with the steps of R12 for the import. The label comment is made
    once before any write, so that a marker or a head that it refuses changes nothing on GitHub."""
    state = label_state(**facts)
    imports = None
    if facts.get("kind") == "pr" and facts.get("outsider"):
        imports = (facts.get("import_paths"), facts.get("decision", ""))
    label_comment(state, "", markers, head, imports)
    apply(number, state, markers, head, imports, labels)


def parse(args):
    """The facts, the marker lines and the head of label's arguments: <fact>=<value> for each fact of FACTS (true or
    false, or empty for false, for each fact that is one or the other), head=<commit>, and marker=<line>. The job gives
    import_paths=<text> only when the variable is set."""
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


# --- the import check (R12) ---------------------------------------------------------------------------------------
# compile_glob, compile_globs, glob_match, translate, bracket, utf16, char_range and without_slash are a port of
# theorem-labs/agent-infra repo-pairs/paths/paths.go at a2295ab4f1d7dc019ad005707b7c6bf1003594c1 (its Compile and
# Match), the path matcher of the import (dispatch://OSSV-318), so that this workflow matches the changed paths as the
# import does. GlobTest in .github/test_review.py holds each case of its paths_test.go at that commit. The rules are
# Copybara's glob(): a pattern is a Java glob over the whole path from the root of the repository.
#
# - `*` matches any run of characters inside one part of the path, and `?` one character.
# - `**` matches any run of characters across parts, so `dir/**` covers each file under `dir/`, and `**/x` matches `x`
#   only below the top folder.
# - `[...]` matches one character of a set, `[!...]` one character outside it, and neither ever matches `/`.
# - `{a,b}` matches either choice, and `\` makes the next character literal.
#
# Java's `.` does not match a line end, so `**` stops at a newline, a carriage return, U+0085, U+2028 and U+2029, while
# `*`, `?` and a bracket expression match them. A pattern that Copybara refuses is refused here: an empty string, a `.`
# or `..` part, a leading `/`, and a glob that Java cannot translate. Java reads a bracket expression in UTF-16 code
# units (bracket says how). Like paths.go, the port is stricter than Copybara on some inputs, and never looser: it
# refuses an empty bracket expression, a range that ends on `\`, on `[` or on `&` before `&`, and a pattern or a path
# that is not valid UTF-8 (in Python, a str that holds a surrogate, as surrogateescape gives for such bytes).
# glob_match raises ValueError for such a path, so that a refusal is never read as a path that does not match.

# The check run of R12.
CHECK = "repo-pairs/import-approved"
# Java's `.*`: any run of characters but the line ends that Java's `.` does not match.
ANY_RUN = r"[^\n\r\x85\u2028\u2029]*"
# Copybara's FileUtil.RELATIVISM, (.*/)?[.][.]?(/.*)?, with Java's `.`.
RELATIVISM = re.compile(rf"(?:{ANY_RUN}/)?\.\.?(?:/{ANY_RUN})?")
SURROGATE = re.compile(r"[\ud800-\udfff]")
# The markers at the start of a review comment (D8): the head that it reviewed, and the review's verdict at that head,
# after the soundness rule, with will-fix when the author said they will make the change.
REVIEWED = re.compile(r"<!-- review -->\n<!-- review-head ([0-9a-f]{40}) -->\n"
                      r"<!-- review-verdict \1 (pass|blocking|person)( will-fix)? -->(?:\n|$)")


def compile_glob(pattern):
    """The regular expression of one pattern of the import, for re.fullmatch: paths.go's compile."""
    if not isinstance(pattern, str) or pattern == "":
        raise ValueError("an empty pattern")
    if SURROGATE.search(pattern):
        raise ValueError("not valid UTF-8")
    if RELATIVISM.fullmatch(pattern):
        raise ValueError("a `.` or `..` part")
    if pattern.startswith("/"):
        raise ValueError("a leading /")
    try:
        return re.compile(translate(pattern))
    except re.error as e:
        raise ValueError(f"not a pattern that Java can translate: {e}") from None


def compile_globs(patterns):
    """The compiled patterns of a list, for glob_match: paths.go's Compile. An empty list matches nothing."""
    compiled = []
    for pattern in patterns:
        try:
            compiled.append(compile_glob(pattern))
        except ValueError as e:
            raise ValueError(f"path pattern {pattern!r}: {e}") from None
    return compiled


def glob_match(compiled, path):
    """Whether path, relative to the root of the repository and with / between its parts, as git gives it, matches
    one pattern of compiled: paths.go's Match. A ValueError when path is not valid UTF-8."""
    if SURROGATE.search(path):
        raise ValueError(f"path {path!r}: not valid UTF-8")
    return any(r.fullmatch(path) for r in compiled)


def translate(glob):
    """The regular expression of glob: Java's sun.nio.fs.Globs.toUnixRegexPattern, as paths.go writes it for Go and
    this function for Python. Java writes a bracket expression as the class intersection [[^/]&&[...]], which Python
    lacks, so bracket builds the set with / taken out of it."""
    out, i, group = [], 0, False
    while i < len(glob):
        c = glob[i]
        i += 1
        if c == "\\":
            if i == len(glob):
                raise ValueError("no character to escape at the end")
            out.append(re.escape(glob[i]))
            i += 1
        elif c == "[":
            found, i = bracket(glob, i)
            out.append(found)
        elif c == "{":
            if group:
                raise ValueError("a group inside a group")
            out.append("(?:(?:")
            group = True
        elif c == "}":
            out.append("))" if group else r"\}")
            group = False
        elif c == "," and group:
            out.append(")|(?:")
        elif c == "*":
            if glob[i:i + 1] == "*":
                out.append(ANY_RUN)
                i += 1
            else:
                out.append("[^/]*")
        elif c == "?":
            out.append("[^/]")
        else:
            out.append(re.escape(c))
    if group:
        raise ValueError("a group with no closing }")
    return "".join(out)


def utf16(text):
    """The UTF-16 code units of text, in which Java reads a bracket expression."""
    units = []
    for c in text:
        n = ord(c)
        if n > 0xFFFF:
            units += [0xD800 + ((n - 0x10000) >> 10), 0xDC00 + ((n - 0x10000) & 0x3FF)]
        else:
            units.append(n)
    return units


def bracket(glob, i):
    """The character class of the bracket expression whose [ is just before glob[i], as Java reads it, and the index
    after its ].

    Java's translation reads the expression in UTF-16 code units. A leading ^ is a literal ^; otherwise a leading !
    negates, and a - after it, or first, is a literal -. After that, a unit other than -, / and ] that does not end a
    range is a range start, and a - right after a range start makes a range from it to the next unit, refused when the
    end's unit is below the start's; a - with no range start before it refuses the pattern, as / does. ] closes the
    expression, also in place of a range end, which leaves that - a literal -; the end of the pattern, or a NUL in place
    of a range end, leaves it unclosed. The translation copies the units to its regular expression, and leaves a range
    end that is \\, [, or & before & unescaped, which Java's regular expression would read as syntax: such a range is
    refused here.

    Java's regular expression reads the units back in characters, joining each surrogate pair: a character, a - and one
    more character make a range, refused when its end is below its start, and every other character, a - just before ]
    too, stands for itself."""
    units = utf16(glob[i:])

    def unit(k):
        # Java's next(): the unit at k, or 0, Java's end of the pattern, past the last unit.
        return units[k] if k < len(units) else 0

    k, negate, found = 0, False, []
    if unit(k) == ord("^"):
        found.append((ord("^"), ord("^")))
        k += 1
    else:
        if unit(k) == ord("!"):
            negate = True
            k += 1
        if unit(k) == ord("-"):
            found.append((ord("-"), ord("-")))
            k += 1
    start, has_start, last, closed = k, False, 0, False
    while k < len(units):
        c = units[k]
        k += 1
        if c == ord("]"):
            closed = True
            break
        if c == ord("/"):
            raise ValueError("a / inside a bracket expression")
        if c != ord("-"):
            has_start, last = True, c
            continue
        if not has_start:
            raise ValueError("a range with no start in a bracket expression")
        end = unit(k)
        k += 1
        if end == 0:
            break
        if end == ord("]"):
            closed = True
            break
        if end < last:
            raise ValueError("a range whose end is before its start in UTF-16 code units, as Java compares them, in a "
                             "bracket expression")
        if end in (ord("\\"), ord("[")) or (end == ord("&") and unit(k) == ord("&")):
            raise ValueError("a range that ends on \\, on [ or on && in a bracket expression, which the import's rules "
                             "refuse though Copybara may accept it")
        has_start = False
    if not closed:
        raise ValueError("a bracket expression with no closing ]")
    # Java closed the expression at the first ] after the prefix. The prefix is ASCII, and no surrogate pair holds a ],
    # so the characters between are the characters up to the first ].
    body = glob[i + start:]
    body = body[:body.index("]")]
    rest = i + start + len(body) + 1
    j = 0
    while j < len(body):
        lo = hi = ord(body[j])
        j += 1
        if j + 1 < len(body) and body[j] == "-":
            hi = ord(body[j + 1])
            j += 2
            if hi < lo:
                raise ValueError("a range whose end is before its start in a bracket expression")
        found.append((lo, hi))
    if not found:
        raise ValueError("an empty bracket expression")
    if negate:
        # Java's [[^/]&&[^set]]: neither the set nor /.
        return "[^/" + "".join(map(char_range, found)) + "]", rest
    # Java's [[^/]&&[set]]: the set without /, which only a range can hold.
    parts = [part for r in found for part in without_slash(r)]
    if not parts:
        return r"[^\x00-\U0010ffff]", rest
    return "[" + "".join(map(char_range, parts)) + "]", rest


def without_slash(r):
    lo, hi = r
    slash = ord("/")
    if lo > slash or hi < slash:
        return [r]
    return ([(lo, slash - 1)] if lo < slash else []) + ([(slash + 1, hi)] if hi > slash else [])


def char_range(r):
    lo, hi = r
    return f"\\U{lo:08x}" + (f"-\\U{hi:08x}" if hi != lo else "")


def steering(path):
    """Whether path is a steering file: each file under .github/, as this repository has no CODEOWNERS."""
    return path.startswith(".github/")


def import_globs(value):
    """The compiled globs of the text value of REPO_PAIRS_IMPORT_PATHS: one glob on each line, and none on an empty
    line."""
    try:
        return compile_globs([line for line in value.split("\n") if line])
    except ValueError as e:
        raise ValueError(f"REPO_PAIRS_IMPORT_PATHS: {e}") from None


def imported(globs, path):
    """Whether the import takes path: one of its globs matches it. The import does not take a path that its rules
    refuse."""
    try:
        return glob_match(globs, path)
    except ValueError:
        return False


def changed_paths(files):
    """Each path that files change, as the API lists them (pulls/<n>/files): the path of each file, and the path that
    it had before a rename."""
    paths = []
    for f in files:
        if not (isinstance(f, dict) and isinstance(f.get("filename"), str) and f["filename"]
                and isinstance(f.get("previous_filename") or "", str)):
            raise ValueError(f"not a file as pulls/<n>/files lists it: {f!r}")
        paths.append(f["filename"])
        if f.get("previous_filename"):
            paths.append(f["previous_filename"])
    return paths


def import_decision(files, changed_files, screen, verdict, hold, value):
    """R12's decision on the import check run at a head of an outside pull request: record, or the first of its rules
    that does not hold (DECISIONS). files are the head's files as the API lists them on every page of pulls/<n>/files,
    and changed_files is the pull request's count of them, which the list reaches only up to 3,000 files. screen is
    whether the screen passed the head, verdict the review's verdict after the soundness rule (SOUNDNESS_HOLD), hold
    whether the soundness hold lasts, and value the text of REPO_PAIRS_IMPORT_PATHS (None when it is not set). The
    rules on each changed path are judged first on the paths that the list gives, so that a steering file, or a path
    that the import does not take, gives its own decision also when the list is not whole."""
    if verdict not in VERDICTS:
        raise ValueError(f"not a verdict: {verdict!r}")
    paths = changed_paths(files)
    if not screen:
        return "screen"
    if verdict not in ("pass", "person"):
        return "verdict"
    if any(steering(p) for p in paths):
        return "steering"
    if value is not None:
        globs = import_globs(value)
        if not all(imported(globs, p) for p in paths):
            return "outside"
    if len(files) != changed_files:
        return "unread"
    if verdict == "person":
        return "person"
    if hold and not all(p.endswith(".md") for p in paths):
        return "markdown"
    return "record"


def import_marker(head, value):
    """The marker line of R12 that records the value of REPO_PAIRS_IMPORT_PATHS on which a decision on head rested: the
    text value as one JSON string, or null when the variable is not set (value None). Each character outside ASCII,
    <, > and & is a \\u escape, so the line holds no line break and no --> before its end."""
    if not HEAD.fullmatch(head):
        raise ValueError(f"not a head commit: {head!r}")
    data = "null" if value is None else json.dumps(value)
    for c in "<>&":
        data = data.replace(c, f"\\u{ord(c):04x}")
    return f"<!-- repo-pairs-import-paths {head}: {data} -->"


def check_run(head, value, hold):
    """The body of the request that records the import check run on head (POST repos/<repo>/check-runs), when
    import_decision gives record. Its output text is the marker line of import_marker, alone."""
    summary = ["The automated screen and the automated review passed this head commit.",
               "No changed file is under `.github/`."]
    if hold:
        summary.append("Each changed file is a Markdown file. For now, the workflow records this check only for such "
                       "a change, because stock Rocq accepts three public proofs of `False`.")
    summary.append("The import copies each changed path." if value is not None else
                   "The variable `REPO_PAIRS_IMPORT_PATHS` is not set, so the workflow did not compare the changed "
                   "paths with the paths of the import.")
    return {"name": CHECK, "head_sha": head, "status": "completed", "conclusion": "success",
            "output": {"title": "Approved for the import", "summary": " ".join(summary),
                       "text": import_marker(head, value)}}


def review_verdict(comments, head):
    """The verdict of the review comment of BOT that names head, from comments, the item's comments as the API lists
    them (issues/<n>/comments), the last one when more name it. "" when none names head. Only the markers at the start
    of the comment count: no marker of the model's or the reader's text reaches a comment (trim.py inert)."""
    found = ""
    for c in comments:
        m = REVIEWED.match(c.get("body") or "")
        if m and of_bot(c) and m.group(1) == head:
            found = m.group(2)
    return found


# --- the soundness rule (R8) --------------------------------------------------------------------------------------
# uses, code, section and the constants from USES to LISTED are copied from theorem-labs/oss-verify-proofs-internal
# .github/review/rules.py at 573d0cde18e1, and adapted to this repository: its checks are its CI lanes on stock Rocq,
# not oft check; code keeps a path of any form in one code span, because trim.py does not make the section inert; and
# the section names Sami and the files of the build. The files that the rule counts (proofs, dune_names) and the rule
# itself (soundness, forced) are this file's own.

# Each construct of "Soundness of a Rocq proof" that a line can use: its name in the section, and its pattern.
USES = (
    ("vm_compute", re.compile(r"\bvm_compute\b")),
    ("vm_cast_no_check", re.compile(r"\bvm_cast_no_check\b")),
    ("native_compute", re.compile(r"\bnative_compute\b")),
    ("native_cast_no_check", re.compile(r"\bnative_cast_no_check\b")),
    ("<:", re.compile(r"(?<!<)<:")),
    ("<<:", re.compile(r"<<:")),
    ("PArray", re.compile(r"\bPArray\b")),
    ("PrimArray", re.compile(r"\bPrimArray\b")),
    # The primitives of the array type, which a file can register itself with no PArray (Primitive array := ...).
    ("#array_", re.compile(r"#array_\w*")),
)
# An array literal, [| a; b | default |], which can span lines: the elements and the default hold no |, [ or ]. An
# intro pattern such as [|n IH], [|[|]] or [|destruct n as [|]] is none.
LITERAL = re.compile(r"\[\|[^|\[\]]*\|[^|\[\]]*\|\]")
# make of the array module: PArray.make, or make in a file that names the array module or its primitives.
MAKE = re.compile(r"\bmake\b")
ARRAY_MODULE = re.compile(r"\bPArray\b|\bPrimArray\b|#array_")
# The most lines that the section of the comment lists, and the most characters of its list, so that the comment
# stays under GitHub's limit whatever the paths are; the section in the run's summary lists them all.
LISTED = 100
LISTED_CHARACTERS = 10_000
# The issues of stock Rocq's three public proofs of False. The section gives each in a code span: GitHub links none of
# them, and so adds no mention of each review to these issues of rocq-prover/rocq.
ISSUES = ("rocq-prover/rocq#22651", "rocq-prover/rocq#22760", "rocq-prover/rocq#22772")
# The facts of the rule that the gather job writes into the .review/ of a pull request (proofs), and why a changed path
# counts: a .v file, a file of the build (BUILD), a file that a dune file names, or the file that such a link points to.
SOUNDNESS_FILE = "soundness.json"
WHYS = ("proof", "build", "named", "target")
# The files that tell dune how to build the proofs, by their name in any directory.
BUILD = ("dune", "dune-project", "dune-workspace")
# The modes of a regular file and of a link in a tree of git.
REGULAR = ("100644", "100755")
LINK = "120000"
# The most bytes of a dune file, or of a file that it includes, that the rule reads, and the most includes in a chain:
# a longer file or chain is a file of the build that the job could not read.
DUNE_BYTES = 1 << 20
INCLUDES = 20
# The characters between the tokens of a dune file, an atom, and the escapes of a quoted string, as dune 3 reads them.
BLANKS = " \t\n\r\f"
ATOM = re.compile(r'[^ \t\n\r\f;()"]+')
STRING_ESCAPES = {"n": "\n", "t": "\t", "b": "\b", "r": "\r", "\\": "\\", '"': '"', "'": "'", "%": "%"}
# A variable of a dune file, %{<name>} or %{<name>:<argument>}, and the characters that make a name a glob.
VARIABLE = re.compile(r"%\{([^}]*)\}")
GLOB = re.compile(r"[*?\[{]")
# The actions whose strings a shell reads, and the shells that (run <shell> ...) starts: the rule takes each word of
# such a string as a name too.
SHELL_ACTIONS = ("system", "bash")
SHELLS = ("sh", "bash", "dash", "ksh", "zsh")
SHELL_WORD = re.compile(r"[^\s;|&<>()`'\"$=]+")
# A line of omitted.txt, as the gather job writes it, for a changed file that .review/head/ holds only in part.
CUT = re.compile(r"(.+): cut at 2 MiB of its [0-9]+ bytes")
# A question on soundness in the review's list, and the question that the rule adds when the list has none.
ON_SOUNDNESS = re.compile(r"(?i)sound")
QUESTION = {"kind": "question", "ref": None, "optional": False,
            "text": "Are the proofs sound after the changes of this pull request? A pass of the CI lanes on stock Rocq "
                    "does not show it."}


def head_proofs(review):
    """The .v files under <review>/head/, which holds each file that the pull request adds or changes as its head has
    it, as paths of the pull request, in order."""
    head = os.path.join(review, "head")
    found = []
    for root, _dirs, files in os.walk(head):
        for name in files:
            if name.endswith(".v"):
                found.append(os.path.relpath(os.path.join(root, name), head).replace(os.sep, "/"))
    return sorted(found)


def dune_sexps(text):
    """The S-expressions of the text of a dune file, as dune 3 reads them: a list is a list, and an atom or a quoted
    string is a str. A ; starts a comment to the end of its line, also inside an atom, and #| and #; are atoms. A
    ValueError for a text that dune refuses or that this reader does not read: a ( or a ) with no pair, a string with
    no end, or an escape that dune does not know (a block string, "\\| or "\\>, among them)."""
    stack, i = [[]], 0
    while i < len(text):
        c = text[i]
        if c in BLANKS:
            i += 1
        elif c == ";":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif c == "(":
            stack.append([])
            i += 1
        elif c == ")":
            if len(stack) == 1:
                raise ValueError("a ) with no (")
            done = stack.pop()
            stack[-1].append(done)
            i += 1
        elif c == '"':
            value, i = dune_string(text, i + 1)
            stack[-1].append(value)
        else:
            m = ATOM.match(text, i)
            stack[-1].append(m.group())
            i = m.end()
    if len(stack) > 1:
        raise ValueError("a ( with no )")
    return stack[0]


def dune_string(text, i):
    """The value of the quoted string of a dune file whose first character is text[i], after its opening quote, and
    the index after its closing quote."""
    out = []
    while i < len(text):
        c = text[i]
        if c == '"':
            return "".join(out), i + 1
        if c != "\\":
            out.append(c)
            i += 1
            continue
        escape, digits = text[i + 1:i + 2], text[i + 1:i + 4]
        if escape in STRING_ESCAPES:
            out.append(STRING_ESCAPES[escape])
            i += 2
        elif escape == "\n":
            i += 2
            while i < len(text) and text[i] in " \t":
                i += 1
        elif re.fullmatch(r"[0-9]{3}", digits) and int(digits) < 256:
            out.append(chr(int(digits)))
            i += 4
        elif escape == "x" and re.fullmatch(r"[0-9A-Fa-f]{2}", text[i + 2:i + 4]):
            out.append(chr(int(text[i + 2:i + 4], 16)))
            i += 4
        else:
            raise ValueError(f"an escape that dune does not know: \\{escape}")
    raise ValueError("a string with no end")


def from_root(base, name):
    """The path from the root of the repository of name, a path of a dune file from the directory base: "" for the
    root itself, and None for a path outside the repository."""
    if name.startswith("/"):
        return None
    path = posixpath.normpath(posixpath.join(base, name))
    if path == ".":
        return ""
    return None if path == ".." or path.startswith("../") else path


def expand(name, base):
    """name, an atom or a quoted string of a dune file in the directory base, after dune's variables, and the argument
    of each variable %{<name>:<argument>} (dep, read, exe and the others name a file so), or None when name is one
    variable with no argument alone (%{target}, %{deps}), which names no file of its own. %{project_root} and
    %{workspace_root} are the root, and any other variable in a longer name can be any text (a * of a glob)."""
    arguments = []
    up = "/".join([".."] * (base.count("/") + 1)) if base else "."

    def value(m):
        inner = m.group(1)
        if inner in ("project_root", "workspace_root"):
            return up
        if ":" in inner:
            arguments.append(inner.split(":", 1)[1])
            return arguments[-1]
        return "*"
    alone = VARIABLE.fullmatch(name)
    text = VARIABLE.sub(value, name)
    if alone and text == "*":
        return None, arguments
    return text, arguments


def braces_close(glob, i):
    """Whether the { at glob[i] has a } that closes it."""
    depth = 0
    while i < len(glob):
        if glob[i] == "\\":
            i += 2
            continue
        depth += {"{": 1, "}": -1}.get(glob[i], 0)
        if depth == 0:
            return True
        i += 1
    return False


def glob_pattern(glob):
    """The regular expression of a dune glob from the root of the repository, wider than dune's, so that it misses no
    path that dune's glob matches, nor one that glob_files_rec matches, which applies the glob in each directory below
    its own: * and ? match any characters, / among them, a bracket expression matches any one character, {a,b} either
    choice, and \\ makes the next character literal. A { or a [ with no pair is a character of the name."""
    out, i, depth = [], 0, 0
    while i < len(glob):
        c = glob[i]
        if c == "\\" and i + 1 < len(glob):
            out.append(re.escape(glob[i + 1]))
            i += 2
            continue
        if c == "[" and (end := glob.find("]", i + 2)) > 0:
            out.append(".")
            i = end + 1
            continue
        if c == "*":
            out.append(".*")
        elif c == "?":
            out.append(".")
        elif c == "{" and braces_close(glob, i):
            out.append("(?:")
            depth += 1
        elif c == "," and depth:
            out.append("|")
        elif c == "}" and depth:
            out.append(")")
            depth -= 1
        else:
            out.append(re.escape(c))
        i += 1
    return re.compile("".join(out), re.S)


class Names:
    """The files that the dune files of a head name, each from the root of the repository, with the file that names
    it: files by their path, trees (each file below a directory, for source_tree) and globs (glob_pattern)."""

    def __init__(self):
        self.files, self.trees, self.globs = {}, [], []

    def add(self, by, name, base, tree=False):
        """Takes name, an atom or a quoted string of the file by, as the name of a file (of each file below a directory
        for tree) from the directory base, with the argument of each of its variables (expand)."""
        text, arguments = expand(name, base)
        for argument in arguments:
            self.add(by, argument, base, tree)
        path = None if text is None else from_root(base, text)
        if path is None or (not path and not tree):
            return
        if GLOB.search(path):
            self.globs.append((glob_pattern(path + "/*" if tree else path), by))
        elif tree:
            self.trees.append((path, by))
        else:
            self.files.setdefault(path, by)

    def of(self, path):
        """The file that names path, or None when no dune file names it."""
        if path in self.files:
            return self.files[path]
        for tree, by in self.trees:
            if not tree or path.startswith(tree + "/"):
                return by
        return next((by for pattern, by in self.globs if pattern.fullmatch(path)), None)


def dune_names(names, by, node, here, bases, read, depth=0, shell=False):
    """Adds to names each file that node, an S-expression of the file by (a dune file, or a file that one includes),
    names: each atom and each quoted string, from the directory of its stanza (here) and from each directory of a
    chdir around it (bases), and each word of a string that a shell reads. (subdir <dir> ...) moves here to <dir>,
    (source_tree <dir>) names each file below <dir>, and (include <file>) names <file> and, from here, each file that
    the stanzas of <file> name: read(path) gives the text of a file of the head. A ValueError for a subdir outside the
    repository, and for an include that the job cannot read or that is deeper than INCLUDES."""
    if isinstance(node, str):
        for word in [node] + (SHELL_WORD.findall(node) if shell else []):
            for base in bases:
                names.add(by, word, base)
        return
    head = node[0] if node and isinstance(node[0], str) else None
    if head == "subdir" and len(node) > 1 and isinstance(node[1], str):
        sub = from_root(here, node[1])
        if sub is None:
            raise ValueError(f"(subdir {node[1]}) is outside the repository")
        for child in node[2:]:
            dune_names(names, by, child, sub, [sub], read, depth)
        return
    if head == "include" and len(node) == 2 and isinstance(node[1], str):
        path = from_root(here, node[1])
        if not path or depth >= INCLUDES:
            raise ValueError(f"(include {node[1]}) cannot be read")
        names.add(by, node[1], here)
        for stanza in dune_sexps(read(path)):
            dune_names(names, path, stanza, here, [here], read, depth + 1)
        return
    if head == "source_tree" and len(node) == 2 and isinstance(node[1], str):
        for base in bases:
            names.add(by, node[1], base, tree=True)
    if head == "chdir" and len(node) > 2 and isinstance(node[1], str):
        moved = [from_root(base, text) for base in bases for text in [expand(node[1], base)[0]] if text is not None]
        bases = bases + [d for d in moved if d is not None]
    shell = shell or head in SHELL_ACTIONS or (head == "run" and len(node) > 2 and isinstance(node[1], str)
                                               and posixpath.basename(node[1]) in SHELLS)
    for child in node:
        dune_names(names, by, child, here, bases, read, depth, shell)


def git(*args, cwd=None):
    """The standard output of git with args, as bytes."""
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, check=True).stdout


def head_tree(head, cwd=None):
    """{path: (mode, object)} of each file of the tree of the commit head, from git objects."""
    tree = {}
    for entry in git("ls-tree", "-r", "-z", "--full-tree", head, cwd=cwd).split(b"\0"):
        if entry:
            meta, path = entry.split(b"\t", 1)
            mode, _kind, oid = meta.decode("ascii").split(" ")
            tree[path.decode("utf-8", "surrogateescape")] = (mode, oid)
    return tree


def proofs(head, files, count, cwd=None):
    """The facts of the soundness rule at the commit head of a pull request, as soundness.json holds them: {whole,
    files, unparsed}. files are the files of the pull request at head as the API lists them on every page of
    pulls/<n>/files, and count its changed_files, None when a read did not finish or read another head. whole: the
    list holds each changed file. files: each changed path (of a file, and the path that it had before a rename) that
    can change a proof, {path, why, by, at_head}: why is proof for a .v file, build for a file of BUILD, named for a
    file that the dune file by names (dune_names), and target for the file that the link by points to, when the link's
    own path counts; at_head says whether head has the path. unparsed: each dune file, or link that counts, that the
    job could not read: not a regular file, over DUNE_BYTES, not UTF-8, or not read by dune_sexps. The dune files and
    the links come from git objects of head, in the repository of cwd."""
    tree = head_tree(head, cwd)

    def read(path, kinds=REGULAR, limit=DUNE_BYTES):
        mode, oid = tree.get(path, ("", ""))
        if mode not in kinds:
            raise ValueError(f"{path} has the mode {mode or 'of no file'} at {head}")
        if int(git("cat-file", "-s", oid, cwd=cwd)) > limit:
            raise ValueError(f"{path} holds over {limit} bytes")
        try:
            return git("cat-file", "blob", oid, cwd=cwd).decode("utf-8")
        except UnicodeDecodeError:
            raise ValueError(f"{path} is not UTF-8 text") from None

    names, unparsed, targets = Names(), [], {}
    for path in sorted(tree):
        if posixpath.basename(path) == "dune":
            here = posixpath.dirname(path)
            try:
                for stanza in dune_sexps(read(path)):
                    dune_names(names, path, stanza, here, [here], read)
            except ValueError:
                unparsed.append(path)

    def counts(path):
        if path.endswith(".v"):
            return "proof", None
        if posixpath.basename(path) in BUILD:
            return "build", None
        by = names.of(path)
        if by:
            return "named", by
        to = next((t for t in targets if path == t or path.startswith(t + "/")), None)
        return ("target", targets[to]) if to is not None else (None, None)
    # The build reads a file through a link to it: so the file that a link that counts points to counts too (a link
    # in the place of a dune file among them), and a chain of links reaches its end in at most as many rounds as there
    # are links.
    links = sorted(p for p, (mode, _oid) in tree.items() if mode == LINK)
    failed = set()
    for _ in links:
        before = len(targets)
        for link in links:
            if link in failed or not counts(link)[0]:
                continue
            try:
                to = from_root(posixpath.dirname(link), read(link, (LINK,), 4096))
            except ValueError:
                failed.add(link)
                continue
            if to:
                targets.setdefault(to, link)
        if len(targets) == before:
            break
    unparsed = sorted(set(unparsed) | failed)
    paths = set()
    for f in files:
        try:
            paths.update(changed_paths([f]))
        except ValueError:
            count = None
    found = [{"path": p, "why": why, "by": by, "at_head": p in tree}
             for p in sorted(paths) for why, by in [counts(p)] if why]
    return {"whole": count is not None and count == len(files), "files": found, "unparsed": unparsed}


def facts_of(review):
    """The facts of soundness.json in review, a .review/ (proofs), or None for an issue's, which has none. A pull
    request's .review/ (it holds commits.txt) with no such file, or with one in another form, gives a list that is not
    whole."""
    path = os.path.join(review, SOUNDNESS_FILE)
    unread = {"whole": False, "files": [], "unparsed": []}
    if not os.path.exists(path):
        return unread if os.path.exists(os.path.join(review, "commits.txt")) else None
    try:
        with open(path, encoding="utf-8") as f:
            facts = json.load(f)
    except ValueError:
        return unread
    if not (isinstance(facts, dict) and isinstance(facts.get("whole"), bool)
            and isinstance(facts.get("files"), list) and isinstance(facts.get("unparsed"), list)
            and all(isinstance(f, dict) and isinstance(f.get("path"), str) and f.get("why") in WHYS
                    for f in facts["files"])
            and all(isinstance(p, str) for p in facts["unparsed"])):
        return unread
    return facts


def cut_files(review):
    """The changed files that omitted.txt of review names as cut at 2 MiB."""
    path = os.path.join(review, "omitted.txt")
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8", errors="replace") as f:
        return {m.group(1) for line in f.read().split("\n") if (m := CUT.fullmatch(line))}


def uses(review):
    """[(path, line, [construct, ...])] of each line of the .v files under <review>/head/ that uses a construct of
    USES, an array literal or make of the array module, in the order of the files and their lines. A deleted file has
    no line."""
    found = []
    for path in head_proofs(review):
        with open(os.path.join(review, "head", path), encoding="utf-8", errors="replace") as f:
            text = f.read()
        lines = text.split("\n")
        at = {}
        for n, line in enumerate(lines, 1):
            for name, pattern in USES:
                if pattern.search(line):
                    at.setdefault(n, []).append(name)
        for m in LITERAL.finditer(text):
            at.setdefault(text.count("\n", 0, m.start()) + 1, []).append("[| |]")
        array_module = bool(ARRAY_MODULE.search(text))
        for n, line in enumerate(lines, 1):
            if MAKE.search(line) and (array_module or re.search(r"\bPArray\.make\b", line)):
                at.setdefault(n, []).append("make")
        found += [(path, n, names) for n, names in sorted(at.items())]
    return found


def code(text):
    """text as one Markdown code span on one line, whatever it holds: a path of a pull request can hold backticks and
    line breaks. Each control character shows as \\x and its two hex digits, and the backticks of the span outnumber
    each run of backticks in text. GitHub shows no mention, reference, link or HTML in a code span."""
    text = re.sub(r"[\x00-\x1f\x7f]", lambda m: f"\\x{ord(m.group(0)):02x}", text)
    ticks = "`" * (max((len(r) for r in re.findall(r"`+", text)), default=0) + 1)
    pad = " " if text.startswith("`") or text.endswith("`") else ""
    return f"{ticks}{pad}{text}{pad}{ticks}"


def section(found, listed=LISTED, characters=LISTED_CHARACTERS, scope=None):
    """The fixed section on soundness: why the rule holds, from scope (soundness; None for a change of a .v file and
    nothing else), and the facts for Sami: the changed files of the build, the files of the build that the job could
    not read, the lines that found holds (uses), and the changed .v files at the head that the search did not read
    whole. Its lists hold at most listed lines in at most characters characters in all, and a list that holds fewer
    than it has ends with a line that says how many more there are."""
    scope = scope or {"v": True, "others": [], "whole": True, "unparsed": [], "unread": []}
    issues = ", ".join(code(i) for i in ISSUES[:-1]) + f" and {code(ISSUES[-1])}"
    if scope["v"]:
        why = "This pull request adds, changes or deletes a `.v` file, which holds Rocq proofs."
    elif scope["others"]:
        why = "This pull request changes a file that the build of the Rocq proofs reads or writes."
    else:
        why = "The workflow cannot show that this pull request changes no Rocq proof."
    parts = [f"**Soundness of the proofs.** {why} The CI lanes of this repository check the proofs on stock Rocq. "
             f"Stock Rocq accepts three public proofs of `False`: {issues}. So when these lanes pass, that does not "
             "show that the proofs are sound. Sami answers whether the proofs are sound. You do not need to do "
             "anything for this point."]
    room = [listed, characters]

    def listing(lines, more):
        kept = []
        for line in lines:
            if not room[0] or len(line) > room[1]:
                break
            kept.append(line)
            room[0] -= 1
            room[1] -= len(line) + 1
        if len(kept) < len(lines):
            kept.append(more(len(lines) - len(kept)))
        return "\n".join(kept)

    def files(n):
        return f"- {n} more {'file' if n == 1 else 'files'}. The summary of the workflow run lists all files."
    if scope["others"]:
        lines = [f"- {code(path)}" + (f": {code(by)} names it." if kind == "named" else
                                      f": the link {code(by)} points to it." if kind == "target" else "")
                 for path, kind, by in scope["others"]]
        parts.append("The build of the proofs reads or writes these changed files:\n\n" + listing(lines, files))
    if not scope["whole"]:
        parts.append("GitHub did not give the full list of the files that this pull request changes, so the workflow "
                     "could not check each of them.")
    if scope["unparsed"]:
        parts.append("The workflow could not read these files of the build:\n\n"
                     + listing([f"- {code(path)}" for path in scope["unparsed"]], files))
    if scope["v"]:
        what = "the VM, the native compiler, a cast with no check or a primitive array"
        searched = "The workflow searched the text of the `.v` files that this pull request adds or changes."
        forgery = ("A text search cannot show that a proof is not forged. For example, a proof can use the VM through "
                   "a tactic such as `lia`, with no line that names the VM.")
        if not found:
            parts.append(f"{searched} It found no use of {what}. {forgery}")
        else:
            lines = [f"- {code(f'{path}:{n}')}: {', '.join(code(name) for name in names)}" for path, n, names in found]
            parts.append(f"{searched} It found these uses of {what}. The workflow lists these uses as facts, not as "
                         f"failures. Honest proofs use the same constructs. {forgery}\n\n" + listing(
                             lines, lambda n: f"- {n} more {'line uses' if n == 1 else 'lines use'} these constructs. "
                                              "The summary of the workflow run lists all lines."))
        if scope["unread"]:
            lines = [f"- {code(path)}: " + ("the workflow read only its first 2 MiB." if how == "cut" else
                                            "the workflow did not read it.") for path, how in scope["unread"]]
            parts.append("The workflow did not read all of the text of these `.v` files:\n\n" + listing(lines, files))
    return "\n\n".join(parts)


def forced(output):
    """The review's output after the soundness rule: the verdict person, whatever the model gave, and QUESTION at the
    end of the list when the list has no question on soundness that is not optional."""
    items = list(output["items"])
    if not any(isinstance(i, dict) and i.get("kind") == "question" and not i.get("optional")
               and ON_SOUNDNESS.search(i.get("text") or "") for i in items):
        items.append(dict(QUESTION))
    return dict(output, verdict="person", items=items)


def soundness(review, output, hold, outside):
    """(output, section, all): the review's output after the soundness rule, the section of the comment, and the
    section with every line for the run's summary. The rule holds while hold is true, for an outside pull request
    (outside is not false) that changes a path that the facts of review count (facts_of) or a .v file under head/,
    whose list of changed paths is not whole, or for which a file of the build could not be read. When it does not
    hold: output as it is, and no section."""
    if hold != "true" or outside == "false":
        return output, "", ""
    facts = facts_of(review) or {"whole": True, "files": [], "unparsed": []}
    read = set(head_proofs(review))
    changed = [f for f in facts["files"] if f["why"] == "proof"]
    others = [(f["path"], f["why"], f.get("by")) for f in facts["files"] if f["why"] != "proof"]
    if not (read or changed or others or not facts["whole"] or facts["unparsed"]):
        return output, "", ""
    # The .v files at the head that the search did not read whole: the gather job cut them, removed them with a
    # directory of Claude Code's instructions, or found a link or a submodule in their place.
    cut = cut_files(review)
    at_head = read | {f["path"] for f in changed if f.get("at_head")}
    unread = [(path, "cut" if path in cut else "unread") for path in sorted(at_head) if path in cut or path not in read]
    scope = {"v": bool(read or changed), "others": others, "whole": facts["whole"], "unparsed": facts["unparsed"],
             "unread": unread}
    found = uses(review)
    return forced(output), section(found, scope=scope), section(found, sys.maxsize, sys.maxsize, scope)


# --- the fix (R2) -------------------------------------------------------------------------------------------------
# BOT, FIX_MARKER, HUNK, ESCAPES, suggested, since_push, fixes, unquote, hunks, whole, on_diff, suggestions and
# json_lines are copied from theorem-labs/oss-verify-proofs-internal .github/review/rules.py at 573d0cde18e1, and
# adapted to this repository: its rules file is .github/review-answer.md, and the sentence of a suggestion off the
# diff names its file and lines with this file's code.

# The account of this workflow's comments and reviews, the marker of a fix review, and the header of a hunk of a git
# diff (its first line and its count of lines on each side, 1 when the diff leaves the count out).
BOT = "github-actions[bot]"
FIX_MARKER = re.compile(r"(?:^|\n)<!-- review-fix ([0-9a-f]{40}) -->(?:\n|$)")
HUNK = re.compile(r"@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")
# The escapes of a path that git writes in quotes (core.quotePath): a byte in octal, and these.
ESCAPES = {"a": 7, "b": 8, "t": 9, "n": 10, "v": 11, "f": 12, "r": 13, '"': 34, "\\": 92}


def suggested(commit):
    """Whether GitHub made the commit from a suggested change: its committer is web-flow, and its message starts with
    "Apply suggestion" (GitHub's "Apply suggestion from @<login>" and "Apply suggestions from code review")."""
    return ((commit.get("committer") or {}).get("login") == "web-flow"
            and ((commit.get("commit") or {}).get("message") or "").startswith("Apply suggestion"))


def since_push(commits, head):
    """The commits from the author's last own push to head, newest first: head, and each first parent while GitHub
    made the commit from a suggested change, up to the first commit that GitHub did not make so. commits is head's
    history as the API gives it; a ValueError when head is not in it."""
    by_sha = {c.get("sha"): c for c in commits}
    if head not in by_sha:
        raise ValueError(f"{head} is not in the commits of its history")
    found, sha = [], head
    while sha in by_sha and sha not in found:
        found.append(sha)
        commit = by_sha[sha]
        parents = commit.get("parents") or []
        if not suggested(commit) or not parents:
            break
        sha = parents[0].get("sha")
    return found


def fixes(commits, reviews, head):
    """The fix reviews of BOT for head or a commit back to the author's last own push."""
    since = set(since_push(commits, head))
    count = 0
    for review in reviews:
        m = FIX_MARKER.search(review.get("body") or "")
        if (review.get("user") or {}).get("login") == BOT and m and m.group(1) in since:
            count += 1
    return count


def unquote(path):
    """A path of a git diff as the file system names it: git writes a path with a quote, a backslash, a control
    character or a byte over 127 in quotes, with escapes."""
    if not (len(path) >= 2 and path[0] == path[-1] == '"'):
        return path
    body, out, i = path[1:-1], bytearray(), 0
    while i < len(body):
        if body[i] == "\\" and re.match(r"[0-7]{3}", body[i + 1:i + 4]):
            out.append(int(body[i + 1:i + 4], 8))
            i += 4
        elif body[i] == "\\" and body[i + 1:i + 2] in ESCAPES:
            out.append(ESCAPES[body[i + 1]])
            i += 2
        else:
            out += body[i].encode("utf-8", "surrogateescape")
            i += 1
    return out.decode("utf-8", "surrogateescape")


def hunks(diff):
    """{path: [(first, last)]}: the right-side lines of each hunk of a git diff, by the path of its right side. Each
    line of a hunk is counted against its header, so a line of a file that starts as a header does (+++, diff --git)
    is read as the file's line. git ends the +++ line of a path that holds a space with a TAB, after the quotes of a
    path that it quotes (diff.c), and quotes a path that holds a TAB: so a TAB at the end of the line is never part of
    the path."""
    found, path, old, new = {}, None, 0, 0
    for line in diff.split("\n"):
        if old > 0 or new > 0:
            tag = line[:1]
            if tag == "\\":
                continue
            old -= tag in (" ", "-")
            new -= tag in (" ", "+")
            continue
        if line.startswith("diff --git "):
            path = None
        elif line.startswith("+++ "):
            right = unquote(line[4:].removesuffix("\t"))
            path = right[2:] if right.startswith("b/") else None
        elif path is not None and (m := HUNK.match(line)):
            old = int(m.group(1) or 1)
            first, new = int(m.group(2)), int(m.group(3) or 1)
            if new:
                found.setdefault(path, []).append((first, first + new - 1))
    return found


def whole(n):
    return isinstance(n, int) and not isinstance(n, bool)


def on_diff(suggestion, found):
    """Whether each line that the suggestion replaces is a right-side line of one hunk of the diff."""
    first, last = suggestion["start_line"], suggestion["line"]
    return 1 <= first <= last and any(a <= first and last <= b for a, b in found.get(suggestion["path"], ()))


def suggestions(fix, diff):
    """The fix {summary, suggestions[, off]}, with only the suggestions on the diff in suggestions. off, there only
    when a suggestion is off the diff, holds each such one as {sentence, why}: the sentence that names its file and
    lines, and its why, which trim.py puts after the trimmed summary. A ValueError when the fix is not {summary,
    suggestions} of .github/review-answer.md."""
    if not (isinstance(fix, dict) and isinstance(fix.get("summary"), str) and isinstance(fix.get("suggestions"), list)):
        raise ValueError("the fix is not {summary, suggestions}")
    found, kept, off = hunks(diff), [], []
    for s in fix["suggestions"]:
        if not (isinstance(s, dict) and isinstance(s.get("path"), str) and whole(s.get("start_line"))
                and whole(s.get("line")) and isinstance(s.get("replacement"), str) and isinstance(s.get("why"), str)):
            raise ValueError("a suggestion is not {path, start_line, line, replacement, why}")
        s = {k: s[k] for k in ("path", "start_line", "line", "replacement", "why")}
        if on_diff(s, found):
            kept.append(s)
        else:
            where = s["path"] + (f":{s['line']}" if s["start_line"] == s["line"] else f":{s['start_line']}-{s['line']}")
            off.append({"sentence": f"The diff of this pull request does not show {code(where)}, so no suggested "
                                    "change can change it.", "why": s["why"]})
    return {"summary": fix["summary"].strip(), "suggestions": kept, **({"off": off} if off else {})}


# --- the relabel (D16) ----------------------------------------------------------------------------------------------
# A relabel run sets the state of a head again, with no model, from what the workflow wrote of that head: after a
# merge conflict that went away with no push, after a change of REPO_PAIRS_IMPORT_PATHS, and when the post job could
# not record the import check run.

# The markers of a hold comment (D8): the hold of work that the rescreen pass tries again, with its task and, for an
# answer, its comment; and the head that the hold names.
TRIED = re.compile(r"\n<!-- review-held-(?:limit|cap|transient) [0-9]+(?: [0-9]+(?: ([a-z]+)(?: [1-9][0-9]*)?)?)? -->"
                   r"(?:\n|$)")
HELD_HEAD = re.compile(r"\n<!-- review-held-head ([0-9a-f]{40}) -->(?:\n|$)")
# The first line of an answer whose author said they will make the change, at the head that it names.
ANSWER_WILL_FIX = re.compile(r"<!-- review-answer [0-9]+ will-fix ([0-9a-f]{40}) -->(?:\n|$)")
# The words of the holds that are not tried again: the screen's, and the catch-up's that could not reopen a pull
# request. Each other such hold is a last try.
SCREEN_HELD = "The automated screen held "
LEFT_CLOSED = ("The workflow closed this pull request so that GitHub starts its checks. It could not reopen the pull "
               "request")


def hold_fact(body):
    """The fact of label_state that the hold comment body gives: held for a hold that the rescreen pass tries again,
    but None for such a hold of an answer, which leaves the state as it was; screen_held for a hold of the screen;
    left_closed for a catch-up that could not reopen the pull request; tries_used_up for each other hold."""
    m = TRIED.search(body)
    if m:
        return None if m.group(1) == "answer" else "held"
    if SCREEN_HELD in body:
        return "screen_held"
    if LEFT_CLOSED in body:
        return "left_closed"
    return "tries_used_up"


def of_bot(item):
    """Whether item, a comment or a review as the API lists it, is BOT's."""
    return (item.get("user") or {}).get("login") == BOT


def fix_heads(reviews):
    """The head that each fix review of BOT among reviews names (FIX_MARKER), in order."""
    return [m.group(1) for r in reviews if of_bot(r) and (m := FIX_MARKER.search(r.get("body") or ""))]


def relabel_facts(comments, reviews, head, history):
    """The facts of label_state for head from what the workflow wrote of it, or None when it wrote nothing of it.
    comments are the item's comments as the API lists them (issues/<n>/comments, with updated_at), reviews() gives the
    pull request's reviews (pulls/<n>/reviews), and history() the history of head (commits?sha=<head>), each read
    only when the facts need it. The newer of the review side (the review comment of BOT that names head, and an
    answer at head whose author said they will make the change) and of a hold comment of BOT that names head gives
    the facts; an answer's hold that is tried again gives none. The review side gives the verdict, will_fix (of the
    review or of an answer), fix_posted (a fix review of head) and fix_stop (a blocking verdict after 2 fix reviews
    since the author's last own push, the fix review of head not counted, as the review job decided it before it
    posted that fix). With neither, a label comment that holds the conflict-state line of head gives no fact: the
    head goes back to the workflow, and the line goes."""
    verdict, will_fix, reviewed, answered = "", False, "", ""
    fact, held, conflicted = None, "", False
    for c in comments:
        if not of_bot(c):
            continue
        body, at = c.get("body") or "", c.get("updated_at") or ""
        m = REVIEWED.match(body)
        if m and m.group(1) == head:
            verdict, will_fix, reviewed = m.group(2), bool(m.group(3)), at
            continue
        m = ANSWER_WILL_FIX.match(body)
        if m and m.group(1) == head:
            answered = max(answered, at)
        elif body.startswith("<!-- review-held -->"):
            m = HELD_HEAD.search(body)
            if m and m.group(1) == head and hold_fact(body) and at >= held:
                fact, held = hold_fact(body), at
        elif body.startswith(FIRST) and conflict_state(head) in body.split("\n"):
            conflicted = True
    side = max(reviewed, answered)
    if fact and held > side:
        return {fact: True}
    if side:
        will_fix = will_fix or bool(answered)
        found = reviews()
        heads = fix_heads(found)
        own = heads.count(head)
        fix_stop = (verdict == "blocking" and not will_fix and len(heads) - own >= 2
                    and fixes(history(), found, head) - own >= 2)
        return {"verdict": verdict, "will_fix": will_fix, "fix_posted": own > 0, "fix_stop": fix_stop}
    if conflicted:
        return {}
    return None


def json_lines(path):
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def main(argv):
    try:
        if len(argv) == 2 and argv[0] == "make-label" and argv[1] in LABELS:
            make_label(argv[1])
            return 0
        if len(argv) >= 2 and argv[0] == "label" and NUMBER.fullmatch(argv[1]):
            facts, markers, head = parse(argv[2:])
            set_state(argv[1], facts, markers, head)
            return 0
        if len(argv) == 3 and argv[0] == "mark" and NUMBER.fullmatch(argv[1]):
            mark(argv[1], argv[2])
            return 0
        if len(argv) == 4 and argv[0] == "proofs" and HEAD.fullmatch(argv[1]):
            count = int(argv[3]) if re.fullmatch(r"0|[1-9][0-9]*", argv[3]) else None
            try:
                files = json_lines(argv[2])
            except ValueError:
                files, count = [], None
            print(json.dumps(proofs(argv[1], files, count)))
            return 0
        if len(argv) == 7 and argv[0] == "soundness":
            review, path, hold, outside, section_path, all_path = argv[1:]
            with open(path, encoding="utf-8") as f:
                output = json.load(f)
            output, text, every = soundness(review, output, hold, outside)
            if text:
                with open(path, "w", encoding="utf-8") as f:
                    json.dump(output, f, ensure_ascii=False)
            for name, part in ((section_path, text), (all_path, every)):
                with open(name, "w", encoding="utf-8") as f:
                    f.write(part + "\n" if part else "")
            print("The soundness rule holds: the verdict is person, and the comment gets the section on soundness."
                  if text else "The soundness rule does not hold: the verdict is the review's own.")
            return 0
        if len(argv) == 4 and argv[0] == "fixes" and HEAD.fullmatch(argv[3]):
            print(fixes(json_lines(argv[1]), json_lines(argv[2]), argv[3]))
            return 0
        if len(argv) == 3 and argv[0] == "suggestions":
            with open(argv[1], encoding="utf-8") as f:
                fix = json.load(f)
            with open(argv[2], "rb") as f:
                diff = f.read().decode("utf-8", "surrogateescape")
            sys.stdout.write(json.dumps(suggestions(fix, diff), ensure_ascii=False) + "\n")
            return 0
        if len(argv) in (8, 9) and argv[0] == "import-check":
            path, count, head, screen, verdict, hold, request = argv[1:8]
            value = argv[8] if len(argv) == 9 else None
            if not (re.fullmatch(r"0|[1-9][0-9]*", count) and HEAD.fullmatch(head) and screen in ("true", "false")):
                raise ValueError("not a count of changed files, a head commit and true or false for the screen")
            decision = import_decision(json_lines(path), int(count), screen == "true", verdict, hold == "true", value)
            if decision == "record":
                with open(request, "w", encoding="utf-8") as f:
                    json.dump(check_run(head, value, hold == "true"), f)
            print(decision)
            return 0
        if len(argv) in (2, 3) and argv[0] == "import-marker":
            print(import_marker(argv[1], argv[2] if len(argv) == 3 else None))
            return 0
        if len(argv) == 3 and argv[0] == "verdict" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2]):
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body} | @json")
            print(review_verdict(comments, argv[2]))
            return 0
        if len(argv) >= 3 and argv[0] == "relabel" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2]):
            number, head = argv[1], argv[2]
            facts, markers, given = parse(argv[3:])
            if given:
                raise ValueError("relabel names its head before the facts, not as head=")
            repo = os.environ["REPO"]
            comments = gh_objects("--paginate", f"repos/{repo}/issues/{number}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {id, user: {login: .user.login}, body, updated_at} | @json")
            found = relabel_facts(
                comments,
                lambda: gh_objects("--paginate", f"repos/{repo}/pulls/{number}/reviews", "--jq", ".[] | @json"),
                head, lambda: gh_objects(f"repos/{repo}/commits?sha={head}&per_page=100", "--jq", ".[] | @json"))
            if found is None:
                print(f"#{number}: the workflow wrote nothing of {head}, so the labels stay.")
                return 0
            both = sorted(set(found) & set(facts))
            if both:
                raise ValueError(f"relabel reads these facts itself: {', '.join(both)}")
            facts.update(found)
            # The label comments that apply would read again: nothing between the two reads writes a comment.
            labels = [{"id": c.get("id"), "body": c["body"]} for c in comments
                      if isinstance(c.get("body"), str) and c["body"].startswith(FIRST)]
            set_state(number, facts, markers, head, labels)
            return 0
    except ValueError as e:
        print(f"::error::rules.py: {e}", file=sys.stderr)
        return 2
    except GhError as e:
        print(f"::error::rules.py: {e}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as e:
        print(f"::error::rules.py: {e}: {e.stderr.decode('utf-8', 'replace').strip()}", file=sys.stderr)
        return 1
    print(__doc__.split("\n\n")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
