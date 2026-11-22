#!/usr/bin/env python3
"""The rules of the review workflow that code applies, whatever the model wrote (.github/review.md, "Outside items and
labels").

    python3 .github/review/rules.py label <number> task=<task> outside=<outside> outsider=<outsider> author=<kind>
        [<fact>=<value> ...] [head=<commit>] [marker=<line> ...]
    python3 .github/review/rules.py mark <number> <line> [state=<state>]
    python3 .github/review/rules.py owed <number> owed=<head and why> withdrawn=<head> task=<task> outside=<outside>
        outsider=<outsider> author=<kind>
    python3 .github/review/rules.py hold-head <number> <head>
    python3 .github/review/rules.py make-label <name>
    python3 .github/review/rules.py proofs <head> <main> <files.jsonl> <changed files>
    python3 .github/review/rules.py soundness <the .review directory> <output.json> <hold> <outside> <kind> <section>
        <all>
    python3 .github/review/rules.py blocking <output.json>
    python3 .github/review/rules.py fixes <commits.jsonl> <reviews.jsonl> <head>
    python3 .github/review/rules.py suggestions <fix.json> <pr.diff>
    python3 .github/review/rules.py import-check <files.jsonl> <changed files> <number> <head> <screen> <verdict>
        <hold> <request.json> [<import paths>]
    python3 .github/review/rules.py import-marker <head> [<import paths>]
    python3 .github/review/rules.py verdict <number> <head>
    python3 .github/review/rules.py withdrawal <number> <head> <why> <checks.jsonl> <directory> [owed]
    python3 .github/review/rules.py steering <files.jsonl>
    python3 .github/review/rules.py relabel <number> <head> outside=<outside> outsider=<outsider> author=<kind>
        [<fact>=<value> ...] [marker=<line> ...]
    python3 .github/review/rules.py answers <task> <outside> <outsider> [<kind>]

label: the state of the pull request or issue <number> after the event of this run (label_state, from the facts of
FACTS that the job gives), and on GitHub its one state label and its label comment (apply). The job also gives the
task of the run, one of TASKS, and the trust job's outputs outside, outsider and kind as they are (author=<kind>).
The answer label of the author-kind table (answers) tells what this does. For an outside author (outside_author: the
trust job's outside is true) it gives the item the state label of its state. For an author whose write access GitHub
did not give (author=unknown) it changes nothing: no state label goes on or off, the label comment stays as it is, and
a notice says why. For any other author, the item gets no state label and loses each one that it has, but its label
comment is the one of its state, with the marker of the state's label. The state label is waits-on-author when the
next step is the author's, waits-on-theorem when it is Sami's (or a person's at Theorem, in the states steering and
no-key), and none while the workflow works on the item. Setting one label takes the other off. review-held, the mark
of a hold, stays beside them. The label comment is one comment of github-actions[bot] on the item, edited in place
(label_comment). Its first line is <!-- review-label -->, its text names the next step and who takes it, and with a
state label its last line is the marker <!-- waits-on-author --> or <!-- waits-on-theorem: Sami -->. It keeps each
marker line of KEPT that it holds, and a marker=<line> of the same kind takes the place of that line. It holds
<!-- review-conflict-state <head> --> while it gives the head waits-on-author for a merge conflict, and loses that line
with any other state. The state steering (the fact steering=true, with head=<commit>) records
<!-- review-steering <head> -->, a line of KEPT: the head changes a file under .github/, so the post job approves none
of its runs, and the rescreen pass starts no approval of it. The state no-key (the fact no_key=true, with
head=<commit>) records <!-- review-no-key <head> -->, a line of KEPT: the screen passed the head, but the environment
post held no key of the OSS Verify App, so the post job approved none of its runs, and the rescreen pass starts no
approval of it. In a state with no state label (working, reviewed or import), an item that has a label comment gets
the text of its state. An item that has none gets none, unless a marker=<line> is the line of an owed withdrawal
(OWED): then it gets the label comment of its state, with that line. For an outside pull request (the fact kind=pr,
and an outside author) in the state decide or person, the text also names the step of R12 for the import into the
internal repository (import_steps), from the facts import_paths, the text of the variable REPO_PAIRS_IMPORT_PATHS,
given only when it is set, and decision, the post job's decision (DECISIONS). With head=<commit>, the label comment of
an outside pull request holds the marker line of R12 for that head and that text (import_marker). A pull request whose
review gave a verdict, and that no rule before it takes (a conflict, a hold, a stop of the post job, a refusal, or the
outcome of an outside author's item), is in the state reviewed, whoever started the run: its review names the next
step. GH_TOKEN and REPO come from the job's environment, as for gh in the workflow.

mark: records the marker line <line> of KEPT in the label comment of <number>, and changes nothing else
(with_marker): the state label, the text and the other lines stay as they are, as label would keep them for the same
state. <line> takes the place of the line of its kind. An item with no label comment gets one, of the state working,
or of state=<state>, which must be a state with no state label. The comment job of a catch-up records the line
<!-- review-catchup <head> --> with it. The rescreen pass reads that line, so that each head gets one catch-up. The
comment job's label step records the line of an owed withdrawal (OWED) with it when a hold made after its run started
stops that step. It gives state=working when the rescreen pass tries that hold again. Else it gives state=after-hold,
which names Sami's next step and has no state label. When mark posts a new label comment, its log says so.

owed: records in the label comment of <number> the withdrawal of the import check runs of a head that a run owes
(owe), and changes nothing else: the comment job calls it, and the hold job for a held screen, before the steps that
can fail. owed=<head> <why> (the post job's output owed: a withdrawal that it found a reason for and did not finish;
or <head> screen from the hold job, for a screen that held the head in a review, a rescreen or an approval of its run,
when the post job did not withdraw for that head) gives the line <!-- withdraw-owed <head> <why> --> of KEPT (OWED), as
mark does, but it never makes a label comment. When the item has none, it writes nothing, a line says so, and the
status is 3: the step then gives the line to the label step of its job, which gives it as marker=<line> to the call
that writes the label comment. withdrawn=<head> (its output withdrawn: it finished the withdrawal of the head, as it
found no import check run of the head with conclusion success or withdrew each one) takes the line of that head out.
The run's task and the trust job's outputs outside, outsider and kind are given as for label: when the author-kind
table's answer label is unchanged, this writes nothing, and a notice says why.

hold-head: the one check of each writer of a hold comment, before it writes anything (held_head): the hold job, and the
comment job's step that writes a stop of the rescreen pass. <head> is the head that the new hold names, and empty for
the hold of an issue, which names no head: then the status is 0, with no read. Else the status is 0 when <head> is the
head of the pull request <number> that GitHub gives now. When it is not, the hold is stale: a line says so on standard
output and in the step's summary, and the status is 3. Its writer then writes no hold comment and changes no label, so
that a stale hold never takes the place of the hold of the screen of the current head. The status is 1 when GitHub
could not say.

make-label: makes the label <name> of LABELS with its colour and description, or sets its description when the label
is there with another one. It reads the label first, and writes only what differs. A failure only warns: adding a
label that does not exist makes it, with no description.

proofs: the facts of the soundness rule at the head <head> of a pull request, as JSON on standard output, which the
gather job writes into .review/ as soundness.json (proofs): each changed path that counts, with why, whether the list
of the changed paths is whole, and each dune file that the job could not read. <files.jsonl> holds the files of the
pull request as the API lists them on every page of pulls/<n>/files, one {filename, previous_filename} on each line,
and <changed files> is the pull request's changed_files, or empty when a read did not finish or read another head:
then the list is not whole. The rule fails closed and models no feature of dune. A changed path counts when it is not
a Markdown file (markdown: its name ends with .md). A Markdown file counts when a dune file (dune_file: dune,
dune-project or dune-workspace*) of <head> or of <main> in the directory of the Markdown file or in a directory above
it holds the text .md anywhere, and each Markdown file counts when a dune file anywhere in either tree holds a text of
trigger (a word of KEYWORDS, a glob whose pattern does not end with one fixed extension other than md, or a word or a
string that holds .md and also .., %{project_root} or %{workspace_root}, or that starts with /), or cannot be read (a
link or a submodule in its place, or an object that git does not hold). <main> is the commit of main that the pull
request merges into. The dune files come from git objects of <head> and <main>, in the repository of the working
directory, never from a checkout, and the job reads them once, only when a changed path is a Markdown file. Each
dune file that the job cannot read goes on the list of such files.

soundness: the soundness rule of R8 (.github/review.md, "Soundness of a Rocq proof"), which code applies whatever the
model wrote. Stock Rocq accepts three public proofs of False (ISSUES), and this repository's CI lanes check the proofs
on stock Rocq, as the checks that the import's copy must pass do. So a pass of the checks does not show a proof sound.
The rule holds while <hold> (SOUNDNESS_HOLD) is true, for a pull request whose author the rule treats as outside
(holds_back: <outside>, the trust job's outside, is not false, or <kind>, the trust job's kind, is unknown) that
changes a path that soundness.json counts or a .v file under head/, or whose list of changed paths is not whole: the
job cannot show then that no proof changed. Then <output.json>, the review's output {comment, verdict, will_fix,
items}, gets the verdict person whatever the model gave, and QUESTION when its list has no question on soundness
(forced). <section> gets the fixed section on soundness, which trim.py puts after the trimmed text, where
the reader never sees it: it says why the rule holds, and lists, as facts for Sami, the rule with each changed file
other than a .v file that it counts, each dune file that the job could not read, each line of the changed .v files at
the head that uses one of USES, an array literal or make of the array module (uses), and each changed .v file at the
head that the gather job did not keep whole. None of them is a fail: honest proofs use the same constructs. A proof
with no such line gets the section too: a proof reaches the VM through a tactic such as lia, and a primitive array
through make with no array literal, so a search of the text cannot rule a forgery out. The section lists at most
LISTED lines in at most LISTED_CHARACTERS characters, and says how many more there are. <all> gets the section with
every line, for the run's summary. When the rule does not hold, <output.json> stays as it is and the two files are
empty.

blocking: the rule of the verdict blocking (.github/review.md, "The verdict"), which code applies whatever the model
wrote, after the soundness rule. A blocking finding is a change item whose optional is false. When <output.json>, the
review's output, gives the verdict blocking and its list holds no blocking finding and one question item or more, the
file gets the verdict person (settled). So the item waits on Sami, who answers the questions, and no fix runs. Any
other output stays as it is, also a verdict blocking whose list holds no question.

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

import-check: the decision of R12 on the head <head> of the outside pull request <number> (import_decision), on
standard output: record, or the first rule that does not hold. <files.jsonl> holds the files of the pull request at
<head> as the API lists them on every page of pulls/<n>/files, one {filename, previous_filename} on each line, and
<changed files> is the pull request's changed_files. <screen> is true when the screen passed the head, <verdict> is the
review's verdict after the soundness rule, and <hold> is SOUNDNESS_HOLD. <import paths> is the text of the variable
REPO_PAIRS_IMPORT_PATHS, one glob of the import on each line, given only when the variable is set: with none, the
import is not live. The check run repo-pairs/import-approved is recorded only when the screen passed, the verdict is
pass, no changed path (of a file, or the path it had before a rename) is a steering file (under .github/), with the
variable each changed path matches one of its globs by the import's glob rules (glob_match), the list holds each
changed file (GitHub lists at most 3,000), and, while the hold lasts, each changed path ends with .md. Then
<request.json> gets the body of the request that records it (check_run, for POST repos/<repo>/check-runs). A check run
belongs to a commit, and so shows on each pull request of that commit: its external_id, <number>:<head>, names the
pull request that it approves, as the import reads it, and so does its output title. Its output text is the marker
line of import-marker. The status is 2 when an argument is not one of these, or when the import's glob rules refuse a
glob of the variable.

import-marker: the marker line <!-- repo-pairs-import-paths <head>: <value> --> of R12, which the output text of the
check run and each label comment of an outside pull request hold (import_marker): <value> is <import paths> as one
JSON string, or null when it is not given. The JSON writes each character outside ASCII, <, > and & as a \\u escape,
so that the line holds no line break and no --> before its end.

verdict: "<verdict> <state> <why> <from>" on standard output for <head> of the pull request <number> (review_verdict),
from the comments of github-actions[bot]: <verdict> is the verdict of the marker
<!-- review-verdict <head> <verdict>[ will-fix] --> of the newest review comment that names <head>, or - when none
does. A review comment of <head> is screened when it holds <!-- review-screened <head> --> as the next marker line, so
that the screen passed <head> in the run of that review. <state> is held when a hold comment of the screen that names
<head> is newer than the newest screened review comment, or when no review comment of <head> is screened and such a
hold comment exists: a later screen held <head>. Else it is screened when the newest review comment of <head> is
screened, earlier when only an older one is, and unscreened when none is (a review by hand runs no screen). <why> is
the reason for which a relabel or a review by hand withdraws each import check run of <head> that stands: screen for
held; else the <why> of the line <!-- withdraw-owed <head> <why> --> of a label comment (OWED), whatever the newest
review says; else blocking or person, of the newest review comment newer than the newest screened one that gives one,
or of the newest screened review comment when it does not pass; else -. <from> is owed when <why> is the line's, and
- else. The line gives only the reason, never the state. A relabel records the import check run only for screened
with the verdict pass and no <why>: with a <why> (OWED), its decision is screened. For earlier with the verdict pass,
its decision is hand with no <why>, and screened with one. A review by hand with no screen records none. Its post
job's decision is hand for screened or earlier with no <why>, and screened with a <why>: the review of this run has
not posted yet. It is held for held, and screen for unscreened. For the decision hand, the label step counts an import
check run of <head> that still stands, for the value of the variable now, as recorded.

withdrawal: the requests that withdraw the import check runs of <checks.jsonl> on <head> of the pull request
<number> (withdrawal), for <why>: blocking or person, the verdict of a later review of <head>, or screen, a later
screen that held it (R12). With owed, <why> is the reason of the line of OWED, whose review or hold can be older than
the check run: the texts then do not say later (OWED_WITHDRAWN). <checks.jsonl> holds each check run {id, text}, its
id and its output text, one on each line. Each request goes to <directory>/withdraw-<id>.json, for PATCH
repos/<repo>/check-runs/<id>, and each id goes to standard output, one on each line. The status is 2 when an argument
or a line is not one of these.

steering: whether a pull request changes a steering file (steering, a file under .github/), from <files.jsonl>, its
files as the API lists them on every page of pulls/<n>/files, one {filename, previous_filename} on each line: true
when the path of a file, or the path that it had before a rename, is one, else false, on standard output. The post
job approves no held run of such a head (R10). The status is 2 when a line is not such a file.

relabel: label (above) for the head <head> of the pull request <number>, for the task relabel (the job gives no
task=), with the facts that the workflow wrote of that head (relabel_facts) beside the facts and the marker lines of
the job: the verdict and will-fix of the review comment that names <head>, an answer at <head> whose author said they
will make the change, the fix reviews of <head> and the count of fix reviews since the author's last own push, or the
hold comment that names <head> when it is newer than all of those. When the workflow wrote nothing of <head> but the
conflict-state line of its label comment, the item gets no state label and the line goes. When it wrote nothing of
<head>, nothing changes.

answers: the answers of the author-kind table (TABLE) for <task>, one of TASKS, as <answer>=<value> lines for
$GITHUB_OUTPUT: label (set, off or unchanged), then approve, record, withdraw and retry (true or false). <outside> and
<outsider> are the trust job's outputs of those names, and <kind> is its output kind, which only a label step gives.
The author is outside when <outside> is true, and only then (outside_author). <outsider> is a GitHub login or empty,
and no answer reads it. The status is 2 when an argument is not one of these.

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
    THEOREM: ("5319e7",
              "A person at Theorem takes the next step. A review workflow comment names the person and the step."),
    "review-held": ("d93f0b",
                    "The review workflow held this pull request or issue. Its hold comment tells what happens next."),
}

# The facts of a run that the rule reads, with their values when a job does not give them. label_state's outsider is
# no fact of a job: set_state reads it from the trust job's outside (outside_author).
FACTS = {
    # pr or issue.
    "kind": "",
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
    # A held pull request whose head changes a file under .github/, so the post job approved none of its runs (R10):
    # a person at Theorem approves them.
    "steering": False,
    # A held pull request whose head the screen passed, while the environment post held no key of the
    # OSS Verify App, so the post job approved none of its runs (R10): a person at Theorem approves them.
    "no_key": False,
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
# The post job's decisions on the import check run at a head: record, or the first rule of R12 that does not hold
# (import_decision), or moved when the pull request moved on from the head, or writer when its author is no outside
# author (it has write access, or GitHub did not say: the author-kind table's record is false). A relabel and a review
# by hand with no screen read the review comments of the head (review_verdict). The decision is held when a hold
# comment of the screen is newer than each review comment whose run screened the head. For a review by hand, a run
# with no screen that records no check run, the decision is hand or screened when the run of an earlier review
# screened the head and no hold comment of the screen is newer (the states screened and earlier). It is screened when
# review_verdict gives a reason to withdraw (its why: the newest screened review comment does not pass, one newer
# than it gives a blocking finding or the verdict person, or a label comment holds the line of OWED of the head), and
# this run withdraws each check run of the head that still stands. So the state follows the verdict of this run, and a
# pass gets PASSED. Else it is hand, and so is a relabel's in the state earlier with the verdict pass and no such
# reason. A relabel's decision is screened also in the state screened with the verdict pass and a line of OWED: such a
# relabel withdraws, and records no check run. The line of OWED gives only the reason, never the state: with no
# screened review comment of the head, the decision is screen. For the decision hand, the label step counts an import
# check run of the head that still stands, for the value of the variable now, as recorded (the post job's standing),
# so its state is import or decide as that check run gives. Empty when the job gave none.
DECISIONS = ("", "record", "screen", "verdict", "steering", "outside", "unread", "person", "markdown", "moved",
             "writer", "held", "hand", "screened")

# The texts of R12 for an outside pull request that the screen and the review passed (import_steps). With no variable
# REPO_PAIRS_IMPORT_PATHS, the workflow cannot tell whether the import does not run yet, a move is under way or the
# import is paused, so the comment names each step that can come next. With the variable, it names the step for the
# paths that the pull request changes.
PASSED = "The automated screen and the automated review passed this pull request."
# The decision screen of an outside pull request whose review passed: no screen passed its head in the run of a review.
# A review by hand with no screen and a relabel run none, and no review comment of the head holds the marker of a
# screen that passed it (review_verdict). So the text says so in the place of PASSED. After such a review comment, a
# review by hand gets the decision hand or screened, and a relabel's pass the decision hand (DECISIONS).
UNSCREENED = ("The automated review passed this pull request. No automated screen passed its head commit in a run that "
              "also reviewed it, so the workflow did not record the check `repo-pairs/import-approved`.")
# The decision held: a screen held the head after each review whose run screened it, so the text says so in the place
# of PASSED. A check run that a run recorded before stays on the head, with the conclusion neutral.
SCREEN_HELD_AFTER = ("The automated review passed this pull request. An automated screen held its head commit. After "
                     "that, no automated screen passed it in a run that also reviewed it. So the check "
                     "`repo-pairs/import-approved` does not approve this head commit for the import.")
MERGE_STEPS = (
    "- If the rules of this repository allow a merge, Sami merges the pull request in this repository.\n"
    "- If not, when the import into the internal repository runs and copies each changed path, Sami approves the "
    "head commit for the import.\n"
    "- If the import runs but does not copy each changed path, Sami copies the change into the internal repository by "
    "hand.")
APPROVE = "Sami approves the head commit for the import into the internal repository."
COPY = "Sami copies the change into the internal repository by hand."
IMPORT_STEPS = (f"- {APPROVE.removesuffix('.')}, if the import copies each path that the pull request changes.\n"
                f"- If not, {COPY}")
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
        "The automated review asks for a change. The automated fix posted suggested changes for it. When the branch "
        "gets a new commit, the automated review runs again."),
    "change": (
        AUTHOR, "You make the change that the automated review names. Then you push the change.",
        "The automated review asks for a change, and the automated fix posted no suggested change for it. After your "
        "push, the automated review runs again."),
    "replied": (
        AUTHOR, "You read the reply to this issue.",
        "If a question stays open, write it in a comment on this issue."),
    "draft": (THEOREM, "Sami approves the text of a reply.", "You do not need to do anything."),
    # The fresh reader refused the text (the fact refused): nothing of it posted.
    "refused-review": (
        THEOREM, "Sami writes the review by hand.",
        "The workflow stopped the automated review, so the workflow did not post it. You do not need to do anything."),
    "refused-answer": (
        THEOREM, "Sami answers your comment by hand.",
        "The workflow stopped the automated answer to your comment, so the workflow did not post it. You do not need "
        "to do anything."),
    "refused-fix": (
        THEOREM, "Sami writes the fix by hand.",
        "The automated review asks for a change. The workflow stopped the automated fix for it, so the workflow posted "
        "no suggested change. You can push your own change."),
    "person": (THEOREM, "Sami answers the questions of the automated review.", "You do not need to do anything."),
    "screen": (
        THEOREM, "Sami starts the work that the hold comment names, by hand.", "You do not need to do anything."),
    # A held pull request whose head changes a file under .github/ (R10): the post job approved none of its runs. The
    # label comment records the head (steering_line).
    "steering": (
        THEOREM, "A person at Theorem approves the checks of this pull request.",
        "This pull request changes a file under `.github/`, so the workflow does not approve its checks. You do not "
        "need to do anything."),
    # A held pull request whose head the screen passed, while the environment post held no key of the
    # OSS Verify App (R10, until the LPS move of dispatch://OSSV-321): the post job approved none of its runs. The
    # label comment records the head (no_key_line).
    "no-key": (
        THEOREM, "A person at Theorem approves the checks of this pull request.",
        "The workflow cannot approve the checks of a pull request in this repository yet. You do not need to do "
        "anything."),
    "will-fix": (
        THEOREM, "Sami replies to your comment.",
        "You wrote that you will make the change, so no automated fix runs. After your push, the automated review "
        "runs again."),
    "fix-stop": (
        THEOREM, "Sami writes a comment on the change that the automated review asks for.",
        "The workflow posted 2 automated fixes since your last push, and the automated review still asks for a change. "
        "No automated fix runs again. You do not need to do anything."),
    # The hold comment says what did not finish, after how many tries, and that the workflow does not try it again.
    "stopped": (
        THEOREM, "Sami starts again, by hand, the work that the hold comment names.",
        "You do not need to do anything."),
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
        None, "The workflow tries again.",
        "You do not need to do anything. When a hold comment gives a time, the workflow tries again from that time."),
    # A pull request whose review gave a verdict, with no state of an outside pull request: its author is no outside
    # author (outside_author). The review names the next step, and nothing in this workflow tries the review of the
    # head again.
    "reviewed": (
        None, "The automated review of the head commit names the next step and who takes it.",
        "After a push, the automated review runs again."),
    # The label comment that the comment job's label step posts (mark) for the line of a withdrawal that its run owes
    # (OWED), on an item with no label comment, when a hold made after its run started stops that step, and the
    # rescreen pass does not try that hold again: a hold of the screen, or a stop. It names Sami's next step in the
    # words of the state screen (the state stopped says the same), but has no state label, as mark writes none. For a
    # hold that the rescreen pass tries again, the step gives the state working. label_state never gives this state.
    "after-hold": (
        None, "Sami starts the work that the hold comment names, by hand.", "You do not need to do anything."),
}

FIRST = "<!-- review-label -->"
HEAD = re.compile(r"[0-9a-f]{40}")
NUMBER = re.compile(r"[1-9][0-9]*")
# The marker lines of other kinds that a label comment keeps: the import's paths that a decision on a head read
# (R12), the stored draft of an issue's reply, the approved reply that posted, the head that a catch-up closed and
# reopened the pull request at (D16 (a): once for each head), the head whose runs the post job did not approve,
# because it changes a file under .github/ or because the environment post held no key of the OSS Verify App
# (R10: the rescreen pass starts no approval of it again), and the withdrawal of the import check runs of a head
# that a run owes (OWED).
KEPT = re.compile(r"<!-- (repo-pairs-import-paths) [0-9a-f]{40}: .* -->|<!-- (issue-draft) [0-9]+-[0-9]+ -->"
                  r"|<!-- (issue-reply-posted) [0-9]+ -->|<!-- (review-catchup) [0-9a-f]{40} -->"
                  r"|<!-- (review-steering) [0-9a-f]{40} -->|<!-- (review-no-key) [0-9a-f]{40} -->"
                  r"|<!-- (withdraw-owed) [0-9a-f]{40} (?:blocking|person|screen) -->")
# The marker line of a withdrawal of the import check runs of a head (R12) that a run found a reason for and did not
# finish: GitHub refused it, or the job failed or stopped before it. The head, and why (WITHDRAWN). Each job writes it
# ahead, before its first step that can fail or that withdraws: the post job through its output owed, which the
# comment job or the hold job records, and the hold job for a screen that held the head in a review, a rescreen or an
# approval of its run, unless the post job withdrew for that head. It goes into a label comment that the item has: no
# record of it makes one (owe). An item with no label comment gets the line from the label step of that job. Its label
# call writes a label comment with the line in any state (apply). The comment job's label step also writes the line
# when it stops for a hold made after the run started (mark). When the label step stops before its label call for any
# other cause, the line is not recorded. A relabel and a review by hand of that head withdraw for why while the line
# stands, whatever the newest review says (review_verdict). Only a run that finished the withdrawal of that head (it
# found no import check run of the head with conclusion success, or withdrew each one) takes the line out (owe). Each
# head has a line of its own (marker_kind).
OWED = re.compile(r"<!-- withdraw-owed ([0-9a-f]{40}) (blocking|person|screen) -->")


def marker_line(line):
    """Whether line is a marker line, as the last part of a label comment holds them: <!-- and a space, then any
    text with no line break, then a space and -->."""
    return len(line) >= 9 and line.startswith("<!-- ") and line.endswith(" -->") and "\n" not in line


def label_state(kind="", outsider=False, verdict="", fix_posted=False, will_fix=False, fix_stop=False,
                conflict=False, draft_stored=False, reply_posted=False, refused="", screen_held=False, steering=False,
                no_key=False, held=False, tries_used_up=False, left_closed=False, recorded=False, import_paths=None,
                decision=""):
    """The state of an item after the event of a run, a key of STATES, from the facts of FACTS, and outsider, true for
    the item of an outside author (outside_author). The first rule that holds gives it."""
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
    if steering:
        return "steering"
    if no_key:
        return "no-key"
    if held:
        return "working"
    if reply_posted:
        return "replied"
    if draft_stored:
        return "draft"
    # A text that the fresh reader refused never posts: Sami writes it, whoever wrote the item.
    if refused:
        return f"refused-{refused}"
    # The review's outcome, for the item of an outside author.
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
    # A pull request whose review gave a verdict and that no rule above takes: its author is no outside author. Its
    # review names the next step, and nothing tries the review of the head again, so the text does not say that the
    # workflow tries again.
    if kind == "pr" and verdict:
        return "reviewed"
    return "working"


def label_of(state):
    """The state label of state: waits-on-author, waits-on-theorem, or None."""
    return STATES[state][0]


def marker_kind(line):
    """The kind of a marker line of KEPT: repo-pairs-import-paths, issue-draft, issue-reply-posted, review-catchup,
    review-steering or review-no-key, and "withdraw-owed <head>" for the line of OWED of head: a withdrawal owed for
    one head never takes the place of the line of another head."""
    m = KEPT.fullmatch(line)
    if not m:
        raise ValueError(f"not a marker line that the label comment keeps: {line!r}")
    owed = OWED.fullmatch(line)
    return f"withdraw-owed {owed.group(1)}" if owed else next(g for g in m.groups() if g)


def import_steps(state, value, decision):
    """(step, text) of the label comment of an outside pull request in the state decide or person (R12), for value, the
    text of the variable REPO_PAIRS_IMPORT_PATHS (None when it is not set), and the post job's decision. With the
    variable, the step is Sami's approval of the head commit when the import takes each changed path, and a copy by
    hand when it does not take one or a file is under .github/. A decision that does not say which, as when the list of
    changed files is not whole or the post job did not succeed, gives both. With no variable, each step of
    MERGE_STEPS. For the decision screen, the text says that no screen passed the head in the run of a review
    (UNSCREENED), and for the decision held that a screen held the head after each screened review
    (SCREEN_HELD_AFTER), in the place of PASSED. The decisions hand and screened (a review by hand with no screen, or
    a relabel, after a review whose run screened the head) give PASSED, and do not say which step: they compared no
    path. The decision hand gives the state decide only when no import check run of the head stands (the post job's
    standing): one that stands gives the state import while the variable is set."""
    if state not in ("decide", "person"):
        raise ValueError(f"no step of the import for the state {state!r}")
    if decision not in DECISIONS:
        raise ValueError(f"not a decision of the post job: {decision!r}")
    live = value is not None
    steps = IMPORT_STEPS if live else MERGE_STEPS
    unread = f"{UNREAD} " if decision == "unread" else ""
    passed = {"screen": UNSCREENED, "held": SCREEN_HELD_AFTER}.get(decision, PASSED)
    if state == "decide":
        if live and decision in ("person", "markdown"):
            return APPROVE, (f"{passed} The import copies each path that this pull request changes. You do not need "
                             "to do anything.")
        if live and decision in NOT_TAKEN:
            return COPY, f"{passed} {NOT_TAKEN[decision]} You do not need to do anything."
        return STATES[state][1], f"{passed} {unread}You do not need to do anything.\n\n{steps}"
    _label, step, text = STATES[state]
    # No text promises a merge or an import before the questions have their answers.
    answered = "If the answers to the questions leave no change to make,"
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


def steering_line(head):
    """The marker line of KEPT that records head as a head that changes a file under .github/ (the state steering):
    the post job approved none of its runs, and the rescreen pass starts no approval of it again."""
    return f"<!-- review-steering {head} -->"


def no_key_line(head):
    """The marker line of KEPT that records head as a head that the screen passed while the environment post held no
    key of the OSS Verify App (the state no-key): the post job approved none of its runs, and the rescreen pass
    starts no approval of it again."""
    return f"<!-- review-no-key {head} -->"


def label_comment(state, old="", markers=(), head="", imports=None):
    """The text of the label comment of an item in state, which takes the place of old (its label comment, or "" when
    it has none): FIRST, the next step, the text when the state has one, then each marker line of KEPT that old holds
    or markers gives (a marker of markers takes the place of old's line of its kind), with the steering line of head
    in the state steering and its no-key line in the state no-key, the conflict-state line of head for a conflict, and
    the marker of the state label. imports is (value, decision) of import_steps for an outside pull request, and None
    for any other item. The state decide is an outside pull request's alone, so there None reads as no variable and no
    decision."""
    label, step, text = STATES[state]
    if state == "decide" or (state == "person" and imports is not None):
        step, text = import_steps(state, *(imports or (None, "")))
    if state in ("conflict", "steering", "no-key") and not HEAD.fullmatch(head):
        raise ValueError(f"the state {state} needs its head commit, not {head!r}")
    if state == "steering":
        markers = [*markers, steering_line(head)]
    if state == "no-key":
        markers = [*markers, no_key_line(head)]
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


def loads(text):
    """json.loads of text from a service or from a file that the model wrote, with a ValueError also for JSON that nests
    deeper than Python reads: json.loads raises RecursionError for it, which is no ValueError. So each caller takes such
    a text as one that is not JSON."""
    try:
        return json.loads(text)
    except RecursionError:
        raise ValueError("JSON that nests too deep to read") from None


def gh_objects(*args):
    """The JSON objects that gh api with args gives, one on each line (its --jq ends with @json)."""
    return [loads(line) for line in gh(*args).split("\n") if line.strip()]


def make_label(name):
    """Makes the label name of LABELS, or sets its description when the label is there with another one: one read,
    and a write only when one is needed. A failure only warns."""
    repo = os.environ["REPO"]
    color, description = LABELS[name]
    try:
        try:
            label = loads(gh(f"repos/{repo}/labels/{name}"))
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


def apply(number, state, markers=(), head="", imports=None, labels=None, labelled=True):
    """Gives the item number the state label of state, takes the other one off, and writes its label comment
    (label_comment, with imports). labels are the item's label comments of BOT, each {id, body}, when the caller read
    them already; else this reads them. When labelled is False (the label answer off of the author-kind table), the
    item gets no state label and loses each one that it has, but its label comment is the state's all the same, with
    the marker of the state's label. An item with no label comment gets one when state has a state label, or when a
    line of OWED is among markers, so that a label step records that line in any state. Else it gets none."""
    repo = os.environ["REPO"]
    want = label_of(state) if labelled else None
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
    if old is None and label_of(state) is None and not any(OWED.fullmatch(m) for m in markers):
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


def mark(number, line, make=True, state="working"):
    """Records line, a marker line of KEPT, in the label comment of the item number (with_marker), and writes nothing
    else: the state label and the text of the label comment stay as they are. An item with no label comment gets one
    of state, with line, when make is True. state is working unless the caller gives another. It must be a state with
    no state label, as mark writes no state label: a ValueError for any other. The comment job's label step gives
    working or after-hold, by the hold that stopped it. When make is False (owe: a line of OWED), such an item gets
    nothing, and the result is False. Else the result is True."""
    marker_kind(line)
    if state not in STATES or label_of(state) is not None:
        raise ValueError(f"mark makes a label comment only in a state with no state label, not {state!r}")
    labels = read_labels(number)
    old = labels[-1] if labels else None
    if old is None and not make:
        return False
    if old is None:
        write_label(number, None, label_comment(state, "", [line]))
        print(f"#{number}: it had no label comment, so this step posted one, with {line}.")
        return True
    body = with_marker(old["body"], line)
    if body == old["body"]:
        print(f"#{number}: its label comment holds {line} already.")
        return True
    write_label(number, old, body)
    print(f"#{number}: its label comment holds {line}.")
    return True


def without_marker(body, kind):
    """The label comment body with no marker line of KEPT of kind (marker_kind) in its last part, which holds the marker
    lines. A last part with no other line goes, with the gap before it. The rest of body stays as it is."""
    text, gap, last = body.rpartition("\n\n")
    lines = last.split("\n")
    if not gap or not all(marker_line(m) for m in lines):
        return body
    kept = [m for m in lines if not (KEPT.fullmatch(m) and marker_kind(m) == kind)]
    return text + gap + "\n".join(kept) if kept else text


def unmark(number, kind, what):
    """Takes the marker line of KEPT of kind (marker_kind) out of the label comment of the item number
    (without_marker), and writes nothing else: the state label and the text of the label comment stay as they are.
    Nothing is written when no label comment holds such a line. what names what the line records, for the log."""
    labels = read_labels(number)
    old = labels[-1] if labels else None
    body = old["body"] if old else ""
    if old is None or without_marker(body, kind) == body:
        print(f"#{number}: its label comment records no {what}.")
        return
    write_label(number, old, without_marker(body, kind))
    print(f"#{number}: its label comment no longer records an {what}.")


# --- the author-kind table ------------------------------------------------------------------------------------------
# What the workflow does for the item of a run, by the kind of its author. The trust job decides the kind once
# (trusted): its output outside is true for an outside author, and its output kind is writer, outsider or unknown
# (GitHub did not say whether the author has write access). Each step of review.yml reads its answer here (answers):
# the post job's steps read approve, record, withdraw and retry, and the label steps read label. A rule that grants
# (approve, record, the import's pass, a state label, a fix) reads outside alone (outside_author). A rule that holds
# back or asks a person treats an author whose write access GitHub did not say as outside, as OSSV-221's architect
# ruled on 2026-11-20 at 16:22Z: the soundness rule reads holds_back, the review's prompt in review.yml has the same
# form, and a withdrawal runs for every author.
#
# - label: set gives the item the state label of its state. off takes each state label off, and the label comment is
#   the state's all the same. unchanged writes nothing of the state: no state label goes on or off, and the label
#   comment stays as it is. review-held belongs to a hold, and no answer of this table names it.
# - approve: the post job approves the held runs of the head when the screen of this run passed the head (R10).
# - record: the post job decides on the import check run of the head, and records it when the rules of R12 hold.
# - withdraw: the post job withdraws the import check runs of the head when this run gives a reason (R12): a review of
#   the head with a blocking finding or the verdict person, a screen that held the head, or a relabel or a review by
#   hand with no screen that finds such a review or a later hold of the screen, for every author.
# - retry: the error of a withdrawal that GitHub refused, or that could not be read, says that the rescreen pass tries
#   it again, but only when the name of the run gives the head too (review.yml): the pass tries no other run again
#   (held.sh, take and due_retry). The pass tries no App write of the item of another author again (held.sh, consider
#   and access_of). So for such an author, and for a run whose name gives no head, the error says "Re-run this run."
#   instead.
#
# The tasks are the trust job's (the top of review.yml), and hold is the hold job. The hold job makes no App write: in
# the same run, the post job withdraws the import check runs of a head that the screen held, by the row of the task.
# The hold job records the line of OWED of that withdrawal with the task of the run, when the post job did not finish
# it.
TASKS = ("review", "rescreen", "approve", "relabel", "answer", "draft", "reply", "conflict", "stop", "catchup", "hold")
# The classes of an author (author_class): outside, unknown, and other (a writer, or a kind that the step did not give).
CLASSES = ("outside", "unknown", "other")
ANSWERS = ("label", "approve", "record", "withdraw", "retry")
# For each class, the answers of each task, in the order of ANSWERS. An unknown author gets the answers of other but
# label: each answer but label reads outside alone.
TABLE = {
    # (task, class)            label        approve record withdraw retry
    ("review", "outside"):     ("set",       False,  True,  True,    True),
    ("review", "unknown"):     ("unchanged", False,  False, True,    False),
    ("review", "other"):       ("off",       False,  False, True,    False),
    ("rescreen", "outside"):   ("set",       False,  True,  True,    True),
    ("rescreen", "unknown"):   ("unchanged", False,  False, True,    False),
    ("rescreen", "other"):     ("off",       False,  False, True,    False),
    ("approve", "outside"):    ("set",       True,   False, True,    True),
    ("approve", "unknown"):    ("unchanged", False,  False, True,    False),
    ("approve", "other"):      ("off",       False,  False, True,    False),
    ("relabel", "outside"):    ("set",       False,  True,  True,    True),
    ("relabel", "unknown"):    ("unchanged", False,  False, True,    False),
    ("relabel", "other"):      ("off",       False,  False, True,    False),
    ("answer", "outside"):     ("set",       False,  False, False,   False),
    ("answer", "unknown"):     ("unchanged", False,  False, False,   False),
    ("answer", "other"):       ("off",       False,  False, False,   False),
    ("draft", "outside"):      ("set",       False,  False, False,   False),
    ("draft", "unknown"):      ("unchanged", False,  False, False,   False),
    ("draft", "other"):        ("off",       False,  False, False,   False),
    ("reply", "outside"):      ("set",       False,  False, False,   False),
    ("reply", "unknown"):      ("unchanged", False,  False, False,   False),
    ("reply", "other"):        ("off",       False,  False, False,   False),
    ("conflict", "outside"):   ("set",       False,  False, False,   False),
    ("conflict", "unknown"):   ("unchanged", False,  False, False,   False),
    ("conflict", "other"):     ("off",       False,  False, False,   False),
    ("stop", "outside"):       ("set",       False,  False, False,   False),
    ("stop", "unknown"):       ("unchanged", False,  False, False,   False),
    ("stop", "other"):         ("off",       False,  False, False,   False),
    ("catchup", "outside"):    ("set",       False,  False, False,   False),
    ("catchup", "unknown"):    ("unchanged", False,  False, False,   False),
    ("catchup", "other"):      ("off",       False,  False, False,   False),
    ("hold", "outside"):       ("set",       False,  False, False,   False),
    ("hold", "unknown"):       ("unchanged", False,  False, False,   False),
    ("hold", "other"):         ("off",       False,  False, False,   False),
}
# The values of the trust job's outputs outside and kind, and the form of a GitHub login, which its output outsider
# is when it is not empty.
OUTSIDE_VALUES = ("", "true", "false")
KINDS = ("", "writer", "outsider", "unknown")
LOGIN = re.compile(r"[A-Za-z0-9-]+(?:\[bot\])?")
# The arguments of label that give the run: its task, and the trust job's outputs outside, outsider and kind (author).
RUN = ("task", "outside", "outsider", "author")


def outside_author(outside):
    """Whether the item's author is an outside author, from the trust job's output outside: true, and only then. The
    trust job gives true when trusted gives 1 for the author (no write access, an App that the workflow's APPS list
    does not name, or no GitHub login), and false when it gives 0 (write access, or one of the APPS) or 2 (GitHub did
    not say). An empty or missing value is not outside, so that it gives no state label, approves no held run and
    records no import check run. The trust job's output outsider is never read for it: a review by hand of an outside
    pull request screens no account, and its outsider is empty."""
    return outside == "true"


def author_class(outside, kind=""):
    """The class of CLASSES of the item's author: outside when outside_author holds, unknown when the trust job's output
    kind is unknown, and other for any other author. An empty or missing kind is not unknown."""
    if outside_author(outside):
        return "outside"
    return "unknown" if kind == "unknown" else "other"


def holds_back(outside, kind=""):
    """Whether a rule that holds back or asks a person applies to the item's author, from the trust job's outputs
    outside and kind: unless outside is false, and also when kind is unknown (GitHub did not say whether the author
    has write access). It fails closed: an empty, missing or other value of outside counts as outside. An empty or
    missing kind is not unknown. A rule that grants reads outside_author instead."""
    return outside != "false" or kind == "unknown"


def answers(task, outside, outsider, kind=""):
    """{answer: value} of TABLE for task and the class of the author (author_class) that the trust job's outputs
    outside and kind give. outsider is checked and read for no answer. A ValueError when task is not one of TASKS,
    outside is not one of OUTSIDE_VALUES, outsider is neither empty nor a GitHub login, or kind is not one of KINDS."""
    if task not in TASKS:
        raise ValueError(f"not a task of the author-kind table: {task!r}")
    if outside not in OUTSIDE_VALUES:
        raise ValueError(f"the trust job's outside is true, false or empty, not {outside!r}")
    if outsider and not LOGIN.fullmatch(outsider):
        raise ValueError(f"the trust job's outsider is a GitHub login or empty, not {outsider!r}")
    if kind not in KINDS:
        raise ValueError(f"the trust job's kind is writer, outsider, unknown or empty, not {kind!r}")
    return dict(zip(ANSWERS, TABLE[(task, author_class(outside, kind))]))


def set_state(number, run, facts, markers=(), head="", labels=None):
    """Gives the item number the state that facts give (label_state), as the label answer of the author-kind table for
    run says (answers, with RUN): set, off (apply, with labels), or unchanged, which writes nothing and gives a notice.
    label_state's outsider is outside_author of the trust job's outside. For an outside pull request, the label comment
    names the steps of R12 for the import, and holds the marker line of R12 for head when head is given (import_marker).
    The label comment is made once before any write, so that a marker or a head that it refuses changes nothing on
    GitHub."""
    label = answers(run["task"], run["outside"], run["outsider"], run["author"])["label"]
    if label == "unchanged":
        print(f"::notice::#{number}: GitHub did not say whether its author has write access, so the workflow changes "
              "neither its state label nor its label comment.")
        return
    outsider = outside_author(run["outside"])
    state = label_state(outsider=outsider, **facts)
    imports = None
    if facts.get("kind") == "pr" and outsider:
        imports = (facts.get("import_paths"), facts.get("decision", ""))
        if head:
            markers = [*markers, import_marker(head, imports[0])]
    label_comment(state, "", markers, head, imports)
    apply(number, state, markers, head, imports, labels, labelled=label == "set")


def owe(number, run, owed="", withdrawn=""):
    """Records in the label comment of the item number the withdrawal of the import check runs of a head that a run
    owes (OWED), from the post job's outputs: owed, "<head> <why>" of a withdrawal that it found a reason for and did
    not finish (or "<head> screen" from the hold job, for a screen that held the head in a review, a rescreen or an
    approval of its run), gives the line <!-- withdraw-owed <head> <why> --> (mark), in a label comment that the item
    has: it never makes one. When the item has none, it writes nothing, says so, and the result is False: the step
    gives the line to the label step of its job. withdrawn, a head whose withdrawal the job finished, takes the line of
    that head out (unmark), and then owed is not read. The state label and the text of the label comment stay as they
    are. As for set_state, the label answer of the author-kind table for run unchanged writes nothing, and gives a
    notice. Else the result is True."""
    head, _, why = owed.partition(" ")
    line = f"<!-- withdraw-owed {head} {why} -->" if owed else ""
    if owed and not OWED.fullmatch(line):
        raise ValueError(f"not a head commit and a reason to withdraw: {owed!r}")
    if withdrawn and not HEAD.fullmatch(withdrawn):
        raise ValueError(f"not a head commit: {withdrawn!r}")
    if answers(run["task"], run["outside"], run["outsider"], run["author"])["label"] == "unchanged":
        print(f"::notice::#{number}: GitHub did not say whether its author has write access, so the workflow changes "
              "neither its state label nor its label comment.")
        return True
    if withdrawn:
        unmark(number, f"withdraw-owed {withdrawn}", f"owed withdrawal of the import check runs of {withdrawn}")
    elif line and not mark(number, line, make=False):
        print(f"#{number}: it has no label comment, and this command writes none. If a later command of this job "
              f"writes a label comment, that comment gets {line}. If no later command writes one, the workflow does "
              f"not record {line}.")
        return False
    return True


def parse(args, run=()):
    """The facts, the marker lines, the head and the run of label's arguments: <fact>=<value> for each fact of FACTS
    (true or false, or empty for false, for each fact that is one or the other), head=<commit>, marker=<line>, and
    <name>=<value> for each name of run, which each must be given once. The job gives import_paths=<text> only when the
    variable is set."""
    facts, markers, head, given = {}, [], "", {}
    for arg in args:
        name, eq, value = arg.partition("=")
        if not eq:
            raise ValueError(f"not <name>=<value>: {arg!r}")
        if name in run:
            if name in given:
                raise ValueError(f"{name} is given twice")
            given[name] = value
        elif name == "marker":
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
    missing = [name for name in run if name not in given]
    if missing:
        raise ValueError(f"the label rule needs {', '.join(f'{name}=' for name in missing)}")
    return facts, markers, head, given


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
# The markers at the start of a review comment (D8): the head that it reviewed, the review's verdict at that head,
# after the soundness rule, with will-fix when the author said they will make the change, and, when the screen passed
# that head in the run of the review, the marker <!-- review-screened <head> --> (R12).
REVIEWED = re.compile(r"<!-- review -->\n<!-- review-head ([0-9a-f]{40}) -->\n"
                      r"<!-- review-verdict \1 (pass|blocking|person)( will-fix)? -->"
                      r"(\n<!-- review-screened \1 -->)?(?:\n|$)")


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


def markdown(path):
    """Whether path is a Markdown file: its name ends with .md. While the soundness hold lasts, the rule of R8 counts
    each changed path that is not one, and R12 records the import check run only when each changed path is one."""
    return path.endswith(".md")


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
    if hold and not all(markdown(p) for p in paths):
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


def check_run(number, head, value, hold):
    """The body of the request that records the import check run on head of pull request number (POST
    repos/<repo>/check-runs), when import_decision gives record. Its external_id, <number>:<head>, and its output title
    name the pull request that it approves: the check run of a commit shows on each pull request of that commit. Its
    output text is the marker line of import_marker, alone."""
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head)):
        raise ValueError(f"not a pull request number and a head commit: {number!r} {head!r}")
    summary = ["The automated screen and the automated review passed this head commit.",
               "No changed file is under `.github/`."]
    if hold:
        summary.append("Each changed path ends with `.md`. The workflow records this check only for such a change. "
                       "This rule lasts until the checks of the import use a Rocq that fixes the three public proofs "
                       "of `False`.")
    summary.append("The import copies each changed path." if value is not None else
                   "The variable `REPO_PAIRS_IMPORT_PATHS` is not set, so the workflow did not compare the changed "
                   "paths with the paths of the import.")
    return {"name": CHECK, "head_sha": head, "external_id": f"{number}:{head}", "status": "completed",
            "conclusion": "success",
            "output": {"title": f"Approved for the import: pull request #{number} at {head[:12]}",
                       "summary": " ".join(summary), "text": import_marker(head, value)}}


# Why a later run of a head withdraws the import check run that the workflow recorded on it (R12): its review gave a
# blocking finding or the verdict person, or its screen held the head. Each is (the end of the output title, the
# summary's first sentence).
WITHDRAWN = {
    "blocking": ("because a later review asks for a change",
                 "A later automated review of this head commit asks for a change."),
    "person": ("because a later review has questions for Sami",
               "A later automated review of this head commit has questions for Sami."),
    "screen": ("because a later screen held it", "A later automated screen held this head commit."),
}
# The same reasons when they come from the line of OWED: an earlier run owes the withdrawal, and the review or the hold
# that gave the reason can be older than the check run. So these texts do not say later. A review's reason is a past
# verdict: an edit of the review comment in place can replace that review. So these texts say what it asked.
OWED_WITHDRAWN = {
    "blocking": ("because an automated review of this head commit asked for a change",
                 "An automated review of this head commit asked for a change."),
    "person": ("because an automated review of this head commit had questions for Sami",
               "An automated review of this head commit had questions for Sami."),
    "screen": ("because an automated screen held this head commit", "An automated screen held this head commit."),
}


def withdrawal(number, head, why, text, owed=False):
    """The body of the request that updates an import check run on head of pull request number (PATCH
    repos/<repo>/check-runs/<id>) for why (WITHDRAWN, or OWED_WITHDRAWN when owed: the reason of the line of OWED): the
    conclusion neutral, so that the import no longer reads it as the approval of the pull request, and an output title
    that names the pull request and says why. Its name and its external_id stay, and so does text, its output text:
    the marker line of the value that it recorded."""
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head)) or why not in WITHDRAWN:
        raise ValueError(f"not a pull request number, a head commit and a reason: {number!r} {head!r} {why!r}")
    end, first = (OWED_WITHDRAWN if owed else WITHDRAWN)[why]
    return {"status": "completed", "conclusion": "neutral",
            "output": {"title": f"Not approved for the import: pull request #{number} at {head[:12]}, {end}",
                       "summary": f"{first} So this check is no longer an approval for the import.", "text": text}}


# The verdicts of a review that withdraw an import check run of its head (WITHDRAWN).
WITHDRAWING = ("blocking", "person")


def review_verdict(comments, head):
    """(verdict, state, why) of head, from comments, the item's comments as the API lists them (issues/<n>/comments,
    with updated_at): the one rule by which a run that reads the head, a relabel or a review by hand, records or
    withdraws its import check run (R12; OSSV-221's architect, 2026-11-20 21:33Z and 22:21Z). verdict is the verdict of
    the review comment of BOT that names head, the last one when more name it ("" when none names head). A review
    comment of head is screened when it holds the marker <!-- review-screened <head> --> after its verdict, so that the
    screen passed head in the run of that review. state is held when a hold comment of BOT of the screen (hold_fact
    screen_held) that names head is newer than the newest screened review comment of head, or when no review comment
    of head is screened and such a hold comment exists: a later screen held the head. Else it is screened when the
    newest review comment of head is screened, earlier when an older one is screened but the newest is not (a review by
    hand runs no screen), and unscreened when none is. Such a run records the check run only for the state screened
    with the verdict pass and no why: the newest review comment is a screened pass. why is the reason for which it
    withdraws each check run of head that stands (WITHDRAWN): screen for held; else the why of the line of OWED of head
    in a label comment of BOT (owed_why), whatever the newest review says, as an edit of a review comment in place can
    hide the review that gave it; else the verdict blocking or person of the newest review comment newer than the newest
    screened one (of any review comment of head when none is screened) that gives one; else that of the newest screened
    review comment when it does not pass; else "". The line of OWED gives only the reason, never the state. So an
    unscreened pass newer than a screened pass neither records nor withdraws, and a check run that stands stays, unless
    such a line stands. Only the markers at the start of a review comment count: no marker of the model's or the
    reader's text reaches a comment (trim.py inert). The marker of a hold comment and the lines of a label comment are
    the workflow's own."""
    reviews, screened, held = [], None, ""
    for c in comments:
        if not of_bot(c):
            continue
        body, at = c.get("body") or "", c.get("updated_at") or ""
        m = REVIEWED.match(body)
        if m and m.group(1) == head:
            reviews.append((m.group(2), bool(m.group(4))))
            if m.group(4):
                screened = max(screened or "", at)
        elif body.startswith("<!-- review-held -->"):
            m = HELD_HEAD.search(body)
            if m and m.group(1) == head and hold_fact(body) == "screen_held":
                held = max(held, at)
    verdict = reviews[-1][0] if reviews else ""
    if held and (screened is None or held > screened):
        return verdict, "held", "screen"
    last = max((i for i, (_v, marked) in enumerate(reviews) if marked), default=-1)
    newer = [v for v, _marked in reviews[last + 1:] if v in WITHDRAWING]
    why = owed_why(comments, head) or (
        newer[-1] if newer else reviews[last][0] if last >= 0 and reviews[last][0] in WITHDRAWING else "")
    if last < 0:
        return verdict, "unscreened", why
    return verdict, "screened" if last == len(reviews) - 1 else "earlier", why


def owed_why(comments, head):
    """The why of the line of OWED of head in a label comment of BOT among comments (the newest such line), or "": the
    reason of a withdrawal of the import check runs of head that an earlier run owes."""
    owed = ""
    for c in comments:
        body = c.get("body") or ""
        if of_bot(c) and body.startswith(FIRST):
            for line in body.split("\n"):
                m = OWED.fullmatch(line)
                if m and m.group(1) == head:
                    owed = m.group(2)
    return owed


# --- the soundness rule (R8) --------------------------------------------------------------------------------------
# uses, code, section and the constants from USES to LISTED are copied from theorem-labs/oss-verify-proofs-internal
# .github/review/rules.py at 573d0cde18e1, and adapted to this repository: its checks are its CI lanes on stock Rocq,
# not oft check; code keeps a path of any form in one code span, because trim.py does not make the section inert; and
# the section names Sami and the changed files that count. The files that the rule counts (proofs) and the rule itself
# (soundness, forced) are this file's own.

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
# counts: proof for a .v file, other for any other file that is not a Markdown file (markdown), and for a Markdown file
# named when a dune file (dune_file) holds what made it count (dune_marks), and unread when the job could not read a
# dune file.
SOUNDNESS_FILE = "soundness.json"
WHYS = ("proof", "other", "named", "unread")
# The modes of a regular file in a tree of git: a dune file in another mode, a link or a submodule, is one that the job
# cannot read.
REGULAR = ("100644", "100755")
# The texts of a dune file that make each changed Markdown file count, wherever it is (trigger), as plain text: a word
# of KEYWORDS, a field or a stanza that reads files whose names the dune file does not hold, as a whole word of the text
# split at white space and parentheses (SPLIT), after each line whose first character other than a space or a tab is ;
# goes (COMMENT_LINE), so not include_subdirs, and a word after code on a line all the same; a glob field (GLOB_FIELD)
# whose pattern, the word or the string after it as dune reads it (dune_text), does not end with a . and a fixed
# extension (EXTENSION: letters, digits and _ only), or ends with .md, .MD, .Md or .mD, or whose next word starts with ;
# (a comment to the end of the line) or with #, whose pattern is then "", so the glob counts; and a word or a string
# (WORD, as dune reads it, and each word of a comment) that holds .md and also one of ROOTS, or that starts with /.
# dune 3.23 reads neither #| ... |# nor #; as a comment, but trigger counts a glob whose next word starts with # all the
# same: that can only give the person verdict.
# WORD splits the text as dune 3.23 does: a comment from ; to the end of its line; a block string from "\| or "\> to
# the end of its line, whatever it holds; a quoted string, in which a backslash and the character after it, a line
# break too, are one escape, so a string goes on after a backslash before a line break; or an atom. dune reads a block
# string from after its "\| or "\> and the one space after it (BLOCK), and a quoted string between its quotes (STRING),
# with no backslash before a line break, nor that line break and the spaces and tabs after it (CONTINUED).
KEYWORDS = ("include", ":include", "source_tree", "copy_files", "copy_files#")
COMMENT_LINE = re.compile(r"(?m)^[ \t]*;.*$")
SPLIT = re.compile(r"[\s()]+")
GLOB_FIELD = re.compile(r"glob_files(?:_rec)?")
EXTENSION = re.compile(r"[A-Za-z0-9_]+")
WORD = re.compile(r';[^\n]*|"\\[|>][^\n]*|"(?:[^"\\]|\\[\s\S])*"?|[^\s();"]+')
BLOCK = re.compile(r'"\\[|>] ?')
STRING = re.compile(r'"((?:[^"\\]|\\[\s\S])*)"?')
CONTINUED = re.compile(r"\\(?:\r?\n[ \t]*|([\s\S]))")
ATOM = re.compile(r'[^\s();"]+')
BLANKS = re.compile(r"\s*")
ROOTS = ("..", "%{project_root}", "%{workspace_root}")
# A line of omitted.txt, as the gather job writes it, for a changed file that .review/head/ holds only in part.
CUT = re.compile(r"(.+): cut at 2 MiB of its [0-9]+ bytes")
# A question on soundness in the review's list, and the question that the rule adds when the list has none.
ON_SOUNDNESS = re.compile(r"(?i)sound")
QUESTION = {"kind": "question", "ref": None, "optional": False,
            "text": "Are the proofs sound after the changes of this pull request? When the CI checks pass on stock "
                    "Rocq, they do not show that the proofs are sound."}


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


def git(*args, cwd=None, input=None):
    """The standard output of git with args, as bytes, with input (bytes) on its standard input."""
    return subprocess.run(["git", *args], cwd=cwd, input=input, capture_output=True, check=True).stdout


def tree_of(commit, cwd=None):
    """{path: (mode, object)} of each file of the tree of commit, from git objects."""
    tree = {}
    for entry in git("ls-tree", "-r", "-z", "--full-tree", commit, cwd=cwd).split(b"\0"):
        if entry:
            meta, path = entry.split(b"\t", 1)
            mode, _kind, oid = meta.decode("ascii").split(" ")
            tree[path.decode("utf-8", "surrogateescape")] = (mode, oid)
    return tree


def blob_data(oids, cwd=None):
    """{object: bytes} of each object of oids that git holds: one git cat-file --batch."""
    oids = sorted(set(oids))
    if not oids:
        return {}
    out, at, found = git("cat-file", "--batch", cwd=cwd, input="".join(oid + "\n" for oid in oids).encode()), 0, {}
    for oid in oids:
        end = out.index(b"\n", at)
        header = out[at:end].split()
        if len(header) != 3:   # <object> missing
            at = end + 1
            continue
        size = int(header[2])
        found[oid] = out[end + 1:end + 1 + size]
        at = end + 1 + size + 1
    return found


def dune_file(path):
    """Whether path is a file whose text the soundness rule reads for the changed Markdown files (dune_marks): dune,
    dune-project, or a file whose name starts with dune-workspace, in any directory."""
    base = posixpath.basename(path)
    return base in ("dune", "dune-project") or base.startswith("dune-workspace")


def dune_text(word):
    """The text that dune reads from word, a word of WORD that is not a comment: of a block string, the rest of its
    line after BLOCK; of a quoted string, the text between its quotes with each backslash before a line break, that
    line break and the spaces and tabs after it taken out (CONTINUED), and each other escape as the file holds it; of
    an atom, word."""
    block = BLOCK.match(word)
    if block:
        return word[block.end():]
    string = STRING.fullmatch(word)
    return CONTINUED.sub(lambda m: m.group() if m.group(1) else "", string.group(1)) if string else word


def trigger(text):
    """The first part of text, the text of a dune file, that makes each changed Markdown file count wherever it is, or
    None: a word of KEYWORDS in text split at SPLIT after its lines of COMMENT_LINE go; the text from the start of a
    glob field to the end of the word after it, also inside a longer word, when the part of its pattern (that word as
    dune reads it, dune_text) after its last . is not a fixed extension (EXTENSION), or is md, MD, Md or mD, or when
    that word starts with ; or # (a comment, or an odd pattern, which can only give the person verdict), whose pattern
    is then ""; or a word or a string (WORD) that holds .md and also one of ROOTS, or that starts with /, as dune reads
    it, each word of a comment as a word of its own."""
    word = next((w for w in SPLIT.split(COMMENT_LINE.sub("", text)) if w in KEYWORDS), None)
    if word:
        return word
    for m in GLOB_FIELD.finditer(text):
        w = WORD.match(text, BLANKS.match(text, m.end()).end())
        pattern = dune_text(w.group()) if w and not w.group().startswith((";", "#")) else ""
        extension = pattern.rpartition(".")[2] if "." in pattern else ""
        if not EXTENSION.fullmatch(extension) or extension.lower() == "md":
            return text[m.start():w.end() if w else m.end()]
    for w in WORD.finditer(text):
        for word in ATOM.findall(w.group()) if w.group().startswith(";") else [w.group()]:
            read = dune_text(word)
            if ".md" in read and (any(root in read for root in ROOTS) or read.startswith("/")):
                return word
    return None


def dune_marks(trees, cwd=None):
    """(near, anywhere, unread), from the dune files (dune_file) of trees (tree_of): near: {directory: (path, why,
    what)} of the first dune file by path in each directory that makes each changed Markdown file in that directory
    and below it count, named with what .md when its text holds .md in one of the trees, else unread when the job
    could not read it in one of them (a link or a submodule in the place of a file, or an object that git does not
    hold). anywhere: (path, why, what) of the first dune file by path that makes each changed Markdown file count
    wherever it is, unread when the job could not read it, else named with what the first text that trigger gives in
    one of the trees, or None. unread: the paths of the dune files that the job could not read, in order. One git
    cat-file --batch reads them all."""
    objects, unread = {}, set()
    for tree in trees:
        for path, (mode, oid) in tree.items():
            if not dune_file(path):
                continue
            if mode in REGULAR:
                objects.setdefault(path, set()).add(oid)
            else:
                unread.add(path)
    data = blob_data({oid for oids in objects.values() for oid in oids}, cwd)
    unread.update(path for path, oids in objects.items() if any(oid not in data for oid in oids))
    near, anywhere = {}, None
    for path in sorted(set(objects) | unread):
        if path in unread:
            mark = found = (path, "unread", None)
        else:
            texts = [data[oid].decode("utf-8", "replace") for oid in sorted(objects[path])]
            mark = (path, "named", ".md") if any(".md" in text for text in texts) else None
            found = next(((path, "named", what) for what in map(trigger, texts) if what), None)
        if mark:
            near.setdefault(posixpath.dirname(path), mark)
        anywhere = anywhere or found
    return near, anywhere, sorted(unread)


def proofs(head, files, count, cwd=None, main=None):
    """The facts of the soundness rule at the commit head of a pull request, as soundness.json holds them: {whole,
    files, unparsed}. files are the files of the pull request at head as the API lists them on every page of
    pulls/<n>/files, and count its changed_files, None when a read did not finish or read another head. whole: the
    list holds each changed file. files: each changed path (of a file, and the path that it had before a rename) that
    counts, {path, why, by, what, at_head}, in order: why is proof for a .v file, other for any other path that is not
    a Markdown file (markdown), and for a Markdown file the why of by, the dune file that makes it count (dune_marks):
    the nearest one in its directory or in a directory above it, else the one that makes each Markdown file count.
    what is the text of by that made it count (None for unread and for a path that is not a Markdown file). at_head
    says whether head has the path. unparsed: each dune file that the job could not read. The dune files are those of
    the trees of head and of main, the commit of main that the pull request merges into, from git objects in the
    repository of cwd, read only when a changed path is a Markdown file."""
    paths = set()
    for f in files:
        try:
            paths.update(changed_paths([f]))
        except ValueError:
            count = None
    tree = tree_of(head, cwd)
    near, anywhere, unparsed = {}, None, []
    if any(markdown(p) for p in paths):
        near, anywhere, unparsed = dune_marks([tree] + ([tree_of(main, cwd)] if main else []), cwd)

    def counts(path):
        if not markdown(path):
            return ("proof" if path.endswith(".v") else "other"), None, None
        directory = path
        while directory:
            directory = posixpath.dirname(directory)
            if directory in near:
                by, why, what = near[directory]
                return why, by, what
        by, why, what = anywhere or (None, None, None)
        return why, by, what
    found = [{"path": p, "why": why, "by": by, "what": what, "at_head": p in tree}
             for p in sorted(paths) for why, by, what in [counts(p)] if why]
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
                    and isinstance(f.get("by") or "", str) and isinstance(f.get("what") or "", str)
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
    """The fixed section on soundness: first that Sami answers whether the proofs are sound, then why the rule holds,
    from scope (soundness; None for a change of a .v file and nothing else), and the facts for Sami: the rule with the
    changed files other than .v files that it counts (with the cases of a Markdown file only when it counts one), the
    dune files that the job could not read, the lines that found holds (uses), and the changed .v files at the head
    that the search did not read whole. Its lists hold at most listed lines in at most characters characters in all,
    and a list that holds fewer than it has ends with a line that says how many more there are."""
    scope = scope or {"v": True, "others": [], "whole": True, "unparsed": [], "unread": []}
    issues = ", ".join(code(i) for i in ISSUES[:-1]) + f" and {code(ISSUES[-1])}"
    if scope["v"]:
        why = "This pull request adds, changes or deletes a `.v` file, which holds Rocq proofs."
    else:
        why = "The workflow cannot show that this pull request changes no Rocq proof."
    parts = [f"**Soundness of the proofs.** Sami answers whether the proofs are sound. You do not need to do anything "
             f"for this point. {why} The CI checks of this repository (Build and check) build the proofs with stock "
             f"Rocq. Stock Rocq accepts three public proofs of `False`: {issues}. So when these checks pass, they do "
             "not show that the proofs are sound."]
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
        lines = [f"- {code(path)}" + (f": {code(by)} holds {code(what or '.md')}." if kind == "named" else
                                      f": the workflow could not read {code(by)}." if kind == "unread" else "")
                 for path, kind, by, what in scope["others"]]
        rule = ("The workflow does not examine which files the build of the proofs reads. So it counts each changed "
                "file that is not a Markdown file (`.md`) as a change of the proofs.")
        if any(markdown(path) for path, _kind, _by, _what in scope["others"]):
            rule += (" It also counts each changed Markdown file in these cases. Here a `dune` file is a `dune`, "
                     "`dune-project` or `dune-workspace*` file of the head or of `main`.\n\n"
                     "- A `dune` file in the directory of the Markdown file, or in a directory above it, holds the "
                     "text `.md`.\n"
                     "- A `dune` file anywhere holds one of the words `include`, `:include`, `source_tree`, "
                     "`copy_files` or `copy_files#`. A word ends at white space or at a parenthesis, so "
                     "`include_subdirs` does not count. A word on a comment line, whose first character other than a "
                     "space or a tab is `;`, does not count. A word after code on the same line counts.\n"
                     "- A `dune` file anywhere holds `glob_files` or `glob_files_rec`, also in a comment, with a "
                     "pattern. The pattern counts unless its part after the last `.` is one fixed extension other "
                     "than `md`, `MD`, `Md` or `mD`. A fixed extension has only letters, digits and `_`. So `*.vo` "
                     "does not count, but `*.md`, `*.MD`, `*.{v,md}`, `*.[ch]` and `*` count. When a comment is "
                     "between `glob_files` and its pattern, the case applies whatever the pattern is.\n"
                     "- A `dune` file anywhere holds a word or a quoted string that holds `.md`, also in a comment. "
                     "The case applies only when that word or string also holds `..`, `%{project_root}` or "
                     "`%{workspace_root}`, or starts with `/`. For example: `%{dep:../docs/x.md}`.\n"
                     "- The workflow cannot read one of the `dune` files, in any directory.")
        parts.append(f"{rule}\n\nThe workflow counts these changed files, other than `.v` files, as changes of the "
                     "proofs:\n\n" + listing(lines, files))
    if not scope["whole"]:
        parts.append("GitHub did not give the full list of the files that this pull request changes, so the workflow "
                     "could not check each of them.")
    if scope["unparsed"]:
        parts.append("The workflow could not read these `dune` files, so it counts each changed Markdown file:\n\n"
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


def blocking_finding(item):
    """Whether item of the review's list is a blocking finding: a change item whose optional is false. An item with no
    optional key is not optional, as for trim.py."""
    return isinstance(item, dict) and item.get("kind") == "change" and not item.get("optional")


def settled(output):
    """The review's output after the rule of the verdict blocking: the verdict person when the output gives the verdict
    blocking and its list holds no blocking finding and one question item or more, else output as it is."""
    items = output.get("items") or ()
    if (output.get("verdict") == "blocking" and not any(blocking_finding(i) for i in items)
            and any(isinstance(i, dict) and i.get("kind") == "question" for i in items)):
        return dict(output, verdict="person")
    return output


def soundness(review, output, hold, outside, kind=""):
    """(output, section, all): the review's output after the soundness rule, the section of the comment, and the
    section with every line for the run's summary. The rule holds while hold is true, for a pull request of an author
    that the rule treats as outside (holds_back of the trust job's outside and kind) that changes a path that the
    facts of review count (facts_of) or a .v file under head/, or whose list of changed paths is not whole. When it
    does not hold: output as it is, and no section."""
    if hold != "true" or not holds_back(outside, kind):
        return output, "", ""
    facts = facts_of(review) or {"whole": True, "files": [], "unparsed": []}
    read = set(head_proofs(review))
    changed = [f for f in facts["files"] if f["why"] == "proof"]
    others = [(f["path"], f["why"], f.get("by"), f.get("what")) for f in facts["files"] if f["why"] != "proof"]
    if not (read or facts["files"] or not facts["whole"]):
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


def held_head(number, head):
    """The one check of each writer of a hold comment, before it writes anything: the hold job, and the comment job's
    step that writes a stop of the rescreen pass (halt, which names the head that the trust job of that run read). True
    when head, the head that the new hold names, is empty (the hold of an issue, which names no head: no read), or when
    it is the head of the pull request number that GitHub gives now. Else the hold is stale: a line says so on standard
    output and in the step's summary (GITHUB_STEP_SUMMARY), and this gives False. Its writer then writes no hold comment
    and changes no label, so that a stale hold never takes the place of the hold of the screen of the current head.
    GhError when GitHub could not say."""
    if not head:
        return True
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head)):
        raise ValueError(f"not a pull request number and a head commit: {number!r} {head!r}")
    now = gh(f"repos/{os.environ['REPO']}/pulls/{number}", "--jq", ".head.sha").strip()
    if not HEAD.fullmatch(now):
        raise GhError(f"pull request #{number} names no head commit: {now!r}")
    if now == head:
        return True
    line = (f"#{number} is at {now} now, not at {head}, the head that this hold names. So this hold is stale: this run "
            "writes no hold comment and changes no label.")
    print(line)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    return False


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
    """The JSON object on each line of the file path (an answer of the API, one on each line), with loads."""
    with open(path, encoding="utf-8") as f:
        return [loads(line) for line in f if line.strip()]


def main(argv):
    try:
        if len(argv) == 2 and argv[0] == "make-label" and argv[1] in LABELS:
            make_label(argv[1])
            return 0
        if len(argv) >= 2 and argv[0] == "label" and NUMBER.fullmatch(argv[1]):
            facts, markers, head, run = parse(argv[2:], RUN)
            set_state(argv[1], run, facts, markers, head)
            return 0
        if len(argv) >= 2 and argv[0] == "owed" and NUMBER.fullmatch(argv[1]):
            facts, markers, head, given = parse(argv[2:], RUN + ("owed", "withdrawn"))
            if facts or markers or head:
                raise ValueError("owed takes the run, owed= and withdrawn= alone")
            owed, withdrawn = given.pop("owed"), given.pop("withdrawn")
            return 0 if owe(argv[1], given, owed, withdrawn) else 3
        if len(argv) == 3 and argv[0] == "hold-head" and NUMBER.fullmatch(argv[1]):
            return 0 if held_head(argv[1], argv[2]) else 3
        if len(argv) in (4, 5) and argv[0] == "answers":
            for name, value in answers(*argv[1:]).items():
                print(f"{name}={str(value).lower() if isinstance(value, bool) else value}")
            return 0
        if len(argv) in (3, 4) and argv[0] == "mark" and NUMBER.fullmatch(argv[1]):
            state = "working"
            if len(argv) == 4:
                name, eq, state = argv[3].partition("=")
                if (name, eq) != ("state", "="):
                    raise ValueError(f"not state=<state>: {argv[3]!r}")
            mark(argv[1], argv[2], state=state)
            return 0
        if len(argv) == 5 and argv[0] == "proofs" and HEAD.fullmatch(argv[1]) and HEAD.fullmatch(argv[2]):
            count = int(argv[4]) if re.fullmatch(r"0|[1-9][0-9]*", argv[4]) else None
            try:
                files = json_lines(argv[3])
            except ValueError:
                files, count = [], None
            print(json.dumps(proofs(argv[1], files, count, main=argv[2])))
            return 0
        if len(argv) == 8 and argv[0] == "soundness":
            review, path, hold, outside, kind, section_path, all_path = argv[1:]
            with open(path, encoding="utf-8") as f:
                output = loads(f.read())
            output, text, every = soundness(review, output, hold, outside, kind)
            if text:
                with open(path, "w", encoding="utf-8") as f:
                    json.dump(output, f, ensure_ascii=False)
            for name, part in ((section_path, text), (all_path, every)):
                with open(name, "w", encoding="utf-8") as f:
                    f.write(part + "\n" if part else "")
            print("The soundness rule applies. So the workflow gives the verdict person, and the comment gets the "
                  "section on soundness." if text else
                  "The soundness rule does not apply, so it does not change the review's verdict.")
            return 0
        if len(argv) == 2 and argv[0] == "blocking":
            with open(argv[1], encoding="utf-8") as f:
                output = loads(f.read())
            if not isinstance(output, dict):
                raise ValueError(f"{argv[1]} holds no output of the review")
            after = settled(output)
            if after is not output:
                with open(argv[1], "w", encoding="utf-8") as f:
                    json.dump(after, f, ensure_ascii=False)
                print("The review gives the verdict blocking, but its list holds no blocking finding and holds a "
                      "question. So the workflow changes the verdict to person.")
            return 0
        if len(argv) == 4 and argv[0] == "fixes" and HEAD.fullmatch(argv[3]):
            print(fixes(json_lines(argv[1]), json_lines(argv[2]), argv[3]))
            return 0
        if len(argv) == 3 and argv[0] == "suggestions":
            with open(argv[1], encoding="utf-8") as f:
                fix = loads(f.read())
            with open(argv[2], "rb") as f:
                diff = f.read().decode("utf-8", "surrogateescape")
            sys.stdout.write(json.dumps(suggestions(fix, diff), ensure_ascii=False) + "\n")
            return 0
        if len(argv) in (9, 10) and argv[0] == "import-check":
            path, count, number, head, screen, verdict, hold, request = argv[1:9]
            value = argv[9] if len(argv) == 10 else None
            if not (re.fullmatch(r"0|[1-9][0-9]*", count) and NUMBER.fullmatch(number) and HEAD.fullmatch(head)
                    and screen in ("true", "false")):
                raise ValueError("not a count of changed files, a pull request number, a head commit and true or false "
                                 "for the screen")
            decision = import_decision(json_lines(path), int(count), screen == "true", verdict, hold == "true", value)
            if decision == "record":
                with open(request, "w", encoding="utf-8") as f:
                    json.dump(check_run(number, head, value, hold == "true"), f)
            print(decision)
            return 0
        if len(argv) in (2, 3) and argv[0] == "import-marker":
            print(import_marker(argv[1], argv[2] if len(argv) == 3 else None))
            return 0
        if len(argv) == 3 and argv[0] == "verdict" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2]):
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body, updated_at} | @json")
            verdict, state, why = review_verdict(comments, argv[2])
            owed = state != "held" and owed_why(comments, argv[2]) != ""
            print(f"{verdict or '-'} {state} {why or '-'} {'owed' if owed else '-'}")
            return 0
        if len(argv) in (6, 7) and argv[0] == "withdrawal" and argv[6:] in ([], ["owed"]):
            number, head, why, path, directory = argv[1:6]
            for check in json_lines(path):
                if not (isinstance(check, dict) and NUMBER.fullmatch(str(check.get("id")))
                        and isinstance(check.get("text"), str)):
                    raise ValueError(f"not a check run with its id and its output text: {check!r}")
                with open(os.path.join(directory, f"withdraw-{check['id']}.json"), "w", encoding="utf-8") as f:
                    json.dump(withdrawal(number, head, why, check["text"], len(argv) == 7), f)
                print(check["id"])
            return 0
        if len(argv) == 2 and argv[0] == "steering":
            print("true" if any(steering(p) for p in changed_paths(json_lines(argv[1]))) else "false")
            return 0
        if len(argv) >= 3 and argv[0] == "relabel" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2]):
            number, head = argv[1], argv[2]
            facts, markers, given, run = parse(argv[3:], RUN[1:])
            if given:
                raise ValueError("relabel names its head before the facts, not as head=")
            run["task"] = "relabel"
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
            set_state(number, run, facts, markers, head, labels)
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
