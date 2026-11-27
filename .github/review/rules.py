#!/usr/bin/env python3
"""The rules of the review workflow that code applies, whatever the model wrote (.github/review.md, "Outside items and
labels").

    python3 .github/review/rules.py label <number> task=<task> outside=<outside> outsider=<outsider> author=<kind>
        [<fact>=<value> ...] [head=<commit>] [marker=<line> ...]
    python3 .github/review/rules.py mark <number> <line> [state=<state>]
    python3 .github/review/rules.py owed <number> owed=<head, why, run and read> withdrawn=<head> own=<true or false>
        task=<task> outside=<outside> outsider=<outsider> author=<kind>
    python3 .github/review/rules.py hold-head <number> <head>
    python3 .github/review/rules.py unclaim <number>
    python3 .github/review/rules.py log <number> <head> <decision> <cause> <read> [<field> <value> ...]
    python3 .github/review/rules.py make-label <name>
    python3 .github/review/rules.py proofs <head> <main> <files.jsonl> <changed files>
    python3 .github/review/rules.py soundness <the .review directory> <output.json> <hold> <outside> <kind> <section>
        <all>
    python3 .github/review/rules.py blocking <output.json>
    python3 .github/review/rules.py fixes <commits.jsonl> <reviews.jsonl> <head>
    python3 .github/review/rules.py suggestions <fix.json> <pr.diff>
    python3 .github/review/rules.py import-check <files.jsonl> <changed files> <number> <head> <screen> <verdict>
        <hold> <run> <read> <request.json> [<import paths>]
    python3 .github/review/rules.py import-marker <head> [<import paths>]
    python3 .github/review/rules.py verdict <number> <head> [<checks.jsonl>] [own=<verdict> started=<time>]
    python3 .github/review/rules.py own-record <number> <head> <started> <run> <checks.jsonl>
    python3 .github/review/rules.py newer-word <number> <head> <started> <run> [<kind>]
    python3 .github/review/rules.py relabel-withdraws <number> <head> <comments.jsonl>
    python3 .github/review/rules.py words < <comments.jsonl>
    python3 .github/review/rules.py holds < <comments.jsonl>
    python3 .github/review/rules.py replaced-hold <work> <screen> <head> <started> < <comments.jsonl>
    python3 .github/review/rules.py stays <head> <started> <kind> <work> < <words.jsonl>
    python3 .github/review/rules.py outranks <time> <kind> <time> <kind>
    python3 .github/review/rules.py withdraw-word <number> <head> <started> <run> <task> <verdict> <author kind>
        <route> <checks.jsonl>
    python3 .github/review/rules.py withdrawal <number> <head> <why> <kind> <run> <source> <at> <checks.jsonl>
        <directory>
    python3 .github/review/rules.py not-approved <number> <head> <why> <run> <read> <request.json> [<import paths>]
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
a notice says why. Only owed rewrites such a label comment, when it says recorded and no record stands (F5). For any
other author, the item gets no state label and loses each one that it has, but its label
comment is the one of its state, with the marker of the state's label. The state label is waits-on-author when the
next step is the author's, waits-on-theorem when it is Sami's, and none while the workflow works on the item. Setting
one label takes the other off. review-held, the mark of a hold, stays beside them. The label comment is one comment of
github-actions[bot] on the item, edited in place (label_comment). Its first line is <!-- review-label -->, its text
names the next step and who takes it, and with a state label its last line is the marker <!-- waits-on-author --> or
<!-- waits-on-theorem: Sami -->. It keeps each marker line of KEPT that it holds, and a marker=<line> of the same kind
takes the place of that line, but a line of OWED never takes the place of a line of its head that outranks it as a
word on the head (owed_keeps): that line stays, and a line says so. It holds <!-- review-conflict-state <head> -->
while it gives the head waits-on-author
for a merge conflict, and loses that line with any other state. The state steering (the fact steering=true, with
head=<commit>) records <!-- review-steering <head> -->, a line of KEPT: the head changes a file under .github/, or
3,000 files or more, so the post job approves none of its runs, and the rescreen pass starts no approval of it. The
state no-key (the fact no_key=true, with head=<commit>) records <!-- review-no-key <head> -->, a line of KEPT: the
screen passed the head, but the environment post held no key of the OSS Verify App, so the post job approved none of
its runs, and the rescreen pass starts no approval of it. In a state with no state label (working, reviewed or
import), an item that has a label comment gets the text of its state. An item that has none gets none, unless a
marker=<line> is the line of an owed withdrawal (OWED): then it gets the label comment of its state, with that line.
For an outside pull request (the fact kind=pr, and an outside author) in the state decide or person, the text also
names the step of R12 for the import into the internal repository (import_steps), from the facts import_paths, the
text of the variable REPO_PAIRS_IMPORT_PATHS, given only when it is set, and decision, the post job's decision, or
gone when the label step finds the check run of that decision withdrawn (DECISIONS). With head=<commit>, the label
comment of an outside pull request holds the marker line of R12 for that head and that text (import_marker). A pull
request whose review gave a verdict, and that no rule before it takes (a conflict, a hold, a stop of the post job, a
refusal, or the outcome of an outside author's item), is in the state reviewed, whoever started the run: its review
names the next step. GH_TOKEN and REPO come from the job's environment, as for gh in the workflow.

mark: records the marker line <line> of KEPT in the label comment of <number>, and changes nothing else
(with_marker): the state label, the text and the other lines stay as they are, as label would keep them for the same
state. <line> takes the place of the line of its kind, but a line of OWED never takes the place of a line of its head
that outranks it, as for label. An item with no label comment gets one, of the state working,
or of state=<state>, which must be a state with no state label. The comment job of a catch-up records the line
<!-- review-catchup <head> --> with it. The rescreen pass reads that line, so that each head gets one catch-up. The
comment job's label step records the line of an owed withdrawal (OWED) with it when a hold made after its run started
stops that step. It gives state=working when the rescreen pass tries that hold again. Else it gives state=after-hold,
which names Sami's next step and has no state label. When mark posts a new label comment, its log says so.

owed: records in the label comment of <number> the withdrawal of the import check runs of a head that a run owes
(owe), and changes nothing else: the comment job calls it, and the hold job for a held screen, before the steps that
can fail, and again after the step that posts the comment of its reason. owed=<head> <why> <run> <read> (the post
job's output owed, <head> <why>, of a withdrawal that it found a reason for and did not finish; or <head> screen from
the hold job, for a screen that held the head in a review, a rescreen or an approval of its run; then <run>, the id of
the run that writes the line, and <read>, the time when that run read the item, its trust job's started) gives the line
<!-- withdraw-owed <head> <why> <run> <read> --> of KEPT (OWED), as mark does, but it never makes a label comment.
own=true says that the line names this run and its read. The hold job gives own=true for the line of its own screen.
The comment job gives it for the line of its own review, whether that review gives the verdict or the fresh reader
refused it. Else (own=false, or empty with no owed=) the line names the run of the comment that
gives <why> and the read of that run (owed_run): the run and the read of a line of that head and reason that stands,
or else the run of the newest such hold or review comment and its time (word_time), and <run> and <read> only when
none names a run. When the item has no label comment, this writes nothing, a line says so, and the status is 3: it
writes line=<line> to the step's outputs (GITHUB_OUTPUT), and the step gives that line to the label step of its job,
which gives it as marker=<line> to the call that writes the label comment. withdrawn=<head> (its output withdrawn: it
finished the withdrawal of the head, as it found no import check run of the head with conclusion success to
withdraw, withdrew each one, or recorded the check run of not-approved) takes the line of that head out, but only
while a comment of github-actions[bot] gives a reason for it (line_reason). That comment is the hold comment or the
review comment of the line's run that gives the reason of the line, or a review comment of the head that counts from
a time after the time of the line: the time when its run read the item (its marker <!-- review-read <time> -->),
never when it posted, and with no such marker, when GitHub last changed it for a blocking finding or the verdict
person and no time for a pass (word_time). The time of the line is its <read> (OSSV-221's architect, 2026-11-25
01:30Z).
Unless the trust job's outside is false, that review comment must be screened. Else the line stays, and a line says
so. Both, for one head, are a withdrawal that the job finished before a later step of the job posts the comment of
its reason: the review of the comment job, or the hold comment of the hold job. They give the line as owed alone
does, but for an item with no label comment the status is 0, and no label step gets the line. The run's task and the
trust job's outputs outside, outsider and kind are given as for label: when the author-kind table's answer label is
unchanged, this takes no line out, and a notice says so. A line of owed= goes in all the same, as the post job
withdraws for every author. For that answer, withdrawn=<head> also reads the label comment (unrecord; OSSV-221's
architect, 2026-11-24 16:19Z, F5). When it says that the workflow recorded the check on <head> (the state import),
this reads the import check runs of <head> again. When no such check run with the conclusion success stands now, the
label comment becomes the one of the state decide with the decision gone (GONE). No state label goes on or off.

unclaim: the last step of a comment job or a hold job that failed or was cancelled (OSSV-613's architect, 2026-11-25
23:02Z, G2). Whichever step failed, the label comment of <number> must not say that the workflow recorded the check
`repo-pairs/import-approved` when no such check run stands. Only the newest label comment of github-actions[bot]
counts. It makes that claim when its next step and its text are those of the state import (says_recorded). Its marker
line <!-- repo-pairs-import-paths <head>: <value> --> names the head, for any author. A label comment that makes no
such claim, or holds no such marker line, stays as it is, and the status is 0. Else this reads the import check runs
of <head> (import_checks, with OSS_VERIFY_APP_ID). When one with the conclusion success and that marker line stands,
the claim is true, and this writes nothing. Else, and also when GitHub does not give the check runs, this writes the
label comment of the state working in its place. That label comment keeps each marker line of KEPT, and it says that
the workflow tries again. The state working has no state label, so this adds and takes off no state label. The status
is 1 when GitHub does not give the label comments or does not take the write. Nothing more can be done then, and the
re-run of the failed jobs of the run tries again (held.sh due_rerun).

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
line of import-marker. Its summary names <run>, the run whose screen and review passed <head>, and <read>, the time
when that run read the pull request, or neither when both are -: a withdrawal withdraws the check run only for a
reason at or after <read> (withdrawal, below), and each one withdraws a check run that names no such time. The status
is 2 when an argument is not one of these, or when the import's glob rules refuse a glob of the variable.

import-marker: the marker line <!-- repo-pairs-import-paths <head>: <value> --> of R12, which the output text of the
check run and each label comment of an outside pull request hold (import_marker): <value> is <import paths> as one
JSON string, or null when it is not given. The JSON writes each character outside ASCII, <, > and & as a \\u escape,
so that the line holds no line break and no --> before its end.

verdict: "<verdict> <state> <why> <from> <posted> <stands> <since> <run> <read>" on standard output for <head> of the
pull request <number> (review_verdict), from the comments of github-actions[bot] and the import check runs of
<checks.jsonl> when it is given. Each word on <head> comes from the one model of the order of the words on a head
(head_words, newest_word, below). A review comment that names <head> counts from the time when its run read the item,
its marker <!-- review-read <time> -->, never from when it posted. One with no such marker counts from when GitHub last
changed it for a blocking finding or the verdict person, and at no time for a pass (word_time). Of two at the same
time, a blocking finding or the verdict person is the newer. A hold comment of the screen counts from the time when its
run read the item, its marker <!-- review-held-read <time> -->, and one with no such marker from when GitHub last
changed it. <verdict> is the verdict of the marker <!-- review-verdict <head> <verdict>[ will-fix] --> of the newest
review comment that names <head>, or - when none does. A review comment of <head> is screened when it holds
<!-- review-screened <head> --> as the next marker line, so that the screen passed <head> in the run of that review.
A hold of the screen is a hold comment of the screen that names <head>, the line
<!-- withdraw-owed <head> screen <run> <read> --> of a label comment (OWED) from its <read>, or an import check run of
<head> for the reason screen. <state> is held when a hold of the screen is as new as the newest screened review comment
or newer (a hold at the same time outranks a pass), or when no review comment of <head> is screened and such a hold
exists: a later screen held <head>. Else it is screened when the newest review comment of <head> is screened, earlier
when only an older one is, and unscreened when none is (a review by hand runs no screen). <why> is the reason for which
a relabel or a review by hand withdraws each import check run of <head> that stands: screen for held; else blocking,
person or refused, of the newest word that gives one (a review comment, the line
<!-- withdraw-owed <head> <why> <run> <read> --> from its <read>, or an import check run), when the newest screened
review comment of <head> does not outrank it; else -. <from> is owed when the line gives a reason, as the newest
screened review comment does not outrank it (owed_reason), outranked when that review outranks the line, so that the
line gives no reason, and - else. <posted> is, for <from> owed, posted when a comment of github-actions[bot] gives a
reason for the line to go, as for an outside author (line_reason: from the <read> of the line), and unposted when none
does; - else. <checks.jsonl> holds the import check runs of <head> for <number>, {id, conclusion, completed_at,
summary} one on each line; with none given, no check run is read. They are in the order of the time that each one
names, never of completed_at: for a success, the time when its run read the item, and for a withdrawal (the
conclusion neutral), the time from which it counts. A success that names no time is older than each other one, and a
withdrawal that names no time is newer; at a tie, the withdrawal is the newer (standing_withdrawal; OSSV-221's
architect, 2026-11-24 09:43Z). <stands> is the id of the withdrawal of the newest read when no success names a newer
read and when it blocks a record: its summary names no time, or no screened review comment that passes <head> counts
from a time after that time (withdrawal_stands); - else. <since> is that time, or - when <stands> is - or the summary
names no time. <run> and <read> are the run of the newest review comment of <head> and the time when that run read the
item, from its markers <!-- review-read <time> --> and <!-- review-run <run> -->, or - and - when it has none: a
relabel's record names them. Only the line for screen gives a state (held). A relabel records the import check run
only for screened with the verdict pass, no <why>, <stands> - and <from> -: with a <why>, its decision is withdrawn
when <posted> is unposted, and screened else, and with <stands> it is withdrawn.
With <from> outranked, it records none while the line stands, and it withdraws none for the line: its decision is
hand, and the step OWE of its comment job takes the line out. For earlier with the verdict pass, its decision is hand
with no <why>, and screened with one. A review by hand with no screen records none. Its post job's decision is hand for
screened or earlier with no <why>, and screened with a <why>: the review of this run has not posted yet. It is held for
held, and screen for unscreened. For the decision hand, the label step counts an import check run of <head> that still
stands, for the value of the variable now, as recorded. The comment job's label step reads the check runs again
before it writes the state import, and writes it only while such a check run stands: else its decision is gone (GONE).
With own=<verdict> started=<time>, for a review by hand (the decision step's by_hand), a tenth word <owed> follows:
the why of the output owed that the decision step writes as soon as it reads from the comments why the import check
runs of <head> are withdrawn (owed_why), or - when it reads none (neither held nor a <why>). <verdict> is the verdict
of the review of this run, which has not posted yet, and <time> the time when the trust job of this run read the item
(empty when not known). A blocking finding, the verdict person or a refused review is the own word of this run from
<time>, and the step that withdraws reads only the words at or before <time> for it (withdraw-word): <owed> is the
why of the newest of that own word and the word that gives the reason (screen, a hold of the screen, for held; else
<why>). Any other verdict gives no own word, and <owed> is screen for held, else <why>.

own-record: "<decision> <what> <since> <verdict>" on standard output for <head> of the pull request <number>, for a
run on the route screen whose own screen and review passed <head> (own_record): whether a newer run held <head>,
withdrew its import check run or gave it a verdict while this run ran. <started> is the time when the trust job of
this run read the item, and <run> is the id of this run. The pass of this run is the word (<started>, pass) in the
order of the words on <head> (outranks, below). <decision> is held when a hold comment of the screen that names <head>
outranks it (word_time: the time when its run read the item, or when GitHub last changed one with no marker of that
read), or the line <!-- withdraw-owed <head> screen <run> <read> --> does, of another run, and <what> is that time;
else withdrawn when a withdrawal among the import check runs of <checks.jsonl> stands (withdrawal_stands, the
withdrawal of the newest read in the order of verdict) and outranks it, and then <what> is its id and <since> the time
from which it counts, or - when its summary names none; else newer when a review comment of <head> of another run
gives the verdict blocking or person and outranks it (word_time: the time when its run read the item), or the
withdraw-owed line of <head> of another run for blocking, person or refused outranks it from its <read>, and then
<what> is that run (- for a comment that names none), <since> that time and <verdict> that verdict or reason; and -
for none, with the others -. The run records nothing for held, withdrawn and newer. A hold, a withdrawal or a review
older than <started> leaves the record of this run, as after a blocking review, a fix and a screen that passed <head>
again.

newer-word: "<other> <kind> <time>" on standard output for <head> of the pull request <number>: the newest word on
<head> of another run that outranks the own word of this run, (<started>, <kind>) (newer_word, outranks below).
<started> is the time when the trust job of this run read the item, <run> the id of this run, and <kind> the kind of
its own word: its verdict pass, blocking, person or refused, hold for a hold of its screen, or read (the default) for
a run that gives no word. A word comes from the one model of the order of the words on a head (head_words,
newest_word): a review comment of github-actions[bot] that names <head> (<kind>: its verdict), a hold comment of the
screen that names <head> (<kind>: hold), the line <!-- withdraw-owed <head> <why> <run> <read> --> of a label comment
(<kind>: <why>, or hold for screen), or an import check run of <head> with the conclusion neutral for the reason
refused (<kind>: refused), of another run than <run>. A refused review posts no comment, so only its check run or its
line gives its word; each other word has a comment of its own, or the line when that comment could not post. A review
or a hold counts from the time when its run read the item (its marker <!-- review-read <time> --> or
<!-- review-held-read <time> -->), a hold with no such marker from when GitHub last changed it, and a pass with none
at no time. The line counts from its <read>, and the check run from the time that its summary names. <other> is the
run of that word, or - when it names none. "-" alone when no such word stands. A run whose own word such a word
outranks posts nothing on the item: the comment job and the hold job read this. It reads the comments and the import
check runs of <head> of the OSS Verify App (OSS_VERIFY_APP_ID) for <number>. The status is 1 when GitHub could not give
the comments or the check runs, and 2 when <kind> is no kind of word or OSS_VERIFY_APP_ID is not a whole number
greater than 0 (NUMBER).

relabel-withdraws: why a relabel of <head> of the pull request <number> withdraws the import check runs of <head>, by
the rule that the post job of that relabel reads (review_verdict, with the import check runs of <head>), from
<comments.jsonl>, the comments of the item as the API lists them, one on each line, and the import check runs of
<head> of the OSS Verify App (OSS_VERIFY_APP_ID) for <number>, which it reads (import_checks; OSSV-613's architect,
round 30, item 1): screen for a hold of the screen that outranks each screened review (a hold comment of the screen,
the line <!-- withdraw-owed <head> screen <run> <read> --> of a label comment from its <read>, or a check run for the
reason screen); else blocking, person or refused, of the newest word that gives one (a review comment, the line from
its <read>, or a check run from the time that its summary names: a refused review posts no comment, so only its line
or its check run gives its word) when the newest screened review of <head> does not outrank it; else - when a relabel
withdraws nothing. " owed" follows that why while the line <!-- withdraw-owed <head> <why> <run> <read> --> gives a
reason: the newest screened review of <head> does not outrank it (owed_reason). The rescreen pass reads it (held.sh
relabel_withdraws), so that it orders the words on <head> by the one model of this file. It writes nothing. The status
is 1 when GitHub could not give the check runs, and 2 when an argument or a line is not one of these or
OSS_VERIFY_APP_ID is not a whole number greater than 0 (NUMBER).

words: each comment of standard input, one JSON object on each line as the API lists them, with its time as a word
on its head (word_time) in the field word, one on each line of standard output. The comment job's label step gives
its output to stays.

holds: the newest hold comment of github-actions[bot] of each work (newest_holds), from the comments of standard
input, one JSON object on each line as the API lists them. Each one goes to a line of standard output as it came in,
with its work in the field work, in the order of the names of the works. The work of a hold is the task that its
marker of a hold that is tried again names (answer, draft or approve; review for such a marker with no task), else the
one that its title names (answer, draft for a reply, approve, import or catchup), else review (hold_work). A hold of
the screen counts from the time when its run read the item (its marker <!-- review-held-read <time> -->), any other
hold, or one with no such marker, from when GitHub last changed it (word_time), and of holds at the same time the later
as the API lists them is the newest (newest_word; OSSV-613's architect, round 30, item 1). held.sh holds and the
comment job's label step read it. It writes nothing. The status is 2 when a line is not a comment.

replaced-hold: the id of the hold comment of github-actions[bot] that a new hold of <work> replaces (replaced_hold),
from the comments of standard input, one JSON object on each line as the API lists them, or nothing: then the new hold
posts a comment of its own. <work> is the work of the new hold (review, answer, draft, approve, import or catchup, as
hold_work gives it), <screen> true for a new hold of the screen and false else, <head> the head that the new hold
names (- for none), and <started> the time when the trust job of its run read the item (- for none), which it compares
as text with the time of each hold. A hold of the screen is replaced only by a new hold of the screen of the same
head, and a new hold of the screen with a <started> replaces no hold that counts from a time after it. Of the holds
that may be replaced, the newest goes, by the time from which each counts (word_time) and, of holds at the same time,
the later as the API lists them (newest_word; OSSV-613's architect, round 30, item 1). held.sh replaced_hold reads it,
for each writer of a hold comment. It writes nothing.
The status is 2 when <work>, <screen>, <head> or a line is not one of these, or when that hold comment has no id.

stays: "<last> <tried> <stays>" on standard output for the comment job's label step: the newest hold that stops the
labels of this run, and whether it outranks the own word of this run, (<started>, <kind>), in the order of the words on
a head (stays). Standard input holds the comments of the item, one JSON object on each line, each with the field word
of words. <head> is the head that this run read, or - for an issue. <started> is the time when the trust job of this
run read the item, <kind> the kind of its own word (one of RANKS), and <work> the work of this run: review, answer or
draft. A hold that stops the labels is a hold comment of github-actions[bot] of the head of this run: one that holds
the marker <!-- review-held-head <head> -->, or, for - (an issue), one that names no head. Of these, for the work
answer each one, and for any other work each one but a hold of an answer that the rescreen pass tries again. The line
<!-- withdraw-owed <head> screen <run> <read> --> of a label comment is such a hold too, from its <read>. <last> is the
time of the newest of them, or - when there is none or it counts at no time: such a hold stops nothing. <tried> is
true when that hold is a hold comment that the rescreen pass tries again, else false. <stays> is true when <last> is
not - and that hold outranks the own word, else false. The status is 2 when an argument or a line is not one of
these.

outranks: the status is 0 when the word (<time>, <kind>) outranks the word of the next two arguments in the order of
the words on a head (outranks: by time, then by the rank of the kind, RANKS), and 3 when it does not. A <time> is a
time as GitHub gives it, or empty for no time, which is before each time. A <kind> is one of RANKS: read, pass,
success, blocking, person, refused, neutral or hold. The status is 2 when an argument is not one of these.

withdraw-word: "<why> <kind> <source> <at> <outranked>" on standard output for the step that finds the import check
runs of <head> of the pull request <number> to withdraw (withdraw_word): the newest word on <head> that withdraws,
whichever carrier gives it (OSSV-221's architect, 2026-11-25 23:02Z, G1). It reads the comments of github-actions[bot]
on <number>, and <checks.jsonl>, the import check runs of <head>, {id, conclusion, completed_at, summary} one on each
line. <started> is the time when the trust job of this run read the item, or - when it is not known, and <run> is the
id of this run. The step gives the facts of this run alone, and this decides the own word of this run, which has not
posted yet, and where it stands in the order (own_word; OSSV-613's architect, round 30, item 1): <task> is the task
of this run, <verdict> the verdict of its review, screen when its screen held <head> (an approval, or a run whose
review job did not run), or - for none, <kind> the trust job's kind (empty when it gave none), and <route> the route
of this run. A relabel gives no own word. A blocking finding, the verdict person, a refused review and the screen are
the own word. A pass is the own word access when GitHub did not say whether the author has write access (<kind>
unknown), as such a pass is no approval (OSSV-221's architect, 2026-11-24 14:29Z, F3): on the route screen it is a
word at <started>, and for a review by hand it comes after each other word that withdraws (access-last, below). Else a
pass is the own word pass on the route screen, and no own word for a review by hand, whose pass ran no screen. Any
other verdict gives no own word. The own word counts from <started>, or after each time when <started> is -. A word
withdraws when it gives a blocking finding, the verdict person or a refused review, when it is a hold of the screen (a
hold comment of the screen, the line <!-- withdraw-owed <head> screen <run> <read> -->, an import check run for the
reason screen, or the own word screen), and when it is the own word access. A word lifts when it is a screened pass or
the own word pass. A success lifts nothing: a word that withdraws withdraws each success of a read at or before its
time, and leaves the success of a newer read (withdrawal). A run whose own word counts from <started> reads only the
words at or before <started>: a newer word is the word of a newer run, which withdraws for it or owes that
withdrawal. A run with no such word (a relabel, or a review by hand of a pass) reads each word, whatever its time. Of
the words that it reads, the newest one that withdraws decides, unless one that lifts outranks it. A word that import
check runs alone carry is a withdrawal that a run finished already (withdrawal_stands): it decides only while a
success of a read at or before its time stands, and else the newest of the other words that withdraw decides, as it
does at the same place. With none, or when one that lifts outranks it, the own word access of a review by hand
(access-last) decides. With no word that decides, the line is "- - - - <outranked>": <outranked>
is outranked when the line <!-- withdraw-owed <head> <why> <run> <read> --> of a label comment stands and a screened
review comment of <head> outranks it, and - else. Else <why> is screen for a hold, access for the own word access, and
the kind of that word else. <kind> is own for the own word, held for a hold comment or a check run for screen, owed
for the line, and earlier for a review comment or another check run. <source> and <at> are the run of that word and
the time from which it counts, or - and - when it names no run or no time: then the withdrawal counts from the time
now, which fails closed. For own, <source> is - and <at> is <started>. <outranked> is - then. The status is 1 when
GitHub could not give the comments, and 2 when an argument or a line is not one of these: <task> one of the tasks,
<kind> one of the trust job's kinds.

withdrawal: the requests that withdraw the import check runs of <checks.jsonl> on <head> of the pull request
<number> (withdrawal), for <why>: blocking or person, the verdict of a review of <head>, refused, a review of <head>
that the fresh reader refused (OSSV-221's architect, 2026-11-25 10:21Z), screen, a screen that held it (R12), or
access, a run in which GitHub did not say whether the author has write access (its verdict is no approval;
2026-11-24 14:29Z, F3). <kind> is own when <why> is the verdict, the screen or the access of <run>, the id of the run
that withdraws them, and else held, owed or earlier, as withdraw-word gives it. For own, the
texts say later when the run that recorded the check run read the pull request before <at>, or names no such run
(recorded_by: it counts as read at no time; WITHDRAWN). When that run read it at <at>, the same time as <run>, they
name <run> (TIE_WITHDRAWN). For each other kind, the review
or the hold that gave <why> can be older than the check run, so the texts do not say later (OWED_WITHDRAWN). <source>
and <at> are the source run of <why> and the time from which the withdrawal counts (withdraw-word), or - and the time
when <run> read the pull request for own, or - and - when no time of the source is known: then the time is now. The
summary of each request names <run>, <head>, <why>, the source and the time (WITHDREW), and its completed_at is the
time now. <checks.jsonl> holds each check run {id, conclusion, summary, text}, one on each line. A request goes only
for a check run whose run read the pull request at or before <at>, or that names no such run, or for each one when
<at> is - (withdraws; OSSV-221's architect, 2026-11-24 05:23Z): an older read never withdraws the record of a newer
read. Each request goes to <directory>/withdraw-<id>.json, for PATCH repos/<repo>/check-runs/<id>, and its id goes to
standard output, one on each line. The status is 2 when an argument or a line is not one of these.

not-approved: the request that records the check run repo-pairs/import-approved with the conclusion neutral on <head>
of the pull request <number> (not_approved), for POST repos/<repo>/check-runs, in <request.json>. <why> is the reason
of <run> itself: blocking or person, the verdict of its review, refused, its review that the fresh reader refused,
screen, its screen that held <head>, or access (F3, above). <read> is the time when <run> read the pull request. The
post job of <run> makes it when no import check run
of <head> for <number> has the conclusion success, as it then has no success to withdraw (OSSV-221's architect,
2026-11-24 05:33Z), for an author whom holds_back treats as outside (2026-11-24 09:28Z). The write jobs of an item
run one at a time (the group write-<n>), and the post job of a run that read the item before <read> can come after
it. The summary names <why>, <run>, <read>, <head> and <number> in plain sentences (NOT_APPROVED). So own-record,
verdict and source read this check run as a withdrawal by <run> that counts from <read> (withdrawn_by), and that
older run records nothing. Its name, its external_id <number>:<head> and its output text, the marker line of
import-marker for <import paths>, are those of a record. The import reads only a check run with the conclusion
success, so this one approves nothing. The status is 2 when an argument is not one of these.

steering: whether a pull request changes a steering file (steering, a file under .github/), from <files.jsonl>, its
files as the API lists them on every page of pulls/<n>/files, one {filename, previous_filename} on each line: true
when the path of a file, or the path that it had before a rename, is one, else false, on standard output. The post
job approves no held run of such a head (R10). The status is 2 when a line is not such a file.

relabel: label (above) for the head <head> of the pull request <number>, for the task relabel (the job gives no
task=), with the facts that the workflow wrote of that head (relabel_facts) beside the facts and the marker lines of
the job. Each word comes from the one model of the order of the words on a head (head_words, newest_word): a word
outranks another when it is later, or at the same time when its kind has a higher rank (RANKS). The review side is the
word that outranks each other word of a verdict or a refusal: the verdict of a review comment that names <head>, or a
review that the fresh reader refused, which the line <!-- withdraw-owed <head> refused <run> <read> --> of a label
comment or an import check run of <head> for the reason refused carries; and an answer at <head> whose author said
they will make the change. A blocking finding or the verdict person of the line or of a check run gives no verdict:
its review comment never posted, so the decision withdrawn says that no comment gives the reason. The review side
gives the verdict and will-fix, the fix reviews of <head> and the count of fix reviews since the author's last own
push. A hold that names <head> (a hold comment, the line for screen, or an import check run for the reason screen)
that outranks the review side gives the state of the hold. Else a refusal that outranks the rest of the review side
gives the state refused-review. It reads the import check runs of <head> of the OSS Verify App (OSS_VERIFY_APP_ID)
for <number> for that. A review comment and a hold comment of the screen count from the time when their run read the
item, never from when they posted, a pass with no marker of that time counts at no time, and a hold with none from
when GitHub last changed it (word_time). When the workflow wrote nothing of <head> but the conflict-state line of its
label comment, the item gets no state label and the line goes. When it wrote nothing of <head>, nothing changes. A
relabel gives no word of its own, so no word of its run (GITHUB_RUN_ID) counts, such as its own withdrawal for a word
whose run is not known, which counts from when it withdrew.

answers: the answers of the author-kind table (TABLE) for <task>, one of TASKS, as <answer>=<value> lines for
$GITHUB_OUTPUT: label (set, off or unchanged), then approve, record, withdraw and retry (true or false). <outside> and
<outsider> are the trust job's outputs of those names, and <kind> is its output kind, which only a label step gives.
The author is outside when <outside> is true, and only then (outside_author). <outsider> is a GitHub login or empty,
and no answer reads it. The status is 2 when an argument is not one of these.

log: the log line of one decision of the workflow (decision_log) on standard output, in the one form of the decision log
(LOG_DECISIONS, LOG_CAUSES and LOG_FIELDS): "#<number> at <head>: decision <decision>, cause <cause>, read <read>", then
each <field> <value> in the order of LOG_FIELDS. <head> is - for an item that has none, <read> is the time when the
trust job of the run read the item, and a value that is - or empty is none. The status is 2 when a word, a field or a
value is not one of the tables'.

The standard library of Python 3 alone.
"""

import json
import os
import posixpath
import re
import subprocess
import sys
import time
from collections import namedtuple

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
    # A held pull request whose head changes a file under .github/, or 3,000 files or more, so the post job approved
    # none of its runs (R10): Sami approves them.
    "steering": False,
    # A held pull request whose head the screen passed, while the environment post held no key of the
    # OSS Verify App, so the post job approved none of its runs (R10): Sami approves them.
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
# by hand with no screen read the review comments of the head (review_verdict). Each comment there counts from its
# word_time: a review comment or a hold comment of the screen from the time when its run read the item, never from when
# it posted, and a hold with no marker of that read from when GitHub last changed it. The decision is held when a hold
# comment of the screen is newer than each review comment whose run screened the head. For a review by hand, a run with
# no screen that records no check run, the decision is hand or screened when the run of an earlier review screened the
# head and no hold comment of the screen is newer (the states screened and earlier). It is screened when review_verdict
# gives a reason to withdraw (its why:
# the newest screened review comment does not pass, one newer than it gives a blocking finding or the verdict person,
# or a label comment holds the line of OWED of the head, which that newest screened review does not outrank:
# owed_reason), and this run withdraws each check run of the head that still stands. So the state follows the verdict
# of this run, and a pass gets PASSED. Else it is hand, and so is a relabel's in the state earlier with the verdict
# pass and no such reason. A relabel withdraws, and records no check run, also in the state screened with the verdict
# pass and a line of OWED that gives a reason. Its decision is then withdrawn when no comment of BOT
# gives a reason for that line to go (line_reason): the comment of its reason did not post, and no screened review
# comment is newer than the time of the line. The label step gets a decision only from a post job that succeeded, so
# the withdrawal is done by then, and the text says so in the place of PASSED (NO_REASON). Else its decision is
# screened. Its decision is withdrawn also in the state screened with the verdict pass and no such line, when a
# withdrawal among the import check runs of the head stands: the one of the newest read, by the time that each check
# run names, when no success names a newer read and no screened pass of the head is newer (withdrawal_stands). A
# withdrawal that succeeded is itself the record of its reason, and the comment of that reason may not have posted.
# A line that the newest screened review outranks gives no reason (OSSV-221's architect, 2026-11-25 01:13Z, G1). With
# such a line and no withdrawal that stands, a relabel in the state screened with the verdict pass records no check
# run while the line stands, and withdraws none for it: its decision is hand, and the step OWE of its comment job
# takes the line out (owe).
# The line of OWED gives only the reason, never the state: with no screened review comment of the head, the decision
# is screen. For the decision hand, the label step counts an import check run of the head that still stands, for the
# value of the variable now, as recorded (the post job's standing), so its state is import or decide as that check run
# gives. A run on the route screen whose own screen and review passed the head records nothing when another run gave a
# word on the head that counts from a time at or after its trust job read the item (own_record): held for a hold
# comment of the screen, withdrawn for a withdrawal that stands, and newer for a review comment that gives a blocking
# finding or the verdict person. A withdraw-owed line of another run gives held for screen, and newer for blocking,
# person or refused. Each of these three also goes to the post job's output gave_way, and the comment job of such a
# run posts nothing on the item: no review, no label and no label comment. Empty when the job gave none.
# The comment job's label step gives one more, gone, in the place of the post job's decision: that job recorded the
# check run, or one stood for its decision hand, and when the label step reads the check runs of the head again, none
# with the conclusion success and the marker line of the value stands (GONE).
# Each of these words is also a decision of the decision log, with its meaning (LOG_DECISIONS).
DECISIONS = ("", "record", "screen", "verdict", "steering", "outside", "unread", "person", "markdown", "moved",
             "writer", "held", "hand", "screened", "withdrawn", "newer", "gone")

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
# The decision withdrawn: a run found a reason to withdraw the check run of the head, this relabel or an earlier run (a
# line of OWED, or a withdrawal that stands), and no comment gives that reason; the head can also have had no such
# check run. The run whose review passed can be the earlier or the later of the two, so the text gives no order. It
# says so in the place of PASSED and of the steps of the import. The next step is a review of the head by hand
# (REVIEW_AGAIN), whose comment gives a verdict of the head.
NO_REASON = ("The automated review passed this pull request. A run of the workflow found a reason to withdraw the "
             "check `repo-pairs/import-approved` from its head commit. No comment on this pull request gives that "
             "reason. So no such check approves this head commit for the import.")
REVIEW_AGAIN = "Sami starts the automated review of the head commit again, by hand."
# The decision gone of the label step: the screen and the review passed the head, the post job recorded the check run or
# found one that stands, and after that a run of the workflow withdrew it. The comment that gives the reason of that run
# can have posted already, so the text does not say that no comment gives it (NO_REASON). It says that a run withdrew
# the check, in the place of PASSED and of the steps of the import. The next step is a review of the head by hand
# (REVIEW_AGAIN), as for withdrawn.
GONE = ("The automated screen and the automated review passed this pull request. After that, a run of the workflow "
        "withdrew the check `repo-pairs/import-approved` from its head commit. So no such check approves this head "
        "commit for the import.")
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
    # A held pull request whose head changes a file under .github/, or that changes 3,000 files or more (R10): GitHub
    # lists at most 3,000 files of a pull request, so the workflow counts such a pull request as one that changes a
    # file under .github/. The post job approved none of its runs. Its next step names Sami, a person at Theorem with
    # write access, who approves them on GitHub, and the label comment records the head (steering_line).
    "steering": (
        THEOREM, "Sami, a person at Theorem with write access, approves the runs of this pull request on GitHub.",
        "The workflow does not approve the runs of this pull request, because it changes a file under `.github/` or "
        "it changes 3,000 files or more. GitHub lists at most 3,000 files of a pull request. So the workflow counts "
        "a pull request of 3,000 files or more as one that changes a file under `.github/`. You do not need to do "
        "anything."),
    # A held pull request whose head the screen passed, while the environment post held no key of the
    # OSS Verify App (R10, until the LPS move of dispatch://OSSV-321): the post job approved none of its runs. Its
    # next step names Sami, as for the state steering, and the label comment records the head (no_key_line).
    "no-key": (
        THEOREM, "Sami, a person at Theorem with write access, approves the runs of this pull request on GitHub.",
        "The workflow cannot approve the runs of a pull request in this repository yet. You do not need to do "
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
# A time as GitHub gives it in UTC: 2026-11-23T01:47:00Z.
TIME = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z")
# The marker lines of other kinds that a label comment keeps: the import's paths that a decision on a head read
# (R12), the stored draft of an issue's reply, the approved reply that posted, the head that a catch-up closed and
# reopened the pull request at (D16 (a): once for each head), the head whose runs the post job did not approve,
# because it changes a file under .github/ or 3,000 files or more, or because the environment post held no key of the
# OSS Verify App (R10: the rescreen pass starts no approval of it again), and the withdrawal of the import check runs
# of a head that a run owes (OWED).
KEPT = re.compile(r"<!-- (repo-pairs-import-paths) [0-9a-f]{40}: .* -->|<!-- (issue-draft) [0-9]+-[0-9]+ -->"
                  r"|<!-- (issue-reply-posted) [0-9]+ -->|<!-- (review-catchup) [0-9a-f]{40} -->"
                  r"|<!-- (review-steering) [0-9a-f]{40} -->|<!-- (review-no-key) [0-9a-f]{40} -->"
                  r"|<!-- (withdraw-owed) [0-9a-f]{40} (?:blocking|person|refused|screen) [1-9][0-9]*"
                  rf" {TIME.pattern} -->")
# The marker line of a withdrawal of the import check runs of a head (R12) that a run found a reason for and did not
# finish (GitHub refused it, or the job failed or stopped before it), or whose reason no comment of the item gives yet.
# The head, why (WITHDRAWN), a run (OSSV-221's architect, 2026-11-22 16:06Z and 17:27Z): the run whose own comment
# gives why, and the read of that run, the time when it read the item, which is the time of the line (2026-11-25
# 01:30Z). The hold job's line of its own screen, and the comment job's line of its own review's verdict, name their
# own run and its trust job's started. Any other writer, as a relabel whose withdrawal GitHub refused, keeps the run and
# the read of the line of that head and why that stands, or names the run of the comment that gives why and the time of
# that comment (word_time), and its own run and read only when no comment names a run (owed_run). That comment must
# have a time of TIME: else owed_run gives an error, and no line goes without a read. Each job writes it ahead,
# before its first step that can fail or that withdraws: the post job through
# its output owed, which the comment job or the hold job of its run records; the hold job for a screen that held the
# head in a review, a rescreen or an approval of its run; and the comment job for a blocking finding or the verdict
# person of its run's review, when the post job finished the withdrawal before that review posted. It goes into a
# label comment that the item has: no record of it makes one (owe). An item with no label comment gets the line from
# the label step of that job, but not when the job finished the withdrawal and posts the comment of the reason itself.
# Its label call writes a label comment with the line in any state (apply). The comment job's label step also writes
# the line when it stops for a hold made after the run started (mark). When the label step stops before its label call
# for any other cause, the line is not recorded. A relabel and a review by hand of that head withdraw for why while
# the line stands and the newest screened review of the head does not outrank it, whatever the newest review says else
# (review_verdict, owed_reason: the line is a word from its read). The line goes only after a run finished the
# withdrawal of that head (it found no import check run of the head with conclusion success, or withdrew each one, or
# a newer screened review outranks the line), and only while a comment of BOT gives a reason for it (line_reason): the
# comment of the line's run that gives why, or a review of the head newer than the time of the line. Until then, each
# relabel records nothing (owe). The why refused is the reason of a review that the fresh reader refused (OSSV-221's
# architect, 2026-11-25 10:21Z). That review never posts, so no comment gives refused. The comment job's line of its
# own refused review names its own run and read. Any other writer keeps the run and the read of the refused line of
# that head that stands. With no such line, owed_run gives the writer's own run and read. owe takes the line out only
# when a later review gives the reason (line_reason). A line of that head with a later read also takes its place
# (owed_keeps).
# Each head has a line of its own (marker_kind). A line takes the place of the line of its head only when that line
# does not outrank it as a word on the head (owed_keeps; OSSV-221's architect, 2026-11-25 07:24Z), for each writer:
# owe, also for the line of its own run, mark, and the label call (apply). So no older read's line takes the place of
# a newer read's line whose comment never posted.
OWED = re.compile(rf"<!-- withdraw-owed ([0-9a-f]{{40}}) (blocking|person|refused|screen) ([1-9][0-9]*)"
                  rf" ({TIME.pattern}) -->")

# --- the decision log -----------------------------------------------------------------------------------------------
# The one short fixed form of each log line, and of each line of a job summary, that states a decision of the workflow
# (OSSV-221's architect, 2026-11-24 14:36Z). Only the readers of the workflow's runs see it. A comment that an outside
# author reads, and the title and the summary of a check run, keep their plain sentences. decision_log builds the line,
# and each step that states a decision calls it through the command log, so that the words and their order are the
# same everywhere:
#     #<number> at <head>: decision <decision>, cause <cause>, read <time>[, <name> <value>]...
# An item that has no head (an issue) gets no " at <head>". read is the time when the trust job of the run read the
# item. The fields come after read, in the order of LOG_FIELDS, and only where the decision needs one. A value that
# the step does not know is none. Each word of the three tables has one meaning. Each sentence of a meaning has 25 words
# or fewer. A word outranks another word when its time is later, or when the times are the same and its kind comes
# later in RANKS (word_key, outranks).
LOG_DECISIONS = {
    # The decide step of the post job: the decisions of DECISIONS. Where a decision says that this run records no
    # import check run with the conclusion success, the job can still record a check run with the conclusion neutral
    # (not-approved).
    "record": ("This run records the import check run of the head, while the GitHub environment named post holds the "
               "key of the OSS Verify App."),
    "screen": ("No screen passed the head in the run of the review that this decision rests on, or the head has no "
               "review. So this run records no import check run with the conclusion success."),
    "verdict": ("The verdict of the review is neither pass nor person, so this run records no import check run with "
                "the conclusion success."),
    "steering": ("The pull request changes a file under .github/, so this run records no import check run with the "
                 "conclusion success."),
    "outside": ("The pull request changes a path that the import does not take, so this run records no import check "
                "run with the conclusion success."),
    "unread": ("The step did not read each changed file, so this run records no import check run with the conclusion "
               "success."),
    "person": ("The verdict is person, so Sami decides, and this run records no import check run with the conclusion "
               "success."),
    "markdown": ("The soundness hold lasts and a changed path is not a Markdown file, so this run records no import "
                 "check run with the conclusion success."),
    "moved": ("The pull request has another head now, so this run records no import check run with the conclusion "
              "success for this head."),
    "writer": ("The author is not known to be an outside author, so this run records no import check run with the "
               "conclusion success."),
    "held": ("In a relabel or a review by hand, a hold of the screen that names the head outranks each screened review "
             "of the head. Such a hold is a hold comment of the screen or the withdraw-owed line for screen. In a run "
             "on the route screen, such a hold of another run outranks the pass of this run. For an outside author, a "
             "relabel whose newest review is a screened pass also counts an import check run for screen as such a "
             "hold. So this run records no import check run with the conclusion success."),
    "hand": ("This run records no import check run with the conclusion success. No word that this step reads gives a "
             "reason to withdraw one, except a word that the newest screened review outranks. A later step can still "
             "withdraw for the newest word that withdraws, unless a screened review that passes outranks it. That word "
             "is a review comment, the withdraw-owed line or a hold of the screen. An import check run is that word "
             "only while a success that it withdraws stands. In a review by hand, the verdict of this run's own "
             "review can also withdraw."),
    "screened": ("This run records no import check run with the conclusion success. A later step withdraws each import "
                 "check run with the conclusion success whose run read the item at or before a time. The withdraw or "
                 "keep line of the step that finds those check runs names that time in the field from. The later step "
                 "also withdraws each one that names no read, and each one when from is none. Both steps run only "
                 "while the GitHub environment named post holds the key of the OSS Verify App."),
    "withdrawn": ("A withdrawal of the import check run stands, or the label comment holds a withdraw-owed line whose "
                  "reason no workflow comment gives (cause unposted). So this run records no import check run with "
                  "the conclusion success."),
    "newer": ("A run that read the item at or after this run gave the head a blocking finding, the verdict person or a "
              "refused review. So this run records no import check run with the conclusion success."),
    # The label step: gone, in the place of the post job's decision, and the hold that keeps the labels.
    "gone": ("No import check run of the head with the conclusion success and the marker of the import's paths "
             "stands now. So the label comment does not say that the workflow recorded the check."),
    "stay": ("The label step leaves the state label and the text of the label comment as they are. When the item has "
             "no label comment and this run owes a withdrawal, the label step posts a label comment with the "
             "withdraw-owed line. That label comment has the state working or after-hold."),
    # The step that finds the import check runs to withdraw, and the step that records the check run of not-approved.
    "withdraw": "A later step of this job withdraws the import check runs that check names.",
    "keep": ("This job leaves the import check runs that check names: the run that recorded each one read the item "
             "after the time in from."),
    "clear": "This job withdraws no import check run of the head.",
    "not-approved": ("This job records the check run that says that the head is not approved for the import. The field "
                     "check names that check run in the line of the step that records it."),
    # The step of the comment job and of the hold job that gives way to a newer word.
    "skip": ("The later steps of this run post no comment and no label comment, and add or remove no label. A "
             "withdraw-owed line that an earlier step wrote stays."),
}
LOG_CAUSES = {
    "blocking": ("A review of the head, the withdraw-owed line of the label comment, or an import check run of the "
                 "head gives a blocking finding."),
    "person": ("A review of the head, the withdraw-owed line of the label comment, or an import check run of the head "
               "gives the verdict person."),
    "refused": ("The fresh reader refused a review of the head, whatever verdict the model gave. The withdraw-owed "
                "line of the label comment, or an import check run of the head, can give that refusal."),
    "pass": "A review of the head gives the verdict pass.",
    "verdict": ("A review of the head gives a blocking finding or the verdict person, or the fresh reader refused it. "
                "The output gave_way of the post job does not say which. The post job's log line of the decision newer "
                "says which."),
    "screen": "A screen held the head.",
    "hold": ("A hold comment of the workflow, or the withdraw-owed line for screen, counts from a time at or after the "
             "read of this run."),
    "access": "GitHub did not say whether the author has write access.",
    "writer": "The author has write access, or is an App that the workflow trusts.",
    "neutral": ("When the post job read the import check runs, one of them was a withdrawal: a check run with the "
                "conclusion neutral. No success and no screened pass outranked it."),
    "missing": ("No import check run of the head with the conclusion success and the marker of the import's paths "
                "stands."),
    "unposted": "The label comment holds a withdraw-owed line, and no comment of the workflow gives its reason.",
    "outranked": ("The run of a screened review read the item after the run that the withdraw-owed line names. That "
                  "review outranks the line, so the line gives no reason to withdraw an import check run."),
    "earlier": "A screen passed the head in the run of an earlier review.",
    "standing": "An import check run of the head with the conclusion success stands.",
    "head": "The head of the pull request is not the head that this run read.",
    "rule": ("The decide step of the post job applies the rules of R12 (import_decision). They read the verdict, the "
             "soundness hold, the import's paths, the changed files that the step read, and whether a screen passed "
             "the head."),
    "none": "This run has no reason to withdraw an import check run.",
}
# The fields after read, in this order: the pattern of the value, and what it says. The check run ids of check are
# separated by commas.
LOG_FIELDS = {
    "run": (re.compile(r"[1-9][0-9]*"),
            "The id of the run that gave the word that decides, none when its comment names no run. The withdraw and "
            "keep lines have no field run for this run's own word, or for a word whose run this run does not know. "
            "The skip line of the comment job has no field run when the post job of this run gave way."),
    "check": (re.compile(r"[1-9][0-9]*(?:,[1-9][0-9]*)*"), "The ids of the import check runs that the decision names."),
    "from": (TIME, "The time from which that word counts, none when it names no time."),
    "files": (re.compile(r"0|[1-9][0-9]*"), "The number of changed files that the step read."),
    "changed": (re.compile(r"0|[1-9][0-9]*"), "The number of files that the pull request changes."),
    "now": (HEAD, "The head that the pull request has now."),
}


def decision_log(number, head, decision, cause, read, fields=None):
    """The log line of a decision of the workflow, in the form of the section above: item number at head ("" or "-" for
    an item with no head), a decision of LOG_DECISIONS, its cause of LOG_CAUSES, the time read, and each field of fields
    ({name: value}, the names of LOG_FIELDS), in the order of LOG_FIELDS. "" and "-" mean none, for read and each value.
    The line has no line break and no period at its end. A ValueError for a word, a name or a value that the tables and
    their patterns do not give: no step can write a line that breaks the form."""
    fields = fields or {}

    def known(pattern, value):
        value = "none" if value in ("", "-") else value
        if value != "none" and not pattern.fullmatch(value):
            raise ValueError(f"not a value of the decision log: {value!r}")
        return value

    if not NUMBER.fullmatch(number) or (head not in ("", "-") and not HEAD.fullmatch(head)):
        raise ValueError(f"not a pull request number and a head commit: {number!r} {head!r}")
    if decision not in LOG_DECISIONS or cause not in LOG_CAUSES or set(fields) - set(LOG_FIELDS):
        raise ValueError(
            f"not a decision, a cause and fields of the decision log: {decision!r} {cause!r} {sorted(fields)}")
    parts = [f"decision {decision}", f"cause {cause}", f"read {known(TIME, read)}"]
    parts += [f"{name} {known(pattern, fields[name])}" for name, (pattern, _) in LOG_FIELDS.items() if name in fields]
    return f"#{number}{'' if head in ('', '-') else f' at {head}'}: {', '.join(parts)}"


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
    standing): one that stands gives the state import while the variable is set. In the state decide, the decision
    withdrawn gives NO_REASON in the place of PASSED and REVIEW_AGAIN in the place of the steps of the import, whatever
    the variable, and the decision gone of the label step gives GONE in the place of NO_REASON."""
    if state not in ("decide", "person"):
        raise ValueError(f"no step of the import for the state {state!r}")
    if decision not in DECISIONS:
        raise ValueError(f"not a decision of the post job: {decision!r}")
    live = value is not None
    steps = IMPORT_STEPS if live else MERGE_STEPS
    unread = f"{UNREAD} " if decision == "unread" else ""
    passed = {"screen": UNSCREENED, "held": SCREEN_HELD_AFTER}.get(decision, PASSED)
    if state == "decide" and decision in ("withdrawn", "gone"):
        return REVIEW_AGAIN, f"{NO_REASON if decision == 'withdrawn' else GONE} You do not need to do anything."
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
    """The marker line of KEPT that records head as a head that changes a file under .github/, or 3,000 files or more
    (the state steering): the post job approved none of its runs, and the rescreen pass starts no approval of it
    again."""
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


def apply(number, state, markers=(), head="", imports=None, comments=None, labelled=True):
    """Gives the item number the state label of state, takes the other one off, and writes its label comment
    (label_comment, with imports). comments are the item's comments of BOT as the API lists them (read_comments), when
    the caller read them already, and this takes its label comments from them; else this reads only its label
    comments (read_labels). When labelled is False (the label answer off of the author-kind table), the item gets no
    state label and loses each one that it has, but its label comment is the state's all the same, with the marker of
    the state's label. An item with no label comment gets one when state has a state label, or when a line of OWED is
    among markers, so that a label step records that line in any state. Else it gets none. A line of OWED among markers
    does not take the place of the line of its head that outranks it (owed_keeps; OSSV-221's architect, 2026-11-25
    07:24Z): that line stays, and the log says so."""
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
    labels = read_labels(number) if comments is None else label_list(comments)
    old = labels[-1] if labels else None
    kept = [owed_keeps(number, old["body"], m) if old else "" for m in markers]
    for said in filter(None, kept):
        print(said)
    markers = [m for m, said in zip(markers, kept) if not said]
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


def read_comments(number):
    """The comments of BOT on the item number as the API lists them, each {id, user: {login}, body, updated_at}, in the
    order that GitHub lists them."""
    return gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{number}/comments", "--jq",
                      f".[] | select(.user.login == {json.dumps(BOT)})"
                      " | {id, user: {login: .user.login}, body, updated_at} | @json")


def label_list(comments):
    """The label comments among comments, the item's comments of BOT as the API lists them, each {id, body}, in their
    order (read_labels)."""
    return [{"id": c.get("id"), "body": c["body"]} for c in comments
            if isinstance(c.get("body"), str) and c["body"].startswith(FIRST)]


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


def mark(number, line, make=True, state="working", labels=None):
    """Records line, a marker line of KEPT, in the label comment of the item number (with_marker), and writes nothing
    else: the state label and the text of the label comment stay as they are. An item with no label comment gets one
    of state, with line, when make is True. state is working unless the caller gives another. It must be a state with
    no state label, as mark writes no state label: a ValueError for any other. The comment job's label step gives
    working or after-hold, by the hold that stopped it. When make is False (owe: a line of OWED), such an item gets
    nothing, and the result is False. Else the result is True. A line of OWED does not take the place of the line of
    its head that outranks it (owed_keeps; OSSV-221's architect, 2026-11-25 07:24Z): that line stays, and the log says
    so. labels are the item's label comments of BOT, each {id, body}, when the caller read them already; else this
    reads them."""
    marker_kind(line)
    if state not in STATES or label_of(state) is not None:
        raise ValueError(f"mark makes a label comment only in a state with no state label, not {state!r}")
    if labels is None:
        labels = read_labels(number)
    old = labels[-1] if labels else None
    if old is None and not make:
        return False
    if old is None:
        write_label(number, None, label_comment(state, "", [line]))
        print(f"#{number}: it had no label comment, so this step posted one, with {line}.")
        return True
    kept = owed_keeps(number, old["body"], line)
    if kept:
        print(kept)
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


def unmark(number, kind, what, labels=None):
    """Takes the marker line of KEPT of kind (marker_kind) out of the label comment of the item number
    (without_marker), and writes nothing else: the state label and the text of the label comment stay as they are.
    Nothing is written when no label comment holds such a line. what names what the line records, for the log. labels
    are the item's label comments of BOT, each {id, body}, when the caller read them already; else this reads them."""
    if labels is None:
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
# form, and a withdrawal runs for every author. The post job's check run that says that the head is not approved for
# the import (not_approved) has that form too (2026-11-24 09:28Z): a failed read of the author's access never leaves
# an older pass standing under the verdict or the hold of a run.
#
# - label: set gives the item the state label of its state. off takes each state label off, and the label comment is
#   the state's all the same. unchanged writes nothing of the state: no state label goes on or off, and the label
#   comment stays as it is, but for one case (OSSV-221's architect, 2026-11-24 16:19Z, F5). After a run of such an
#   author finished a withdrawal of a head, a label comment that says that the workflow recorded the check on that
#   head becomes the one of the state decide with the decision gone, when no such record stands (owe, unrecord).
#   review-held belongs to a hold, and no answer of this table names it.
# - approve: the post job approves the held runs of the head when the screen of this run passed the head (R10).
# - record: the post job decides on the import check run of the head, and records it when the rules of R12 hold.
# - withdraw: the post job withdraws the import check runs of the head when this run gives a reason (R12): a review of
#   the head with a blocking finding or the verdict person, a screen that held the head, or a relabel or a review by
#   hand with no screen that finds such a review or a later hold of the screen, for every author. A run whose author's
#   write access GitHub did not say gives the reason access for its pass too (OSSV-221's architect, 2026-11-24 14:29Z,
#   F3): whatever its verdict, it is no approval.
# - retry: the error of a withdrawal that GitHub refused, or that could not be read, says that the rescreen pass tries
#   it again, but only when the name of the run gives the head too (review.yml): the pass tries no other run again
#   (held.sh, take and due_retry). The pass tries no App write of the item of another author again (held.sh, consider
#   and access_of). So for such an author, and for a run whose name gives no head, the error says "Re-run this run."
#   instead.
#
# The tasks are the trust job's (the top of review.yml), and hold is the hold job. In the same run, the post job
# withdraws the import check runs of a head that the screen held, by the row of the task. An answer has no post job:
# for an answer whose screen held the head of a pull request, the hold job makes that withdrawal itself, with the post
# job's steps (OSSV-221's architect, 2026-11-24 14:29Z, F2). The answer's row withdraw stays false: it is the answer of
# the post job, which an answer does not run.
# The hold job records the line of OWED of that withdrawal with the task of the run, also when the post job finished
# it: the line stays until the hold comment of its run for the head stands, or a review of the head that is newer than
# the time of the line (owe, line_reason).
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


def set_state(number, run, facts, markers=(), head="", comments=None):
    """Gives the item number the state that facts give (label_state), as the label answer of the author-kind table for
    run says (answers, with RUN): set, off (apply with comments), or unchanged, which writes nothing and gives a notice.
    That notice names each line of OWED among markers, which the workflow then does not record: the step gives such a
    line only for an item with no label comment (owe). label_state's outsider is outside_author of the trust job's
    outside. For an outside pull request, the label comment names the steps of R12 for the import, and holds the marker
    line of R12 for head when head is given (import_marker). The label comment is made once before any write, so that a
    marker or a head that it refuses changes nothing on GitHub."""
    label = answers(run["task"], run["outside"], run["outsider"], run["author"])["label"]
    if label == "unchanged":
        dropped = "".join(f" The workflow does not record {m}." for m in markers if OWED.fullmatch(m))
        print(f"::notice::#{number}: GitHub did not say whether its author has write access. So this step does not "
              f"change its state label, and it does not write or change a label comment.{dropped}")
        return
    outsider = outside_author(run["outside"])
    state = label_state(outsider=outsider, **facts)
    imports = None
    if facts.get("kind") == "pr" and outsider:
        imports = (facts.get("import_paths"), facts.get("decision", ""))
        if head:
            markers = [*markers, import_marker(head, imports[0])]
    label_comment(state, "", markers, head, imports)
    apply(number, state, markers, head, imports, comments, labelled=label == "set")


# The marker line of R12 (import_marker) in a label comment: the head, and the value of REPO_PAIRS_IMPORT_PATHS as JSON.
IMPORT_LINE = re.compile(r"<!-- repo-pairs-import-paths ([0-9a-f]{40}): (.*) -->")


def says_recorded(body):
    """True when body, a label comment of BOT, says that the workflow recorded the import check run: its next step and
    its text are those of the state import."""
    _label, step, text = STATES["import"]
    return body.startswith(f"{FIRST}\n**Next step:** {step}\n\n{text}")


def record_line(body, head):
    """(line, value) when body, a label comment of BOT, says that the workflow recorded the import check run on head
    (says_recorded), and it holds the marker line of R12 of head (import_marker), line, with value, the text of
    REPO_PAIRS_IMPORT_PATHS (None for null) on which the record rested. Else None."""
    if not says_recorded(body):
        return None
    for line in body.split("\n"):
        m = IMPORT_LINE.fullmatch(line)
        if m and m.group(1) == head:
            value = loads(m.group(2))
            return (line, value) if value is None or isinstance(value, str) else None
    return None


def import_checks(number, head):
    """The import check runs of head for the pull request number, as the API lists them (commits/<head>/check-runs),
    of any conclusion (filter=all), as the comment job's label step reads them. Each one has the name CHECK, is of the
    OSS Verify App (OSS_VERIFY_APP_ID), and is for this pull request (external_id <number>:<head>). A ValueError when
    OSS_VERIFY_APP_ID is not a whole number greater than 0 (NUMBER), and GhError when GitHub does not give them."""
    app = os.environ.get("OSS_VERIFY_APP_ID", "")
    if not NUMBER.fullmatch(app):
        raise ValueError(f"not the id of the OSS Verify App: {app!r}")
    checks = gh_objects("--method", "GET", "--paginate", f"repos/{os.environ['REPO']}/commits/{head}/check-runs",
                        "-f", f"check_name={CHECK}", "-f", "filter=all", "-F", "per_page=100",
                        "--jq", ".check_runs[] | @json")

    def ours(c):
        return (isinstance(c, dict) and c.get("name") == CHECK and c.get("head_sha") == head
                and str((c.get("app") if isinstance(c.get("app"), dict) else {}).get("id")) == app
                and c.get("external_id") == f"{number}:{head}")

    return [c for c in checks if ours(c)]


def record_stands(checks, line):
    """True when one of checks, the import check runs of a head, has the conclusion success and holds line, the marker
    line of R12 of its label comment (import_marker), in its output text."""
    def record(c):
        output = c.get("output") if isinstance(c.get("output"), dict) else {}
        return c.get("conclusion") == "success" and line in str(output.get("text") or "").split("\n")

    return any(record(c) for c in checks)


def unrecord(number, head):
    """For an author whose write access GitHub did not give, after a run of that author finished the withdrawal of the
    import check runs of head (owe; OSSV-221's architect, 2026-11-24 16:19Z, F5). When the label comment of the item
    number says that the workflow recorded the check on head (record_line), it must not say so once no such record
    stands. So this reads the import check runs of head again (filter=all, as the comment job's label step reads
    them). When none of the OSS Verify App (OSS_VERIFY_APP_ID) for this pull request (external_id <number>:<head>) has
    the conclusion success and that marker line, this writes the label comment of the state decide with the decision
    gone (GONE) in its place. It adds and takes off no state label, as the label answer unchanged of the author-kind
    table says. Else it writes nothing. The result is the item's label comments of BOT, each {id, body}, as they are
    after that write, so that the caller does not read them again; None when it wrote nothing."""
    labels = read_labels(number)
    old = labels[-1] if labels else None
    found = record_line(old["body"], head) if old else None
    if found is None:
        return None
    line, value = found
    if record_stands(import_checks(number, head), line):
        print(f"#{number}: its label comment says that the workflow recorded the check `{CHECK}` on {head}, and "
              "that check run stands.")
        return None
    body = label_comment("decide", old["body"], (), "", (value, "gone"))
    write_label(number, old, body)
    print(f"#{number}: its label comment said that the workflow recorded the check `{CHECK}` on {head}. No such "
          "check run with the conclusion success stands now: a run withdrew it. So this step wrote the label comment, "
          "which says that a run withdrew the check. GitHub did not say whether the author has write access, so this "
          "step did not add or remove a state label.")
    return [*labels[:-1], dict(old, body=body)]


def unclaim(number):
    """The last step of a comment job or a hold job that failed or was cancelled: whichever step failed, the label
    comment of the item number never keeps a claim that is not true (OSSV-613's architect, 2026-11-25 23:02Z, G2). The
    claim is the text that says that the workflow recorded the check on a head (says_recorded), with the marker line of
    R12 of that head (IMPORT_LINE): the head is the one of that marker line, for any author. Only the newest label
    comment counts. This reads the import check runs of that head (import_checks). When one with the conclusion success
    and that marker line stands, the claim is true, and this writes nothing. Else, and also when GitHub does not give
    the check runs, this writes the label comment of the state working in its place (the marker lines of KEPT stay).
    That state has no state label, so this adds and takes off no state label. A label comment with no such claim stays
    as it is. GhError when GitHub does not give the label comments or does not take the write: nothing more can be
    done here, and the re-run of the failed jobs of the run tries again (held.sh due_rerun)."""
    labels = read_labels(number)
    old = labels[-1] if labels else None
    named = next((m for m in map(IMPORT_LINE.fullmatch, old["body"].split("\n")) if m), None) if old else None
    if named is None or not says_recorded(old["body"]):
        print(f"#{number}: its label comment does not say that the workflow recorded the check `{CHECK}`, so this "
              "step changes nothing.")
        return
    head = named.group(1)
    try:
        if record_stands(import_checks(number, head), named.group(0)):
            print(f"#{number}: its label comment says that the workflow recorded the check `{CHECK}` on {head}, and "
                  "that check run stands.")
            return
        why = "No such check run with the conclusion success stands now: a run withdrew it."
    except (GhError, ValueError) as e:
        why = (f"GitHub did not give the check runs of {head} ({' '.join(str(e).split())}), so this step cannot show "
               "that such a check run stands.")
    write_label(number, old, label_comment("working", old["body"]))
    print(f"#{number}: its label comment said that the workflow recorded the check `{CHECK}` on {head}. {why} So this "
          "step wrote the label comment of the state working, which does not say that the workflow recorded the "
          "check. This step did not add or remove a state label.")


def owe(number, run, owed="", withdrawn="", own=False):
    """Records in the label comment of the item number the withdrawal of the import check runs of a head that a run
    owes (OWED). owed, "<head> <why> <run> <read>", is the post job's output owed, "<head> <why>" of a withdrawal that
    it found a reason for and did not finish (or "<head> screen" from the hold job, for a screen that held the head in
    a review, a rescreen or an approval of its run), <run>, the id of the run that writes the line, and <read>, the
    time when that run read the item (its trust job's started). It gives the line
    <!-- withdraw-owed <head> <why> <run> <read> --> (mark), in a label comment that the item has: it never makes one.
    own is True when the line names <run> and <read> of owed. The hold job gives it for the line of its own screen.
    The comment job gives it for the line of its own review, whether that review gives the verdict or the fresh reader
    refused it. Else the line names the run of the comment that gives why, and the read of that run (owed_run;
    OSSV-221's architect, 2026-11-22 17:27Z and 2026-11-25 01:30Z), so that a refused withdrawal of a relabel never
    takes the place of that run and its read. When the item has no label comment, it writes nothing, says so, and the
    result is the line: the step gives it to the label step of its job. withdrawn alone, a head whose withdrawal the
    job finished (or the head of a line that a newer screened review outranks, owed_reason, for which a relabel
    withdraws nothing), takes the line of that head out (unmark), but only while a comment of BOT gives a reason for it
    (line_reason; OSSV-221's architect, 2026-11-22 16:06Z): the comment of the line's run that gives its why, or a
    review comment of the head whose run read the item after the time of the line, its read (2026-11-25 01:30Z). That
    review comment must be screened when the rule holds back for the author of run (holds_back). Else the line stays,
    and each later relabel records nothing; it withdraws for the line while the line gives a reason. owed and withdrawn
    of one head are a withdrawal that the job finished before a later step of the job posts the comment of its reason
    (the review of the comment job, or the hold comment of the hold job): the line goes in as for owed alone, so that
    it stands when that step fails. An item with no label comment then gets nothing, and the result is "", so that no
    label step gets the line: that comment gives the reason once it posts. owed and withdrawn of two heads are a
    ValueError. The state label and the text of the label comment stay as they are. As for set_state, the label answer
    of the author-kind table for run unchanged takes no line out, and gives a notice, but for owed: the line of a
    withdrawal that a run owes goes in for every author, as the post job withdraws for every author (OSSV-221's
    architect, 2026-11-23 01:47Z). For that answer, withdrawn also rewrites a label comment that says that the workflow
    recorded the check on that head, when no such record stands (unrecord, first; F5): the label step of such a run
    changes no label comment. Else the result is "". Also with own, the line of owed does not take the place of the
    line of its head that outranks it as a word on the head (mark, owed_keeps; OSSV-221's architect, 2026-11-25
    07:24Z): that line stays, and the log says so."""
    line = f"<!-- withdraw-owed {owed} -->" if owed else ""
    m = OWED.fullmatch(line) if owed else None
    if owed and not m:
        raise ValueError(f"not a head commit, a reason to withdraw, a run id and a read time: {owed!r}")
    head, why = (m.group(1), m.group(2)) if m else ("", "")
    if withdrawn and not HEAD.fullmatch(withdrawn):
        raise ValueError(f"not a head commit: {withdrawn!r}")
    if owed and withdrawn and head != withdrawn:
        raise ValueError(f"owed and withdrawn name two heads: {owed!r} {withdrawn!r}")
    unchanged = bool(withdrawn) and (
        answers(run["task"], run["outside"], run["outsider"], run["author"])["label"] == "unchanged")
    # The label comments as unrecord left them, when it wrote one: the later writes of this command start from them.
    rewritten = unrecord(number, withdrawn) if unchanged else None
    if unchanged and not owed:
        print(f"::notice::#{number}: GitHub did not say whether its author has write access, so this step removes no "
              f"withdraw-owed line of {withdrawn} from its label comment.")
        return ""
    comments = read_comments(number) if owed or withdrawn else []
    labels = rewritten or label_list(comments)
    if withdrawn and not owed:
        why, wrote, read = owed_line(comments, withdrawn)
        screened = holds_back(run["outside"], run["author"])
        posted, since = line_reason(comments, withdrawn, why, wrote, read, screened) if why else (True, "")
        if not posted:
            kept = owed_marker(withdrawn, why, wrote, read)
            if why == "screen":
                said = f"No hold comment of the screen of run {wrote} names {withdrawn}."
            elif why == "refused":
                said = (f"No comment of run {wrote} gives {withdrawn} the reason refused: a review that the fresh "
                        "reader refuses posts no comment.")
            else:
                said = f"No review comment of run {wrote} gives {withdrawn} the verdict {why}."
            newer = (f"No {'screened ' if screened else ''}review comment of {withdrawn} comes from a run that read "
                     f"#{number} after {since}. That is the time of the line, when run {wrote} read #{number}.")
            print(f"#{number}: its label comment keeps {kept}. {said} {newer}")
            return ""
        unmark(number, f"withdraw-owed {withdrawn}", f"owed withdrawal of the import check runs of {withdrawn}", labels)
        return ""
    if owed and not own:
        line = owed_marker(head, why, *owed_run(comments, head, why, m.group(3), m.group(4)))
    if line and not mark(number, line, make=False, labels=labels):
        if withdrawn:
            comment = (f"the hold comment of the screen that held {head}" if why == "screen"
                       else f"the review comment that gives {head} the verdict {why}")
            print(f"#{number}: it has no label comment, and this command writes none. A later step of this job posts "
                  f"{comment}. If that step fails or posts no such comment, the workflow does not record {line}.")
            return ""
        print(f"#{number}: it has no label comment, and this command writes none. If a later command of this job "
              f"writes a label comment, that comment gets {line}, unless a line of {head} that outranks it stands "
              f"there. If no later command writes one, the workflow does not record {line}.")
        return line
    return ""


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
# The last two markers of that header: the time when the trust job of its run decided it, and the id of the run that
# wrote the comment, <!-- review-run <run> -->. A review that replaces the comment in place writes its own run there.
REVIEW_RUN = re.compile(r"<!-- review-read [^\n]* -->\n<!-- review-run ([1-9][0-9]*) -->(?:\n|$)")
# The same two markers when the first one holds a time as GitHub gives it: the time when the run of the review read the
# item, by which the review counts as a word on its head (word_time).
REVIEW_READ = re.compile(rf"<!-- review-read ({TIME.pattern}) -->\n<!-- review-run [1-9][0-9]* -->(?:\n|$)")


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


def check_run(number, head, value, hold, run="", read=""):
    """The body of the request that records the import check run on head of pull request number (POST
    repos/<repo>/check-runs), when import_decision gives record. Its external_id, <number>:<head>, and its output title
    name the pull request that it approves: the check run of a commit shows on each pull request of that commit. Its
    output text is the marker line of import_marker, alone. Its summary names run, the run whose screen and review
    passed head, and read, the time when that run read the pull request (RECORDED_BY), when both are given: a
    withdrawal withdraws it only for a reason at or after that time (withdraws). With neither, it names no such run,
    and each withdrawal withdraws it, which fails closed."""
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head) and bool(run) == bool(read)
            and (not run or NUMBER.fullmatch(run) and TIME.fullmatch(read))):
        raise ValueError(f"not a pull request number, a head commit, a run id and a time: {number!r} {head!r} {run!r} "
                         f"{read!r}")
    summary = ["The automated screen and the automated review passed this head commit."]
    if run:
        summary = [f"The automated screen and the automated review in run {run} of the review workflow passed this "
                   f"head commit. That run read the pull request at {read}."]
    summary.append("No changed file is under `.github/`.")
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


# The first two sentences of the summary of a check run that the workflow recorded (check_run): the run whose screen
# and review passed the head, and the time when that run read the pull request.
RECORDED_BY = re.compile(r"The automated screen and the automated review in run (?P<run>[1-9][0-9]*) of the review "
                         rf"workflow passed this head commit\. That run read the pull request at (?P<at>{TIME.pattern})"
                         r"\.(?: |$)")


def recorded_by(check):
    """(run, at) that the summary of check, an import check run with the conclusion success, names (RECORDED_BY): the
    run whose screen and review passed its head, and the time when that run read the pull request. None for any other
    check run, and for a success whose summary names no such run: it counts as read at no time."""
    summary = check.get("summary") or (check.get("output") or {}).get("summary") or ""
    m = RECORDED_BY.match(summary) if check.get("conclusion") == "success" and isinstance(summary, str) else None
    return (m.group("run"), m.group("at")) if m else None


def withdraws(check, at):
    """Whether a withdrawal whose reason counts from at withdraws check, an import check run with the conclusion
    success (OSSV-221's architect, 2026-11-24 05:23Z): an older read never withdraws a newer read's record. So it
    withdraws check unless the word of check (check_word: the time when the run that recorded it read the pull request,
    recorded_by) outranks the word of the withdrawal, a neutral check run from at (outranks). It withdraws each one
    when at is empty (no time of the reason is known, so the withdrawal counts after each time), and each one that
    names no such run (it counts at no time, which fails closed). At the same time, it withdraws: a neutral check run
    outranks a success (RANKS)."""
    word = check_word(check)
    return word is None or not outranks(word, (at or NEWEST, "neutral"))


# Why a later run of a head withdraws the import check run that the workflow recorded on it (R12), for the kind own
# (CAUSES) alone: its own review gave a blocking finding or the verdict person, or its own screen held the head, or
# GitHub did not say in that run whether the author has write access (access: its pass is no approval; OSSV-221's
# architect, 2026-11-24 14:29Z, F3). The reason refused is a review of that run that the fresh reader refused, whatever
# verdict the model gave (2026-11-25 10:21Z). Each is (the end of the output title, the summary's first sentence). They
# say later: the run that recorded the check run read the pull request before the run that withdraws it, or names no
# such run, and then counts as read at no time (recorded_by). The texts of refused say that the workflow stopped the
# review, as the label comment of its state does (STATES, refused-review). An outside author reads them on the pull
# request.
WITHDRAWN = {
    "blocking": ("because a later review asks for a change",
                 "A later automated review of this head commit asks for a change."),
    "person": ("because a later review has questions for Sami",
               "A later automated review of this head commit has questions for Sami."),
    "refused": ("because the workflow stopped a later review",
                "The workflow stopped a later automated review of this head commit and did not post it."),
    "screen": ("because a later screen held it", "A later automated screen held this head commit."),
    "access": ("because GitHub did not say in a later run whether the author has write access",
               "GitHub did not say in a later run of the review workflow whether the author of this pull request has "
               "write access."),
}
# The same reasons of the kind own when the run that recorded the check run read the pull request at the same time as
# the run that withdraws it (a tie, which withdraws: withdraws). That run is not later, so these texts name it: {run}.
TIE_WITHDRAWN = {
    "blocking": ("because the review of run {run} asks for a change",
                 "The automated review in run {run} asks for a change."),
    "person": ("because the review of run {run} has questions for Sami",
               "The automated review in run {run} has questions for Sami."),
    "refused": ("because the workflow stopped the review of run {run}",
                "The workflow stopped the automated review in run {run} and did not post it."),
    "screen": ("because the screen of run {run} held it", "The automated screen in run {run} held this head commit."),
    "access": ("because GitHub did not say in run {run} whether the author has write access",
               "GitHub did not say in run {run} of the review workflow whether the author of this pull request has "
               "write access."),
}
# The same reasons for each other kind (held, owed and earlier): an earlier run gave the reason, in a hold of its
# screen, the line of OWED or a review comment that a relabel or a review by hand reads. That hold or review can be
# older than the check run: a relabel can withdraw a check run for a review that came before it. So these texts do not
# say later. A review's reason is a past verdict: an edit of the review comment in place can replace that review. So
# these texts say what it asked. The check run of not_approved uses them too: it takes the place of no check run.
OWED_WITHDRAWN = {
    "blocking": ("because an automated review of this head commit asked for a change",
                 "An automated review of this head commit asked for a change."),
    "person": ("because an automated review of this head commit had questions for Sami",
               "An automated review of this head commit had questions for Sami."),
    "refused": ("because the workflow stopped an automated review of this head commit",
                "The workflow stopped an automated review of this head commit and did not post it."),
    "screen": ("because an automated screen held this head commit", "An automated screen held this head commit."),
    "access": ("because GitHub did not say in a run whether the author has write access",
               "GitHub did not say in a run of the review workflow whether the author of this pull request has write "
               "access."),
}

# The kinds of the cause of a withdrawal, as the step that finds the check runs gives them (withdraw_word): own, the
# verdict, the screen or the access of the run that withdraws; held, a hold comment of the screen or a check run for
# screen; owed, the line of OWED; earlier, a review comment of the head or another check run.
CAUSES = ("own", "held", "owed", "earlier")


def withdrawal(number, head, why, text, run, kind="own", source="", at="", read=""):
    """The body of the request that updates an import check run on head of pull request number (PATCH
    repos/<repo>/check-runs/<id>) for why, whose cause is kind, one of CAUSES (WITHDRAWN or TIE_WITHDRAWN for own, else
    OWED_WITHDRAWN: the hold or the review of another kind can be older than the check run): the conclusion neutral, so
    that the import no longer reads it as the approval of the pull request, and an output title that names the pull
    request and says why. Its name and its external_id stay, and so does text, its output text: the marker line of the
    value that it recorded. A withdrawal is itself the record of its reason (OSSV-221's architect, 2026-11-23 01:47Z and
    03:06Z): its summary also names run, the run that withdraws it, the head, why, and the time from which the
    withdrawal counts (WITHDREW; withdrawal_stands). For own, why is the reason of run itself, and at, which must be
    given, is the time when run read the pull request (its trust job's started): an own withdrawal counts from that
    read, never from the time when run wrote it (2026-11-24 05:23Z). read is the time when the run that recorded the
    check run read the pull request (recorded_by), or empty when the check run names no such run. The texts of own say
    later only when read is empty or before at (WITHDRAWN); else they name run (TIE_WITHDRAWN). For another kind,
    source and at are the run that gave why and the time of its word (withdraw_word): the time when that run read the
    item (of its review, of its hold of the screen, or the read of the line of OWED), or the time that its check run
    names. The summary names the run and the time. When neither is given, the workflow knows no time of that
    earlier run: the summary says so, and the withdrawal counts from now, which fails closed. Its completed_at is the
    time now."""
    now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    own = kind == "own"
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head) and NUMBER.fullmatch(run) and why in WITHDRAWN
            and kind in CAUSES and (not at or TIME.fullmatch(at)) and (not read or TIME.fullmatch(read))
            and (not source and at if own else bool(source) == bool(at) and (not source or NUMBER.fullmatch(source)))):
        raise ValueError(f"not a pull request number, a head commit, a reason, a run id, a cause, a source run and "
                         f"times: {number!r} {head!r} {why!r} {run!r} {kind!r} {source!r} {at!r} {read!r}")
    texts = OWED_WITHDRAWN if not own else TIE_WITHDRAWN if read and read >= at else WITHDRAWN
    end, first = (t.format(run=run) for t in texts[why])
    did = (f"{first} So this check is no longer an approval for the import. Run {run} of the review workflow withdrew "
           f"it from head commit {head}")
    if own:
        summary = (f"{did}, for the reason `{why}` of run {run} itself. The withdrawal counts from {at}, the time when "
                   f"run {run} read the pull request.")
    elif source:
        summary = (f"{did}, for the reason `{why}` of run {source}. The withdrawal counts from {at}, a time of run "
                   f"{source}. It is the time when run {source} read the pull request, or the time of a hold or a "
                   f"withdrawal by run {source}.")
    else:
        summary = (f"{did} at {now}, for the reason `{why}` of an earlier run. The workflow knows no time of that run, "
                   "so the withdrawal counts from this time.")
    return {"status": "completed", "conclusion": "neutral", "completed_at": now,
            "output": {"title": f"Not approved for the import: pull request #{number} at {head[:12]}, {end}",
                       "summary": summary, "text": text}}


# The reasons that the summary of a withdrawal (WITHDREW) or of a check run of not_approved (NOT_APPROVED) names, as one
# pattern: each reason of WITHDRAWN.
WITHDRAWN_WHY = "|".join(WITHDRAWN)
# The last sentences of the summary of a withdrawal (withdrawal), in each of its three forms: the run that withdrew it,
# the head, the reason, and the time from which the withdrawal counts (for own, the time when that run read the pull
# request), with the run that gave the reason when the summary names one.
WITHDREW = re.compile(
    r" Run (?P<run>[1-9][0-9]*) of the review workflow withdrew it from head commit (?P<head>[0-9a-f]{40})"
    rf"(?:, for the reason `(?P<own>{WITHDRAWN_WHY})` of run (?P=run) itself\. The withdrawal counts "
    rf"from (?P<read>{TIME.pattern}), the time when run (?P=run) read the pull request"
    rf"| at (?P<at>{TIME.pattern}), for the reason `(?P<earlier>{WITHDRAWN_WHY})` of an earlier run\. "
    r"The workflow knows no time of that run, so the withdrawal counts from this time"
    rf"|, for the reason `(?P<why>{WITHDRAWN_WHY})` of run (?P<source>[1-9][0-9]*)\. The withdrawal "
    rf"counts from (?P<since>{TIME.pattern}), a time of run (?P=source)\. It is the time when run (?P=source) read the "
    r"pull request, or the time of a hold or a withdrawal by run (?P=source))\.$")


def not_approved(number, head, why, value, run, at):
    """The body of the request that records a check run with the conclusion neutral on head of pull request number
    (POST repos/<repo>/check-runs) for why, the verdict blocking or person of the review of run, refused, the review
    of run that the fresh reader refused (OSSV-221's architect, 2026-11-25 10:21Z), screen, the screen of run that held
    head, or access, a run in which GitHub did not say whether the author has write access, so that its verdict is no
    approval whatever it is (2026-11-24 14:29Z, F3): the reason of run itself.
    The post job of run makes it when no import check run of head for number has the conclusion success, as it then
    has no success to withdraw (OSSV-221's architect, 2026-11-24 05:33Z; spec R12), for an author whom holds_back
    treats as outside (2026-11-24 09:28Z). The write jobs of an item run one at a time (the group write-<n>), and the
    post job of a run that read the item before run can come after this one. Its summary names why, run, at, the time
    when run read the pull request (its trust job's started), head and number, in plain sentences, as an outside author
    reads them on the pull request (NOT_APPROVED). A check run belongs to the commit, so it shows
    on each pull request of head: the summary says which pull request it is about. So each reader takes it as a
    withdrawal by run that counts from at (withdrawn_by), in the order of the time that each check run names
    (newest_withdrawal): that older run records nothing over it (own_record), and a screened pass whose run read the
    item after at lifts it (withdrawal_stands). Its name, its external_id <number>:<head> and its output text, the
    marker line of value (import_marker), are those of a record (check_run). Its output title names the pull request
    and says why, in the words of OWED_WITHDRAWN: it takes the place of no earlier check run, so it does not say later.
    The import reads only a check run with the conclusion success, so this one approves nothing."""
    if not (NUMBER.fullmatch(number) and HEAD.fullmatch(head) and why in OWED_WITHDRAWN and NUMBER.fullmatch(run)
            and TIME.fullmatch(at)):
        raise ValueError(f"not a pull request number, a head commit, a reason, a run id and a time: {number!r} "
                         f"{head!r} {why!r} {run!r} {at!r}")
    end, first = OWED_WITHDRAWN[why]
    summary = (f"{first} Run {run} of the review workflow read the pull request at {at}. Then it found no import "
               f"check run of head commit {head} for pull request #{number} that was an approval for the import. So "
               f"this check records that pull request #{number} is not approved for the import, for the reason `{why}` "
               f"of run {run} itself.")
    return {"name": CHECK, "head_sha": head, "external_id": f"{number}:{head}", "status": "completed",
            "conclusion": "neutral",
            "output": {"title": f"Not approved for the import: pull request #{number} at {head[:12]}, {end}",
                       "summary": summary, "text": import_marker(head, value)}}


# The last sentences of the summary of a check run of not_approved: the run, the time when it read the pull request,
# the head, the pull request, and the reason of that run. withdrawn_by reads them as those of a withdrawal by that run,
# for its own reason, that counts from that time.
NOT_APPROVED = re.compile(
    rf" Run (?P<run>[1-9][0-9]*) of the review workflow read the pull request at (?P<read>{TIME.pattern})\. Then it "
    r"found no import check run of head commit (?P<head>[0-9a-f]{40}) for pull request #(?P<number>[1-9][0-9]*) that "
    r"was an approval for the import\. So this check records that pull request #(?P=number) is not approved for the "
    rf"import, for the reason `(?P<own>{WITHDRAWN_WHY})` of run (?P=run) itself\.$")
# The verdicts of a review that withdraw an import check run of its head (WITHDRAWN).
WITHDRAWING = ("blocking", "person")


# --- the order of the words on a head -------------------------------------------------------------------------------
# The one model by which each reader and each writer of the import check run, of a review or hold comment and of the
# label orders what the workflow wrote of a head (OSSV-221's architect, 2026-11-24 14:29Z to 14:40Z). A word is
# (read, kind): the time from which it counts, and its kind (RANKS). head_words gives each word on a head as a Word,
# from each carrier of a word, and newest_word gives the newest of them that a reader asks for. Each reader takes its
# word from newest_word, and no reader orders words by itself (OSSV-221's architect, 2026-11-25 23:02Z). The carriers:
# - review: a review comment of BOT that names the head: its verdict, pass, blocking or person, from the time when its
#   run read the item, its marker <!-- review-read <time> --> (word_time). With no such marker, a pass counts at no
#   time ("", before each time), and a blocking finding or the verdict person from when GitHub last changed it.
# - hold: a hold comment of BOT that names the head: hold. A hold of the screen (hold_fact screen_held) counts from the
#   time when its run read the item, its marker <!-- review-held-read <time> -->, and with no such marker from when
#   GitHub last changed it (word_time). Each other hold counts from when GitHub last changed it. A reader of the hold
#   of the screen reads no other hold (screen_hold).
# - line: the line <!-- withdraw-owed <head> <why> <run> <read> --> of a label comment of BOT (OWED): blocking, person
#   or refused as a verdict, and hold for screen, from <read>, the time when its run read the item, never from when
#   its step wrote the line (line_word; OSSV-221's architect, 2026-11-25 01:13Z, G1). It never posts as a comment.
# - check: an import check run of the head. A success is a pass, from the time when the run that recorded it read the
#   pull request (recorded_by), and at no time when its summary names none. A check run with the conclusion neutral (a
#   withdrawal, or a check run of not_approved) has the kind of its reason (withdrawn_by): blocking, person or refused
#   as a verdict, hold for screen, and neutral for access. It counts from the time that its summary names
#   (blocks_from). One whose summary names no time is neutral, and counts after each time (NEWEST).
# A review that the fresh reader refused is the word refused, from the time when its run read the item. The kind
# refused ranks as a verdict. Such a review posts no comment, so two other carriers carry its word (OSSV-221's
# architect, 2026-11-25 10:21Z and 19:29Z). Its post job records a neutral check run, or withdraws, for the reason
# refused at its own read. When GitHub refuses that write, its comment job writes the line for refused. The read of a
# run that gives no word of its own, such as a relabel or an approval, is the word read, from the time when its trust
# job read the item.
# The order is by time. At the same time, a kind of a higher rank outranks a kind of a lower one: a verdict or a hold
# outranks a pass, a neutral check run outranks a success, a hold outranks a verdict (review_verdict reads a hold at
# the time of a screened review as held), and each word outranks a read. Two words of the same rank at the same time
# do not outrank each other. A run whose author's write access GitHub did not say gives no approval, whatever its
# verdict: its post job records a neutral check run, or withdraws, for the reason access at its own read, which its
# pass does not outrank (F3).
# Each writer applies the order before it writes. So at the end of each order of the post, comment and hold jobs of
# the runs of a head: (I1) a success stands only while the newest word is a pass of a run of an outside author;
# (I2) the label says that the workflow recorded the check exactly while a success stands; (I3) the label's state is
# the state of the newest word; (I4) the review or the hold of the newest verdict posts, and no older run takes its
# place; (I5) no run withdraws a success of a newer read. The post job records only while its pass outranks each other
# word (own_record), and withdraws only a success that does not outrank its own word (withdraws), for the newest word
# that withdraws (withdraw_word). The comment and hold jobs post nothing while a word of another run outranks their
# own (newer_word), and the label step writes no label while a hold of its head outranks its own word (stays). A
# relabel, a review by hand and the rescreen pass read the newest word (review_verdict, relabel_facts, and held.sh
# relabel_withdraws through the command relabel-withdraws, with the import check runs of the head), the rescreen pass
# and the label step the newest hold of each work (newest_holds, through the command holds), and each writer of a hold
# comment the hold that it replaces (replaced_hold, through the command replaced-hold). The line gives its
# reason only while the newest screened review comment does not outrank it (owed_reason): so an older read's line
# never withdraws a newer read's record.
RANKS = {"read": 0, "pass": 1, "success": 1, "blocking": 2, "person": 2, "refused": 2, "neutral": 2, "hold": 3}
# The time of a word that counts after each time: a neutral check run whose summary names no time (head_words).
NEWEST = None
# A word on a head (head_words): read and kind, as above; run, the id of the run that gave it ("" when none is known);
# carrier, review, hold, line or check, as above (and own for the word of this run that has not posted yet, answer for
# an answer that relabel_facts reads); why: a review's verdict, a hold's hold_fact, the why of the line, and for a
# check run pass for a success, else the reason that withdrawn_by names ("" for none); screened, True for a review
# comment that holds the marker <!-- review-screened <head> -->; check and comment, the check run or the comment that
# carries it, or None.
Word = namedtuple("Word", "read kind run carrier why screened check comment")
# The kinds of the words that withdraw as a verdict does: a blocking finding, the verdict person, a refused review.
VERDICT_WITHDRAWS = ("blocking", "person", "refused")


def word_key(read, kind):
    """The place of the word (read, kind) in the order of the words on a head: by read, a time as GitHub gives it, ""
    (no time, before each time) or NEWEST (after each time), then by the rank of kind (RANKS). A ValueError for a kind
    that RANKS does not name."""
    if kind not in RANKS:
        raise ValueError(f"not a kind of word: {kind!r}")
    return read is NEWEST, read or "", RANKS[kind]


def outranks(word, other):
    """Whether word, (read, kind), comes after other in the order of the words on a head (word_key)."""
    return word_key(*word) > word_key(*other)


def head_words(comments, head, checks=()):
    """Each word on head as a Word, from each of its carriers, in the order of the words on head (word_key; words at
    the same place keep the order below): each review comment and each hold comment of BOT among comments, the item's
    comments as the API lists them (with updated_at), that names head (REVIEWED, HELD_HEAD), in the API's order; then
    the line of OWED of head (owed_line); then each check run among checks, the import check runs of head as the API
    lists them (import_checks), in the API's order. A review comment gives its verdict, from its word_time, with the
    run of REVIEW_RUN. A hold comment gives hold, from its word_time, with the run of HELD_RUN and its fact
    (hold_fact): a reader of the hold of the screen reads only one whose fact is screen_held (screen_hold). The line
    gives line_word, with the run that it names. A success gives pass, from the read of recorded_by, with its run. A
    check run with the conclusion neutral gives the kind of the reason that withdrawn_by names (hold for screen, neutral
    for access), from the time that it names, with the run that gave the reason; with no such time, neutral after each
    time (NEWEST). A check run of another conclusion gives no word."""
    words = []
    for c in comments:
        if not of_bot(c):
            continue
        body = c.get("body") or ""
        m = REVIEWED.match(body)
        if m:
            if m.group(1) == head:
                r = REVIEW_RUN.match(body, m.end())
                words.append(Word(word_time(c), m.group(2), r.group(1) if r else "", "review", m.group(2),
                                  bool(m.group(4)), None, c))
        elif body.startswith("<!-- review-held -->"):
            h, r = HELD_HEAD.search(body), HELD_RUN.search(body)
            if h and h.group(1) == head:
                run = r.group(1) if r else ""
                words.append(Word(word_time(c), "hold", run, "hold", hold_fact(body), False, None, c))
    why, run, read = owed_line(comments, head)
    if why:
        words.append(Word(*line_word(why, read)[:2], run, "line", why, False, None, None))
    for check in checks:
        if check.get("conclusion") == "success":
            run, read = recorded_by(check) or ("", "")
            words.append(Word(read, "pass", run, "check", "pass", False, check, None))
        elif check.get("conclusion") == "neutral":
            why, run, _at = withdrawn_by(check, head) or ("", "", "")
            kind = {"screen": "hold", "access": "neutral", "": "neutral"}.get(why, why)
            words.append(Word(blocks_from(check, head) or NEWEST, kind, run, "check", why, False, check, None))
    words.sort(key=lambda word: word_key(word.read, word.kind))
    return words


def newest_word(words, *, kinds=None, carriers=None, run=None, over=None, until=None, where=None):
    """The newest Word among words (head_words, or Words of the same form) that a reader asks for, or None: the one
    rule by which each reader takes its word (OSSV-221's architect, 2026-11-25 23:02Z). The newest is the last in the
    order of the words on a head (word_key), and of words at the same place the later in words. It reads only a word
    whose kind is in kinds and whose carrier is in carriers (when they are given), whose run is not run (when it is
    given: the word of this run never counts), that outranks over, a word (read, kind) (when it is given), whose read
    is at or before until, a time (when it is given: never NEWEST), and for which where(word) holds (when it is
    given)."""
    found = None
    for word in words:
        if (kinds is not None and word.kind not in kinds or carriers is not None and word.carrier not in carriers
                or run is not None and word.run == run or over is not None and not outranks(word[:2], over)
                or until is not None and (word.read is NEWEST or word.read > until)
                or where is not None and not where(word)):
            continue
        if found is None or word_key(*word[:2]) >= word_key(*found[:2]):
            found = word
    return found


def screen_hold(word):
    """Whether word, a Word, is a hold of the screen: a hold comment of the screen (hold_fact screen_held), the line of
    OWED for screen, a check run for the reason screen, or the own word of a run whose screen held the head."""
    return word.kind == "hold" and (word.carrier != "hold" or word.why == "screen_held")


def comment_word(c, head):
    """(read, kind, run) of the word on head that c, a comment as the API lists it, gives (head_words), or None: a
    review comment of BOT that names head (kind: its verdict), or a hold comment of BOT of the screen that names head
    (screen_hold; kind: hold). read is its word_time, and run the run that wrote it, or "" when it names none."""
    found = [word[:3] for word in head_words([c], head) if word.carrier == "review" or word.why == "screen_held"]
    return found[0] if found else None


def check_word(check, head=""):
    """(read, kind) of the word that check, an import check run as the API lists it, gives on head (head_words), or
    None for a check run of another conclusion than success or neutral: pass, from the time that recorded_by names, or
    "" when it names none, for a success; for a check run with the conclusion neutral, the kind of its reason, from the
    time that withdrawn_by names for head, or neutral after each time (NEWEST) when it names none."""
    found = head_words((), head, (check,))
    return found[0][:2] if found else None


def word_time(c):
    """The time by which c, a comment of BOT as the API lists it (with updated_at), counts as a word on its head: the
    one rule by which each reader orders a review comment or a hold comment of the screen against a hold, a withdrawal
    or another review (OSSV-221's architect, 2026-11-24 01:20Z and 01:26Z, and 09:43Z, A3). A review comment
    (REVIEWED) counts from the time when its run read the item, the marker <!-- review-read <time> --> of its header
    (REVIEW_READ), never from the time when it posted. With no such marker (a review of before the marker), it counts
    from when GitHub last changed it (updated_at) for the verdicts blocking and person, which fails closed, and at no
    time ("", before each time) for pass: such a pass never outranks a hold or a verdict, and never lifts a withdrawal.
    A hold comment of the screen (hold_fact screen_held) counts from the time when its run read the item too, its
    marker <!-- review-held-read <time> --> (HELD_READ), never from the time when it posted. With no such marker (a
    hold of before the marker), it counts from its updated_at, which fails closed: it posts after its run read the
    item. Each other comment, such as a hold of another kind, counts from its updated_at."""
    body, at = c.get("body") or "", c.get("updated_at") or ""
    m = REVIEWED.match(body)
    if not m:
        held = body.startswith("<!-- review-held -->") and hold_fact(body) == "screen_held" and HELD_READ.search(body)
        return held.group(1) if held else at
    read = REVIEW_READ.match(body, m.end())
    return read.group(1) if read else "" if m.group(2) == "pass" else at


def review_verdict(comments, head, checks=()):
    """(verdict, state, why) of head, from comments, the item's comments as the API lists them (issues/<n>/comments,
    with updated_at), and checks, the import check runs of head (import_checks; none when not given): the one rule by
    which a run that reads the head, a relabel or a review by hand, records or withdraws its import check run (R12;
    OSSV-221's architect, 2026-11-20 21:33Z and 22:21Z). Each word comes from head_words and newest_word: the order of
    the words on head (2026-11-24 01:20Z and 01:26Z, 05:23Z, and 2026-11-25 23:02Z). verdict is the verdict of the
    newest review comment of head ("" when none names head). A review comment of head is screened when it holds the
    marker <!-- review-screened <head> --> after its verdict, so that the screen passed head in the run of that review.
    state is held when a hold of the screen (screen_hold: a hold comment of the screen, the line of OWED for screen, or
    a check run for the reason screen) outranks the newest screened review comment of head, or when no review comment
    of head is screened and such a hold exists: a later screen held the head. A hold at the same time as a screened
    review outranks it, which fails closed. Else it is screened when the newest review comment of head is screened,
    earlier when an older one is screened but the newest is not (a review by hand runs no screen), and unscreened when
    none is. Such a run records the check run only for the state screened with the verdict pass and no why: the newest
    review comment is a screened pass. why is the reason for which it withdraws each check run of head that stands
    (WITHDRAWN): screen for held; else the kind of the newest word that withdraws as a verdict does (blocking, person or
    refused, of a review comment, of the line of OWED or of a check run) when the newest screened review comment does
    not outrank it; else "". So an older read's line never withdraws a newer read's record (OSSV-221's architect,
    2026-11-25 01:13Z, G1), and an unscreened pass newer than a screened pass neither records nor withdraws: a check run
    that stands stays, unless a word that gives a reason stands. Only the markers at the start of a review comment
    count: no marker of the model's or the reader's text reaches a comment (trim.py inert). The markers of a hold
    comment and the lines of a label comment are the workflow's own."""
    words = head_words(comments, head, checks)
    newest = newest_word(words, carriers={"review"})
    screened = newest_word(words, carriers={"review"}, where=lambda word: word.screened)
    verdict = newest.kind if newest else ""
    if newest_word(words, over=screened[:2] if screened else None, where=screen_hold):
        return verdict, "held", "screen"
    found = newest_word(words, kinds=VERDICT_WITHDRAWS, carriers={"review", "line", "check"})
    why = found.kind if found and not (screened and outranks(screened[:2], found[:2])) else ""
    if not screened:
        return verdict, "unscreened", why
    return verdict, "screened" if newest is screened else "earlier", why


def owed_line(comments, head):
    """(why, run, read) of the line of OWED of head in a label comment of BOT among comments (the newest such line), or
    ("", "", ""): the reason of a withdrawal of the import check runs of head that a run owes, the id of the run that
    the line names, and its read, the time when that run read the item, which is the time of the line (OSSV-221's
    architect, 2026-11-25 01:30Z)."""
    owed = ("", "", "")
    for c in comments:
        body = c.get("body") or ""
        if of_bot(c) and body.startswith(FIRST):
            for line in body.split("\n"):
                m = OWED.fullmatch(line)
                if m and m.group(1) == head:
                    owed = (m.group(2), m.group(3), m.group(4))
    return owed


def line_word(why, read):
    """(read, kind, why) of the line of OWED for why that names read (owed_marker) as a word on its head. read is the
    read of the line, the time when its run read the item, never the time when a step wrote the line. kind is the rank
    of why (RANKS): blocking, person or refused as a verdict, and hold for screen."""
    return read, "hold" if why == "screen" else why, why


def owed_keeps(number, body, line):
    """The log text that says why line, a marker line of KEPT, does not take the place of the line of OWED of its head
    in body, the label comment of the item number: that line outranks line as a word on the head (line_word). Else "",
    and line takes its place. A line of OWED is replaced only by a line that the line that stands does not outrank
    (OSSV-221's architect, 2026-11-25 07:24Z), for each writer (mark, apply), so that no older read's line takes the
    place of a newer read's line whose comment never posted."""
    new = OWED.fullmatch(line)
    if not new:
        return ""
    stands = [m for m in map(OWED.fullmatch, body.split("\n")) if m and m.group(1) == new.group(1)]
    if not stands:
        return ""
    kept = stands[-1]
    (at, kind, _why), (other, rank, _new) = (line_word(m.group(2), m.group(4)) for m in (kept, new))
    if not outranks((at, kind), (other, rank)):
        return ""
    if at == other:
        said = {"blocking": "a blocking finding", "person": "the verdict person", "refused": "a refused review"}
        why = (f"Both lines count from {at}. The line that stands is for a hold of the screen, which outranks "
               f"{said[new.group(2)]} at the same time.")
    else:
        why = f"The line that stands counts from {at}, later than {other}, so it outranks the other line."
    return f"#{number}: its label comment keeps {kept.group(0)}. This step does not write {line}. {why}"


def owed_reason(comments, head):
    """The why of the line of OWED of head when it gives a reason to withdraw the import check runs of head, else "".
    It gives one while the newest screened review comment of head does not outrank the line as a word (head_words,
    newest_word), so an older read's line never withdraws a newer read's record (OSSV-221's architect, 2026-11-25
    01:13Z, G1). A line that such a review outranks gives no reason. That review read the item after the time of the
    line, so it gives the reason for the line to go (line_reason), and the step OWE of the comment job takes the line
    out (owe). A review with no screen never outranks the line, as the decide step reads only a screened review as the
    verdict of an outside author, which fails closed."""
    words = head_words(comments, head)
    line = newest_word(words, carriers={"line"})
    if line is None or newest_word(words, carriers={"review"}, over=line[:2], where=lambda word: word.screened):
        return ""
    return line.why


def owed_marker(head, why, run, read):
    """The line of OWED of head for why, which names run and read, the time when run read the item (owed_run)."""
    return f"<!-- withdraw-owed {head} {why} {run} {read} -->"


def owed_run(comments, head, why, run, read):
    """(run, read) that the line of OWED of head and why names when its writer is not the run whose own comment gives
    why: a relabel whose withdrawal GitHub refused, or any run whose own review gives no such verdict (OSSV-221's
    architect, 2026-11-22 17:27Z). read is the time when that run read the item, the time of the line (2026-11-25
    01:30Z). comments are the item's comments as the API lists them. The run and the read of the line of head and why
    that stands (owed_line), so that the line keeps naming the run of its reason. Else, the run of the comment of BOT
    that gives why, the newest by word_time, the time when its run read the item, with that time: for screen, a hold
    comment of the screen that names head (or its updated_at with no marker of that read); for blocking or person, a
    review comment of head with that verdict. No comment gives refused: the fresh reader refused that review, so it
    never posted. Else run and read, the writer's own run and the time when it read the item, also when that comment
    names no run: then no comment of an earlier run can take the line out (line_reason), and it fails closed. A
    ValueError when the time of that comment is not one of TIME, as owe gives for an owed value with no read: no line
    goes without a read."""
    standing, wrote, at = owed_line(comments, head)
    if standing == why:
        return wrote, at
    found, at = None, ""
    for c in comments:
        if not of_bot(c):
            continue
        body = c.get("body") or ""
        m = REVIEWED.match(body)
        if why in WITHDRAWING and m and m.group(1) == head and m.group(2) == why:
            if word_time(c) >= at:
                found, at = REVIEW_RUN.match(body, m.end()), word_time(c)
        elif why == "screen" and body.startswith("<!-- review-held -->") and hold_fact(body) == "screen_held":
            h = HELD_HEAD.search(body)
            if h and h.group(1) == head and word_time(c) >= at:
                found, at = HELD_RUN.search(body), word_time(c)
    if not found:
        return run, read
    if not TIME.fullmatch(at):
        comment = "the hold comment of the screen" if why == "screen" else f"the review comment with the verdict {why}"
        raise ValueError(f"{comment}, of run {found.group(1)} on {head}, has no time in the form that GitHub gives: "
                         f"{at!r}. So this step writes no withdraw-owed line.")
    return found.group(1), at


def reason_posted(comments, head, why, run, screened, since):
    """Whether comments, the item's comments as the API lists them, hold a comment of BOT that gives a reason for the
    line <!-- withdraw-owed <head> <why> <run> <read> --> of OWED to go (owe; OSSV-221's architect, 2026-11-22 16:06Z
    and 16:08Z). (a) The comment of run that gives why: for screen, a hold comment of the screen (hold_fact screen_held)
    that names head and run (HELD_HEAD, HELD_RUN); for blocking or person, a review comment of head of run
    (REVIEW_RUN) with that verdict; for refused, none, as that review never posted. (b) A review comment of head that is
    newer than the line: its word_time is after since, the time of the line (line_reason). That is the time when its
    run read the item, never the time when it posted (OSSV-221's architect, 2026-11-24 01:20Z): a review whose run
    read the head before the line gave no verdict after it. A review with no marker of that time counts from when
    GitHub last changed it for a blocking finding or
    the verdict person, and never for a pass (01:26Z). A run's id gives when it started, not when it gave its verdict,
    so it is no such time (2026-11-23 01:47Z and 03:06Z). With since empty, no review comment gives a reason by (b).
    When screened is True, the review comment of (b) must hold the marker <!-- review-screened <head> -->: the decide
    step reads only such a review as the verdict of an outside author. Else any review counts, as for a writer, whose
    item gets no import check run. review_verdict then reads that review: one with a blocking finding or the verdict
    person still withdraws."""
    for c in comments:
        if not of_bot(c):
            continue
        body = c.get("body") or ""
        m = REVIEWED.match(body)
        if m and m.group(1) == head:
            r = REVIEW_RUN.match(body, m.end())
            if r and r.group(1) == run and m.group(2) == why:
                return True
            if since and word_time(c) > since and (m.group(4) or not screened):
                return True
        elif why == "screen" and body.startswith("<!-- review-held -->"):
            h, r = HELD_HEAD.search(body), HELD_RUN.search(body)
            if h and r and h.group(1) == head and r.group(1) == run and hold_fact(body) == "screen_held":
                return True
    return False


def line_reason(comments, head, why, run, read, screened):
    """(posted, since) of the line <!-- withdraw-owed <head> <why> <run> <read> --> of OWED. posted is whether a
    comment of BOT gives a reason for the line to go (reason_posted), with since, the time of the line. That time is
    read, the time when run read the item (OSSV-221's architect, 2026-11-25 01:30Z). The updated_at of the label
    comment is no time of the line: each relabel writes the label comment again."""
    return reason_posted(comments, head, why, run, screened, read), read


def withdrawn_by(check, head):
    """(why, source, at) that the summary of check, an import check run of head with the conclusion neutral, names:
    the reason, the run that gave it, and the time from which the check run counts. It reads two forms. The summary of
    a withdrawal (WITHDREW) names them, and the time is, for own, the time when that run read the pull request. The
    summary of a check run that a run recorded as no approval, when it found no success to withdraw (NOT_APPROVED,
    not_approved), names that run, its own reason and the time when it read the pull request. Each reader takes either
    form as a withdrawal from that time. When the summary of a withdrawal names no run that gave the reason (its time
    was not known), source is the run that withdrew it. None for any other check run, and for a withdrawal whose
    summary names no time."""
    summary = check.get("summary") or (check.get("output") or {}).get("summary") or ""
    m = None
    if check.get("conclusion") == "neutral" and isinstance(summary, str):
        m = WITHDREW.search(summary) or NOT_APPROVED.search(summary)
    if not m or m.group("head") != head:
        return None
    named = m.groupdict()
    return (named["own"] or named.get("earlier") or named.get("why"), named.get("source") or named["run"],
            named["read"] or named.get("at") or named.get("since"))


def blocks_from(check, head):
    """The time from which check, a withdrawal of the import check runs of head, blocks a record: the time that its
    summary names (withdrawn_by), or "" when it names none. A check run of not_approved counts as a withdrawal by its
    run. The one place that decides it (OSSV-221's architect, 2026-11-23 03:06Z and 2026-11-24 05:23Z and 05:33Z): for
    a run's own verdict or screen, the time when that run read the pull request (its trust job's started), never the
    time when it wrote the withdrawal or the check run; for a withdrawal for an older reason, the time when the run that
    gave that reason read the item (its review), or of its hold, its withdrawal or its line, or the time of the
    withdrawal when none was known. The step that withdraws counts from the same time: it withdraws only the records of
    runs that read the pull request at or before it (withdraws)."""
    named = withdrawn_by(check, head)
    return named[2] if named else ""


def standing_withdrawal(words):
    """The Word of the withdrawal that blocks a record among words (head_words), or None (OSSV-221's architect,
    2026-11-24 09:43Z, and 2026-11-25 23:02Z): the newest of the import check runs and of the screened review
    comments that pass (newest_word), when it is a check run with the conclusion neutral. Each one counts in the order
    of the words on the head, never by completed_at: a success from the time when the run that recorded it read the
    pull request (recorded_by), a withdrawal (withdrawn_by reads a check run of not_approved as one) from the time from
    which it counts (blocks_from), and a screened pass from the time when its run read the item (word_time). Each fails
    closed: a success or a pass that names no read counts at no time, so it lifts no withdrawal, and a withdrawal that
    names no time counts after each time. A withdrawal outranks a success or a pass of the same read. A pass of a run
    whose author's write access GitHub did not say lifts no withdrawal: the post job of that run withdrew, or recorded
    a neutral check run, for the reason access from the read of that pass (2026-11-24 14:29Z, F3)."""

    def counts(word):
        return word.carrier == "check" or word.carrier == "review" and word.screened and word.kind == "pass"

    found = newest_word(words, where=counts)
    return found if found and found.carrier == "check" and found.kind != "pass" else None


def newest_withdrawal(checks, head):
    """The withdrawal of the newest read among checks, the import check runs of head as the API lists them, or None:
    standing_withdrawal of their words alone. None when a success outranks it, or when no check run is a withdrawal."""
    found = standing_withdrawal(head_words((), head, checks))
    return found.check if found else None


def withdrawal_stands(checks, comments, head):
    """The id of the withdrawal among checks, the import check runs of head, that blocks a record, else "":
    standing_withdrawal of the words of checks and comments, the item's comments as the API lists them. No success of
    a newer read and no screened pass of a newer read stands over it then. A withdrawal that succeeded is itself the
    record of its reason, so a relabel never records over it unless such a pass stands (OSSV-221's architect,
    2026-11-23 01:47Z and 03:06Z): the run that withdrew it can have ended before its comment posted."""
    found = standing_withdrawal(head_words(comments, head, checks))
    return str(found.check.get("id") or "-") if found else ""


def own_record(checks, comments, head, started, run):
    """Whether a run on the route screen, whose own screen and review passed head, still records its import check run
    at head, and why not (OSSV-221's architect, 2026-11-23 18:38Z): a newer run's post, comment or hold job can run in
    the group write-<n> between the review of this run and its post job. started is the time when this run's trust job
    read the item (its output started), from which its own pass counts (word_time; 2026-11-24 01:20Z), and run is the
    id of this run. Its own word is (started, pass): each test below asks whether another word outranks it, and takes
    that word from head_words and newest_word (2026-11-25 23:02Z). (decision, what, since, verdict), the first that
    holds:
    ("held", the time of the hold, "", "") when the newest hold of the screen (screen_hold: a hold comment of the screen
    or the line of OWED for screen) of another run outranks it: a run that read the item at or after this run held
    head, and this run records nothing. A hold comment counts from its word_time, the time when its run read the item
    (OSSV-221's architect, 2026-11-24 09:43Z, A3), so the hold of a run that read the item before this run leaves its
    record, whenever it posted. A hold with no marker of that read counts from its updated_at, which fails closed.
    ("withdrawn", the id of the check run, the time from which it counts, "") when the withdrawal that blocks a record
    (standing_withdrawal: of the import check runs and the screened passes, the newest is a withdrawal) outranks it.
    A withdrawal whose summary names no time stands, as it does for a relabel, and so does one at started (fail closed:
    a neutral check run outranks a pass at the same time). The check run of not_approved of a newer run is such a
    withdrawal: that run found no success to withdraw, as its post job came before this one (2026-11-24 05:33Z). So is
    one that completed before the check run of not_approved of an older read: the read decides, never the time when a
    check run completed.
    ("newer", the run of the word, its time, its kind) when the newest word of another run that withdraws as a verdict
    does (blocking, person or refused) of a review comment or of the line of OWED outranks it: a run that read the item
    at or after this run gave head that verdict, so the pass of this run is not the newest word on head (2026-11-25
    19:29Z, F1). A refused review posts no comment. So when GitHub refused its withdrawal, its line is the one word of
    that review that this reads. When its withdrawal succeeded, its check run is a withdrawal, which gives withdrawn
    above. The run of a comment that names none is "".
    ("", "", "", "") when none holds: a hold, a withdrawal or a review older than the start of this run leaves its
    record, as after a blocking review, a fix and a screen that passed the head again."""
    own, words = (started, "pass"), head_words(comments, head, checks)
    held = newest_word(words, kinds={"hold"}, carriers={"hold", "line"}, run=run, over=own, where=screen_hold)
    if held:
        return "held", held.read, "", ""
    stands = standing_withdrawal(words)
    if stands and outranks(stands[:2], own):
        return "withdrawn", str(stands.check.get("id") or "-"), stands.read or "", ""
    newer = newest_word(words, kinds=VERDICT_WITHDRAWS, carriers={"review", "line"}, run=run, over=own)
    if newer:
        return "newer", newer.run, newer.read, newer.kind
    return "", "", "", ""


def newer_word(comments, head, started, run, kind="read", checks=()):
    """(run, kind, at) of the newest word on head of another run that outranks the own word of this run, (started,
    kind), or None (OSSV-221's architect, 2026-11-24 01:20Z and 01:26Z, (a), and 14:29Z, F1): a run whose own word is
    outranked by such a word posts nothing on the item, as the newer run owns its comment and its label. comments are
    the item's comments as the API lists them, and checks the import check runs of head (import_checks). started is the
    time when the trust job of this run read the item, and run is the id of this run. kind is the kind of its own word:
    pass, blocking, person or refused for its review, and hold for a hold of its screen. It is read for a run that gives
    no word (a relabel or an approval). The word comes from head_words and newest_word (OSSV-221's architect,
    2026-11-25 23:02Z): a review comment (its verdict), a hold comment of the screen (hold), the line of OWED (its why,
    or hold for screen), and a check run of checks that carries the word of a refused review (refused, from the time
    that its summary names). A refused review posts no comment, so only its check run or its line carries its word
    (2026-11-25 19:29Z, F2). Each other kind of word has a comment of its own, or a line when that comment could not
    post, so no other check run counts: a run whose post job withdrew for its own verdict or screen still lets an
    older run post until that comment posts (the tester's red test of round 21, the label of a newer read's
    withdrawal). A review or a hold counts from the time when its run read the item, never from when it posted
    (2026-11-24 09:43Z, A3). A hold with no marker of that read counts from its updated_at. A pass with no such marker
    counts at no time, so it never makes this run skip its posts. A hold of another kind than the screen's is no word
    here. A word of a later time outranks the own word. At the same time, it outranks only a word of a lower rank
    (RANKS). A verdict, a refusal or a hold makes a pass skip. A pass of the same time does not make a verdict, a
    refusal or a hold skip. Each word makes a read skip, which fails closed. A word of this run never counts: a comment
    whose REVIEW_RUN or HELD_RUN is run, or a line or a check run that names run. An earlier attempt of this run can
    have posted it. The word's run is "" when it names none."""

    def counts(word):
        if word.carrier == "check":
            return word.why == "refused"
        return word.carrier != "hold" or screen_hold(word)

    found = newest_word(head_words(comments, head, checks), run=run, over=(started, kind), where=counts)
    return (found.run, found.kind, found.read) if found else None


def own_word(task, verdict, kind="", route=""):
    """The kind of the own word of a run in the step that withdraws (withdraw_word), which has not posted yet, from the
    facts that the step gives (OSSV-613's architect, round 30, item 1: no choice of it is left in the shell of the
    step): task, the run's task; verdict, the verdict of its review, screen when its screen held the head (an approval,
    or a run whose review job did not run), or anything else for none; kind, the trust job's kind; route, the run's
    route. A relabel gives none (-): it reads the words of the head, and gives no word of its own. blocking, person,
    refused and screen are the verdict. A pass of a run in which GitHub did not say whether the author has write access
    (kind unknown) is no approval (OSSV-221's architect, 2026-11-24 14:29Z, F3): it is access on the route screen, a
    word at the read of the run, as the tester's red test of round 23, F3, asks (ImportCheckTest, a run whose author
    kind is unknown is a not-approved word), and access-last for a review by hand, which comes after each other word
    that withdraws, as the tester's red test asks (KindTableTest, a review by hand withdraws what stands after an
    earlier blocking review or a newer hold for any author: from none). Else a pass is pass on the route screen, and
    none for a review by hand, whose pass ran no screen. Any other verdict gives none."""
    if task == "relabel":
        return "-"
    if verdict in VERDICT_WITHDRAWS or verdict == "screen":
        return verdict
    if verdict != "pass":
        return "-"
    if kind == "unknown":
        return "access" if route == "screen" else "access-last"
    return "pass" if route == "screen" else "-"


def withdraw_word(comments, head, checks, started, run, own):
    """(why, kind, source, at, outranked) of the withdrawal of the import check runs of head that the step which finds
    them makes for run, the id of this run, whose trust job read the item at started ("" when not known): the newest
    word that withdraws, whichever carrier gives it (OSSV-221's architect, 2026-11-25 23:02Z, G1). comments are the
    item's comments as the API lists them, and checks the import check runs of head (import_checks). own is the kind
    of this run's own word (own_word), which has not posted yet: blocking, person or refused for its review, screen for
    a hold of its screen, access for a pass of a run on the route screen in which GitHub did not say whether the author
    has write access, pass for a screened pass, access-last for such a pass of a review by hand, and - for none (a
    relabel, or a review by hand whose pass ran no screen). Each but access-last and - is a word at started, after each
    time when started is "". A word withdraws when it is a blocking finding, the verdict person, a refused review, a
    hold of the screen (screen_hold) or the own word access. A word lifts when it is a screened pass or the own word
    pass. A success lifts nothing: a word that withdraws leaves only the success of a newer read (withdraws), so a
    success of a newer read than the line of OWED stands, and the step still finishes the withdrawal for the line
    (OSSV-613's architect, round 30, item 5b). A run whose own word is at started reads only the words at or before
    started: a newer word is a newer run's, which withdraws for it or owes that withdrawal (newer_word). A run with no
    such word reads each word, whatever its time: a relabel withdraws a success that stands under a hold of the screen
    newer than its read (item 5a). Of the words that the run reads, X is the newest that withdraws. A word that check
    runs alone carry is a withdrawal that a run finished already (withdrawal_stands): it is X only while a success that
    it withdraws stands; else, and when another word that withdraws is at the same place, X is the newest of the other
    words that withdraw (item 5c: a writer's relabel withdraws nothing again for the check runs of a blocking review
    once the line of OWED went). When there is no X, or the newest word that lifts outranks it, X is the own word
    access of a review by hand (own access-last): a pass of such a run is no approval. With no X, all are "-" but
    outranked: "outranked" when the line of OWED of head stands and a screened review comment outranks it, so that the
    step OWE of the comment job takes the line out (owe), else "-". Else why is screen for a hold, access for the own
    word access, and the kind of X else. kind is a cause of CAUSES: own for the own word, held for a hold comment or a
    check run for screen, owed for the line, and earlier for a review comment or another check run. source and at are
    the run of X and the time of X when X names both (for own, "-" and started), else "-" and "-": the withdrawal then
    counts from the time now, and withdraws each success, which fails closed."""
    words = head_words(comments, head, checks)
    placed = own not in ("-", "access-last")
    if placed:
        kind = {"screen": "hold", "access": "neutral"}.get(own, own)
        words.append(Word(started or NEWEST, kind, run, "own", own, own == "pass", None, None))
    until = (started or None) if placed else None

    def withdraws_(word):
        return word.kind in VERDICT_WITHDRAWS or screen_hold(word) or word.carrier == "own" and word.kind == "neutral"

    def lifts(word):
        return word.kind == "pass" and (word.carrier == "own" or word.carrier == "review" and word.screened)

    def since(word):
        # The time from which the withdrawal for word counts: empty, after each time, when word names no run or time.
        return word.read if word.run and word.read else ""

    found = newest_word(words, until=until, where=withdraws_)
    if found is not None and found.carrier == "check":
        other = newest_word(words, until=until, where=lambda word: word.carrier != "check" and withdraws_(word))
        stands = any(c.get("conclusion") == "success" and withdraws(c, since(found)) for c in checks)
        if other is not None and not outranks(found[:2], other[:2]) or not stands:
            found = other
    if found is None or newest_word(words, until=until, over=found[:2], where=lifts):
        if own == "access-last":
            return "access", "own", "-", started or "-", "-"
        line = newest_word(words, carriers={"line"})
        lifted = line and newest_word(words, carriers={"review"}, over=line[:2], where=lambda word: word.screened)
        return "-", "-", "-", "-", "outranked" if lifted else "-"
    if found.carrier == "own":
        return own, "own", "-", started or "-", "-"
    kind = "owed" if found.carrier == "line" else "held" if found.kind == "hold" else "earlier"
    at = since(found)
    return ("screen" if found.kind == "hold" else found.kind, kind, found.run if at else "-", at or "-", "-")


def owed_why(words, state, why, started="", own=""):
    """The why of the output owed that the decision step writes as soon as it reads from the comments of the item why
    the import check runs of the head are withdrawn: screen for the state held, else why (review_verdict), or "" when
    it reads neither (OSSV-613's architect, round 30, item 1: the shell of that step picks no why). words are the words
    on the head (head_words). own is the verdict of this run's review, which has not posted yet ("" for a relabel,
    which gives no verdict of its own). A blocking finding, the verdict person or a refused review is the own word of
    this run at started (after each time when started is ""), and the step that withdraws reads only the words at or
    before started for it (withdraw_word). So the why is that of the newest of the own word and the words at or before
    started that give the reason: a hold of the screen (screen_hold) for held, and a word of the kind why else. The own
    word is the newest unless a hold of the screen at started outranks it. Any other verdict gives no own word."""
    reason = "screen" if state == "held" else why
    if not reason or own not in VERDICT_WITHDRAWS:
        return reason

    def gives(word):
        return word.carrier == "own" or (screen_hold(word) if state == "held" else word.kind == why)

    mine = Word(started or NEWEST, own, "", "own", own, False, None, None)
    found = newest_word([*words, mine], until=started or None, where=gives)
    return "screen" if found.kind == "hold" else found.kind


# The work of a hold comment, as held.sh holds and replaced_hold and the comment job's label step read it (newest_holds,
# replaced_hold, stays). Each work has hold comments of its own, so that a hold of one work never takes the place of a
# hold of another, and the rescreen pass takes each work again. The work is the task of the marker of a hold that is
# tried again (answer, draft or approve; review for a marker with no task, which a rescreen takes again), else the work
# that its title names (TITLE_WORK: answer, draft for a reply, approve, import or catchup), else review.
HOLD_TASK = re.compile(r"\n<!-- review-held-(?:limit|cap|transient) [0-9]+(?: [0-9]+(?: (answer|draft|approve)"
                       r"(?: [1-9][0-9]*)?)?)? -->(?:\n|$)")
HOLD_TITLE = re.compile(r"<!-- review-held -->\n[*][*]Automated (answer|reply|start of the checks|check for the import"
                        r"|close and reopen) held[.][*][*](?:\n|$)")
TITLE_WORK = {"answer": "answer", "reply": "draft", "start of the checks": "approve", "check for the import": "import",
              "close and reopen": "catchup"}
# The marker of a hold that the rescreen pass tries again, as the label step reads it (stays).
TRIED_AGAIN = re.compile(r"\n<!-- review-held-(?:limit|cap|transient) [0-9]+ ")


def hold_work(body):
    """The work of the hold comment body (HOLD_TASK, HOLD_TITLE)."""
    m = HOLD_TASK.search(body)
    if m:
        return m.group(1) or "review"
    m = HOLD_TITLE.match(body)
    return TITLE_WORK[m.group(1)] if m else "review"


def newest_holds(comments):
    """The newest hold comment of BOT of each work (hold_work) among comments, the item's comments as the API lists
    them (with updated_at), as {work: comment}, in the order of the names of the works (OSSV-613's architect, round 30,
    item 1: held.sh holds and the comment job's label step take the newest hold from the one model, not from when
    GitHub last changed it). A hold counts from its word_time: a hold of the screen from the time when its run read
    the item (HELD_READ), any other hold, or one with no such marker, from its updated_at. Of holds at the same time,
    the later as the API lists them is the newest (newest_word)."""
    found = {}
    for c in comments:
        body = c.get("body") or ""
        if of_bot(c) and body.startswith("<!-- review-held -->"):
            word = Word(word_time(c), "hold", "", "hold", hold_fact(body), False, None, c)
            found.setdefault(hold_work(body), []).append(word)
    return {work: newest_word(found[work]).comment for work in sorted(found)}


def replaced_hold(comments, work, screen, head, started=""):
    """The hold comment of BOT among comments, the item's comments as the API lists them (with updated_at), that a new
    hold of work (hold_work) replaces, or None: then the new hold posts a comment of its own (held.sh replaced_hold, the
    one rule of each writer of a hold comment). screen is True for a new hold of the screen, head is the head that the
    new hold names ("" for none), and started is the time when the trust job of its run read the item ("" for none). A
    hold of the screen (hold_fact screen_held) is replaced only by a new hold of the screen that names the same head
    (HELD_HEAD), or none as it does. Each other hold of work is replaced by any new hold of work. A new hold of the
    screen with a started replaces no hold that counts from a time after started (word_time). Of the holds that the new
    hold may replace, it replaces the newest by the one model of the order of the words (OSSV-613's architect, round 30,
    item 1): a hold of the screen counts from the time when its run read the item (HELD_READ), any other hold, or one
    with no such marker, from its updated_at (word_time), and of holds at the same time the later as the API lists them
    is the newest (newest_word)."""
    found = []
    for c in comments:
        body = c.get("body") or ""
        if not (of_bot(c) and body.startswith("<!-- review-held -->") and hold_work(body) == work):
            continue
        fact, at = hold_fact(body), word_time(c)
        if fact == "screen_held" and not (screen and named_head(body) == head):
            continue
        if screen and started and at > started:
            continue
        found.append(Word(at, "hold", "", "hold", fact, False, None, c))
    newest = newest_word(found)
    return newest.comment if newest else None


def stays(comments, head, started, own, work):
    """(last, tried, stays) of the comment job's label step: the newest hold that stops the labels of this run, and
    whether it outranks the own word of this run, (started, own) (OSSV-221's architect, 2026-11-24 09:43Z, A3, and
    2026-11-25 23:02Z). comments are the item's comments as the API lists them, each with its time as a word in the
    field word (the command words, word_time). head is the head that this run read, or "" for an item with no head
    (an issue). work is the work of this run: review, answer or draft. A hold that stops it is a hold comment of BOT
    of its own head (OSSV-613's architect, round 30, item 1): one that names head (HELD_HEAD, as head_words reads
    it), or one that names no head when head is "" (a hold of an issue names none). Of these, for the work answer
    each one, and for any other work each one but a hold of an answer that is tried again (hold_work, TRIED_AGAIN).
    The line of OWED of head for screen is such a hold too, from its read. Of them, the newest (newest_word). last is
    its time, or "" when there is none or it counts at no time: such a hold stops nothing. tried is True when it is a
    hold comment that is tried again. stays is True when last is not "" and that hold outranks the own word."""
    holds = []
    for c in comments:
        body = c.get("body") or ""
        if of_bot(c) and body.startswith("<!-- review-held -->") and (
                named_head(body) == head
                and (work == "answer" or not (hold_work(body) == "answer" and TRIED_AGAIN.search(body)))):
            holds.append(Word(c.get("word") or "", "hold", "", "hold", hold_fact(body), False, None, c))
    why, run, read = owed_line(comments, head)
    if why == "screen":
        holds.append(Word(*line_word(why, read)[:2], run, "line", why, False, None, None))
    last = newest_word(holds)
    tried = bool(last and last.comment and TRIED_AGAIN.search(last.comment.get("body") or ""))
    if last is None or not last.read:
        return "", tried, False
    return last.read, tried, outranks(last[:2], (started, own))


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
# answer, its comment; the head that the hold names; for a hold of the screen of that head, the time when the trust job
# of its run read the item; and, after it, the id of the run that wrote the hold, which a hold that replaces the comment
# in place writes again.
TRIED = re.compile(r"\n<!-- review-held-(?:limit|cap|transient) [0-9]+(?: [0-9]+(?: ([a-z]+)(?: [1-9][0-9]*)?)?)? -->"
                   r"(?:\n|$)")
HELD_HEAD = re.compile(r"\n<!-- review-held-head ([0-9a-f]{40}) -->(?:\n|$)")
# The time of the marker <!-- review-held-read <time> -->, by which a hold of the screen counts as a word on its head
# (word_time; OSSV-221's architect, 2026-11-24 09:43Z, A3).
HELD_READ = re.compile(rf"\n<!-- review-held-read ({TIME.pattern}) -->(?:\n|$)")
HELD_RUN = re.compile(r"\n<!-- review-held-run ([1-9][0-9]*) -->(?:\n|$)")
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


def named_head(body):
    """The head that the hold comment body names (HELD_HEAD), or "" when it names none."""
    named = HELD_HEAD.search(body)
    return named.group(1) if named else ""


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


def relabel_facts(comments, reviews, head, history, checks=(), run=None):
    """The facts of label_state for head from what the workflow wrote of it, or None when it wrote nothing of it.
    comments are the item's comments as the API lists them (issues/<n>/comments, with updated_at), reviews() gives the
    pull request's reviews (pulls/<n>/reviews), history() the history of head (commits?sha=<head>), each read only
    when the facts need it, and checks the import check runs of head (import_checks). Each word comes from head_words
    and newest_word, in the order of the words on head (OSSV-221's architect, 2026-11-24 01:20Z, 01:26Z, 05:23Z and
    09:43Z, A3, and 2026-11-25 23:02Z): a review comment and a hold comment of the screen count from the time when
    their run read the item, never from when they posted. The review side is the newest word that gives a verdict, of
    a review comment alone, or a refusal, of the line of OWED or of a check run, as review_verdict and newer_word take
    it: at the same place, a refusal comes after a review comment, as head_words lists them (OSSV-613's architect,
    round 30, item 1); and an answer at head whose author said they will make the change, a read from its updated_at.
    A blocking finding or the verdict person of the line or of a check run gives no verdict: the review comment of
    that verdict never posted, so the decision withdrawn says that no comment gives the reason (OSSV-221's architect,
    round 17, part 4, M1, as kept in round 29). The newest hold (a hold comment of BOT that names head, the line of
    OWED for screen, or a check run for screen) that outranks the review side gives its fact (hold_fact, or screen_held
    for the line or a check run); an answer's hold that is tried again gives none. A hold outranks the review side at
    the same time. Else a refusal of the fresh reader, the newest of the review side, gives {"refused": "review"}: the
    state refused-review, in which Sami writes the review by hand (2026-11-25 19:29Z). A refused review posts no
    comment, so the line of OWED for refused or a check run of the reason refused carries it. Else the review side
    gives the verdict (of its newest review comment), will_fix (of that review comment, or of an answer), fix_posted (a
    fix review of head) and fix_stop (a blocking verdict after 2 fix reviews since the author's last own push, the fix
    review of head not counted, as the review job decided it before it posted that fix). With none of them, a label
    comment that holds the conflict-state line of head gives no fact: the head goes back to the workflow, and the line
    goes. run, when given, is the id of the relabel: a relabel gives no word of its own, so no word of that run counts
    (newest_word), such as its own withdrawal of a check run for a word whose run is not known, which counts from the
    time when it withdrew."""
    words = head_words(comments, head, checks)
    said = newest_word(words, kinds={"pass", "blocking", "person", "refused"}, carriers={"review", "line", "check"},
                       run=run, where=lambda word: word.carrier == "review" or word.kind == "refused")
    answers = [Word(word_time(c), "read", "", "answer", "will-fix", False, None, c) for c in comments
               if of_bot(c) and (m := ANSWER_WILL_FIX.match(c.get("body") or "")) and m.group(1) == head]
    side = newest_word([*answers, *([said] if said else [])])
    hold = newest_word(words, kinds={"hold"}, carriers={"hold", "line", "check"}, run=run,
                       over=side[:2] if side else ("", "read"), where=lambda word: word.why)
    if hold:
        return {hold.why if hold.carrier == "hold" else "screen_held": True}
    if side is None:
        conflicted = any(of_bot(c) and (c.get("body") or "").startswith(FIRST)
                         and conflict_state(head) in (c.get("body") or "").split("\n") for c in comments)
        return {} if conflicted else None
    if side is said and said.kind == "refused":
        return {"refused": "review"}
    verdict = said.kind if said and said.kind != "refused" else ""
    will_fix = bool(answers) or bool(
        verdict and said.carrier == "review" and REVIEWED.match(said.comment["body"]).group(3))
    found = reviews()
    heads = fix_heads(found)
    own = heads.count(head)
    fix_stop = (verdict == "blocking" and not will_fix and len(heads) - own >= 2
                and fixes(history(), found, head) - own >= 2)
    return {"verdict": verdict, "will_fix": will_fix, "fix_posted": own > 0, "fix_stop": fix_stop}


def json_lines(path):
    """The JSON object on each line of the file path (an answer of the API, one on each line), with loads."""
    with open(path, encoding="utf-8") as f:
        return [loads(line) for line in f if line.strip()]


def check_lines(path):
    """The check runs of the file path, one JSON object on each line (json_lines), as the post job's steps read them:
    {id, conclusion, completed_at, summary[, text]}. A ValueError when a line is not an object."""
    checks = json_lines(path)
    if not all(isinstance(c, dict) for c in checks):
        raise ValueError(f"{path} holds a line that is not a check run")
    return checks


def stdin_comments():
    """The comments on standard input, one JSON object on each line, as the API lists them (with loads). A ValueError
    when a line is not an object."""
    comments = [loads(line) for line in sys.stdin if line.strip()]
    if not all(isinstance(c, dict) for c in comments):
        raise ValueError("a line of standard input is not a comment")
    return comments


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
            facts, markers, head, given = parse(argv[2:], RUN + ("owed", "withdrawn", "own"))
            if facts or markers or head:
                raise ValueError("owed takes task=, outside=, outsider=, author=, owed=, withdrawn= and own= alone: "
                                 "no fact, no head= and no marker=")
            owed, withdrawn, own = given.pop("owed"), given.pop("withdrawn"), given.pop("own")
            if own not in ("", "true", "false"):
                raise ValueError(f"own is true, false or empty, not {own!r}")
            line = owe(argv[1], given, owed, withdrawn, own == "true")
            if not line:
                return 0
            output = os.environ.get("GITHUB_OUTPUT")
            if output:
                with open(output, "a", encoding="utf-8") as f:
                    f.write(f"line={line}\n")
            return 3
        if len(argv) == 3 and argv[0] == "hold-head" and NUMBER.fullmatch(argv[1]):
            return 0 if held_head(argv[1], argv[2]) else 3
        if len(argv) == 2 and argv[0] == "unclaim" and NUMBER.fullmatch(argv[1]):
            unclaim(argv[1])
            return 0
        if len(argv) >= 6 and argv[0] == "log" and len(argv) % 2 == 0:
            names = argv[6::2]
            if len(set(names)) != len(names):
                raise ValueError(f"a field of the decision log twice: {names}")
            print(decision_log(*argv[1:6], dict(zip(names, argv[7::2]))))
            return 0
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
        if len(argv) in (11, 12) and argv[0] == "import-check":
            path, count, number, head, screen, verdict, hold, run, read, request = argv[1:11]
            value = argv[11] if len(argv) == 12 else None
            if not (re.fullmatch(r"0|[1-9][0-9]*", count) and NUMBER.fullmatch(number) and HEAD.fullmatch(head)
                    and screen in ("true", "false")):
                raise ValueError("not a count of changed files, a pull request number, a head commit and true or false "
                                 "for the screen")
            decision = import_decision(json_lines(path), int(count), screen == "true", verdict, hold == "true", value)
            if decision == "record":
                with open(request, "w", encoding="utf-8") as f:
                    json.dump(check_run(number, head, value, hold == "true", "" if run == "-" else run,
                                        "" if read == "-" else read), f)
            print(decision)
            return 0
        if len(argv) in (2, 3) and argv[0] == "import-marker":
            print(import_marker(argv[1], argv[2] if len(argv) == 3 else None))
            return 0
        # The last two arguments of verdict, own=<verdict> and started=<time>, when it is given them (by_hand).
        mine = argv[-2:] if (len(argv) in (5, 6) and argv[-2].startswith("own=")
                             and argv[-1].startswith("started=")) else []
        if (len(argv) - len(mine) in (3, 4) and argv[0] == "verdict" and NUMBER.fullmatch(argv[1])
                and HEAD.fullmatch(argv[2])):
            own, started = (mine[0][len("own="):], mine[1][len("started="):]) if mine else ("", "")
            if started and not TIME.fullmatch(started):
                raise ValueError(f"not a time as GitHub gives it: {started!r}")
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body, updated_at} | @json")
            checks = check_lines(argv[3]) if len(argv) - len(mine) == 4 else []
            verdict, state, why = review_verdict(comments, argv[2], checks)
            words = head_words(comments, argv[2], checks)
            # The run of the newest review comment and the time when that run read the item, from its last two
            # markers (REVIEW_READ), or neither when it has none: a relabel's record names them.
            newest = newest_word(words, carriers={"review"})
            body = newest.comment["body"] if newest else ""
            named = newest and REVIEW_READ.match(body, REVIEWED.match(body).end())
            record_run, record_read = (newest.run, newest.read) if named else ("", "")
            line_why, line_run, line_read = owed_line(comments, argv[2])
            origin = "-"
            if state != "held" and line_why:
                origin = "owed" if owed_reason(comments, argv[2]) else "outranked"
            posted = "-"
            if origin == "owed":
                found = line_reason(comments, argv[2], line_why, line_run, line_read, True)[0]
                posted = "posted" if found else "unposted"
            stands = standing_withdrawal(words)
            stood, since = (str(stands.check.get("id") or "-"), stands.read or "") if stands else ("", "")
            reply = (f"{verdict or '-'} {state} {why or '-'} {origin} {posted} {stood or '-'} {since or '-'} "
                     f"{record_run or '-'} {record_read or '-'}")
            print(f"{reply} {owed_why(words, state, why, started, own) or '-'}" if mine else reply)
            return 0
        if (len(argv) == 6 and argv[0] == "own-record" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2])
                and TIME.fullmatch(argv[3]) and NUMBER.fullmatch(argv[4])):
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body, updated_at} | @json")
            found = own_record(check_lines(argv[5]), comments, argv[2], argv[3], argv[4])
            print(" ".join(part or "-" for part in found))
            return 0
        if (len(argv) in (5, 6) and argv[0] == "newer-word" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2])
                and TIME.fullmatch(argv[3]) and NUMBER.fullmatch(argv[4]) and all(k in RANKS for k in argv[5:])):
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body, updated_at} | @json")
            found = newer_word(comments, argv[2], argv[3], argv[4], *argv[5:], checks=import_checks(argv[1], argv[2]))
            print(" ".join(part or "-" for part in found) if found else "-")
            return 0
        if (len(argv) == 4 and argv[0] == "relabel-withdraws" and NUMBER.fullmatch(argv[1])
                and HEAD.fullmatch(argv[2])):
            comments = json_lines(argv[3])
            if not all(isinstance(c, dict) for c in comments):
                raise ValueError(f"{argv[3]} holds a line that is not a comment")
            _verdict, state, why = review_verdict(comments, argv[2], import_checks(argv[1], argv[2]))
            owed = state != "held" and owed_reason(comments, argv[2]) != ""
            print(f"{why} owed" if owed else why or "-")
            return 0
        if len(argv) == 1 and argv[0] == "words":
            for line in sys.stdin:
                if line.strip():
                    c = loads(line)
                    if not isinstance(c, dict):
                        raise ValueError("a line of standard input is not a comment")
                    print(json.dumps(dict(c, word=word_time(c)), ensure_ascii=False))
            return 0
        if len(argv) == 1 and argv[0] == "holds":
            comments = stdin_comments()
            for work, c in newest_holds(comments).items():
                print(json.dumps(dict(c, work=work), ensure_ascii=False))
            return 0
        # <started> is compared as text with the time of each hold (word_time): the hold job stops a hold of the screen
        # whose STARTED is not a time before it calls replaced_hold, and halt gives none.
        if (len(argv) == 5 and argv[0] == "replaced-hold" and (argv[1] == "review" or argv[1] in TITLE_WORK.values())
                and argv[2] in ("true", "false") and (HEAD.fullmatch(argv[3]) or argv[3] == "-")):
            comments = stdin_comments()
            found = replaced_hold(comments, argv[1], argv[2] == "true", "" if argv[3] == "-" else argv[3],
                                  "" if argv[4] == "-" else argv[4])
            if found is not None:
                if not NUMBER.fullmatch(str(found.get("id"))):
                    raise ValueError(f"a hold comment has no id: {found.get('id')!r}")
                print(found["id"])
            return 0
        if (len(argv) == 5 and argv[0] == "outranks" and all(TIME.fullmatch(t) or t == "" for t in argv[1::2])
                and all(k in RANKS for k in argv[2::2])):
            return 0 if outranks((argv[1], argv[2]), (argv[3], argv[4])) else 3
        if (len(argv) == 10 and argv[0] == "withdraw-word" and NUMBER.fullmatch(argv[1]) and HEAD.fullmatch(argv[2])
                and (TIME.fullmatch(argv[3]) or argv[3] == "-") and NUMBER.fullmatch(argv[4]) and argv[5] in TASKS
                and argv[7] in KINDS):
            comments = gh_objects("--paginate", f"repos/{os.environ['REPO']}/issues/{argv[1]}/comments", "--jq",
                                  f".[] | select(.user.login == {json.dumps(BOT)})"
                                  " | {user: {login: .user.login}, body, updated_at} | @json")
            started = "" if argv[3] == "-" else argv[3]
            own = own_word(*argv[5:9])
            print(" ".join(withdraw_word(comments, argv[2], check_lines(argv[9]), started, argv[4], own)))
            return 0
        if (len(argv) == 5 and argv[0] == "stays" and (HEAD.fullmatch(argv[1]) or argv[1] == "-")
                and TIME.fullmatch(argv[2]) and argv[3] in RANKS and argv[4] in ("review", "answer", "draft")):
            comments = stdin_comments()
            last, tried, stay = stays(comments, "" if argv[1] == "-" else argv[1], argv[2], argv[3], argv[4])
            print(f"{last or '-'} {str(tried).lower()} {str(stay).lower()}")
            return 0
        if len(argv) == 10 and argv[0] == "withdrawal":
            number, head, why, kind, run, source, at, path, directory = argv[1:]
            for check in json_lines(path):
                if not (isinstance(check, dict) and NUMBER.fullmatch(str(check.get("id")))
                        and isinstance(check.get("text"), str)):
                    raise ValueError(f"not a check run with its id and its output text: {check!r}")
                if not withdraws(check, "" if at == "-" else at):
                    continue
                read = (recorded_by(check) or ("", ""))[1]
                with open(os.path.join(directory, f"withdraw-{check['id']}.json"), "w", encoding="utf-8") as f:
                    json.dump(withdrawal(number, head, why, check["text"], run, kind, "" if source == "-" else source,
                                         "" if at == "-" else at, read), f)
                print(check["id"])
            return 0
        if len(argv) in (7, 8) and argv[0] == "not-approved":
            number, head, why, run, at, request = argv[1:7]
            body = not_approved(number, head, why, argv[7] if len(argv) == 8 else None, run, at)
            with open(request, "w", encoding="utf-8") as f:
                json.dump(body, f)
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
            comments = read_comments(number)
            found = relabel_facts(
                comments,
                lambda: gh_objects("--paginate", f"repos/{repo}/pulls/{number}/reviews", "--jq", ".[] | @json"),
                head, lambda: gh_objects(f"repos/{repo}/commits?sha={head}&per_page=100", "--jq", ".[] | @json"),
                import_checks(number, head), os.environ.get("GITHUB_RUN_ID") or None)
            if found is None:
                print(f"#{number}: the workflow wrote nothing of {head}, so the labels stay.")
                return 0
            both = sorted(set(found) & set(facts))
            if both:
                raise ValueError(f"relabel reads these facts itself: {', '.join(both)}")
            facts.update(found)
            # The comments that apply would read again: nothing between the two reads writes a comment.
            set_state(number, run, facts, markers, head, comments)
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
