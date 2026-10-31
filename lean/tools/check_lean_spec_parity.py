#!/usr/bin/env python3
"""A Lean spec twin keeps every Rocq definition, or registers it as unported,
and its baseline names the Rocq tree it really was read from.

`theories/LinuxProcessSem/Sys/**/*.v` are the syscall specs and the source of
truth; `lean/LinuxProcessSemantics/LinuxProcessSem/Sys/**/*.lean` are their
Lean twins, mirrored by path and name (lean/README.md, "Translation
decisions"). A twin's header says "Mirrors `theories/.../X.v`", and nothing
read that sentence. A twin can carry every definition of its Rocq file but
one, and the Lean build stays green -- the dropped definition is simply not
there to fail -- while the Rocq build never reads the Lean tree at all. Ported
by many agents in parallel, each holding one file, a port narrowed that way is
narrowed silently, and the narrowing is exactly what would make a Lean theorem
about the spec say less than the Rocq one it claims to mirror.

The omission cannot be seen from one side alone. Listing the Lean file shows
every definition it has and agrees with itself; listing the Rocq file shows
what there is to port and nothing about what was. So this reads both and
compares the names: every top-level Rocq `Definition`, `Fixpoint`,
`CoFixpoint`, `CoInductive`, `Record`, `Inductive`, `Variant` and
`Abbreviation`, and lemma keywords closed with `Defined.` -- and
each `with` continuation of a mutual block -- must be
a top-level Lean `def`, `abbrev`, `structure`, `inductive`, `coinductive`,
`theorem`, `instance`, `class` or `opaque` -- compared on the last
component, so `def InputStream.uncons` is `uncons` -- or be registered as
unported, in the twin itself, with a reason.  `coinductive` is Lean's own
keyword for a coinductive predicate, and it is how `OmniRun.lean` carries
Rocq's `CoInductive coexec` and `cosafe`: a reader without it reports both
as missing from a twin that has them.

Section `Let` bindings are closure nodes only: Rocq inlines them when the
section closes, so Lean may inline them too. Their bodies are still hashed
in every user's dependency closure, but they impose no name obligation.

Held with the specs are the model files a spec is written against, the
run semantics a statement is written against (`ROCQ_EXTRA` below), and the
statement tree `theories/EquivalenceDefinition/**/*.v`, whose twins live
under `lean/LinuxProcessSemantics/EquivalenceDefinition/`. Statement keys
are relative to the same bases as the other twins: for example,
`../EquivalenceDefinition/Equivalence.v` and
`../EquivalenceDefinition/Equivalence.lean`. A Rocq file with no Lean twin
is skipped; an empty statement tree adds no coverage. A
whole-program theorem quantifies over `Run.valid_input` and unfolds
`Run.sstep`, so a `Run.lean` missing one of Run.v's definitions -- a stance
such as `valid_input_abort`, a run form such as `run_scfg` -- leaves every
statement over it unstatable, as silently as a dropped arm narrows a spec.
(A dropped rule of `sstep` or clause of `valid_input` is inside a name and
beyond this check; see WHAT NAME MATCHING DOES NOT SAY.)

Three rules make a name count as a twin's definition and a register entry
count as a reason, because without them a twin can be green while holding
nothing (docs/lean-port/ADVERSARIAL.md, D1):

  PAR-VISIBLE  a Lean declaration is the twin's only when it is not
               `private` and its full name lies under the twin's own
               module namespace -- `LinuxProcessSemantics.LinuxProcessSem.
               Sys.Mm.Mmap` for `Sys/Mm/Mmap.lean`, and the same one for
               each of the twin's parts (`Sys/Uapi/Fs.lean` declares in
               `…Sys.Uapi`).  A `private def mmap_spec` is unreachable from
               the table and the pins; a `def mmap_spec` in a foreign
               `namespace Scratch` is another definition that happens to
               share a name.  Both matched a Rocq name by its last
               component before this rule.  A sub-namespace of the twin's
               (`…Sys.Syscall.SyscallInput.foo`) is inside and counts;
               `protected` is visible and counts.  Namespaces are tracked
               through `namespace`/`section`/`mutual` and their `end`s on
               the comment-blanked text, and a modifier on a line of its
               own (`private` above `def walk`) is read with the
               declaration it precedes, as Lean reads it.
  PAR-REASON   an `unported:` or `partial:` reason has at least three words of two or
               more letters.  `unported: x -- .` registered every
               definition of a header-only twin before this rule; three
               words is a floor under a sentence that says what is missing
               and why, not a judgement of one.  It is a rule on the tree
               at the head: tools/check_lean_test_monotonic.py reads the
               same headers at the merge base through `parse_header` with
               `strict_reason=False`, so a base that predates this rule is
               read and compared, not refused.
  PAR-REACH    a spec the ROCQ table dispatches is reached by the port or
               registered with the number it declines.  For each arm of
               `theories/…/Sys/SyscallTable.v` whose spec the Rocq file
               defines, the claiming twin either defines that spec as a
               visible `def` at exactly the twin's namespace (the table
               opens that namespace and names the spec unqualified), or
               its `unported:` entry for the spec names the arm's number
               (`brk_spec -- brk (214) is not ported`), and the port
               registers no arm for that number.  The Rocq table is read
               through `strip_rocq_comments`; an absent or empty one is an
               error, since PAR-REACH over no arms holds nothing, and so is
               a registry `gen_lean_registry.registry_arms` refuses.
               The rule does not require a defined dispatched spec to HAVE
               a Lean arm: a twin may define `dup_spec` before its registry
               file lands, the table then declines the number honestly and
               the board shows it todo.  The OTHER direction -- a Lean arm
               dispatching the spec its Rocq arm does, spelled
               `Sys.<Mirror>.<name>_spec` and defined non-`private` by that
               twin -- is not restated here: it is REG-3 in
               `tools/gen_lean_registry.py`, which refuses the arm at the
               registry line and runs in the required `generated-docs`
               context, where this check does not.

A twin may be one Lean file or several. `Sys/Uapi.lean` re-exports
`Sys/Uapi/{Fs,Net,...}.lean`, split by subsystem so that a spec PR edits its
own subsystem's constants and never a shared file, and `State.lean`
re-exports `State/{Geometry,Errno,...}.lean` the same way; the Rocq side is
still the one `Sys/Uapi.v`, the one `State.v`. So a Lean file under `X/` that
mirrors no Rocq file is a PART of the twin `X.lean` when that twin imports
it, and the twin's definitions are the union over the twin and its parts.
This holds for every twin under `Sys/` and for the base twins ROCQ_EXTRA
names, and for statement twins, whose parts likewise live in the directory
beside the twin. Only the twin's own imports are read: a part's imports are not followed, so a part that
itself re-exports is not seen through. The claim below lives on the twin.
A part may repeat the header with the same baseline.
Its `unported:`, `partial:` and `drift-ticket:` entries join the twin's registers.
A part may also omit the header.
The checker rejects a name registered or ticketed twice within one twin.
A part that claims while the twin does
not is an error, because the claim would otherwise be read by nothing. A
file under `X/` that the twin does not import mirrors nothing and fails, as
it would without the twin.

One directory under Sys/ mirrors nothing by design: `Sys/Registry/` holds the
syscall table's registration files, one per twin, from which
`tools/gen_lean_registry.py` renders the syscall table and its pins.
They define no twin's names -- the generator refuses any line that is not an
arm -- and they are imported through a module Lake generates rather than by
the twin, so the part rule above cannot see them.  They are skipped here and
held by that tool's `--check` instead.  The skip is the directory, not the
name: a source file `Sys/Registry.lean` is a twin of nothing and fails as
one, and a registry file that carries the parity header is an error, for
the reason a claiming part under an unclaiming twin is -- a claim nothing
reads is not a claim.

A twin CLAIMS parity with a header block near its top, spelled exactly:

    /-! rocq-baseline: <40-hex commit>
    drift-ticket: <name> <ticket> -- <reason>
    rocq-reread: <name | file.v:name> <64 lowercase hex> -- <reason>
    unported: <name> -- <reason>
    partial: <name> -- <reason> -/

The `unported:`, `partial:`, `drift-ticket:` and `rocq-reread:` lines are optional.
The commit names the Rocq tree the twin read.
The block must START within the first 4096
bytes of the file, after the imports and before the prose: the whole file is
searched for the tag, and a tag found only beyond that window is an error
rather than a claim, so a header that drifted down under a growing preamble
is reported rather than silently becoming no claim. Only the start is held
to the window -- the register may run past it, one line per name, however
many names a file leaves unported -- and the window is measured in bytes of
the file's UTF-8, which is what a reader counting from the top of the file
sees. A mis-spelt tag (`Rocq-Baseline:`, `rocq_baseline:`) is refused by
name rather than read as no claim, for the same reason.

A `partial:` marker names a ported definition that declines some shapes.
Both twins must define that name, and the Lean definition must satisfy PAR-VISIBLE.
The marker keeps the definition in parity and drift checks.
A drift-ticket can name the same definition.
Strict mode applies PAR-REASON to its reason.
A name cannot repeat across either marker kind, including across parts.
Only the baseline header registers these markers.

For a claiming twin, every Rocq name is a Lean name or an `unported:` entry,
and every `unported:` entry names a Rocq definition -- an entry for a name
the Rocq file no longer has is stale and fails too, because a register that
outlives what it registers is the same silence in the other direction. An
entry for a name the Lean file DOES define is reported as well: the port
landed and the register still says it did not. A name registered twice, in
one header or across a twin and its parts, is an error.

A TWIN WITHOUT THE HEADER IS AN ERROR UNLESS `UNCLAIMED_ALLOWED` NAMES IT.
An unclaimed twin is not measured at all: with no baseline there is nothing
to resolve, so the run stops before the name comparison and before the
closure, and every rule above is vacuous on that file -- which is how the
Exit and Namei twins merged, complete but unmeasured, while this check
listed them and passed. Silence there is the one direction that matters, so
the header BRIEF.md section 3 makes mandatory is required here: an unclaimed
twin fails, by path, saying to add the header. The exceptions are the list
below, one entry per twin no PR may hand-write a header into today, each
with the reason and who owes the claim.
Two staleness rules make an entry cost something, both the mirror of the
`unported:` register's:

- an entry whose twin CLAIMS parity is an error -- the claim landed and the
  excuse outlived it, so removing the line is part of claiming;
- an entry that names no twin in the tree is an error -- a renamed file or a
  mistyped path would otherwise excuse nothing while reading as coverage,
  and it is what stops the list from silently becoming the whole Lean side:
  a tree with the twins deleted, the shape that makes every rule above
  vacuous, fails here rather than passing with nothing read. That last
  reading is only as wide as the list: a twin deleted with NO entry for it
  is skipped here, as a Rocq file with no twin always was, so this cover
  shrinks as the list does and is gone once the list is empty. What a
  deleted twin costs beyond this check -- the pins, arms and imports that
  stop compiling -- is the Lean build's answer, not one to read here.

The same rule is what closes the hole docs/lean-port/REDTEAM.md's H10
measured against the earlier one, under which an unclaimed twin was listed
and not an error. A twin nobody has ported and a twin that DELETED its
header are the same tree here, and both passed, so the deletion dropped
every `unported:` obligation above while this check stayed green; now both
fail. What this still cannot see is a twin deleted whole with no entry for
it, skipped above as a Rocq file with no twin always was. Both deletions
are refused where the difference exists, in the PR: the HEADER rule of
tools/check_lean_test_monotonic.py compares the head against the merge
base that still carried the header.

The list only ever shrinks. Nothing in this file can enforce that -- a
constant cannot see its own history -- so the test holds the seed it landed
with as a literal and requires this list to be a subset of it: a name leaves
it in the PR that gives the twin its header -- a `lean: base:` PR for a
frozen twin, the generator change for the table; no plan ticket owns those
PRs today -- and adding one fails the test that nobody may add.

THE BASELINE IS VERIFIED ON EVERY RUN. The header's commit is a claim about
what the porter read, and until this check handed it to git nothing read it
back: a fabricated sha, a sha this clone never fetched, a commit at which the
mirrored file did not yet exist, and a commit off on a side branch all
passed, because name comparison needs no commit at all. So for each claiming
twin the commit must (1) resolve to a commit object in this repository, (2)
be an ancestor of HEAD, and (3) carry the mirrored Rocq file. Each failure is
reported by name and fails the run. A repository git cannot answer for at all
-- no `.git`, no HEAD -- is an error rather than a pass, for the same reason:
a claim nothing can check must not count as checked. CI therefore runs this
on a full checkout (`fetch-depth: 0`): a shallow clone lacks the baseline
commit and fails here by design instead of skipping the question.

WHICH COMMITS SURVIVE THAT TEST. A day lands on `main` through GitHub's
rebase or squash merge (`.agents/skills/nightly-integrate`; #794's hundred
commits are the one commit a71fd38a), both of which rewrite every commit
they land, so once the day integrates no day-branch sha is an ancestor of
`main`, while the day ref stays on origin and its commits still RESOLVE in
a full clone. A header naming a day-branch commit therefore passes (1) and (2) on
every run of its own day -- the PR's merge ref and the day branch both
contain it -- and fails (2) on the first push to `main` and on every PR of
the next day, which is cut from `main`. Since this check gates the merge
(the `generated-docs` context), that is the next integration blocked by a
twin nobody touched. So name a commit on `main` whenever the Rocq you read
is there; when the Rocq you ported exists only on the day branch, name the
day tip and move the header to the landed commit when the day integrates.
A PR-branch commit is never right: the squash that lands the PR rewrites
it and nothing keeps its ref.
A PR that changes a Rocq definition and its twin together keeps the baseline and adds a `rocq-reread:` line for each changed member.
A squash keeps the content, not the commit, so the pin survives the merge.

DRIFT IS PER DEFINITION, OVER THE TWIN'S CLOSURE, AND ALWAYS ON. The question
the baseline exists to answer is whether the Rocq the twin mirrors has moved
since it was read, and name comparison cannot see it: a changed body with the
same name passes every time. Two earlier shapes of the answer were wrong in
opposite directions. Diffing the twin's own Rocq file fires on a comment
edit -- prose is most of what changes -- and is blind to `State.v`, the most
edited Rocq file, whose twin was unclaimed when that shape was written and
whose records every spec is written against. So this reads DEFINITIONS, not
files, and follows USE, not path:

- The twin's CLOSURE is every Rocq definition a ported definition reaches
  through tools/specdeps.py's dependency graph, built over the checkout and
  restricted to the files held to parity: `Sys/**`, `ROCQ_EXTRA`, and the
  statement tree (a dependency through a file outside that set is cut
  there). The graph includes statements and run semantics, so a statement
  reaches the run definitions it uses, and those reach `State.v`: a `ProcInput`
  field added under `Run.valid_input` is `Run.lean`'s drift, as it should
  be, and their baselines have to be read where `State.v` was. The seeds are the twin's Rocq file's
  definitions minus its `unported:` register -- a definition the twin says
  it did not port cannot drift under it -- and an unported definition still
  joins the closure when a ported one reaches it. A closure is never empty:
  every seed is in it, so a twin that ports anything is measured against
  something. A definition specdeps does not read (`CoInductive`,
  `Abbreviation`; its parser predates both) is hashed but its own
  dependencies are not followed, which is the one gap in the closure and is
  named here rather than closed by a second parser.
- Each closure member's BODY is its whole Rocq sentence with comments
  stripped and runs of whitespace collapsed, read at the baseline commit
  (`git show <baseline>:<file>`) and in the checkout, and the two are
  compared by hash. A comment-only or whitespace-only edit therefore does
  not fire (the one whitespace this cannot see is inside a string literal);
  a changed constant, a reordered gate, a new argument does, and it is
  reported by the name of the definition that changed, against every twin
  whose closure reaches it -- a `State.v` change under a spec is that spec's
  drift. A mutual block shares one sentence and hash across its names, but
  each reached identity needs its own acknowledgement.
  A member present in the checkout and absent at the baseline
  was added since, and is drift too. A member whose body this cannot read
  at all is an error, not a pass: the graph saw a definition the body reader
  did not, and the direction of that mistake is the vacuous one.
- A `rocq-reread:` line pins one closure member to its head body hash.
  The hash uses SHA256 over the normalized sentence.
  The member leaves `drifted` when the pin matches and its body differs from the baseline.
  A member absent at the baseline can use a reread.
  A stale pin reports drift with both hashes.
  A pin at the baseline body refuses and asks for a Lean rollback or a baseline move.
  Unknown keys, ambiguous bare names, and duplicate identities refuse.
  Tickets and rereads resolve against the same complete closure.
  A proof-mode member without a definition-body `:=` refuses because the reader measures only its statement.
  A reread line is a claim that someone read the Rocq at that hash and checked the Lean twin, the same trust as a baseline move.
  The existing gaps remain: whitespace inside string literals, a separate Notation, and dependencies specdeps does not follow.
- A drifted definition without a ticket fails the run.
  Re-read the Rocq, port the difference, and move the baseline or add a reread.
  To defer the port, file a ticket and name it in the header:

      drift-ticket: <name> <ticket> -- <reason>

  `<name>` is the drifted definition, or `<file>.v:<name>` (the file relative
  to `theories/LinuxProcessSem/`) when the bare name reaches two definitions
  in the closure; `<ticket>` is a ticket id of docs/lean-port/data/plan.json,
  such as `S-Fs-Sync`. The line silences exactly the one definition it names
  -- two lines reaching one definition, bare and qualified, in one header or
  across the twin and its parts, are an error, since the later reason would
  otherwise win silently -- and is an error when that definition has NOT
  drifted -- a ticket outliving
  its drift would excuse the next one in advance -- when no definition in the
  closure carries the name, when the ticket is not in the plan, when the
  ticket's plan node does not PROVIDE the drifted definition, and when
  docs/lean-port/data/progress.json says the ticket is `done`: a re-port that
  was finished and left the line behind is the same silence as a stale
  register entry. Ownership is the plan's `provides` list, which spells a
  definition `<file>.v:<name>` and a whole file `file:<file>.v`, and it is
  the condition that makes the line cost something: a live ticket of the
  plan is easy to find, and one that does not own the definition will never
  re-port it, so naming it silences the drift while leaving nobody owing the
  work -- which is how a drift is laundered through an unrelated ticket. A
  ticket the plan cannot be read for (no plan.json under
  `--root`) is an error, not a pass. #748's file-level `drift-ticket: #N --
  <reason>` line is retired and is refused by name: it silenced every future
  change to the file, which is the loophole a per-name register closes, and
  a GitHub number is nothing this can check offline for "done". No twin in
  the tree carried one.

`--drift` and `--strict` are accepted and do nothing: the check they used
to switch on is always on, and the briefs and the PR template that name them
still run. `--json` prints, per Rocq file with a twin, {rocq_defs, lean_defs,
parts, missing, stale_unported, registered_and_defined, unported, baseline,
baseline_ok, closure, drifted, drift_tickets, reread, claimed}.
`closure` contains [{file, name}].
`drifted` means changed since the twin last read the member: at its baseline, or at its reread pin.
Each drift record contains {file, name, change, baseline_hash, head_hash, ticket, reason}.
`reread` contains accepted pins as [{file, name, hash, reason}].

WHAT NAME MATCHING DOES NOT SAY. A Lean `def read_spec` beside a Rocq
`Definition read_spec` proves the name was carried over and nothing about
what it means: a body ported wrong, an argument dropped, an `unmodeled` arm
that became an answer, all pass here. That is the equivalence pilot's
question (lean/README.md), not this one. This check is the floor under it --
a definition that is not there cannot be compared at all -- and it is a
floor, not the comparison. The drift half says only that the Rocq moved
under the twin, never that the twin was right before it moved.

Rocq comments are stripped before names are read, with the nesting-aware
reader copied from tools/check_kernel_citations.py's `v_comments`; Lean `--`
and nested `/- -/` comments likewise, EXCEPT the header block, which is read
from the raw text before stripping because it is a comment. The Rocq reader
also lexes string literals in code, because the direction of the mistake
matters: a `(*` inside a literal, taken as a comment opener, would blank
everything up to the next unmatched `*)` -- every Definition in between goes
unread on the Rocq side, so the twin is asked for LESS and PASSES. That is
the vacuous direction, so a literal in code containing `(*` or `*)` is an
error, not a guess. Inside a comment, strings are not lexed -- prose quotes
need not pair -- but a comment delimiter that follows an odd number of `"`
in its comment is ambiguous under either reading and is an error too. The
body reader splits sentences with the same string lexing, so a `. ` inside
a literal does not end a sentence early and leave its tail unhashed;
specdeps' own splitter is not reused for that reason, it blanks literals.
"""
import argparse
import functools
import hashlib
import json
import os
import posixpath
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lean_cases_family as cases_family  # noqa: E402
import specdeps  # noqa: E402

ROCQ_BASE = "theories/LinuxProcessSem"
LEAN_BASE = "lean/LinuxProcessSemantics/LinuxProcessSem"
ROCQ_TABLE = "theories/LinuxProcessSem/Sys/SyscallTable.v"
LEAN_REGISTRY = "lean/LinuxProcessSemantics/LinuxProcessSem/Sys/Registry"
# One Rocq arm, comments already blanked: `mkSpecArm 222%Z (fun i => mmap_spec …`.
ROCQ_ARM = re.compile(r"\bmkSpecArm\s+(\d+)%Z\s*\(\s*fun\s+\S+\s*=>\s*([A-Za-z_][\w']*)")
# PAR-REASON counts words of two or more letters for both decline markers.
REASON_WORD = re.compile(r"[A-Za-z]{2,}")
REASON_WORDS = 3
# Alongside the statement tree, the held Rocq files are everything under Sys/, the
# model files a spec is written against, and the run semantics a statement
# is written against -- Run.v and OmniRun.v, with StackLayout.v and
# RiscvSemantics.v that Run.v's initial configuration and step stand on.
# Sys/Syscall.v, Sys/Uapi.v and Sys/Uaccess.v are under Sys/ already.  The
# drift closure is restricted to the same set.  Run.v also stands on
# MemImageType.v and Specs.v; neither is held.  Holding a file is a decision
# made here and pinned by the test's Specs.v case, not something a file earns
# by being imported: those two twins carry every name today, and the ticket
# that gives each a header widens this tuple.
ROCQ_SUBTREE = "Sys"
ROCQ_EXTRA = ("State.v", "Monad.v", "Fs.v", "BvBase.v",
              "Run.v", "OmniRun.v", "StackLayout.v", "RiscvSemantics.v")
# Statement keys use the plan's spelling relative to ROCQ_BASE / LEAN_BASE.
STATEMENTS_REL = "../" + specdeps.STATEMENTS_TREE

PLAN_JSON = "docs/lean-port/data/plan.json"
PROGRESS_JSON = "docs/lean-port/data/progress.json"
# The syscall table's registration files (tools/gen_lean_registry.py): not
# twins, not parts, held by that tool's --check; see the docstring.
REGISTRY_DIR = "Sys/Registry/"

# The twins allowed to carry no `rocq-baseline:` header, keyed by the path
# below LEAN_BASE, with the reason each cannot have one written today.  This
# list only shrinks: a name leaves it in the PR that gives the twin its
# header, and the test holds the seed as a literal so that nothing may be
# added.  Every entry here is a twin no PR may hand a header to today -- two
# of the frozen files of tools/check_lean_port_scope.py's FROZEN, which only
# a `lean: base:` PR edits -- so the seed is not a backlog of skipped work
# but the set of files whose header is somebody else's PR, and no plan
# ticket owns any of those PRs today.  The generated table left the list
# with T31 rather than earning a header: it is no longer a source file, so
# there is no twin here to claim parity, and what holds its contents to
# Rocq's `spec_table` is `tools/gen_lean_registry.py` -- which reads the
# Rocq table fail-closed and renders ONE LINE PER ROCQ ARM -- with
# `check_lean_table_wiring.py` comparing each arm's wiring and
# `check_syscall_docs.py` the numbers and labels.
UNCLAIMED_ALLOWED = {
    "BvBase.lean":
        "frozen (check_lean_port_scope.py FROZEN); the header arrives with a "
        "`lean: base:` PR, as ticket A14's did for Run.lean and OmniRun.lean. "
        "No plan ticket owns it: A3 and A4, which ported into it, are done.",
    "Sys/Dispatch.lean":
        "frozen (check_lean_port_scope.py FROZEN); the header arrives with a "
        "`lean: base:` PR. Ticket K2 rewrites the CHECKER's dispatcher, "
        "Checks/Sys/Dispatch.lean, not this twin.",
}

ROCQ_KEYWORDS = ("Definition", "Fixpoint", "CoFixpoint", "CoInductive",
                 "Record", "Inductive", "Variant", "Abbreviation") + specdeps.LEMMA_KEYWORDS
ROCQ_PREFIX = r"^\s*(?:Program\s+|Local\s+|Global\s+|#\[[^\]]*\]\s*)*"
ROCQ_DEF = re.compile(
    ROCQ_PREFIX + r"(%s)\s+([A-Za-z_][A-Za-z0-9_']*)" % "|".join(ROCQ_KEYWORDS))
# A mutual block continues with `with <name>` at column 0 after one of the
# keywords above; `match ... with` never puts `with` at column 0 followed by
# an identifier in this tree, and the state below only reads it after a
# definition anyway.
ROCQ_WITH = re.compile(r"^with\s+([A-Za-z_][A-Za-z0-9_']*)")
# The sentences whose bodies are hashed: the parity keywords above, plus
# the kinds specdeps' graph has nodes for that parity does not hold
# (`Class`, `Instance`, `Structure`, `Let`), so that a closure member of any kind
# has a body.  `Notation` names are quoted and have no node; not read.
BODY_KEYWORDS = ROCQ_KEYWORDS + ("Class", "Instance", "Structure", "Let")
ROCQ_BODY = re.compile(
    ROCQ_PREFIX + r"(%s)\s+([A-Za-z_][A-Za-z0-9_']*)" % "|".join(BODY_KEYWORDS),
    re.S)
ROCQ_BODY_WITH = re.compile(r"\bwith\s+([A-Za-z_][A-Za-z0-9_']*)")
MUTUAL_KINDS = ("Fixpoint", "CoFixpoint", "Inductive", "CoInductive")

LEAN_KEYWORDS = ("def", "abbrev", "structure", "inductive", "coinductive",
                 "theorem", "instance", "class", "opaque")
LEAN_MODIFIERS = ("private", "protected", "noncomputable", "partial",
                  "unsafe", "nonrec")
LEAN_DEF = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:%s)\s+)*(%s)\s+([^\s:(\[{]+)"
    % ("|".join(LEAN_MODIFIERS), "|".join(LEAN_KEYWORDS)))
# `private` among a declaration's modifiers (PAR-VISIBLE).  Read apart from
# LEAN_DEF so that its two groups, keyword and name, stay what
# tools/check_lean_test_monotonic.py reads them as.
LEAN_PRIVATE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:%s)\s+)*private\s" % "|".join(LEAN_MODIFIERS))
# A line holding nothing but attributes and modifiers: Lean reads it as the
# prefix of the declaration on the next line, and so does `lean_decls`.
LEAN_MODIFIER_LINE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:%s)\b\s*)+$" % "|".join(LEAN_MODIFIERS))
# The commands that open and close a namespace scope, on one line each.
LEAN_SCOPE = re.compile(
    r"^\s*(?:(namespace)\s+([A-Za-z_][\w'.]*)|(?:noncomputable\s+)?(section)\b\s*([A-Za-z_][\w'.]*)?"
    r"|(mutual)\b|(end)\b\s*([A-Za-z_][\w'.]*)?)\s*$")

# The dotted module name a Lean file under LEAN_BASE is imported by.
LEAN_MODULE_PREFIX = LEAN_BASE.split("/", 1)[1].replace("/", ".") + "."
LEAN_IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", re.M)

HEADER_BYTES = 4096
HEADER_TAG = "rocq-baseline:"
# A mis-spelt tag is a claim the reader cannot read, not an unclaimed twin:
# `Rocq-Baseline:`, `rocq_baseline:` and `rocq-baseline :` are refused by
# name rather than silently dropping the twin out of the held set.
NEAR_TAG = re.compile(r"rocq[-_ ]?baseline\s*:", re.IGNORECASE)
HEADER = re.compile(r"/-!\s*rocq-baseline:\s*([0-9a-f]{40})\b(.*?)-/",
                    re.DOTALL)
UNPORTED = re.compile(r"^unported:\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*--\s*(\S.*)$")
# `drift-ticket: [<file>.v:]<name> <ticket> -- <reason>`.  The ticket is a
# plan.json id: a letter, then letters, digits, `-` or `_` (`T11`, `K6a`,
# `S-Fs-Open-openat`, `E-rwx_flag_ns`).
MEMBER_KEY = (
    rf"(?:((?:{re.escape(STATEMENTS_REL)}/)?[A-Za-z0-9_/]+\.v):)?"
    r"([A-Za-z_][A-Za-z0-9_']*)")
REREAD = re.compile(r"^rocq-reread:\s+" + MEMBER_KEY
                    + r"\s+([0-9a-f]{64})\s+--\s+(\S.*)$")
DRIFT_TICKET = re.compile(r"^drift-ticket:\s+" + MEMBER_KEY
                          + r"\s+([A-Za-z][A-Za-z0-9_-]*)\s+--\s+(\S.*)$")
# #748's retired file-level form, refused with its own message.
DRIFT_TICKET_FILE_LEVEL = re.compile(r"^drift-ticket:\s*#\d+\s*--")

# BUGS-1.  A `bugs/<x>.md` path a held Rocq file cites is a divergence from
# Linux the Rocq model knows about and keeps (AGENTS.md: an entry belongs
# in bugs/ when something the model can answer is wrong).  The twin either
# inherits that answer or fixes it, and its header says which, one line per
# cited entry.
# bugs/README.md is the index, not a divergence entry, and is ignored.
#     divergence: bugs/<x>.md -- inherited
#     divergence: bugs/<x>.md -- fixed: <theorem>
# `inherited` says the twin KEPT Rocq's answer; `fixed:` names the Cases
# pin stating the kernel's, which tools/lean_replay.py reads as the evidence
# a divergence-register entry rests on (its DIVERGENCE rule).  Either way
# the twin's Cases mirror -- Checks/Cases/<path below Sys/>.lean -- carries
# one theorem per declaration whose docstring opens
# `inherited-divergence: bugs/<x>.md`, stating the kernel's answer per the
# entry in the form the model gives it today -- a refutation where the
# model refuses what Linux does, an admission where it allows what Linux
# never does (two of Sys/Mm/Mmap.lean's five are admissions) -- and
# flipped when the line says `fixed:`.  What this rule reads is the tag and
# the name, never the statement: a `fixed:` line over a pin nobody flipped
# passes here, and is caught only where the replay holds the register
# entry's `kernel` verdict to the recording.  A twin that says nothing
# inherits the wrong answer silently, which is what this rule refuses; a
# declaration with no pin is a claim with no evidence, and a pin with no
# declaration is evidence for a claim nobody made.
BUGS_CITE = re.compile(r"(?<![\w/.-])(bugs/[A-Za-z0-9][A-Za-z0-9_.-]*\.md)\b")
DIVERGENCE_TAG = "divergence:"
DIVERGENCE = re.compile(
    r"^divergence:\s+(bugs/[A-Za-z0-9][A-Za-z0-9_.-]*\.md)\s+--\s+"
    r"(?:(inherited)|fixed:\s*([A-Za-z_][A-Za-z0-9_'.]*))\s*$")
INHERITED_PIN_TAG = "inherited-divergence:"
# A Cases pin: the docstring opener, then the theorem it documents.  Only a
# `theorem` counts, and only a visible one -- PAR-VISIBLE's reason: the
# replay names it as evidence, and a `private` name is reachable by nothing.
# The docstring body is fenced at its own `-/`: a lazy `.*?` under DOTALL
# runs on to the NEXT closer whenever the declaration under the opener is
# not a visible `theorem`, and credits the tag to whatever theorem follows
# -- so a `def`, an `example` or a `private theorem` under the tag passed,
# and a `fixed:` clause naming the later theorem read as evidence for a
# theorem that was never the pin (deep review of #1220).
INHERITED_PIN = re.compile(
    r"/--\s*inherited-divergence:\s+(bugs/[A-Za-z0-9][A-Za-z0-9_.-]*\.md)\b(?:(?!-/).)*?-/\s*"
    r"(?:@\[[^\]]*\]\s*)*(?:(?:protected|noncomputable)\s+)*theorem\s+([^\s:(\[{]+)",
    re.DOTALL)
CASES_BASE = "Checks/Cases"

# The claiming twins allowed to declare none of the divergences their Rocq
# source cites, keyed by the path below LEAN_BASE.  Like UNCLAIMED_ALLOWED
# this list only shrinks: a twin leaves it in the PR that gives it its
# `divergence:` lines and pins, and the test holds the seed as a literal
# so that nothing may be added.  The seed is every claiming twin whose Rocq
# source cited a bugs/ entry on the day BUGS-1 landed, less Sys/Mm/Mmap.lean,
# which V-Divergences declared and pinned.  The excuse is the same for
# each: the declarations arrive with the ticket that pins each entry's
# kernel answer in the Cases mirror, and none of these twins has had one.
# The excuse covers a twin that declares NONE.  One that declares some of
# the cited entries is held to the rest: a header naming two of five and
# silent on three is the silence the rule refuses, not the not-yet-audited
# state this list records.
_DIVERGENCE_UNDECLARED_WHY = (
    "its Rocq source cites bugs/ entries and the twin declares none of them; "
    "the `divergence:` lines arrive with the ticket that pins each entry's "
    "kernel answer in the Cases mirror, as V-Divergences did for Sys/Mm/Mmap.lean")
DIVERGENCE_UNDECLARED_ALLOWED = {
    rel: _DIVERGENCE_UNDECLARED_WHY for rel in (
        "Fs.lean", "Run.lean", "StackLayout.lean", "State.lean",
        "Sys/Fs/EventPoll.lean", "Sys/Fs/File.lean", "Sys/Fs/Ioctl.lean",
        "Sys/Fs/Locks.lean", "Sys/Fs/Namei.lean", "Sys/Fs/Open.lean",
        "Sys/Fs/ReadWrite.lean", "Sys/Fs/Readdir.lean", "Sys/Fs/Select.lean",
        "Sys/Fs/Stat.lean", "Sys/Fs/Sync.lean", "Sys/Kernel/Exit.lean",
        "Sys/Kernel/Fork.lean", "Sys/Kernel/Futex/Syscalls.lean",
        "Sys/Kernel/Signal.lean", "Sys/Kernel/Sys.lean",
        "Sys/Kernel/Time/Hrtimer.lean", "Sys/Kernel/Time/PosixTimers.lean",
        "Sys/Kernel/Time/Time.lean", "Sys/Mm/Mremap.lean",
        "Sys/Net/Socket.lean", "Sys/Uaccess.lean", "Sys/Uapi.lean")}


# A separate shrinking seed: the statement tree became held with
# T-Equiv-parity. Each entry excuses only that cited path, even when the
# twin declares none. Its owning plan node removes it by declaring the
# divergence and its Cases pin; an absent or done owner is an error.
# State.lean's old-list entry owns accept-queue debt, inherited and pinned
# by Equivalence.lean rather than seeded here.
STATEMENT_DIVERGENCE_UNDECLARED_ALLOWED = {
    f"{STATEMENTS_REL}/Classifier.lean": {
        "bugs/vm-limit-environment-obligation.md": "A-Classifier"},
}


def repo_path(base, rel):
    """Normalised repository path for a key relative to either held base."""
    return posixpath.normpath(posixpath.join(base, rel))


def relative_key(base, path):
    """The relative key of a normalised path, including sibling trees."""
    return posixpath.relpath(path, base)


def module_name(rel):
    """Shared Rocq/Lean module name, normalised before replacing slashes."""
    return repo_path(LEAN_BASE.split("/", 1)[1],
                     posixpath.splitext(rel)[0]).replace("/", ".")


def lean_module_key(mod):
    """The Lean relative key imported by a dotted module name."""
    return relative_key(LEAN_BASE.split("/", 1)[1],
                        mod.replace(".", "/") + ".lean")


class RocqLexError(Exception):
    """A Rocq file this reader cannot strip without guessing."""


def _string_end(text, i):
    """Index just past the string literal opening at `text[i] == '"'`.

    Rocq escapes a quote inside a literal by doubling it; nothing else is an
    escape. An unterminated literal runs to end of file.
    """
    j, size = i + 1, len(text)
    while j < size:
        if text[j] == '"':
            if j + 1 < size and text[j + 1] == '"':
                j += 2
                continue
            return j + 1
        j += 1
    return size


def _lineno(text, i):
    return text.count("\n", 0, i) + 1


# Both strippers below are pure functions of the text and are asked the same
# question many times over: one site generation (tools/lean_port_status.py)
# strips 48 distinct Rocq texts 218 times and 256 distinct Lean texts 498
# times, because the twins, their parts and their baselines are each read by
# more than one reader -- 3.2 CPU seconds, measured 2026-09-22.  So each lexes
# a text once per process.  A text that fails to lex raises every time: the
# cache holds answers, never refusals.  The bound only caps what a long-lived
# caller holds.
@functools.lru_cache(maxsize=1024)
def strip_rocq_comments(text):
    """`text` with every `(* ... *)` replaced by spaces, newlines kept.

    Copied from tools/check_kernel_citations.py's `v_comments`, which finds
    the same spans to read them; this one blanks them. Rocq nests `(*`, so
    the depth is counted; an unterminated comment runs to end of file.

    String literals in code are lexed so that a `(*` inside one is never
    taken for a comment opener; one that contains `(*` or `*)` raises
    RocqLexError rather than being read either way (the docstring at the
    top says why the wrong way is the passing one). Inside a comment the
    quote pairing of prose is not trusted, so a comment delimiter that
    follows an odd number of `"` in its comment raises as well.
    """
    out, i, size = [], 0, len(text)
    while i < size:
        start = text.find("(*", i)
        quote = text.find('"', i)
        if quote >= 0 and (start < 0 or quote < start):
            end = _string_end(text, quote)
            lit = text[quote:end]
            if "(*" in lit or "*)" in lit:
                shown = lit if len(lit) <= 40 else lit[:37] + "..."
                raise RocqLexError(
                    f"line {_lineno(text, quote)}: the string literal "
                    f"{shown!r} contains a comment delimiter. This reader would either"
                    " open a comment there, blanking every definition up to"
                    " the next unmatched `*)` -- fewer Rocq names, and a"
                    " twin that PASSES missing them -- or have to trust its"
                    " own lexing of the literal. It does neither; reword the"
                    " literal.")
            out.append(text[i:end])
            i = end
            continue
        if start < 0:
            out.append(text[i:])
            break
        out.append(text[i:start])
        depth, j, quoted = 1, start + 2, False
        while j < size and depth:
            delim = text.startswith("(*", j) or text.startswith("*)", j)
            if delim and quoted:
                raise RocqLexError(
                    f"line {_lineno(text, j)}: the comment opened on line "
                    f"{_lineno(text, start)} has `{text[j:j + 2]}` after "
                    "an odd number of `\"`. Whether that is inside a string "
                    "the lexer skips or prose the delimiter counts in "
                    "changes where the comment ends, and one of the two "
                    "readings hides definitions; reword the comment.")
            if text[j] == '"':
                quoted = not quoted
                j += 1
            elif text.startswith("(*", j):
                depth += 1
                j += 2
            elif text.startswith("*)", j):
                depth -= 1
                j += 2
            else:
                j += 1
        out.append(re.sub(r"[^\n]", " ", text[start:j]))
        i = j
    return "".join(out)


@functools.lru_cache(maxsize=1024)
def strip_lean_comments(text):
    """`text` with `-- ...` and nested `/- ... -/` blanked, newlines kept."""
    out, i, size = [], 0, len(text)
    while i < size:
        block = text.find("/-", i)
        line = text.find("--", i)
        if block < 0 and line < 0:
            out.append(text[i:])
            break
        if line >= 0 and (block < 0 or line < block):
            end = text.find("\n", line)
            end = size if end < 0 else end
            out.append(text[i:line])
            out.append(" " * (end - line))
            i = end
            continue
        out.append(text[i:block])
        depth, j = 1, block + 2
        while j < size and depth:
            if text.startswith("/-", j):
                depth += 1
                j += 2
            elif text.startswith("-/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        out.append(re.sub(r"[^\n]", " ", text[block:j]))
        i = j
    return "".join(out)


def rocq_defs(text, path="<rocq>"):
    """Top-level definition names in a Rocq file, in order, comments gone."""
    try:
        stripped = strip_rocq_comments(text)
    except RocqLexError as e:
        sys.exit(f"{path}: {e}")
    names, mutual = [], False
    measured = specdeps.definition_sentences(rocq_sentences(stripped), path)
    for line in "\n".join(measured).splitlines():
        m = ROCQ_DEF.match(line)
        if m:
            names.append(m.group(2))
            mutual = True
            continue
        w = ROCQ_WITH.match(line)
        if w and mutual:
            names.append(w.group(1))
            continue
        if line and not line[0].isspace():
            # any other column-0 command ends the mutual block
            mutual = False
    return names


def rocq_sentences(stripped):
    """The sentences of comment-stripped Rocq text, string literals intact.

    A sentence ends at a `.` followed by whitespace or end of file; `..`
    never ends one, and neither does a `.` inside a string literal, which is
    skipped with the same lexing `strip_rocq_comments` used. specdeps'
    `sentences` is not reused here because it runs on text whose literals
    it has blanked; on text that keeps them a `". "` in a literal would end
    the sentence early and leave the rest of the body unhashed.
    """
    out, start, i, size = [], 0, 0, len(stripped)
    while i < size:
        c = stripped[i]
        if c == '"':
            i = _string_end(stripped, i)
            continue
        if c == "." and (i + 1 == size or stripped[i + 1].isspace()) \
                and not (i > 0 and stripped[i - 1] == "."):
            out.append(stripped[start:i + 1])
            start = i + 1
        i += 1
    if stripped[start:].strip():
        out.append(stripped[start:])
    return out


def rocq_bodies(text, path="<rocq>"):
    """{name: normalized body} for every named top-level sentence of a Rocq
    file: the sentence with comments stripped and whitespace collapsed. A
    mutual block is one sentence, entered under each of its names.
    A transparent lemma includes its proof through Defined.; Qed. is omitted."""
    try:
        stripped = strip_rocq_comments(text)
    except RocqLexError as e:
        sys.exit(f"{path}: {e}")
    bodies, seen = {}, {}
    for sentence in specdeps.definition_sentences(rocq_sentences(stripped), path):
        m = ROCQ_BODY.match(sentence)
        if not m:
            continue
        body = " ".join(sentence.split())
        names = [m.group(2)]
        if m.group(1) in MUTUAL_KINDS:
            names += ROCQ_BODY_WITH.findall(sentence[m.end():])
        specdeps.check_repeated_bindings(seen, names, m.group(1), path)
        for n in names:
            bodies.setdefault(n, body)
    return bodies


def measured_body(body):
    """A full transparent lemma block or an inline definition body."""
    head = ROCQ_BODY.match(body)
    if head and head.group(1) in specdeps.LEMMA_KEYWORDS:
        return re.search(r"\bDefined\s*\.$", body) is not None
    return inline_body(body)


def inline_body(body):
    """On comment-stripped text, each whole-word let, fix or cofix outside
    strings at bracket depth zero opens a pending binder. Its next
    depth-zero := consumes one pending binder; a depth-zero := with no
    pending binder is the definition body.

    A local fix/cofix can have further := members after `with`. Refuse a
    depth-zero `with` after such a binder, before finding the definition
    body. Keep that flag after the binder's first :=: its mutual members
    can still follow. This does not parse the mutual block or its end, so
    it also refuses a later match's `with` in the type. That costs coverage
    but cannot hide a proof body. Brackets shield both `with` and its :=;
    an established inline body needs no scan because we hash all of it.
    """
    depth, pending, i = 0, 0, 0
    local_fix = False
    while i < len(body):
        c = body[i]
        if c == '"':
            i = _string_end(body, i)
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and (c.isalnum() or c in "_'"):
            end = i + 1
            while end < len(body) and (body[end].isalnum() or body[end] in "_'"):
                end += 1
            word = body[i:end]
            if word == "with" and local_fix:
                return False
            if word in ("fix", "cofix"):
                local_fix = True
            if word in ("let", "fix", "cofix"):
                pending += 1
            i = end
            continue
        elif depth == 0 and body.startswith(":=", i):
            if not pending:
                return True
            pending -= 1
        i += 1
    return False


def body_hash(body):
    return hashlib.sha256(body.encode()).hexdigest()


def lean_decls(text):
    """Top-level declarations of a Lean file as dicts {name, full, private,
    line}: `name` is the last component, `full` the namespace-qualified
    name (`namespace`, `section` and `mutual` scopes tracked through the
    comment-blanked text; `_root_.x` is `x`).  A declaration whose name is
    a shape this does not read (`instance : C := …`) is skipped."""
    out, scopes, pending = [], [], ""
    for lineno, line in enumerate(strip_lean_comments(text).splitlines(), 1):
        if LEAN_MODIFIER_LINE.match(line):
            pending += line.strip() + " "
            continue
        if pending and line.strip():
            line, pending = pending + line.lstrip(), ""
        sc = LEAN_SCOPE.match(line)
        if sc:
            if sc.group(1):
                scopes.append(("namespace", sc.group(2)))
            elif sc.group(3):
                scopes.append(("section", sc.group(4)))
            elif sc.group(5):
                scopes.append(("mutual", None))
            elif sc.group(6) and scopes:
                scopes.pop()
            continue
        m = LEAN_DEF.match(line)
        if not m:
            continue
        name = m.group(2)
        if name in (":=", "where", "|"):
            continue  # anonymous instance, or a shape this does not read
        ns = ".".join(n for k, n in scopes if k == "namespace")
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            full = f"{ns}.{name}" if ns else name
        out.append({"name": name.rsplit(".", 1)[-1], "full": full,
                    "private": LEAN_PRIVATE.match(line) is not None, "line": lineno})
    return out


def lean_defs(text):
    """Top-level declaration names in a Lean file, last component only."""
    return [d["name"] for d in lean_decls(text)]


def twin_namespace(lean_rel):
    """The module namespace a twin (or one of its parts) declares in: the
    twin's own module name, `LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.
    Mmap` for `Sys/Mm/Mmap.lean`.  It is `module_name` under the name
    tools/check_lean_port_obligations.py calls."""
    return module_name(lean_rel)


def visible(decl, twin_ns):
    """PAR-VISIBLE: not private, and declared under the twin's namespace."""
    return not decl["private"] and decl["full"].startswith(twin_ns + ".")


def exactly_at(decl, twin_ns):
    """PAR-REACH: a visible declaration at exactly `twin_ns.name`."""
    return visible(decl, twin_ns) and decl["full"] == f"{twin_ns}.{decl['name']}"


def rocq_table_arms(root):
    """[(number, spec)] of the Rocq table, comments blanked; an absent or
    empty table is an error, because PAR-REACH over no arms holds nothing."""
    path = os.path.join(root, ROCQ_TABLE)
    if not os.path.isfile(path):
        sys.exit(f"{ROCQ_TABLE}: no such file. The Rocq table is what PAR-REACH "
                 "holds each twin to; without it no dispatched spec is owed.")
    with open(path) as f:
        text = strip_rocq_comments(f.read())
    arms = [(int(n), spec) for n, spec in ROCQ_ARM.findall(text)]
    if not arms:
        sys.exit(f"{ROCQ_TABLE}: read no arms out of spec_table; PAR-REACH would "
                 "then hold every twin to nothing.")
    return arms


def lean_numbers(root):
    """The syscall numbers the port REGISTERS, through
    tools/gen_lean_registry.py's `registry_arms` -- the one reader of a
    registered arm, and since T31 the only one there can be: the table is
    rendered into `lean/.lake/generated` by the build and committed
    nowhere.  Its refusals (no arm, a duplicate number, an arm applying no
    `<name>_spec`, a file whose `mkSpecArm` count it did not match) are
    fatal here, because PAR-REACH reads this set to decide whether a
    declined number is declined by the table too, and an empty answer
    would clear every such entry.  The import is inside the function:
    `gen_lean_registry` imports THIS module for `twin_parts`, so at module
    level the two would cycle."""
    import gen_lean_registry  # noqa: PLC0415 -- see the docstring: import cycle
    try:
        return set(gen_lean_registry.registry_arms(root))
    except gen_lean_registry.Refusal as e:
        sys.exit(f"check_lean_spec_parity.py: PAR-REACH reads the registered "
                 f"arms through gen_lean_registry, which refused them: {e}")


def lean_imports(text):
    """Dotted module names the file imports, comments gone."""
    return LEAN_IMPORT.findall(strip_lean_comments(text))


def _byte_offset(text, i):
    """Byte offset of character index `i` in `text`'s UTF-8."""
    return len(text[:i].encode("utf-8"))


def parse_header(text, path, strict_reason=True):
    """(baseline, {name: reason}, [ticket]) from the claim block, or None if
    unclaimed; a ticket is {"file", "name", "ticket", "reason"} with "file"
    None for a bare name.

    A block that mentions the tag but does not parse is an error, not an
    unclaimed twin: a claim the reader cannot read must not become a pass.
    PAR-REASON is applied under `strict_reason`; a reader comparing two
    revisions (tools/check_lean_test_monotonic.py) passes False so that a
    merge base written before the rule is still read.

    The block's `divergence:` lines (BUGS-1) are read and held to their
    shape here, and returned by `parse_divergences`: the triple is what a
    dozen readers unpack, so the fourth register has its own reader.
    `parse_rereads` reads the fifth register and `parse_partials` the sixth.
    """
    claim = _parse_header(text, path, strict_reason)
    return None if claim is None else (
        claim[0], claim[1], [{k: t[k] for k in ("file", "name", "ticket", "reason")}
                             for t in claim[2]])


def parse_divergences(text, path):
    """[{bugs, state, theorem, line}] from the claim block's `divergence:`
    lines, in file order; `theorem` is None under `inherited`.  `[]` for
    an unclaimed twin.  Refuses, like `parse_header`, a block it cannot
    read -- the two are one reader."""
    claim = _parse_header(text, path, strict_reason=False)
    return [] if claim is None else claim[3]


def parse_rereads(text, path):
    """Read [{file, name, hash, reason, path, line}] through the header reader."""
    claim = _parse_header(text, path, strict_reason=False)
    return [] if claim is None else claim[4]


def parse_partials(text, path, strict_reason=True):
    """Read partial declines without excluding definitions from parity or drift."""
    claim = _parse_header(text, path, strict_reason)
    return {} if claim is None else claim[5]


def _parse_header(text, path, strict_reason):
    at = text.find(HEADER_TAG)
    if at < 0:
        near = NEAR_TAG.search(text)
        if near:
            sys.exit(f"{path}: has `{near.group(0)}` at byte "
                     f"{_byte_offset(text, near.start())} and no `{HEADER_TAG}`. "
                     "A near-miss of the tag would otherwise read as no "
                     "claim, which is the pass this check exists to refuse; "
                     f"spell it `{HEADER_TAG}`.")
        return None
    # The window is measured in bytes of the file's UTF-8 (the docstring's
    # unit), not in characters: a preamble of multibyte prose is as long as
    # it is on disk.
    if _byte_offset(text, at) >= HEADER_BYTES:
        sys.exit(f"{path}: `{HEADER_TAG}` first appears at byte "
                 f"{_byte_offset(text, at)}, beyond the first {HEADER_BYTES} "
                 "bytes where the parity header is read. Move the block up "
                 "to just after the imports: a claim past the window would "
                 "otherwise count as no claim, which is the pass this check "
                 "exists to refuse.")
    # The block is matched over the whole text: only its START is held to
    # the window, so a register longer than the window is a claim, not a
    # shape error.  Non-greedy, so a block that never closes runs to the
    # next `-/` in the file and its prose fails the line shapes below.
    m = HEADER.search(text)
    if m and _byte_offset(text, m.start()) >= HEADER_BYTES:
        sys.exit(f"{path}: the parity header block starts at byte "
                 f"{_byte_offset(text, m.start())}, beyond the first "
                 f"{HEADER_BYTES} bytes where it is read (an earlier "
                 f"`{HEADER_TAG}` at byte {_byte_offset(text, at)} is not a "
                 "block). Move the block up to just after the imports.")
    if not m:
        sys.exit(f"{path}: has `{HEADER_TAG}` near its top but no parity "
                 "header this reads. The shape is\n"
                 "  /-! rocq-baseline: <40-hex commit>\n"
                 "  unported: <name> -- <reason> -/\n"
                 "and a claim in another shape would otherwise count as no "
                 "claim, which is the pass this check exists to refuse.")
    baseline, body = m.group(1), m.group(2)
    unported, tickets, ticketed = {}, [], set()
    partials = {}
    divergences, declared = [], set()
    rereads = []
    for line in body.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith(DIVERGENCE_TAG):
            v = DIVERGENCE.match(line)
            if not v:
                sys.exit(f"{path}: parity header line {line!r} is neither "
                         "`divergence: bugs/<x>.md -- inherited` nor "
                         "`divergence: bugs/<x>.md -- fixed: <theorem>` "
                         "(BUGS-1). A declaration this cannot read is one it "
                         "cannot hold the Cases pin or the replay to.")
            bugs = v.group(1)
            if bugs in declared:
                sys.exit(f"{path}: parity header declares {bugs} twice; one "
                         "line says whether the twin inherits or fixes it.")
            declared.add(bugs)
            divergences.append({"bugs": bugs,
                                "state": "inherited" if v.group(2) else "fixed",
                                "theorem": v.group(3), "line": line})
            continue
        if line.startswith("rocq-reread"):
            r = REREAD.fullmatch(line)
            if not r:
                sys.exit(f"{path}: malformed rocq-reread line {line!r}. Use "
                         "`rocq-reread: <name | file.v:name> <64 lowercase hex> "
                         "-- <reason>` with a nonempty reason.")
            rereads.append({"file": r[1], "name": r[2], "hash": r[3],
                            "reason": r[4].strip(), "path": path, "line": line})
            continue
        if DRIFT_TICKET_FILE_LEVEL.match(line):
            sys.exit(f"{path}: parity header line {line!r} is the retired "
                     "file-level drift ticket. It silenced every later "
                     "change to the file, and a GitHub number is nothing "
                     "this can check for `done` offline. Name the drifted "
                     "definition and the plan ticket that re-ports it: "
                     "`drift-ticket: <name> <ticket> -- <reason>`.")
        d = DRIFT_TICKET.match(line)
        if d:
            key = (d.group(1), d.group(2))
            if key in ticketed:
                sys.exit(f"{path}: parity header carries two drift-ticket "
                         f"lines for {d.group(2)}: {line!r}.")
            ticketed.add(key)
            tickets.append({"file": d.group(1), "name": d.group(2),
                            "ticket": d.group(3),
                            "reason": d.group(4).strip(), "path": path, "line": line})
            continue
        partial = line.startswith("partial:")
        u = UNPORTED.match("unported:" + line[len("partial:"):] if partial else line)
        if not u:
            sys.exit(f"{path}: parity header line {line!r} is none of "
                     "`unported: <name> -- <reason>`, `partial: <name> -- <reason>`, `drift-ticket: "
                     "<name> <ticket> -- <reason>`, `divergence: bugs/<x>.md "
                     "-- inherited | fixed: <theorem>` or blank. A register "
                     "entry this cannot read is one it cannot hold the Rocq "
                     "file to.")
        name = u.group(1).rsplit(".", 1)[-1]
        if name in unported or name in partials:
            sys.exit(f"{path}: parity header registers {name} twice.")
        reason = u.group(2).strip()
        if strict_reason and len(REASON_WORD.findall(reason)) < REASON_WORDS:
            marker = "partial" if partial else "unported"
            sys.exit(f"{path}: the `{marker}:` reason for {name} is {reason!r}, "
                     f"fewer than {REASON_WORDS} words. A register entry says "
                     "what is missing and why; one that says neither registers "
                     "nothing (PAR-REASON).")
        (partials if partial else unported)[name] = reason
    return baseline, unported, tickets, divergences, rereads, partials


def cases_mirror(lean_rel, root=None):
    """The Cases file that pins a twin's declarations, below LEAN_BASE:
    `Checks/Cases/<path below Sys/>.lean`, and `Checks/Cases/<name>.lean`
    for a base twin (State.lean, Run.lean). Statement twins use
    `Checks/Cases/EquivalenceDefinition/<name>.lean`, outside the held
    statement tree so pins are not mistaken for orphan twins. Two twins break
    the rule: the tree pins Sys/Uapi.lean and Sys/Syscall.lean under
    Checks/Cases/Sys/, beside Checks/Cases/Uaccess.lean, which follows it.
    So with `root` given, a Sys/ twin whose mirror is not on disk at the
    rule's path but is at `Checks/Cases/Sys/<path>` is read there; with no
    root, or with neither on disk, the rule's path is what a finding names.
    A pin placed under Checks/Cases/Sys/ for those two was read by nothing
    before this (deep review of #1220)."""
    under_sys = lean_rel.startswith(ROCQ_SUBTREE + "/")
    below = lean_rel[len(ROCQ_SUBTREE) + 1:] if under_sys else lean_rel
    # Statement pins stay outside the recursively held statement tree.
    if below.startswith(STATEMENTS_REL + "/"):
        below = below[len("../"):]
    mirror = f"{CASES_BASE}/{below}"
    if root is not None and under_sys \
            and not os.path.isfile(os.path.join(root, LEAN_BASE, mirror)) \
            and os.path.isfile(os.path.join(root, LEAN_BASE, CASES_BASE, lean_rel)):
        return f"{CASES_BASE}/{lean_rel}"
    return mirror


def inherited_pins(text):
    """{bugs: [theorem]} over a Cases file's `inherited-divergence:` pins,
    each theorem by its last name component, in file order."""
    out = {}
    for bugs, name in INHERITED_PIN.findall(text):
        out.setdefault(bugs, []).append(name.rsplit(".", 1)[-1])
    return out


def cited_bugs(text):
    """The cited entries, excluding the exact path of the bugs/ index."""
    return sorted(set(BUGS_CITE.findall(text)) - {"bugs/README.md"})


def divergence_problems(root, lean, lean_rel, rocq, rtext, divergences):
    """BUGS-1 over one claiming twin: the problems, as strings.  `lean` and
    `rocq` are the two paths as printed, `lean_rel` the twin below
    LEAN_BASE, `rtext` the Rocq file's text with its comments (a citation
    lives in one), `divergences` the header's lines as `parse_divergences`
    returns them, parts included."""
    problems = []
    cited = cited_bugs(rtext)
    declared = {d["bugs"] for d in divergences}
    mirror = cases_mirror(lean_rel, root)
    mirror_path = os.path.join(root, LEAN_BASE, mirror)
    # The allowlist excuses a twin that declares NONE of the cited entries;
    # one that has begun declaring is held to all of them (the comment on
    # DIVERGENCE_UNDECLARED_ALLOWED).
    if declared or lean_rel not in DIVERGENCE_UNDECLARED_ALLOWED:
        excused = STATEMENT_DIVERGENCE_UNDECLARED_ALLOWED.get(lean_rel, {})
        for bugs in cited:
            if bugs not in declared and bugs not in excused:
                problems.append(
                    f"{lean}: {rocq} cites {bugs}, a divergence from Linux the "
                    "Rocq model records, and the twin's header says neither "
                    f"`divergence: {bugs} -- inherited` nor `divergence: {bugs} "
                    "-- fixed: <theorem>`. A twin that says nothing inherits "
                    "the wrong answer silently: declare which, and pin the "
                    f"kernel's answer in {repo_path(LEAN_BASE, mirror)} under a docstring "
                    f"opening `{INHERITED_PIN_TAG} {bugs}` (BUGS-1).")
    for d in divergences:
        if d["bugs"] not in cited:
            problems.append(
                f"{lean}: declares `{d['line']}`, and {rocq} cites no "
                f"{d['bugs']}. The entry closed or moved and the declaration "
                "outlived it; a line excusing nothing reads as coverage "
                "(BUGS-1).")
        if not os.path.isfile(os.path.join(root, d["bugs"])):
            problems.append(
                f"{lean}: declares `{d['line']}`, and there is no {d['bugs']} "
                "in the tree. The kernel's answer is what the entry carries, "
                "so a citation nobody can open declares nothing (BUGS-1).")
    # The mirror is read whenever it is there, declarations or not: a pin
    # with no declaration behind it is a finding on its own (below), and an
    # early return on "nothing declared" would be the one way to hide it.
    pins = {}
    if os.path.isfile(mirror_path):
        pins = inherited_pins(cases_family.View(root).text(f"{LEAN_BASE}/{mirror}"))
    elif divergences:
        problems.append(
            f"{lean}: declares {len(divergences)} divergence(s) and has no "
            f"Cases mirror {repo_path(LEAN_BASE, mirror)} to pin them in; each "
            "declaration owes a theorem there whose docstring opens "
            f"`{INHERITED_PIN_TAG} <bugs path>` (BUGS-1).")
        return problems
    for d in divergences:
        names = pins.get(d["bugs"], [])
        if not names:
            problems.append(
                f"{lean}: declares `{d['line']}`, and {repo_path(LEAN_BASE, mirror)} has "
                "no theorem whose docstring opens "
                f"`{INHERITED_PIN_TAG} {d['bugs']}`. The pin stating the "
                "kernel's answer per the entry is the declaration's evidence; "
                "without it the line is a claim nobody checked (BUGS-1).")
        elif d["state"] == "fixed" and d["theorem"].rsplit(".", 1)[-1] not in names:
            problems.append(
                f"{lean}: declares `{d['line']}`, and {d['theorem']} is not "
                f"among the `{INHERITED_PIN_TAG} {d['bugs']}` pins of "
                f"{repo_path(LEAN_BASE, mirror)} ({', '.join(names)}). The theorem a "
                "`fixed:` clause names is what the replay reads as the "
                "evidence the twin gives the kernel's answer, so it has to be "
                "the pin (BUGS-1).")
    for bugs in sorted(pins):
        if bugs not in declared:
            problems.append(
                f"{repo_path(LEAN_BASE, mirror)}: pins `{INHERITED_PIN_TAG} {bugs}` "
                f"({', '.join(pins[bugs])}), and {lean}'s header declares no "
                f"`divergence: {bugs}` line. A pin is evidence for a "
                "declaration; one with no declaration says the twin diverges "
                "where the register says it does not (BUGS-1).")
    return problems


def rocq_files(root):
    """Relative paths (below ROCQ_BASE) of the Rocq files held to parity."""
    base = os.path.join(root, ROCQ_BASE)
    out = []
    for subtree in (ROCQ_SUBTREE, STATEMENTS_REL):
        for dirpath, _, names in os.walk(os.path.join(base, subtree)):
            for name in names:
                if name.endswith(".v"):
                    full = os.path.join(dirpath, name)
                    out.append(os.path.relpath(full, base).replace(os.sep, "/"))
    for name in ROCQ_EXTRA:
        if os.path.exists(os.path.join(base, name)):
            out.append(name)
    if not out:
        sys.exit(f"{ROCQ_BASE}: no Rocq spec files found under {root}. An "
                 "empty source side agrees with every twin vacuously, so "
                 "this fails here instead.")
    return sorted(out)


def lean_twin_files(root):
    """Relative paths of the Lean files read as twins or parts: everything
    under the mirrored Sys/ subtree, and for each base twin ROCQ_EXTRA names
    (`State.lean`, ...) the twin itself and everything under its own
    directory (`State/`), where its parts live; also the entire statement tree."""
    base = os.path.join(root, LEAN_BASE)
    subtrees = [ROCQ_SUBTREE, STATEMENTS_REL] + [name[:-len(".v")] for name in ROCQ_EXTRA]
    out = []
    for name in ROCQ_EXTRA:
        twin = name[:-len(".v")] + ".lean"
        if os.path.exists(os.path.join(base, twin)):
            out.append(twin)
    for sub in subtrees:
        for dirpath, _, names in os.walk(os.path.join(base, sub)):
            for name in names:
                if name.endswith(".lean"):
                    full = os.path.join(dirpath, name)
                    out.append(os.path.relpath(full, base).replace(os.sep, "/"))
    return sorted(out)


def git(root, *args):
    return subprocess.run(["git", "-C", root, *args], capture_output=True,
                          text=True)


def git_or_exit(root, *args):
    """stdout of a git command that has to work for the check to mean
    anything; git failing is an error, never a pass."""
    r = git(root, *args)
    if r.returncode:
        sys.exit(f"{root}: `git {' '.join(args)}` failed: "
                 f"{r.stderr.strip() or 'no reason given'}. A repository "
                 "git cannot answer for is one whose baselines nothing can "
                 "verify, and an unverified claim must not read as a "
                 "verified one.")
    return r.stdout


def verify_baseline(root, baseline, rocq_rel):
    """The reason `baseline` is not a commit the twin of `rocq_rel` could
    have been read from, or None when it is: it must name a commit in this
    repository, be an ancestor of HEAD, and carry the mirrored file."""
    path = repo_path(ROCQ_BASE, rocq_rel)
    r = git(root, "rev-parse", "--verify", "--quiet", baseline + "^{commit}")
    if r.returncode == 1 and not r.stderr.strip():
        return (f"baseline {baseline} names no commit in this repository: "
                "either it was never a commit, this clone does not have it "
                "(a shallow checkout drops history; fetch it), or it was a "
                "PR-branch commit that the squash merge left behind. The "
                "header claims a Rocq tree the twin was read from, and "
                "nothing can read that tree; read the Rocq at a commit on "
                "main and name that (the docstring, WHICH COMMITS SURVIVE "
                "THAT TEST, says when the day tip is the honest answer and "
                "what it costs).")
    if r.returncode:
        sys.exit(f"{root}: `git rev-parse` failed: {r.stderr.strip()}. A "
                 "repository git cannot answer for is one whose baselines "
                 "nothing can verify.")
    r = git(root, "merge-base", "--is-ancestor", baseline, "HEAD")
    if r.returncode == 1:
        return (f"baseline {baseline} is not an ancestor of HEAD. The twin "
                "claims to mirror a Rocq tree this history never contained "
                "-- a side branch, a rewritten commit, a dangling one -- so "
                "what it mirrors is not what this tree's Rocq says. Read "
                "the Rocq at a commit on main, never at one of a PR branch, "
                "which the squash that lands it rewrites -- and a day-branch "
                "commit is rewritten the same way when the day integrates, "
                "so a header naming one is green all day and red here on "
                "main and on every PR of the next day (the docstring, WHICH "
                "COMMITS SURVIVE THAT TEST).")
    if r.returncode:
        sys.exit(f"{root}: `git merge-base --is-ancestor` failed: "
                 f"{r.stderr.strip()}. A repository git cannot answer for "
                 "is one whose baselines nothing can verify.")
    listed = git_or_exit(root, "ls-tree", baseline, "--", path)
    if not listed.strip():
        return (f"{path} did not exist at baseline {baseline}. A twin "
                "cannot have been read from a tree its Rocq file was not "
                "in; the header names a commit before the file, and the "
                "twin's real source is unknown.")
    return None


class DriftGraph:
    """tools/specdeps.py's definition graph over the checkout, restricted to
    the files held to parity, with the bodies of each side read once per
    file."""

    def __init__(self, root, held_rels):
        self.root = root
        self.held = {repo_path(ROCQ_BASE, rel): rel for rel in held_rels}
        defs, self.by_name, edges, _ambiguous = specdeps.build_graph(root=root, statements=True)
        self.node = {}       # key -> (rel, name), held nodes only
        for key, d in defs.items():
            rel = self.held.get(d["file"].replace(os.sep, "/"))
            if rel is not None:
                self.node[key] = (rel, key[1])
        self.edges = {k: sorted(d for d in edges.get(k, ()) if d in self.node)
                      for k in self.node}
        self._head = {}      # rel -> {name: body}
        self._base = {}      # (baseline, rel) -> {name: body} or None

    def closure(self, rocq_rel, seeds):
        """Sorted [(rel, name)]: the held definitions the `seeds` of the
        file at `rocq_rel` reach, the seeds included. A seed specdeps has no
        node for stands alone, its dependencies unfollowed."""
        mod = module_name(rocq_rel)
        seen, stack = set(), []
        for name in seeds:
            keys = [k for k in self.by_name.get(name, ()) if k[0] == mod
                    and k in self.node]
            if keys:
                stack += keys
            else:
                seen.add((rocq_rel, name))
        visited = set()
        while stack:
            k = stack.pop()
            if k in visited:
                continue
            visited.add(k)
            seen.add(self.node[k])
            stack += self.edges[k]
        return sorted(seen)

    def head_bodies(self, rel):
        if rel not in self._head:
            with open(os.path.join(self.root, ROCQ_BASE, rel)) as f:
                self._head[rel] = rocq_bodies(f.read(), repo_path(ROCQ_BASE, rel))
        return self._head[rel]

    def base_bodies(self, baseline, rel):
        """The bodies of `rel` at `baseline`, or None when the file was not
        there."""
        key = (baseline, rel)
        if key not in self._base:
            path = repo_path(ROCQ_BASE, rel)
            if git_or_exit(self.root, "ls-tree", baseline, "--", path).strip():
                text = git_or_exit(self.root, "show", f"{baseline}:{path}")
                self._base[key] = rocq_bodies(text, f"{baseline}:{path}")
            else:
                self._base[key] = None
        return self._base[key]

    def drifted(self, baseline, closure):
        """([{file, name, change, baseline_hash, head_hash}], [problems])
        over `closure`: the members whose body differs between `baseline`
        and the checkout, and the members whose body this could not read."""
        out, problems = [], []
        for rel, name in closure:
            head = self.head_bodies(rel).get(name)
            if head is None:
                problems.append(
                    f"{repo_path(ROCQ_BASE, rel)}: the dependency graph reaches {name} "
                    "and the body reader finds no sentence defining it. "
                    "One of the two readers is wrong about this file, and "
                    "a member this cannot hash is one whose drift it cannot "
                    "see; that is the passing direction, so it fails.")
                continue
            if not measured_body(head):
                problems.append(
                    f"{repo_path(ROCQ_BASE, rel)}: unmeasured body for {name}: "
                    "the reader cannot identify a definition-body `:=`. The reader hashes "
                    "only the statement of a proof-mode definition.")
                continue
            base = self.base_bodies(baseline, rel)
            base_body = None if base is None else base.get(name)
            if base_body is not None and not measured_body(base_body):
                problems.append(f"{baseline}:{repo_path(ROCQ_BASE, rel)}: "
                                f"unmeasured baseline body for {name}; move the baseline.")
                continue
            hh = body_hash(head)
            bh = None if base_body is None else body_hash(base_body)
            if bh != hh:
                out.append({"file": rel, "name": name,
                            "change": "added" if bh is None else "changed",
                            "baseline_hash": bh, "head_hash": hh,
                            "ticket": None, "reason": None})
        return out, problems


class Tickets:
    """The plan's ticket ids, what each one provides, and their progress
    states, read once when a drift ticket or divergence owner needs them."""

    def __init__(self, root):
        self.root = root
        self._provides = None
        self._states = None

    def _load(self):
        if self._provides is not None:
            return
        plan = os.path.join(self.root, PLAN_JSON)
        try:
            with open(plan) as f:
                nodes = json.load(f)["nodes"]
            provides = {}
            for n in nodes:
                p = n.get("provides") or []
                if not isinstance(p, list) or any(not isinstance(x, str)
                                                  for x in p):
                    # Fail here rather than read it as owning nothing: a
                    # shape this cannot read would refuse every line the
                    # node really does own, and the reason would be wrong.
                    raise TypeError(
                        f"node {n['id']}: `provides` is not a list of strings")
                provides[n["id"]] = set(p)
            self._provides = provides
        except (OSError, ValueError, KeyError, TypeError) as e:
            sys.exit(f"{PLAN_JSON}: cannot read the plan's ticket ids ({e}), "
                     "and a drift ticket or divergence owner needs them. A ticket nothing "
                     "can look up is one nothing can find done, so the line "
                     "cannot be honoured.")
        self._states = {}
        progress = os.path.join(self.root, PROGRESS_JSON)
        if os.path.exists(progress):
            try:
                with open(progress) as f:
                    tickets = json.load(f).get("tickets", {})
                self._states = {tid: t.get("state") for tid, t in tickets.items()}
            except (OSError, ValueError, AttributeError) as e:
                sys.exit(f"{PROGRESS_JSON}: cannot read ticket states ({e}), "
                         "and a drift ticket or divergence owner needs them.")

    def live_problem(self, ticket, kind):
        """A debt's owner must exist and must still owe work."""
        self._load()
        if ticket not in self._provides:
            return f"{kind} {ticket} is not a ticket of {PLAN_JSON}"
        if self._states.get(ticket) == "done":
            return f"{kind} {ticket} is done in {PROGRESS_JSON}"
        return None

    def problem(self, ticket, file, name):
        """Why `ticket` cannot carry the drift of `name` in `file`, or None."""
        problem = self.live_problem(ticket, "drift-ticket")
        if problem:
            return problem + "; name a live re-port ticket or move the baseline to what it re-read"
        # The plan's `provides` is the only place ownership is written
        # down, per definition or per whole file.  A ticket that does not
        # own the definition cannot re-port it, so without this a drift is
        # silenced by naming any live ticket at all.
        owned = self._provides[ticket]
        if f"{file}:{name}" not in owned and f"file:{file}" not in owned:
            return (f"drift-ticket {ticket} does not provide {file}:{name} "
                    f"in {PLAN_JSON}; a ticket that does not own the "
                    "definition cannot re-port it, so the line excuses the "
                    "drift without anyone owing the work -- name the ticket "
                    "whose `provides` carries it, or add the definition to "
                    "that ticket's provides")
        return None


def member_identities(closure):
    """Index qualified and bare keys over the complete closure."""
    identities = {}
    for identity in closure:
        rel, name = identity
        identities[(rel, name)] = [identity]
        identities.setdefault((None, name), []).append(identity)
    return identities


def apply_tickets(lean, baseline, closure, drifted, tickets, plan, rereads=(), heads=None):
    """Resolve both registers against the closure and validate their claims."""
    problems, accepted, seen, duplicates = [], [], {}, set()
    identities = member_identities(closure)
    changed = {(d["file"], d["name"]): d for d in drifted}
    for t in [*rereads, *tickets]:
        kind = "rocq-reread" if "hash" in t else "drift-ticket"
        shown = (t["file"] + ":" if t["file"] else "") + t["name"]
        label = f"{lean}: {t['path']}: line {t['line']!r}: {kind} {shown}"
        hits = identities.get((t["file"], t["name"]), [])
        if len(hits) > 1:
            problems.append(label + " reaches "
                            + ", ".join(f"{r}:{n}" for r, n in hits)
                            + "; qualify the name with its file.")
            continue
        if not hits:
            problems.append(label + ": no definition in the twin's closure "
                            "carries that name.")
            continue
        identity = hits[0]
        if identity in seen:
            duplicates.add(identity)
            problems.append(label + f": duplicate identity {identity[0]}:{identity[1]}, "
                            f"which another {seen[identity]} line already ticketed or reread in the twin.")
        seen[identity] = kind
        d = changed.get(identity)
        if kind == "rocq-reread":
            if d is None:
                problems.append(label + ": the Rocq is at the baseline body again, "
                                "or its body is unmeasured. Drop the line and revert "
                                "the Lean port to that body, or move the baseline.")
            hh = d["head_hash"] if d else (heads or {}).get(identity)
            if hh is not None and t["hash"] != hh:
                problems.append(label + f": stale reread drift: recorded {t['hash']}, head {hh}.")
            elif d is not None:
                accepted.append({"file": identity[0], "name": identity[1],
                                 "hash": t["hash"], "reason": t["reason"]})
            continue
        if d is None:
            problems.append(label + f": {repo_path(ROCQ_BASE, identity[0])} "
                            f"defines {t['name']} unchanged since baseline {baseline}; "
                            "remove the ticket or move the baseline.")
            continue
        why = plan.problem(t["ticket"], *identity)
        if why:
            problems.append(f"{label}: {why}")
        else:
            d["ticket"], d["reason"] = t["ticket"], t["reason"]
    accepted = [r for r in accepted if (r["file"], r["name"]) not in duplicates]
    acknowledged = {(r["file"], r["name"]) for r in accepted}
    drifted[:] = [d for d in drifted if (d["file"], d["name"]) not in acknowledged]
    return problems, accepted


def twin_parts(lean_rel, ltext, lean_set):
    """The re-exported parts of the twin at `lean_rel`, in import order.

    A part is a file under the twin's own directory -- `Sys/X/...` for the
    twin `Sys/X.lean`, `State/...` for the base twin `State.lean`, and
    `../EquivalenceDefinition/X/...` for its statement twin -- that
    the twin imports and that exists. Only direct imports count; see the
    docstring.
    """
    stem = lean_rel[:-len(".lean")]
    parts = []
    for mod in lean_imports(ltext):
        rel = lean_module_key(mod)
        if rel.startswith(stem + "/") and rel in lean_set and rel not in parts:
            parts.append(rel)
    return parts


def check(root):
    """Per-file records and the problems found, in one pass over the tree."""
    records, problems, unclaimed = {}, [], []

    held = rocq_files(root)
    rocq_set = set(held)
    lean_set = set(lean_twin_files(root))
    graph = None   # built on the first claiming twin; the walk is the cost
    plan = Tickets(root)

    # Which held Lean files are parts of a twin, keyed by part.
    part_of = {}
    for lean_rel in sorted(lean_set):
        rocq_rel = lean_rel[:-len(".lean")] + ".v"
        if rocq_rel not in rocq_set:
            continue
        with open(os.path.join(root, LEAN_BASE, lean_rel)) as f:
            for part in twin_parts(lean_rel, f.read(), lean_set):
                part_of[part] = lean_rel

    for lean_rel in sorted(lean_set):
        rocq_rel = lean_rel[:-len(".lean")] + ".v"
        if rocq_rel in rocq_set or lean_rel in part_of:
            continue
        if lean_rel.startswith(REGISTRY_DIR):
            # errors="replace": an AppleDouble `._` sidecar or any other
            # non-UTF-8 blob here is a skipped file, not a traceback that
            # swallows every other finding
            with open(os.path.join(root, LEAN_BASE, lean_rel), errors="replace") as f:
                if HEADER_TAG in f.read():
                    problems.append(
                        f"{repo_path(LEAN_BASE, lean_rel)}: is a registry file of "
                        "tools/gen_lean_registry.py and claims parity. A "
                        "registry file mirrors no Rocq file, so the claim "
                        "would be read by nothing; drop the header.")
            continue
        msg = (f"{repo_path(LEAN_BASE, lean_rel)}: mirrors no file -- there is no "
               f"{repo_path(ROCQ_BASE, rocq_rel)}. A Lean file in the mirrored tree "
               "with no Rocq source is not a port of anything.")
        parent = lean_rel.rsplit("/", 1)[0] + ".lean" if "/" in lean_rel \
            else None
        if parent in lean_set and parent[:-len(".lean")] + ".v" in rocq_set:
            msg += (f" If it is a part of the twin {repo_path(LEAN_BASE, parent)}, that twin has "
                    "to import it: only what the twin re-exports is read as "
                    "the twin.")
        problems.append(msg)

    # Every held Rocq file's names, twin or not: PAR-REACH asks which file
    # defines a dispatched spec, and the answer "none with a twin" has to be
    # told apart from "none at all".
    all_rdefs, all_rtexts = {}, {}
    for rocq_rel in held:
        with open(os.path.join(root, ROCQ_BASE, rocq_rel)) as f:
            all_rtexts[rocq_rel] = f.read()
        all_rdefs[rocq_rel] = rocq_defs(all_rtexts[rocq_rel],
                                        repo_path(ROCQ_BASE, rocq_rel))
    decls_of, ns_of = {}, {}
    undeclared_of = {}   # claiming twin -> the cited bugs/ paths it declares nothing of

    for rocq_rel in held:
        lean_rel = rocq_rel[:-len(".v")] + ".lean"
        lean_path = os.path.join(root, LEAN_BASE, lean_rel)
        if not os.path.exists(lean_path):
            continue
        rdefs = all_rdefs[rocq_rel]
        with open(lean_path) as f:
            ltext = f.read()
        twin_ns = twin_namespace(lean_rel)
        decls = lean_decls(ltext)
        parts = twin_parts(lean_rel, ltext, lean_set)
        ptexts = {}
        for part in parts:
            with open(os.path.join(root, LEAN_BASE, part)) as f:
                ptexts[part] = f.read()
            decls += lean_decls(ptexts[part])
        decls_of[rocq_rel], ns_of[rocq_rel] = decls, twin_ns
        ldefs = [d["name"] for d in decls]
        rec = {"lean": repo_path(LEAN_BASE, lean_rel),
               "parts": [repo_path(LEAN_BASE, p) for p in parts],
               "twin_namespace": twin_ns,
               "rocq_defs": rdefs, "lean_defs": ldefs,
               "missing": [], "stale_unported": [], "registered_and_defined": [],
               "unported": {}, "baseline": None, "baseline_ok": None,
               "closure": [], "drifted": [], "drift_tickets": [], "reread": [],
               "divergences": [], "bugs_cited": [], "claimed": False}
        records[repo_path(ROCQ_BASE, rocq_rel)] = rec

        claim = _parse_header(ltext, rec["lean"], strict_reason=True)
        part_claims = {p: _parse_header(ptexts[p], repo_path(LEAN_BASE, p), True)
                       for p in parts}
        if claim is None:
            for p, c in part_claims.items():
                if c is not None:
                    problems.append(
                        f"{repo_path(LEAN_BASE, p)}: claims parity, and the twin "
                        f"{rec['lean']} that re-exports it does not. The "
                        "claim is read on the twin; a part's alone is read "
                        "by nothing.")
            unclaimed.append(rec["lean"])
            if lean_rel not in UNCLAIMED_ALLOWED:
                problems.append(
                    f"{rec['lean']}: carries no `{HEADER_TAG}` header, so "
                    "nothing here measures it: the name comparison, the "
                    f"register and the closure all stop before {repo_path(ROCQ_BASE, rocq_rel)} "
                    "is read. Add the header block (BRIEF.md "
                    "section 3) naming the commit the twin was read at; the "
                    "allowlist in check_lean_spec_parity.py is for files no "
                    "PR may hand a header to today -- frozen base twins and "
                    "the generated table -- and only ever shrinks.")
            continue
        baseline, unported, tickets = claim[:3]
        ticketed = {(t["file"], t["name"]) for t in tickets}
        rereads = list(claim[4])
        for p, c in part_claims.items():
            if c is None:
                continue
            pbase, punported, ptickets = c[:3]
            rereads += c[4]
            for t in ptickets:
                key = (t["file"], t["name"])
                if key in ticketed:
                    problems.append(
                        f"{repo_path(LEAN_BASE, p)}: carries a drift-ticket for "
                        f"{t['name']}, and so does another file of the twin "
                        f"{rec['lean']}; the later reason would silently "
                        "win.")
                ticketed.add(key)
            tickets += ptickets
            if pbase != baseline:
                problems.append(
                    f"{repo_path(LEAN_BASE, p)}: baseline {pbase} differs from the "
                    f"twin {rec['lean']}'s {baseline}; one twin is read "
                    "from one Rocq tree.")
            for n, reason in punported.items():
                if n in unported:
                    problems.append(
                        f"{repo_path(LEAN_BASE, p)}: registers {n} as unported, and "
                        f"so does another file of the twin {rec['lean']}.")
                unported[n] = reason
        rec.update(claimed=True, baseline=baseline, unported=unported,
                   drift_tickets=[{k: t[k] for k in ("file", "name", "ticket", "reason")}
                                  for t in tickets])

        # BUGS-1: the header's divergence lines, the twin's and its parts'
        # together (one bugs/ path declared once across the twin), against
        # the bugs/ paths the Rocq file cites and the pins the Cases mirror
        # carries.
        divergences = parse_divergences(ltext, rec["lean"])
        seen = {d["bugs"] for d in divergences}
        for p in parts:
            for d in parse_divergences(ptexts[p], repo_path(LEAN_BASE, p)):
                if d["bugs"] in seen:
                    problems.append(
                        f"{repo_path(LEAN_BASE, p)}: declares a divergence for "
                        f"{d['bugs']}, and so does another file of the twin "
                        f"{rec['lean']}; the later state would silently win.")
                seen.add(d["bugs"])
                divergences.append(d)
        rec["divergences"] = divergences
        rec["bugs_cited"] = cited_bugs(all_rtexts[rocq_rel])
        undeclared_of[lean_rel] = [b for b in rec["bugs_cited"] if b not in seen]
        problems += divergence_problems(root, rec["lean"], lean_rel,
                                        repo_path(ROCQ_BASE, rocq_rel),
                                        all_rtexts[rocq_rel], divergences)

        lset = {d["name"] for d in decls if visible(d, twin_ns)}
        rset = set(rdefs)
        partials = {}
        for part_path, part_text in [(lean_rel, ltext)] + [(p, ptexts[p]) for p in parts]:
            for name, reason in parse_partials(part_text, repo_path(LEAN_BASE, part_path)).items():
                if name in partials or name in unported:
                    problems.append(f"{rec['lean']}: duplicate partial declaration for {name}")
                partials[name] = reason
                if name not in lset or name not in rset:
                    problems.append(f"{rec['lean']}: partial {name} must name visible definitions in both twins")
        rec["missing"] = [n for n in rdefs
                          if n not in lset and n not in unported]
        rec["stale_unported"] = sorted(n for n in unported if n not in rset)
        rec["registered_and_defined"] = sorted(n for n in unported
                                               if n in lset)
        for n in rec["missing"]:
            hidden = [d for d in decls if d["name"] == n]
            if hidden:
                shown = "; ".join(
                    ("`private` " if d["private"] else "")
                    + f"{d['full']} (line {d['line']})" for d in hidden)
                problems.append(
                    f"{rec['lean']}: {repo_path(ROCQ_BASE, rocq_rel)} defines {n}, and "
                    f"the twin's only {n} is {shown} -- not a visible "
                    f"declaration under the twin's namespace {twin_ns}, so "
                    "the table and the pins cannot reach it (PAR-VISIBLE)")
            else:
                problems.append(
                    f"{rec['lean']}: {repo_path(ROCQ_BASE, rocq_rel)} defines {n} and the "
                    "twin neither defines it nor registers it as unported")
        for n in rec["stale_unported"]:
            problems.append(
                f"{rec['lean']}: registers {n} as unported, and "
                f"{repo_path(ROCQ_BASE, rocq_rel)} defines no {n}")
        for n in rec["registered_and_defined"]:
            problems.append(
                f"{rec['lean']}: registers {n} as unported and defines it")

        why = verify_baseline(root, baseline, rocq_rel)
        rec["baseline_ok"] = why is None
        if why:
            problems.append(f"{rec['lean']}: {why}")
            continue
        if graph is None:
            graph = DriftGraph(root, held)
        seeds = [n for n in rdefs if n not in unported]
        closure = graph.closure(rocq_rel, seeds)
        rec["closure"] = [{"file": rel, "name": n} for rel, n in closure]
        drifted, unread = graph.drifted(baseline, closure)
        problems += [f"{rec['lean']}: {p}" for p in unread]
        heads = {(rel, n): body_hash(body) for rel, n in closure
                 if (body := graph.head_bodies(rel).get(n)) is not None}
        issues, rec["reread"] = apply_tickets(
            rec["lean"], baseline, closure, drifted, tickets, plan, rereads, heads)
        problems += issues
        rec["drifted"] = drifted
        for d in drifted:
            if d["ticket"] is None:
                problems.append(
                    f"{rec['lean']}: {repo_path(ROCQ_BASE, d['file'])} {d['name']} "
                    f"{d['change']} since baseline {baseline}. Re-read the "
                    "Rocq, port the difference and move the baseline, or "
                    f"file the re-port: `drift-ticket: {d['name']} <ticket> "
                    "-- <reason>` in the header. Or add "
                    f"`rocq-reread: {d['file']}:{d['name']} {d['head_hash']} "
                    "-- <reason>`. This line claims the porter re-read the Rocq "
                    "at that hash and ported it.")

    # The allowlist's own two staleness rules: an excuse that outlived the
    # claim, and an excuse for a file that is not a twin here at all -- which
    # is also what makes an empty Lean side fail rather than pass with
    # nothing read.
    twins = {relative_key(LEAN_BASE, r["lean"]): r["claimed"]
             for r in records.values()}
    for rel, reason in sorted(UNCLAIMED_ALLOWED.items()):
        if rel not in twins:
            problems.append(
                f"{repo_path(LEAN_BASE, rel)}: is on check_lean_spec_parity.py's "
                "UNCLAIMED_ALLOWED list and is no twin of this tree -- there "
                f"is no {repo_path(LEAN_BASE, rel)} mirroring a held {ROCQ_BASE} file. "
                "An entry that excuses nothing reads as coverage; drop it, or "
                f"correct the path. (Its reason: {reason})")
        elif twins[rel]:
            problems.append(
                f"{repo_path(LEAN_BASE, rel)}: claims parity and is still on "
                "check_lean_spec_parity.py's UNCLAIMED_ALLOWED list. The "
                "claim landed and the excuse outlived it: drop the entry "
                "in the PR that gave the twin its header. "
                f"(Its reason: {reason})")

    # BUGS-1's allowlist has the same two staleness rules, and a third: an
    # entry for a twin that declares every bugs/ path its Rocq source cites
    # -- or whose source cites none -- excuses nothing, and an entry for an
    # unclaimed twin excuses nothing either, since the rule reads a header
    # the twin does not have.
    def unheld_divergence(rel, list_name):
        prefix = (f"{repo_path(LEAN_BASE, rel)}: is on check_lean_spec_parity.py's "
                  f"{list_name} list")
        if rel not in twins:
            return (prefix + " and is no twin of this tree -- there is no "
                    f"{repo_path(LEAN_BASE, rel)} mirroring a held "
                    f"{repo_path(ROCQ_BASE, rel[:-len('.lean')] + '.v')} file. "
                    "An entry that excuses nothing reads as coverage; drop it, "
                    "or correct the path.")
        if not twins[rel]:
            return (prefix + " and claims no parity, so BUGS-1 reads no header "
                    "of its and the entry excuses nothing; the divergence "
                    "lines arrive with the header. Drop the entry.")
        return None

    for rel, reason in sorted(DIVERGENCE_UNDECLARED_ALLOWED.items()):
        problem = unheld_divergence(rel, "DIVERGENCE_UNDECLARED_ALLOWED")
        if problem:
            problems.append(f"{problem} (Its reason: {reason})")
        elif not undeclared_of.get(rel):
            problems.append(
                f"{repo_path(LEAN_BASE, rel)}: declares every bugs/ entry its Rocq "
                "source cites and is still on check_lean_spec_parity.py's "
                "DIVERGENCE_UNDECLARED_ALLOWED list. The declarations landed "
                "and the excuse outlived them: drop the entry in the PR that "
                f"gave the twin its `divergence:` lines. (Its reason: {reason})")

    for rel, entries in sorted(STATEMENT_DIVERGENCE_UNDECLARED_ALLOWED.items()):
        problem = unheld_divergence(rel, "STATEMENT_DIVERGENCE_UNDECLARED_ALLOWED")
        if problem:
            problems.append(problem)
        for bugs, owner in sorted(entries.items()):
            prefix = (f"{repo_path(LEAN_BASE, rel)}: "
                      f"STATEMENT_DIVERGENCE_UNDECLARED_ALLOWED entry {bugs} "
                      f"(owner {owner})")
            if not problem:
                rec = records[repo_path(ROCQ_BASE, rel[:-len(".lean")] + ".v")]
                if bugs not in rec["bugs_cited"]:
                    problems.append(prefix + " is not cited by the twin's Rocq file; "
                                    "drop the entry or correct the path.")
                if any(d["bugs"] == bugs for d in rec["divergences"]):
                    problems.append(prefix + " is already declared by the twin; "
                                    "the declaration landed, so drop the entry.")
            owner_problem = plan.live_problem(owner, "owning node")
            if owner_problem:
                problems.append(prefix + ": " + owner_problem + "; the owner must "
                                "declare the divergence and its Cases pin before finishing.")

    # PAR-REACH.  Both tables, then each dispatched spec against its twin.
    rocq_arms = rocq_table_arms(root)
    registered = lean_numbers(root)
    home = {}
    for rocq_rel, names in all_rdefs.items():
        for n in names:
            home.setdefault(n, rocq_rel)

    def defined_at(rocq_rel, spec, qualified=None):
        """A visible `def spec` at exactly the twin's namespace; when the
        arm writes the name qualified from `Sys` (the generated table's
        spelling), that spelling has to resolve to the same declaration."""
        want = LEAN_MODULE_PREFIX + qualified if qualified and "." in qualified else None
        return any(d["name"] == spec and exactly_at(d, ns_of[rocq_rel])
                   and (want is None or d["full"] == want)
                   for d in decls_of[rocq_rel])

    def nearest(rocq_rel, spec):
        near = [d for d in decls_of[rocq_rel] if d["name"] == spec]
        if not near:
            return "no `def " + spec + "` at all"
        return "only " + "; ".join(("`private` " if d["private"] else "")
                                   + f"{d['full']} (line {d['line']})" for d in near)

    for key, rec in records.items():
        if not rec["claimed"]:
            continue
        rocq_rel = relative_key(ROCQ_BASE, key)
        for n, spec in rocq_arms:
            if home.get(spec) != rocq_rel:
                continue
            if spec in rec["unported"]:
                reason = rec["unported"][spec]
                if not re.search(rf"(?<![\w.]){n}(?![\w.])", reason):
                    problems.append(
                        f"{rec['lean']}: registers {spec} as unported, and "
                        f"{ROCQ_TABLE} dispatches {n} to it; the reason "
                        f"{reason!r} does not name {n}, the number the port "
                        "declines (PAR-REACH)")
                if n in registered:
                    problems.append(
                        f"{rec['lean']}: registers {spec} as unported, and "
                        f"{LEAN_REGISTRY} registers an arm for {n}, the arm "
                        f"{ROCQ_TABLE} gives {spec} (PAR-REACH)")
            elif not defined_at(rocq_rel, spec):
                problems.append(
                    f"{rec['lean']}: {ROCQ_TABLE} dispatches {n} to {spec}, and "
                    f"the twin has {nearest(rocq_rel, spec)} -- a dispatched "
                    f"spec is a visible `def {spec}` at exactly the namespace "
                    f"{rec['twin_namespace']}, or an `unported:` entry naming "
                    f"{n} (PAR-REACH)")

    return records, problems, unclaimed


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=".", help="repository root")
    ap.add_argument("--drift", action="store_true",
                    help="accepted and ignored: the drift check is always on")
    ap.add_argument("--strict", action="store_true",
                    help="accepted and ignored: unticketed drift always fails")
    ap.add_argument("--json", action="store_true",
                    help="print the per-file records as JSON on stdout")
    args = ap.parse_args()

    records, problems, unclaimed = check(args.root)
    drifts = sorted(k for k, r in records.items() if r["drifted"])
    ndrift = sum(len(r["drifted"]) for r in records.values())
    claimed = sorted(k for k, r in records.items() if r["claimed"])

    if args.json:
        json.dump({"files": records, "unclaimed": unclaimed,
                   "drifted": drifts, "problems": problems},
                  sys.stdout, indent=2, sort_keys=True)
        print()
    else:
        for k in claimed:
            r = records[k]
            n = len(r["unported"])
            print(f"claimed   {r['lean']}  (baseline {r['baseline'][:12]}, "
                  f"{n} unported"
                  + (f", {len(r['parts'])} parts" if r["parts"] else "")
                  + (f", {len(r['divergences'])} divergences declared"
                     if r["divergences"] else "")
                  + (f", {len(r['closure'])} in closure" if r["closure"] else "")
                  + (f", {len(r['drifted'])} DRIFTED" if r["drifted"] else "")
                  + ")")
        for u in unclaimed:
            print(f"unclaimed {u}")

    for p in problems:
        print(p, file=sys.stderr)
    for k in drifts:
        r = records[k]
        for d in r["drifted"]:
            if d["ticket"] is not None:
                print(f"{r['lean']}: {repo_path(ROCQ_BASE, d['file'])} {d['name']} "
                      f"{d['change']} since baseline {r['baseline']} "
                      f"(drift-ticket {d['ticket']} -- {d['reason']})",
                      file=sys.stderr)
    if problems:
        plural = "" if len(problems) == 1 else "s"
        sys.exit(f"check_lean_spec_parity.py: {len(problems)} problem{plural} "
                 f"across {len(records)} twins")
    # The summary keeps stdout clean JSON for the reader --json exists for.
    print(f"check_lean_spec_parity.py: {len(records)} twins, {len(claimed)} "
          f"claiming parity, {len(unclaimed)} unclaimed, {ndrift} drifted",
          file=sys.stderr if args.json else sys.stdout)


if __name__ == "__main__":
    main()
