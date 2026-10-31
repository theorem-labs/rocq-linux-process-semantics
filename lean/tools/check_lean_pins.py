#!/usr/bin/env python3
"""Refuse the shortcuts the Lean port can take that read fine in review.

This reads theorems and helpers recursively under
`lean/LinuxProcessSemantics/LinuxProcessSem/Checks/Cases/`, including the
statement twins' `EquivalenceDefinition/<file>.lean` mirrors, the path
check_lean_spec_parity.cases_mirror gives a statement twin. It does not read pins beside the
definitions under `lean/LinuxProcessSemantics/EquivalenceDefinition/`.
Statement pins follow the strong_universal_iff pattern: an iff between
independently stated judgments, plus concrete accept and refute cases.
The same rules below apply to every Cases mirror; the rules conditional
on a `*_spec` name remain conditional there too. In particular, this lint
does not establish that two statement judgments are independent or require
an accept/refute pair for a statement: PIN-8 covers registered syscall arms.

Syscall pins state what a `*_spec` answers for one concrete call, with the
kernel line that justifies the answer in the docstring. Such a pin is
evidence only while its right-hand side is something the kernel does.
Ways of writing one that is not:

  PIN-1  a statement mentioning two different `*_spec` names.  Such a pin
         compares one spec to another spec -- or to a re-encoding of the
         Rocq definition -- and proves that the two agree, never that either
         agrees with Linux.  AGENTS.md says why that is the one thing the
         proofs cannot catch: change both sides the same wrong way and every
         proof still closes.  The legitimate shape that looks similar is the
         SAME spec at two argument lists,

             mmap_spec 0 4096 3 34 3 0 i m o ↔
               mmap_spec 0 4096 3 34 mmap_fd_none 0 i m o

         which says an argument is ignored, so the rule counts DISTINCT
         names rather than occurrences.  A name counts when `_spec` is one
         of its segments (`mmap_spec`, `mmap_spec'`, `mmap_spec_rocq`), so
         a re-encoding named after the spec it copies is still seen.
         Names are compared as written,
         qualification included: `Mm.Mmap.mmap_spec` beside `mmap_spec` is
         reported, and the fix is to spell one definition one way.  The
         declaration's own name is not counted.

  PIN-2  a statement `A ↔ A`, `A = A` or `A → A` whose two sides are the
         same text once whitespace and redundant outer parentheses are
         dropped: `A ↔ (A)` is `A ↔ A`.  It closes by `Iff.rfl`, `rfl` or
         `id`, pins nothing, and is what PIN-1's "same spec, two argument
         lists" exception degenerates into when the two lists are the same
         list.  A leading `∀ binders,` is stripped first so the sides are
         compared, not the quantifier prefix, and the comparison is made
         on the CONCLUSION of an implication chain as well as on the whole:
         `mmap_spec … → o = o` is `A → (B = B)`, reported on `o = o`.

  PIN-3  a pin that takes a HYPOTHESIS that cannot be about its call: a
         binder whose type is a proposition, or a top-level `→` premise,
         that is CLOSED -- `(h : False)`, `(h : (1 : Int) = 2)` and the same
         wrapped once more, `(h : ((1 : Int) = 2))`; names none of the
         pin's LIVE variables -- those its conclusion uses, and those
         sharing a hypothesis with a live one, to a fixpoint -- so that
         `(x : Int) (h : 0 < x ∧ x < 0)` beside a call that never reads
         `x` is closed, and so is the same split in two, `(h1 : 0 < x)
         (h2 : x < 0)`, while `(hx : x = (m_vmmaps m).vm_limit) (h : 0 <
         x)` keeps `h` because `hx` ties `x` to the call; typed by a
         `def … : Prop` of the model or of Checks/Cases, `(h : never)`
         over `def never : Prop := (1 : Int) = 2`, which no token marks
         as a proposition and is judged like one written out -- or
         REFLEXIVE -- `(h : m = m)`, `(h : m ≠ m)`,
         `(h : ¬ (m = m))`, `A ↔ A`, over any one relation of `= ≠ ↔ < ≤ >
         ≥`.  Each of those makes a pin whose every proof closes (`h.elim`,
         `omega`, `(h rfl).elim`) or a premise the pin never needed, and a
         reader sees a pin.
         A hypothesis over the pin's own variables -- `(hm :
         m_has_children m = false)`, `(h : bv_unsigned upid ≠
         WAIT_ANY32)`, `exit_sysno i.in_sysno → …` -- is a claim about
         every model or input satisfying it, and whether such a premise is
         satisfiable is exactly what this reader cannot decide, so it is
         accepted and is review's to read: a premise unsatisfiable only in
         combination (`m = a ∧ m = b`) passes here.  A premise that IS the
         spec -- `mmap_spec … i m o → o ≠ Unmodeled`, or the same written
         as a binder, `(hspec : set_tid_address_spec i m (Ok eff m' evs)) :
         eff = mkEffect tid [] [] ∧ m' = m ∧ evs = []` -- is the
         one-directional half of an `iff`, the shape Checks/Cases/Kernel/
         Fork.lean's `set_tid_address_later_call_moves_nothing` forces the
         repeated call's answer with, and passes because it names the pin's
         variables;
         the same spec applied to closed arguments, `(h : mmap_spec … 65536
         12288 0 50 … two_maps_model Unmodeled)`, names none and is refused
         as closed -- it is `False` in spec clothing, and one `.elim` of the
         pin that refutes that outcome proves anything under it.  What
         PIN-2 refuses is the degenerate case whose conclusion is the
         premise, `(h : spec …) : spec …`, which is `A → A` in binder
         clothing.
         Data binders -- `(i : SyscallInput)`, `(mem : word → Option
         byte)` -- are not hypotheses; a `→` inside a binder is a function
         type, which is why the token list below does not carry it.

         A CONJUNCT is judged on its own as well: `(h : x = 3 ∧ (0 :
         Int) = 1)` and `(h : bv_unsigned n < 8 ∧ m ≠ m)` each carry a
         part that is closed, or reflexive, by itself; such a part closes
         the whole hypothesis whatever the others say, and the pin under
         it closes with it.  That does not contradict the pair
         unsatisfiable only in combination above: `m = a ∧ m = b` has no
         such part, and this reader still cannot decide it.
  PIN-4  the propositional constants: `True` anywhere in a statement, and
         `False` in a pin.  `spec … ∨ True`, `spec … ↔ spec … ∧ True`,
         `(spec … ↔ o = X) ∨ True` and a bare `theorem t : True` under a
         docstring quoting mm/mmap.c each prove nothing about the spec
         and are closed by `trivial`; a pin refutes an outcome by `¬ spec
         … (Ok …)`, never by concluding `False` from it.

  PIN-5  a pin whose non-spec side names no kernel outcome.  The side of a
         pin's `↔` (or `=`) that does not hold the spec is the kernel's
         answer to the call: an `Ok` outcome, an errno inside one
         (`ENOMEM`, `errno_ret`), or the decline `o = Unmodeled`.
         `mmap_spec … ↔ True` admits every outcome, `↔ False` admits none,
         `↔ 1 = 1` says something about nothing, and each closes and reads,
         in a listing, as a pin.  So the non-spec side must mention `Ok`,
         an errno name or `Unmodeled`, directly or through a helper under
         Checks/Cases whose own text does (`einval_outcome m`, a `def`
         building `Ok (mkEffect (errno_ret EINVAL) [] []) m []`, is an
         outcome; helpers resolve through each other).  A helper that
         takes an arm, builds one or opens one -- a `SpecArm` or
         `CheckedArm` in its signature, `.2`, `sa_spec` or `dispatch` in
         its value -- is never that helper: `def admits (c : CheckedArm) …
         : Prop := c.1.2 i m o ∧ …` mentions `Unmodeled` and builds no
         outcome, and read as one it would supply the outcome the pin
         owes for handing the arm to it.  The CHECKER'S
         WITNESS is one too: `syscall_spec i m (table_witness t i m)` says
         the dispatcher admits whatever the checker answers there, and the
         outcome it names is computed rather than written out
         (WITNESS_READERS, on a premise about the model's declaration).  The
         decline `o = Unmodeled` alone is accepted under any name: it is a real
         answer of the model, and PIN-8 is what refuses a port that gives
         no other.  The brief asked that a bare decline be named
         `…_unmodeled`; the merged ports name theirs at least five ways
         (`…_is_unmodeled`, `…_unmodeled_iff`, `…_declines`,
         `…_is_declined`, `…_fails_closed`), and a rule that renamed them
         would be a house-style edit across other ports' files, so the
         name stays review's.  A pin whose spec application sits in a
         HYPOTHESIS (`(hspec : set_tid_address_spec i m (Ok …))` with a
         conclusion about `m'`) is the implication shape: the outcome is
         looked for in the whole statement.  A statement with no
         top-level `↔`/`=` -- an admitted outcome `spec … (Ok …)`, a
         refutation `¬ spec … (Ok …)`, an implication -- must name an
         outcome somewhere in it.  The argument-ignored shape PIN-1 permits
         puts the same spec on both sides and names no outcome; it is
         exempt, because what it says is that two calls agree, and the
         `iff` it is rewritten with is the pin.  One occurrence of a spec
         is not read at all: the argument of `mkSpecArm`, where the arm
         stands as an IDENTITY.  An arm names its spec to say WHICH arm
         it is, so `arm.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec
         …)` is the table's wiring and claims nothing about Linux; asking
         it for an outcome asks it about something it was never about,
         and a `def` holding an arm would be a PIN-7 alias of the spec
         besides, which turns every lookup over the table into a pin.  The
         exemption is by position, not spelling: compared with `=`/`≠`,
         a member, listed, wrapped in `some`, handed to `lookup_arm`,
         `lookup_ca`, `mkCheckedArm`, `ca_no` or `arms_agree`, or read
         for its number or checker fields.  An arm OPENED -- `arm.2 i m
         o`, `match arm with | ⟨_, s⟩ => s`, a `def` that projects it,
         `dispatch [arm]`, any head this reader does not know -- applies
         its spec, and the theorem is a pin on it: a `def` that binds an
         arm HOLDS its specs, a name a statement equates with an arm
         holds them locally, and opening either owes the outcome.  The
         `sa_spec` projection is a `_spec` name of its own, so
         `arm.sa_spec i m o ↔ True` is a pin without any of this.

  PIN-6  a STATE PREDICATE on a pin's non-spec side: a `def` of the
         model's own bookkeeping (State, Monad, Fs, BvBase, each with its
         parts) whose result type is `Bool` or `Prop`, applied on the side
         that should be the kernel's answer -- `region_free [(65536, 4096)]
         a 4096 = true`.  That side then restates the spec's own decision
         over the ledger instead of the decision, a smaller instance of
         PIN-1: the disjointness of two literal ranges is arithmetic, and
         is spelled as arithmetic.  A predicate a spec file or the Uapi
         layer defines (`stat_buf_wf`, `timeval_ok_b`) encodes an ABI
         fact about the bytes a call writes, and the merged stat and time
         ports state their written buffers through such predicates rather
         than by spelling every byte; that is a weaker pin than the bytes
         (the Q7 oracle rows are the stronger form), reviewed as such, and
         not refused here -- and so, as the price of that scope, is a
         spec file's own GATE restated on the kernel side
         (`mmap_off_aligned_b off = false`), which is E3's shape one
         directory over and stays review's.  Constructors, constants,
         projections and the fixtures under Checks/Cases are not
         predicates and pass -- unless a Cases `def` or `abbrev` applies a
         model predicate in its body, in which case it IS that predicate
         under a Cases name (`def rfree maps lo n : Bool := region_free
         maps lo n`) and is refused on the kernel side like the predicate
         itself, through any depth of such wrappers.  A `*_spec` name on
         that side is PIN-1's, not this rule's.  One live pin sits at this
         rule's edge and is not reached by it: Checks/Cases/Mm/Mremap.lean's
         `inplace_grow_iff` states `mremap_fresh_b … = true` on its kernel
         side, a Sys/ wrapper of `region_free` -- the ledger decision this
         rule refuses when spelled `region_free` -- and passes because the
         rule reads the model's base files and not Sys/.  It is owed to
         the mremap port and named in the PR that added this rule.

  PIN-7  `def` and `abbrev` under Checks/Cases are read for PIN-1 too, over
         their whole text: `def both := spec1 ∧ spec2` would otherwise hide
         the second spec behind a name.  A helper whose text mentions one
         spec is an ALIAS of it, and a declaration mentioning the alias is
         a pin of that spec under every rule here, so `def at (a) :=
         mmap_spec a …` followed by `theorem t : at 0 … ↔ True` is PIN-5
         at `t`.  Aliases resolve through each other.  A Cases file other
         than Checks/Cases/Tactic.lean may not declare `notation`, `macro`,
         `syntax`, `elab` or an `infix`/`prefix`/`postfix` form: `local
         notation "rocq" => mmap_spec_rocq` is an alias no `def` reader
         follows, and a pin through it is PIN-1 hidden behind a token.
         TACTIC syntax is exempt, because that reason does not reach it
         once three rules hold: a tactic stands in a statement only through
         a `by` block, and a `by` block in any statement is PIN-7; a helper
         runs one only by naming its token, and an exempt tactic's token in
         any Cases `def` is PIN-7; and the exemption needs the token
         spelled in the header, and `macro_rules`/`elab_rules` carry none
         there, so those two are read through their ALTERNATIVES instead:
         exempt when every one is a `` `(tactic| token …) `` pattern whose
         token an exempt header declares, refused otherwise -- a term
         alternative, a pattern that binds the syntax, a token nothing
         declares.  A tactic with two alternatives has no other spelling,
         and the token is what the rest of the exemption polices, so
         reading it from the alternative is the same defence one line
         down.  (Without the
         first, `macro "rocq" i:term m:term o:term : tactic => `(tactic|
         exact mmap_spec_rocq … $i $m $o)` and `↔ ((by rocq i m o : Prop) ∨
         o = Ok …)` is PIN-1's agreement hidden behind a token again.)
         Tactic.lean cannot host a tactic naming one module's checkers
         anyway (it imports SysSimp and Specs only).  The exemption is
         read from the declaration's header and fails closed -- `macro
         "check_norm" : tactic =>` is exempt, a `term` category, an
         unreadable header and a `macro_rules` declaring no category are
         all still refused, and so is `notation` however it continues.
         `declares_tactic_syntax` and `tactic_token` say what that costs.
         COMMAND syntax is exempt too, and for a shorter reason than the
         tactic one: Lean has no term position for a command, so no pin
         can be stated through one however the statement is written, and
         the three rules above are not needed.  One condition replaces
         them.  A command elaborator can DECLARE -- `elabCommand` on a
         parsed string, `addDecl`, `Meta.mkAuxDefinition` and a dozen
         other core names put a `def` into the environment whose text is
         in no file, and a pin's statement may then name a helper PIN-6's
         reader cannot resolve, which misses silently.  So the exemption
         is for a command that is READ-ONLY, and that is a positive
         premise: every name its block runs, and every Cases helper it
         calls, transitively, is a name known to read (READ_ONLY_API), a
         local, a keyword, a type, or a name literal; a name this reader
         does not know refuses the exemption rather than being trusted
         (`command_reads_only`).  A blacklist was tried first and was the
         exemption-by-spelling this file refuses elsewhere: `elabCommand`
         with a `\b` after it is not `elabCommandTopLevel`, `addDecl` is not
         `addDeclWithoutChecking`, and both declared a helper under Lean
         v4.34.0.  The family (EMITTER, matched by prefix) is still
         refused, in EVERY Cases file and beside any command or none, as
         are `run_cmd`, `run_elab`, `#eval` and `initialize`
         (RUNS_AT_BUILD), which run elaborator code where they stand and
         declared a helper the same way with no syntax declaration to hang
         a reading on.

  PIN-8  every arm the Lean port REGISTERS (`Sys/Registry/`, the files
         the build renders the table from) has a POSITIVE pin and a
         NEGATIVE pin.  A positive pin admits an `Ok` outcome of the arm's
         spec, in one of two shapes: an `iff` (or `=`) whose non-spec side
         names `Ok`, directly or through a Cases helper that builds one,
         and carries no `True` or `False`; or the bare admitted application
         `spec … (Ok …)` with nothing at its top level -- no `→`, `∨`, `↔`
         or `¬`.  An implication is NOT positive whichever side the spec
         stands on: `spec … → o = Ok … ∨ True`, `spec … (Ok …) → True` and
         `(h : spec … (Ok …)) : True` are all provable of a spec that
         admits nothing, and `↔ (o = Unmodeled ∨ (o = Ok … ∧ False))` is a
         decline wearing an `Ok`.  A negative pin refutes one: `¬ spec …`
         or `spec … → False`, again with no other `True`/`False` in the
         statement (`¬ (spec … ∧ False)` refutes nothing).  The second
         form is unreachable while PIN-4 stands, which refuses `False`
         anywhere in a pin; it is kept because the classification is about
         what a negative pin SAYS, and PIN-4 is a rule about how it is
         spelled that a later ticket could narrow.  A decline `↔ o
         = Unmodeled` is neither -- it admits nothing the kernel does and
         refuses nothing in particular -- so a port that answers every
         shape `unmodeled` and pins each decline has no positive pin and
         fails here, as does a Cases file with no pins at all.  A pin
         reaches an arm by naming its spec, or through the dispatcher:
         `syscall_spec (fcntl_in …)` reaches arm 25 when `fcntl_in` is a
         `def … : SyscallInput := … mkInput 25 …` under Checks/Cases, and
         `syscall_spec (SyscallInput.mkInput 95 …)` reaches 95 directly.
         A builder written in terms of ANOTHER builder is followed to it
         (`faccessat2_in` is `faccessat2_in'` applied, and only the primed
         one writes the number), and a value naming two builders at
         different numbers places it at neither;
         the builder has to be `syscall_spec`'s argument, a builder named
         anywhere else in the statement (`∧ fcntl_in 0 = fcntl_in 0`)
         reaches nothing.  A spec two arms share (`fsync_spec` for
         `fsync` and `fdatasync`) is pinned for both by one pin.  The
         arms are read through `gen_lean_registry.registry_arms`
         (`read_table` below), the one reader of a registered arm, which
         tools/check_syscall_docs.py and tools/lean_port_status.py ask
         too, so the three cannot disagree about what the port
         dispatches -- and whose refusals stop this lint rather than
         shrinking what it holds.


A PIN is a declaration whose statement names a `*_spec`; PIN-3, PIN-5 and
PIN-6, and the `False` half of PIN-4, apply to pins only, so a lemma about
a fixture or a helper -- `path_eqb_false_of_ne (h : p ≠ q)` -- keeps its
hypothesis.  These eight rules refuse the shapes a red team wrote against
this tree (docs/lean-port/REDTEAM.md); they are a closed list of shapes,
not a decision procedure for vacuity, and a pin that is weaker than the
arm it is about -- an `→` where an `↔` was possible, a hypothesis smuggled
into a fixture definition -- passes.  That is review's half.

All eight read the statement text -- from the declaration keyword to its
first `:=` outside every bracket (a `{ m with f := v }` structure update
is inside the statement, not its end), or to the first `| pattern =>` arm
of an equation-style proof -- with comments and string literals blanked
out, so a commented-out theorem is not linted and a `_spec` mentioned in
prose inside the statement is not counted.  PIN-7 reads a def's body too,
up to the next top-level command.
The remaining rules are about the specs themselves, under
`lean/LinuxProcessSemantics/LinuxProcessSem/Sys/`:

  DIV-1  `/` or `%` whose right operand is not known to be positive.  Rocq's
         `Z.div` and `Z.modulo` are FLOOR division; Lean's `/` and `%` on
         `Int` are EUCLIDEAN.  They agree whenever the divisor is positive
         and disagree otherwise -- `(-7) / (-2)` is 3 in Rocq and 4 in Lean,
         `7 % (-2)` is -1 in Rocq and 1 in Lean -- so `x % page_size` is a
         faithful port and `x % n` for an unconstrained `n` is a translation
         bug that no proof in the Lean tree can see, because the Lean tree
         proves things about the Lean definition.  A divisor is accepted
         when it is a closed literal expression (`4096`, `(4096 : Int)`,
         `2 ^ 32`, `(8 * 1024)`; only `+`, `*`, `^` and parentheses, so the
         value is positive by construction) or a name in POSITIVE_DIVISORS
         whose definition the script re-reads and finds to be such a
         literal, in the file the entry names or, when that file is a
         re-export that defines nothing, in the part its own direct
         `import` lines name (`State/Geometry.lean` under `State.lean`
         since A15), one level down and never further.  Anything else is
         reported, including a divisor this
         reader does not understand: a false positive here names itself,
         a false negative would not.

  DIV-2  the same operations under their function names.  `Int.ediv` and
         `Int.emod` are `/` and `%` spelled so that DIV-1 cannot read the
         divisor; `Int.tdiv`, `Int.tmod` and the deprecated `Int.div`,
         `Int.mod` truncate toward zero and differ from Rocq's floor even
         for a positive divisor.  `Int.fdiv` and `Int.fmod` ARE floor
         division and pass.

Why a lint and not review: each of these is a single token in a file that
otherwise reads correctly.  A reviewer checking a pin's citation against
mm/mmap.c is reading the docstring and the outcome, not counting `_spec`
occurrences, and a `%` in a definition transcribed from `Z.modulo` looks
exactly like the right translation because for every argument the reviewer
has in mind it is.

Limits, all on the conservative side: the statement is cut at its first
bracket-level `:=` that is not a depth-0 `let`/`have` binding's (one `:=`
per binding is stepped over, so `let s := arm.2; s i m o ↔ True` is read
whole); a divisor spelled with a `-`, an
identifier not in the list, or a function application is reported rather
than evaluated; and nothing here elaborates Lean, so a `_spec` name that
is a local binder counts as a spec.  PIN-5 reads tokens: `Ok` on the
kernel side counts as an outcome wherever it stands, so an `iff` whose
other side is `o = Ok e m evs ∨ 1 = 1`, or `o ≠ Unmodeled`, or `EINVAL =
EINVAL`, passes PIN-5, and whether the outcome named is the kernel's is
the evidence line's question (tools/check_lean_pin_evidence.py).  The
`mkSpecArm` reader is a reader, not an elaborator: it walks the two
arguments by bracket balance and judges each arm's use by the tokens
beside it, and a shape it cannot place -- a group that never closes, a
head or a field it does not know, a head under a namespace it does not
know, an arm applied to an argument, a `let` binding the arm, an identity
whose other operand it cannot read -- is read as opening the arm, so the
spec stays visible and the statement fails closed as a pin rather than
escaping the rules.  What an identity hands the arm to is read too: a
local name compared with an arm, or standing for its spec in a
constructor with a variable there (`arm = SpecArm.mkSpecArm 222 s`), is
the arm or the spec from then on.  The price is the allowlist: a new
table helper applied to an arm is a PIN-5 finding until it is added to
WRAPPER_ARITY, ARM_READERS or CHECKER_READERS (spelled bare or under
ARM_NAMESPACES).  Those lists, and the fields the projection chain ends
at, are trusted by NAME, so what a name could otherwise be made to mean
is refused: a Cases helper named after any of them (`def length`, `def
SpecArm.isSome`) at its definition, `open … renaming` outright, a number
field applied or projected on (`arm.isSome i m o`) as opening the arm,
and a trusted head whose model body comes to reach a spec at that body.
Beyond that, a
holder that takes parameters is opened by every application, an arm
spelled without `mkSpecArm` (`⟨222, fun i => …⟩`), or with `<|` or an
unparenthesised `fun` after it, is an alias and its identities are pins,
an `Option` combinator other than `some` and `isSome`/`isNone` (`.get!`,
`.getD`, `.head?`) opens the arm it yields, a `def` that opens an arm
is a PIN-7 alias whatever it is called, a `by` block anywhere in a
statement is refused even where it proves an argument (`(mkCheckedArm arm
… (by intro …)).ca_arm`: write the proof as a term), an exempt tactic's
token in a Cases `def` is refused even in a proof field, and `elab_rules :
tactic` is refused with `macro_rules`.  A holder is never the helper
PIN-5 accepts, whatever its body names: the `Unmodeled` in a checked arm's
witness is its checker's answer, not an outcome a pin names by writing the
holder, so `fixture_checked.1.2 i m o ↔ True` is a pin with no outcome.
PIN-8
refuses the `True`/`False` spellings of that hole but not the arithmetic
ones: `↔ (o = Ok … ∧ 1 = 2)` still counts as positive, a closed conjunct
being PIN-6's test for hypotheses and not for the kernel side.  PIN-6
reads a hypothesis as closed when it, or one of its `∧`-conjuncts, names
no variable of the pin, so a premise over the pin's variables that is
unsatisfiable only across two hypotheses (`(h1 : i.in_sysno = 0) (h2 :
i.in_sysno = 1)`) or across two conjuncts (`m = a ∧ m = b`) passes -- the
joint case is tools/check_lean_pin_vacuity.py's VAC-3, for bare
variables; a binder is read as a hypothesis
when its type carries a relation or connective token, so a closed premise
spelled as a bare predicate application (`(h : is_ok x)`) is not seen,
and a subtype data binder (`(k : {n : Nat // n < 5})`) is misread as one.
No Cases file writes either shape today.  A model predicate is read from a
`def` whose result type, after the last top-level `→`, is literally
`Bool` or `Prop`; a predicate declared through a type alias is not one to
this reader, and PIN-6 reports a side that names one whatever position it
stands in, so `bv_unsigned a % page_size = 0` passes (a numeral test on a
projection) and `region_free … = true` does not.  One limit is not
conservative: `_spec` is a NAMING CONVENTION, not a property this script
can check, so a re-encoding of the Rocq definition named without it --
`mmap_model`, `mmap_rocq` -- is not seen by PIN-1, and a pin stated
against such a name passes as if it were stated against the kernel.  The
convention is what the port's own files follow, and a name outside it is
what review has to catch.

Exit status 1 with one `file:line: RULE: …` line per finding; 0 when clean.
    python3 tools/check_lean_pins.py [--root DIR]
"""
import argparse
import os
import re
import sys

CASES_DIR = "lean/LinuxProcessSemantics/LinuxProcessSem/Checks/Cases"
SPECS_DIR = "lean/LinuxProcessSemantics/LinuxProcessSem/Sys"
# The model bookkeeping whose predicates PIN-6 refuses on a pin's kernel
# side: the base files a spec is written against, each read with the
# directory of parts it may be split into (`State.lean` re-exporting
# `State/*.lean` since #779).  Not `Sys/`: a spec file's or the Uapi
# layer's predicate encodes an ABI fact, see PIN-6 in the docstring.
MODEL_ROOTS = ("lean/LinuxProcessSemantics/LinuxProcessSem/State",
               "lean/LinuxProcessSemantics/LinuxProcessSem/Monad",
               "lean/LinuxProcessSemantics/LinuxProcessSem/Fs",
               "lean/LinuxProcessSemantics/LinuxProcessSem/BvBase")

# Names DIV-1 accepts as divisors, each with the file its definition is
# read from.  MAINTENANCE: add a name here only if it is defined as a closed
# positive literal (`def name : Int := <literal expression>`) in the file
# named; the script re-reads that definition on every USE of the name as a
# divisor and reports the use if the definition is missing, is not a closed
# literal, or is not positive.  So an entry cannot go stale silently: rename
# or redefine the constant and the next divisor spelled with it fails here.
# A name listed but never used as a divisor in the tree being checked costs
# nothing, which is what lets one list serve branches at different stages
# of the port (`two_pow_64` exists on the mmap branch and not before it).
POSITIVE_DIVISORS = {
    "page_size": "lean/LinuxProcessSemantics/LinuxProcessSem/State.lean",
    "two_pow_64": "lean/LinuxProcessSemantics/LinuxProcessSem/State.lean",
    "PIPE_BUF": "lean/LinuxProcessSemantics/LinuxProcessSem/State.lean",
}

# Function-name spellings of division (DIV-2).  Floor forms are absent on
# purpose: `Int.fdiv`/`Int.fmod` are what Rocq's `Z.div`/`Z.modulo` mean.
NAMED_DIVISION = re.compile(
    r"\b(?:Int\.(?:ediv|emod|tdiv|tmod|div|mod)|HDiv\.hDiv|HMod\.hMod)\b")

IDENT = r"[^\W\d][\w'!?]*"
QUALIFIED = re.compile(rf"{IDENT}(?:\.{IDENT})*")
# `_spec` as a name segment: `mmap_spec`, `mmap_spec'`, `mmap_spec_rocq`.  A
# suffix-only test would let a re-encoding named `<spec>_rocq` through.
SPEC_NAME = re.compile(r"_spec(?:'|_|$)")
NUMERAL = re.compile(r"0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\d[\d_]*")
# A closed literal expression: numerals joined by + * ^ under parentheses.
CLOSED_LITERAL = re.compile(
    r"^\s*(?:\(|\)|\+|\*|\^|\s|0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\d[\d_]*)+\s*$")
TYPE_ASCRIPTION = re.compile(r"^(.*?)\s*:\s*(?:Int|Nat|ℤ|ℕ)\s*$", re.S)

# A declaration prefixed on its own line by a modifier command -- `open Nat
# in theorem …`, `set_option … in def …` -- is still that declaration, so
# each of the three readers below takes anything up to an ` in ` on the same
# line as a prefix.  Without it the one-line form was not counted at all.
IN_PREFIX = r"(?:[^\n]*?\bin[ \t]+)?"
DECL = re.compile(
    r"^[ \t]*" + IN_PREFIX + r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|scoped|local)[ \t]+)*"
    r"(theorem|lemma|example)\b", re.M)
# A `let`/`have` inside a statement binds a name the statement goes on to
# use, and its `:=` is the binding's, not the proof's (statement_span).
BINDING_KW = re.compile(r"\b(?:let|have)\b")
# Where a statement ends when no `:=` does: the first equation arm, or the
# next top-level command.  Both are conservative -- text up to that point is
# still linted.
STATEMENT_END = re.compile(
    r":=|^[ \t]*\|[ \t]|^(?:theorem|lemma|example|def|abbrev|instance|structure|"
    r"inductive|namespace|section|end|open|set_option|variable|universe|#)\b",
    re.M)

# A helper under Checks/Cases (PIN-7): read to the next top-level command,
# body included.
DEF = re.compile(
    r"^[ \t]*" + IN_PREFIX + r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|scoped|local|partial|unsafe)[ \t]+)*"
    r"(def|abbrev)\b", re.M)
COMMAND = re.compile(
    r"^(?:@\[|(?:theorem|lemma|example|def|abbrev|instance|structure|inductive|"
    r"class|opaque|axiom|macro|macro_rules|syntax|elab|notation|namespace|section|"
    r"end|open|set_option|variable|universe|attribute|export|mutual|private|"
    r"protected|noncomputable|nonrec|scoped|local|partial|unsafe|deriving)\b|#)",
    re.M)
# The outcome tokens a pin's kernel side may name (PIN-5): the `Ok`
# constructor, an errno constant or its wrapper, the decline.
OUTCOME = re.compile(r"\bOk\b|\bE[A-Z][A-Z0-9]+\b|\berrno_ret\b|\bUnmodeled\b")
# An input builder under Checks/Cases (PIN-8): `def name … : SyscallInput :=
# … mkInput N …`, read on the blanked text of the whole def.
INPUT_BUILDER = re.compile(r":\s*SyscallInput\s*:=(.*)$", re.S)
MK_INPUT = re.compile(r"\bmkInput\s+(\d+)\b")
# The literal-input dispatcher shape a pin reaches an arm through (PIN-8):
# the builder or the literal has to be `syscall_spec`'s argument.
SYSCALL_MK_INPUT = re.compile(r"\bsyscall_spec\s*\(\s*(?:SyscallInput\.)?mkInput\s+(\d+)\b")
# The propositional constants a positive or negative pin may not carry
# (PIN-8): `∨ True` admits nothing, `∧ False` refutes nothing.
TRUE_FALSE = re.compile(r"\bTrue\b|\bFalse\b")
# A command that binds a name outside `def`/`abbrev`, which PIN-7 cannot
# follow; refused under Checks/Cases except in Tactic.lean.  `opaque`,
# `instance` (an `Inhabited SpecArm` reached through `default`), `axiom` and
# the type-forming commands bind values or fields the `def` reader never
# reads; Cases files write none of them (`deriving instance` is not
# `instance`, and Tactic.lean's `structure` is exempt with its file).
NOTATION = re.compile(
    r"^[ \t]*" + IN_PREFIX + r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:local|scoped|private|protected|noncomputable|unsafe)[ \t]+)*"
    r"(notation|macro|macro_rules|syntax|elab|elab_rules|infixl|infixr|infix|prefix|postfix|"
    r"declare_syntax_cat|opaque|instance|axiom|structure|inductive|class)\b", re.M)
# The keywords above that CAN declare their syntax category, and so can be
# read as binding tactic syntax rather than a name a statement could use.
# `notation` and the `infix`/`prefix`/`postfix` forms are not among them:
# they bind term notation whatever follows, and stay refused.
CATEGORY_KEYWORDS = frozenset(
    ("macro", "macro_rules", "syntax", "elab", "elab_rules"))
# A guillemet-quoted name, `«fixture arm»`, is one no identifier reader here
# resolves, so a holder or alias spelled that way is invisible: refused.
GUILLEMET = re.compile(r"«")
# `open Foo renaming bar → length`: a second spelling for a definition, and
# the arm reader trusts heads by their spelling (PIN-7).
RENAMING = re.compile(r"(?<![\w'.])renaming(?![\w'])")
# A tactic block.  In a STATEMENT it elaborates to a term no reader here
# follows -- `(by rocq i m o : Prop)` is `mmap_spec_rocq …` once `rocq` is an
# exempt tactic macro -- so it is refused wherever a statement is read.
BY_BLOCK = re.compile(r"(?<![\w'.])by(?![\w'])")
TACTIC_FILE = CASES_DIR + "/Tactic.lean"
# The tactic, its readings and the register moved to TacticCore (T180) so that
# a twin's pins can import them without `Specs`; the file is exempt as Tactic.lean is.
TACTIC_CORE_FILE = CASES_DIR + "/TacticCore.lean"


def declares_tactic_syntax(text, start):
    """Does the syntax declaration at `start` declare the `tactic` category?

    PIN-7 refuses these commands because a name they bind is an alias no
    `def` reader follows, so a pin STATED through it escapes PIN-1 and
    PIN-7.  That reason reaches term syntax and stops at tactic syntax: a
    tactic appears in a theorem's statement only inside a `by` block, and
    check_pins refuses a `by` block in every statement and the tactic's
    token in every Cases helper, so no pin can be stated through one.  Nor
    can the refusal be obeyed -- `Checks/Cases/Tactic.lean`
    imports `SysSimp` and `Specs` only, so a tactic naming one module's
    checkers (`check_getgroups`) cannot live there, and the rule would
    forbid a shape with no home.

    The category is read from the declaration's header: the text up to the
    first `=>` outside brackets, or the end of the KEYWORD'S LINE when there
    is none (`syntax "foo" : tactic`).  A header that wraps onto a second
    line is therefore cut before its category and refused, which is the
    fail-closed direction and is pinned by a case.  A header ending
    `: tactic` is tactic syntax;
    ANYTHING ELSE IS REFUSED, including a header this reader cannot parse
    and a `macro_rules` that declares no category at all.  So the exemption
    fails closed, and the cost is an allowlist of one: a tactic spelled in a
    category this reader does not know is a finding until it is named here.
    """
    i = syntax_header_end(text, start)
    return re.search(r":\s*tactic\s*$", text[start:i].rstrip()) is not None


# The `command` category, and what a command elaborator may not do to stay
# exempt from PIN-7.
COMMAND_CATEGORY = re.compile(r":\s*command\s*$")
# The heads of Lean 4.34's families of functions that put a declaration into
# the environment, or run syntax that does, matched by PREFIX and refused in
# every Cases file: `elabCommand` is also `elabCommandTopLevel`, `addDecl` is
# also `addDeclWithoutChecking` and `Environment.addDeclCore`, and a `\b`
# after the stem read each of those as a different name -- the deep review
# of this branch declared `emitted_free : Nat → Prop` from a Cases file
# through `runParserCategory` and `elabCommandTopLevel`, and again through
# `Meta.mkAuxDefinition`, with this tool silent.  The list is a second line,
# not the premise: the premise is `command_reads_only`, which trusts nothing
# it does not know.
EMITTER = re.compile(
    r"\b(?:addDecl|addAndCompile|addConst|compileDecl|elabCommand|elabDeclaration|"
    r"elabMutualDef|elabInductive|elabStructure|elabClass|mkAuxDefinition|mkAuxTheorem|"
    r"mkAuxLemma|setEnv|modifyEnv|withEnv|runParserCategory|runParser|evalDecl|evalTerm|"
    r"evalExpr|evalConst)\w*")
# A quotation builds syntax; the rest is the family above.  Read over the
# whole file of a command elaborator (`command_emission`).
COMMAND_EMITS = re.compile(r"`\(|" + EMITTER.pattern)
# Commands that RUN elaborator code where they stand, with no syntax
# declaration for the exemption above to read: `run_cmd do … elabCommand
# stx` and `#eval show CommandElabM Unit from …` each declared a helper from
# a Cases file under v4.34.0 (a string parsed with `runParserCategory` has
# no hygiene, so the helper keeps the name a pin then uses), and
# `initialize x : T ← e` declares `x` in a shape the `def` reader never
# sees.  Refused in every Cases file, Tactic.lean included; none uses one.
RUNS_AT_BUILD = re.compile(
    r"^[ \t]*(run_cmd|run_elab|run_meta|#eval|initialize|builtin_initialize)\b", re.M)
# What a READ-ONLY command elaborator may name, by identifier segment.  The
# exemption for the command category rests on this list being read-only:
# every segment of every identifier in the elaborator's block, and in every
# Cases helper it calls, is either here, bound in the block, a Lean keyword,
# a type or namespace (upper-case initial, and not a Cases helper), or a name
# literal (`` `sys_simp ``).  Anything else refuses the exemption, so a new
# API use has to be argued onto this list rather than passing by default.
# The entries are what `Checks/Cases/Prelude.lean`'s `#check_prelude_register`
# and `Tactic.lean`'s `checkSysSimpRegister` need, plus reads of the same
# kind: the environment and its simp extension, logging, and List/Array/Name
# arithmetic.  Nothing here takes a `Declaration`, an `Environment` to
# install, or `Syntax` to elaborate.
READ_ONLY_API = frozenset((
    "getEnv", "getOptions", "getRef", "getScope", "getCurrNamespace", "getMainModule",
    "liftCoreM", "liftTermElabM", "liftMacroM",
    "getSimpExtension?", "getTheorems", "lemmaNames", "toUnfold", "erased", "isLemma",
    "throwError", "throwErrorAt", "logInfo", "logInfoAt", "logWarning", "logWarningAt",
    "logError", "logErrorAt",
    "fold", "foldl", "foldr", "push", "filter", "filterMap", "map", "contains", "isEmpty",
    "isPrefixOf", "isSuffixOf", "any", "all", "size", "length", "toList", "toArray",
    "qsort", "reverse", "find?", "get?", "getD", "head?", "getLast?", "append", "erase",
    "insert", "toString", "isSome", "isNone", "not", "and", "or", "beq", "isEq",
    "decEq", "getPrefix", "components", "isAnonymous", "isInternal", "toName", "str",
    "mkStr", "mkNum", "num",
    # constructor names met in patterns
    "ok", "error", "decl", "fvar", "inl", "inr",
))
# Words Lean reads as syntax, which the identifier regex reads as names.
LEAN_WORDS = frozenset((
    "do", "let", "mut", "match", "with", "if", "then", "else", "unless", "return", "for",
    "in", "fun", "at", "by", "have", "show", "from", "where", "true", "false", "some",
    "none", "pure", "elab", "macro", "syntax", "command", "tactic", "term", "ident",
    "namespace", "section", "end", "open", "rfl", "trivial", "sorry", "Prop", "Type",
    "Sort", "_", "Unit", "unit", "discard", "try", "catch", "finally", "instance",
    "m!", "s!", "f!",  # interpolation prefixes, one identifier each to IDENT
    # declaration keywords, met when a Cases helper's text is walked
    "def", "abbrev", "theorem", "lemma", "example", "private", "protected",
    "noncomputable", "partial", "unsafe", "scoped", "local", "opaque", "structure",
    "inductive", "class", "deriving", "attribute", "export", "universe", "variable",
    "set_option", "mutual", "nonrec",
))
# Where a block binds a name: `let x`, `let some x ←`, `fun x y =>`, `| pat =>`,
# `for x in`, a named argument or field `x :=`, and `(x : T)` binder groups.
BOUND_IN_BLOCK = (
    re.compile(r"\blet\b[ \t]+(?:mut[ \t]+)?([^:=←\n]*)"),
    re.compile(r"(?:\bfun\b|λ)[ \t]+([^=↦\n]*?)(?:=>|↦)"),
    re.compile(r"^[ \t]*\|[ \t]*([^=\n]*?)=>", re.M),
    re.compile(r"\bfor\b[ \t]+([^\n]*?)\bin\b"),
    re.compile(r"([^\W\d][\w'!?]*)[ \t]*:="),
    re.compile(r"[(\[{⦃][ \t]*([^:()\[\]{}⦃⦄\n]*?)[ \t]*:(?!=)"),
    re.compile(r"([^\W\d][\w'!?]*):[A-Za-z]"),  # `x:term` in a syntax header
)


def declares_command_syntax(text, start):
    """Does the syntax declaration at `start` declare the `command` category?

    Read exactly as `declares_tactic_syntax` reads `tactic`, and with the
    same fail-closed cut: a header that wraps past the keyword's line is
    not read as a command."""
    i = syntax_header_end(text, start)
    return COMMAND_CATEGORY.search(text[start:i].rstrip()) is not None


def command_emission(text, start):
    """What the `command` elaborator at `start` does that could put a
    declaration into the environment, or None when its body does none of it.

    PIN-7's reason -- a name bound by a syntax command is an alias no `def`
    reader follows, so a pin STATED through it escapes PIN-1 and PIN-7 --
    reaches the term category and stops at two others.  It stops at
    `tactic` because a tactic reaches a statement only inside a `by` block,
    which is refused everywhere a statement is read; it stops at `command`
    for a stronger reason, which is that Lean has no term position for a
    command at all, so no pin can be stated through one however it is
    written.  `Checks/Cases/Prelude.lean`'s `#check_prelude_register` is
    the shape: a command that READS the `sys_simp` extension after the
    namespace closes and fails the build when the register drifts from what
    the header names.

    What the command category CAN do that a tactic cannot is declare: an
    `elab … : command` that elaborates a quotation, or calls `addDecl`,
    puts a theorem or a `def` into the environment whose text is in no
    file, and every reader here reads text.  A generated PIN is invisible,
    which costs coverage and not soundness (PIN-8 counts what it reads), but
    a generated HELPER is a name a pin's statement can then use and PIN-6's
    predicate reader cannot resolve -- a silent miss, which is the direction
    this file refuses.  So the exemption is for a command elaborator that
    emits nothing, and anything that could emit is a finding naming what it
    matched.

    The scan is over the WHOLE FILE rather than the elaborator's body, which
    is the half of this that text can close: the emission may be one call
    away (`def emit : CommandElabM Unit := do elabCommand …`, run by the
    body), and a reader of the body alone sees only a call it cannot follow.
    Scanning the file catches that helper where it is written, and costs a
    Cases file holding a quotation anywhere its command exemption -- the
    fail-closed direction.  A helper in ANOTHER Cases file is not this
    function's to catch: the emitter family is refused in every Cases file
    by `check_pins` whether a command stands beside it or not, and
    `command_reads_only` walks into every Cases helper the block names,
    whichever file defines it.

    This list is the second line and not the premise.  Matched by prefix
    since the deep review of this branch found `elabCommandTopLevel`,
    `addDeclWithoutChecking`, `Meta.mkAuxDefinition`, `elabDeclaration` and
    `setEnv` after `Environment.addDeclCore` all passing a `\b`-terminated
    version of it, two of them shown declaring a helper under v4.34.0.  A
    name this list does not carry is the premise's to refuse."""
    del start
    hit = COMMAND_EMITS.search(text)
    return hit.group(0) if hit else None


def command_block(text, start):
    """The text of the syntax command at `start`, to the next top-level
    command (the invocation `#name` that usually follows is one)."""
    e = COMMAND.search(text, start + 1)
    return text[start:e.start() if e else len(text)]


def bound_names(block):
    """Every name the block binds, read off the six shapes in BOUND_IN_BLOCK.
    Over-approximate on purpose: a pattern's constructor (`.decl n _ _`
    yields `decl`) and a binder's type land here too, and neither can run
    anything."""
    out = set()
    for rx in BOUND_IN_BLOCK:
        for m in rx.finditer(block):
            out.update(idents(m.group(1)))
    return out


def command_reads_only(block, helpers, seen=None):
    """None when the command elaborator's `block` is read-only under
    READ_ONLY_API, else (identifier, where) for the first name that is not.

    Every segment of every identifier is judged, not the last alone: a
    dotted chain applies each segment to the one before it, so `env.f.g`
    runs `f`.  A segment passes when it is bound in the block, a Lean word,
    on READ_ONLY_API, or upper-case initial and not a Cases helper -- a
    type, a namespace, a constructor; Lean's functions are lowerCamel and
    every declaring API named in EMITTER is.  A name literal (`` `sys_simp ``,
    `` ``Nat ``) is data and skipped whole, and so is the `#token` of the
    file's own command.  A segment that names a Cases helper (`helpers`:
    name -> body, every file of the tree, Tactic.lean included) is judged by
    walking that helper's body under the same rule, which is how the
    emission one call away in another file is met where it is written.
    The residual is a segment on this list, or an upper-case one, that a
    later Lean makes declare; the list's comment says what it admits."""
    seen = set() if seen is None else seen
    bound = bound_names(block) | LEAN_WORDS
    for m in QUALIFIED.finditer(block):
        prev = block[m.start() - 1] if m.start() else ""
        if prev in "`#":
            continue
        for seg in m.group(0).split("."):
            # A Cases helper is walked BEFORE the bound and API sets are
            # consulted: a local or a named argument spelled like a helper
            # would otherwise hide the helper's body, and walking it when
            # the name was only a local is the fail-closed direction.
            if seg in helpers:
                if seg in seen:
                    continue
                seen.add(seg)
                inner = command_reads_only(helpers[seg], helpers, seen)
                if inner is not None:
                    return inner[0], inner[1] or f"the Cases helper `{seg}`"
                continue
            if seg in bound or seg in READ_ONLY_API or seg[:1].isupper():
                continue
            return m.group(0), None
    return None


# The two commands that extend a token declared elsewhere.  Their header
# carries no token of its own, so `tactic_token` reads none and the
# exemption has to come from their ALTERNATIVES instead.
RULES_KEYWORDS = frozenset(("macro_rules", "elab_rules"))
# The head of one alternative's pattern: a tactic quotation and the token it
# extends.  Anything else -- a term quotation, a category this reader does
# not know, a pattern it cannot parse -- leaves the block refused.
TACTIC_ALTERNATIVE = re.compile(r"^\s*`\(\s*tactic\s*\|\s*([^\s()]+)")


def tactic_rule_tokens(text, start):
    """The tactic tokens the `macro_rules` (or `elab_rules`) block at
    `start` extends, or None when it is not purely tactic syntax.

    `macro_rules` binds no token in its header, which is why PIN-7 refused
    it outright: the exemption for tactic syntax needs the token, since
    keeping a tactic out of statements and helpers is by its NAME.  The
    token is in the alternatives instead -- ``| `(tactic| check_norm
    $[$loc]?) => …`` -- so read it there, and read EVERY alternative: one
    that is not a tactic quotation is term syntax under a command that also
    carries tactic syntax, and the block is refused whole.  A block with no
    alternative this reader can find is refused for the same reason it
    refuses an unparseable header.  The caller then requires each token to
    be one an exempt header declared, so a `macro_rules` cannot introduce a
    token no `syntax … : tactic` ever declared."""
    e = COMMAND.search(text, start + 1)
    block = text[start:e.start() if e else len(text)]
    depth, cuts = 0, []
    for i, c in enumerate(block):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == "|" and depth == 0:
            cuts.append(i + 1)
    if not cuts:
        return None
    tokens = set()
    for j, cut in enumerate(cuts):
        alt = block[cut:cuts[j + 1] - 1 if j + 1 < len(cuts) else len(block)]
        depth, arrow = 0, None
        for i, c in enumerate(alt):
            if c in OPENERS:
                depth += 1
            elif c in CLOSERS:
                depth -= 1
            elif depth == 0 and alt.startswith("=>", i):
                arrow = i
                break
        m = TACTIC_ALTERNATIVE.match(alt if arrow is None else alt[:arrow])
        if m is None:
            return None
        tokens.add(m.group(1))
    return tokens


def syntax_header_end(text, start):
    """Where the header of the syntax declaration at `start` ends: the first
    `=>` outside brackets, or the end of the keyword's line."""
    depth, i, end = 0, start, len(text)
    while i < end:
        c = text[i]
        if c == "\n" and depth == 0:
            break
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith("=>", i):
            break
        i += 1
    return i


def tactic_token(clean, raw, start):
    """The token a tactic declaration binds -- `check_norm` for `macro
    "check_norm" : tactic =>` -- read from the first string literal of its
    header in the RAW text (the blanked text has emptied it; offsets agree),
    the header's end located in the blanked text.  None when the header
    carries none: `macro_rules` and `elab_rules` extend a token declared
    elsewhere, which this reader then could not keep out of statements and
    helpers, so they are refused even in the tactic category."""
    m = re.search(r'"([^"\n]+)"', raw[start:syntax_header_end(clean, start)])
    return m.group(1) if m else None
OPENERS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSERS = set(OPENERS.values())


class Findings:
    def __init__(self, root):
        self.root = root
        self.lines = []

    def add(self, path, line, rule, message):
        self.lines.append(f"{os.path.join(self.root, path)}:{line}: {rule}: {message}")


def lean_spans(text):
    """(kind, start, end) for every comment and string literal of `text`, in
    order, kind one of "comment", "string", "char".

    Lean block comments nest, `/-- … -/` and `/-! … -/` are block comments
    with prose (and prose slashes) inside, `--` runs to end of line, strings
    take backslash escapes, and a char literal is `'x'` only where the
    quote does not continue an identifier.  A quote inside a comment opens
    nothing, and a comment opener inside a string opens nothing.
    """
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if two == "/-":
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j:j + 2] == "/-":
                    depth += 1
                    j += 2
                elif text[j:j + 2] == "-/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            yield "comment", i, j
            i = j
        elif two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            yield "comment", i, j
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            yield "string", i, j
            i = j
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")):
            m = re.match(r"'(?:\\.|[^'\\\n])'", text[i:])
            if m:
                yield "char", i, i + m.end()
                i += m.end()
            else:
                i += 1
        else:
            i += 1


def blank_comments_and_strings(text):
    """The same text with every comment and string literal turned to spaces.

    Length and newlines are preserved, so an offset into the result is an
    offset into the source and `text.count('\\n', 0, i)` is still the line.
    What counts as a comment or a literal is `lean_spans`'s.
    """
    out = list(text)
    for _, i, j in lean_spans(text):
        for k in range(i, j):
            if text[k] != "\n":
                out[k] = " "
    return "".join(out)


def lean_files(root, rel):
    d = os.path.join(root, rel)
    if not os.path.isdir(d):
        sys.exit(f"{d}: no such directory. Both rules would then pass over "
                 "nothing, which is the vacuous verdict this check refuses.")
    out = []
    for dirpath, dirnames, filenames in os.walk(d):
        dirnames[:] = sorted(x for x in dirnames if not x.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".lean") and not name.startswith("._"):
                out.append(os.path.relpath(os.path.join(dirpath, name), root))
    if not out:
        sys.exit(f"{d}: holds no .lean file, so there is nothing to lint and "
                 "a clean verdict would be vacuous.")
    return out


def line_of(text, offset):
    return text.count("\n", 0, offset) + 1


# ---------------------------------------------------------------- the table

def read_table(root):
    """The registered arms, `{number: Arm}` of tools/gen_lean_registry.py.

    Since T31 the Lean table is not a file: the build renders it into
    `lean/.lake/generated` from one registry module per twin, and
    `gen_lean_registry.arms_in_texts` is the ONE reader of a registered
    arm -- it blanks comments and strings first, and refuses an empty
    read, a duplicate number, an arm applying no `<name>_spec` and a file
    whose `mkSpecArm` count it did not match.  PIN-8 asks it rather than
    matching arm lines again, because a second reader is how the pin lint
    and the docs guard came to disagree about what a `-- TODO: mkSpecArm
    63` line dispatches.

    Its refusals are fatal here for the reason the missing-table exit was:
    PIN-8 holds every arm to a pin pair, so a reader that answered "no
    arms" would hold nothing and say so as a pass.  The import is inside
    the function because `gen_lean_registry` imports this module for
    `blank_comments_and_strings`; at module level the two would form a
    cycle that fails on whichever is imported first."""
    import gen_lean_registry  # noqa: PLC0415 -- see the docstring: import cycle
    try:
        return gen_lean_registry.registry_arms(root)
    except gen_lean_registry.Refusal as e:
        sys.exit(f"check_lean_pins.py: PIN-8 reads the arms through "
                 f"gen_lean_registry, which refused them: {e}")


# --------------------------------------------------------------- PIN-1/PIN-2

def statement_span(clean, start, after):
    """(end, text) of the statement whose keyword begins at `start` and
    ends at `after`; the search for the end starts past the keyword, which
    STATEMENT_END would otherwise match at once.  A `:=` under an open
    bracket is not the end: `{ m with m_tid := none }` is a structure
    update inside the statement, and cutting there would hide everything
    after it -- a second spec, a `∨ True` -- from every statement rule.
    Nor is the `:=` of a depth-0 `let`/`have` (BINDING_KW), one per
    binding: the statement continues after the bound value."""
    pos, bindings = after, 0
    while True:
        m = STATEMENT_END.search(clean, pos)
        if not m:
            return len(clean), clean[start:]
        if m.group(0) == ":=":
            if bracket_depth(clean, start, m.start()) > 0:
                pos = m.end()
                continue
            # `let x := …; P x` or `have h : T := …; P` in a statement: the
            # `:=` is the binding's, and the statement runs on past it.
            # Cutting there hid everything after the binding from every
            # statement rule.
            bound = sum(1 for b in BINDING_KW.finditer(clean, start, m.start())
                        if bracket_depth(clean, start, b.start()) == 0)
            if bound > bindings:
                bindings += 1
                pos = m.end()
                continue
        return m.start(), clean[start:m.start()]


def bracket_depth(text, a, b):
    """Brackets opened and not closed over `text[a:b]`, never below zero."""
    depth = 0
    for c in text[a:b]:
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS and depth:
            depth -= 1
    return depth


def split_header_binders(stmt):
    """(name, binders, type) of a statement: the name after the keyword,
    the binder text up to the first depth-0 colon, the type after it.
    `example` has no name."""
    body = stmt.lstrip()
    kw, _, rest = body.partition(" ") if " " in body else (body, "", "")
    if kw == "example":
        name = None
    else:
        m = re.match(r"\s*(\S+)", rest)
        name = m.group(1) if m else None
        rest = rest[m.end():] if m else ""
    depth = 0
    for i, c in enumerate(rest):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == ":" and depth == 0:
            return name, rest[:i], rest[i + 1:]
    return name, rest, ""


def split_header(stmt):
    """(name, type) of a statement; tools/check_lean_pin_evidence.py reads
    this shape."""
    name, _, ty = split_header_binders(stmt)
    return name, ty


def strip_foralls(ty):
    """`ty` with every leading `∀ binders,` removed.  Kept as the string
    form because tools/check_lean_pin_evidence.py reads it; the binders
    PIN-3 needs come from `strip_foralls_binders`."""
    return strip_foralls_binders(ty)[0]


def strip_foralls_binders(ty):
    """(type, binder text) with every leading `∀ binders,` removed; the
    binders are returned so PIN-3 and PIN-5 can read them like the header's."""
    ty = ty.lstrip()
    binders = []
    while ty.startswith("∀"):
        depth = 0
        cut = None
        for i, c in enumerate(ty):
            if c in OPENERS:
                depth += 1
            elif c in CLOSERS:
                depth -= 1
            elif c == "," and depth == 0:
                cut = i
                break
        if cut is None:
            break
        group = ty[1:cut].strip()
        # `∀ (o : T),` already brackets its group; `∀ o : T,` and `∀ o,` do
        # not, and would otherwise read as no binder at all -- so a premise
        # naming `o` would count as closed.  Bracket the bare form.
        if not group.startswith(tuple(OPENERS)):
            group = "(" + group + ")"
        binders.append(group)
        ty = ty[cut + 1:].lstrip()
    return ty, " ".join(binders)


def top_level(ty, wanted):
    """Offsets of every depth-0 occurrence of a character in `wanted`; `=`
    counts only as an equation, not as part of `:=`, `=>`, `==`, `≠`…"""
    out = []
    depth = 0
    for i, c in enumerate(ty):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and c in wanted:
            if c == "=":
                before = ty[i - 1] if i else ""
                after = ty[i + 1] if i + 1 < len(ty) else ""
                if before in "<>!=:≠" or after in "=>":
                    continue
            out.append(i)
    return out


def strip_parens(s):
    """`s` without whitespace at the ends and without outer parentheses
    that enclose the whole of it: `((A))` is `A`, `(A) ∧ (B)` stays."""
    s = s.strip()
    while s.startswith("(") and matching_paren(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    return s


def implication(ty):
    """(premises, conclusion) of `A → B → C`, split at every top-level
    `→`: `→` is right-associative, so the conclusion is the last segment."""
    arrows = top_level(ty, "→")
    if not arrows:
        return [], ty
    parts, start = [], 0
    for i in arrows:
        parts.append(ty[start:i])
        start = i + 1
    parts.append(ty[start:])
    return parts[:-1], parts[-1]


def top_level_split(ty):
    """The two sides of the one top-level `↔`, or of the one top-level `=`
    when nothing binds looser than it (no depth-0 `→`, `∧`, `∨` or `¬`, so
    `A → B = C ∧ D` is an implication, not an equation); else None.
    PIN-5 reads the side this returns as the kernel's answer, so splitting
    an implication at its conclusion's `=` would hand it `none` out of
    `… → m_killed m' = none` and report a pin that names `Ok` in its
    premise.  `vacuous` wants the conclusion split too and cuts the chain
    itself, with `implication`, before asking."""
    iffs = top_level(ty, "↔")
    if len(iffs) == 1:
        i = iffs[0]
        return "↔", ty[:i], ty[i + 1:]
    eqs = top_level(ty, "=")
    if not iffs and len(eqs) == 1 and not top_level(ty, "→∧∨¬"):
        i = eqs[0]
        return "=", ty[:i], ty[i + 1:]
    return None


def vacuous(ty, binder_premises=()):
    """(connective, side) when `ty` is `A ↔ A`, `A = A` or `A → A` up to
    whitespace and outer parentheses, on the whole or on the conclusion
    of its implication chain; None otherwise.  `binder_premises` are
    hypotheses written as binders, `(h : A) : A`, read as `A → A`."""
    premises, conclusion = implication(ty)
    premises = list(premises) + list(binder_premises)
    for candidate in (ty, conclusion) if premises else (ty,):
        split = top_level_split(candidate)
        if split and normalize(strip_parens(split[1])) == normalize(strip_parens(split[2])) \
                and normalize(split[1]).strip():
            return split[0], normalize(strip_parens(split[1]))
    for p in premises:
        if normalize(strip_parens(p)) == normalize(strip_parens(conclusion)):
            return "→", normalize(strip_parens(p))
    return None


# A binder type that is a proposition rather than data.  `→` is absent on
# purpose: `(mem : word → Option byte)` is a function type.  `∀` and `∃`
# are propositions in this tree's binders (no dependent function type is
# written with `∀`), and the docstring states that reading.  The set
# memberships are here for the same reason and were added with PIN-5: a
# binder read as data has its names counted among the pin's variables, so
# a missing token does not merely skip a hypothesis, it can make a closed
# one look like it names something.
PROP_TOKEN = re.compile(r"[≠↔<≤>≥¬∧∨∃∀∣∈∉⊆]|\bFalse\b|\bTrue\b")


def binder_groups(binders):
    """[(names, type)] for every `(…)`, `{…}` and `⦃…⦄` binder group;
    instance binders `[…]` are skipped."""
    out = []
    i = 0
    while i < len(binders):
        c = binders[i]
        if c in "({⦃":
            depth, j = 0, i
            while j < len(binders):
                if binders[j] in OPENERS:
                    depth += 1
                elif binders[j] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = binders[i + 1:j]
            k = top_level(inner, ":")
            if k:
                out.append((normalize(inner[:k[0]]), inner[k[0] + 1:]))
            elif normalize(inner):
                # `∀ o,` -- names with no type are data binders (a Prop
                # binder always carries its type).
                out.append((normalize(inner), ""))
            i = j + 1
        else:
            i += 1
    return out


def is_prop(ty, own_name, prop_names=frozenset()):
    """Does a binder type read as a proposition: a relation, a connective,
    a constant, a spec application, or an application of a name in
    `prop_names` -- a `def … : Prop` of the model or of Checks/Cases
    (prop_heads)?  Judged with the outer parentheses off: `(h : ((1 : Int)
    = 2))` is 5e's closed hypothesis wrapped once more, and read with them
    on its `=` sits at depth 1, so the binder passed as data and `h` joined
    the pin's variables (the deep review of #773 wrote that probe)."""
    ty = strip_parens(ty)
    if PROP_TOKEN.search(ty) or top_level(ty, "="):
        return True
    if any(SPEC_NAME.search(w) and w != own_name
           for w in (x.group(0) for x in QUALIFIED.finditer(ty))):
        return True
    head = QUALIFIED.match(ty.strip())
    return bool(head) and last(head.group(0)) in prop_names


def spec_headed(prop, own_name):
    """Is `prop` an application of a spec (optionally negated): the
    antecedent shape PIN-3 accepts as the one-directional half of an iff."""
    head = strip_parens(prop)
    head = head[1:].lstrip() if head.startswith("¬") else head
    first = QUALIFIED.match(head)
    return bool(first and SPEC_NAME.search(first.group(0)) and first.group(0) != own_name)


# The relations a premise can be reflexive over: `A op A` is settled by its
# shape alone, true (`=`, `≤`) or false (`≠`, `<`), so a pin under it either
# never needed it or closes by `(h rfl).elim`.  `top_level_split` knows `↔`
# and `=` alone, and `(h : m ≠ m)` -- 5f with one character changed --
# passed the round's reader (the deep review of #773).
REFLEXIVE_OPS = ("↔", "=", "≠", "<", "≤", ">", "≥")


def reflexive(prop):
    """`A op A` or `¬ (A op A)` when `prop` has that shape over exactly one
    top-level relation, up to whitespace and outer parentheses; None
    otherwise.  The first relation with one top-level occurrence decides,
    so `m = a ∧ m ≠ a` (one `=`, sides differ) is not reflexive."""
    body = strip_parens(prop)
    negated = body.startswith("¬")
    if negated:
        body = strip_parens(body[1:])
    for op in REFLEXIVE_OPS:
        at = top_level(body, op)
        if len(at) != 1:
            continue
        i = at[0]
        left, right = normalize(strip_parens(body[:i])), normalize(strip_parens(body[i + 1:]))
        if left and left == right:
            return f"¬ (A {op} A)" if negated else f"A {op} A"
        return None
    return None


def root_idents(text):
    """The ROOT segment of every qualified name in `text`: `i.in_sysno` and
    `(m_vmmaps m).vm_limit` are about the binders `i` and `m`, and a rule
    that compared the dotted name would call `exit_sysno i.in_sysno` closed
    (it did, on Checks/Cases/Run.lean's `exit_post_model_is_not_killed`)."""
    return {x.group(0).split(".", 1)[0] for x in QUALIFIED.finditer(text)}


def bad_premise(prop, used_names, own_name):
    """Why a hypothesis `prop` cannot be about the pin's call, or None: it
    names none of `used_names` -- the pin's LIVE data binders, those that
    reach its conclusion directly or through another hypothesis (see
    `hypotheses`) -- so it is closed, or about a binder the call never
    reads (`(x : Int) (h : 0 < x ∧ x < 0)`, which passed while the check
    was against every data binder; the deep review of #773); or it is
    reflexive.  Each CONJUNCT is judged the same two ways, so that a part
    closed or reflexive on its own closes the whole hypothesis
    (`(h : x = 3 ∧ (0 : Int) = 1)`), while a pair unsatisfiable only
    together (`m = a ∧ m = b`) still passes -- no part of it is closed,
    and deciding it is not this reader's.  A premise headed by the spec
    gets no exemption: one
    that names the pin's variables passes the closed check on its own
    (Fork.lean's `(hspec : set_tid_address_spec i m (Ok eff m' evs))`),
    and one that names none is `False` in spec clothing -- a spec applied
    to a fixture at an outcome some pin already refutes closes the pin by
    `.elim`, and the round-0 review wrote exactly that probe."""
    if not (root_idents(prop) & used_names):
        return "names none of the pin's variables that reach its conclusion, so it is closed"
    shape = reflexive(prop)
    if shape:
        return f"is `{shape}`"
    parts = conjuncts(prop)
    if len(parts) > 1:
        for part in parts:
            if not (root_idents(part) & used_names):
                return (f"has the conjunct `{normalize(part)}`, which names none of "
                        "them either, so that conjunct is closed on its own and the "
                        "others do not rescue it")
            shape = reflexive(part)
            if shape:
                return f"has the conjunct `{normalize(part)}`, which is `{shape}`"
    return None


def hypotheses(binders, ty, own_name, prop_names=frozenset()):
    """The hypotheses a statement takes that PIN-3 refuses: Prop binders in
    its header and `∀` prefix, and top-level premises, each judged by
    `bad_premise` against the pin's LIVE data binders: those its conclusion
    uses, and those sharing a hypothesis with a live one, to a fixpoint.
    `(x : Int) (hx : x = (m_vmmaps m).vm_limit) (h : 0 < x)` keeps `h`,
    since `hx` ties `x` to `m`; `(x : Int) (h1 : 0 < x) (h2 : x < 0)` loses
    both, since nothing ties `x` to the call -- judged against "the rest of
    the statement" instead, each of the pair vouched for the other and the
    split passed what the conjunction `(h : 0 < x ∧ x < 0)` is refused for
    (the deep review of #813, round 5).  `prop_names` are the heads whose
    application is a proposition without a token saying so (prop_heads)."""
    groups = binder_groups(binders)
    data_names = set()
    for names, bty in groups:
        if not is_prop(bty, own_name, prop_names):
            data_names.update(names.split())
    props = [(names, bty) for names, bty in groups if is_prop(bty, own_name, prop_names)]
    premises, conclusion = implication(ty)
    parts = [bty for _, bty in props] + list(premises)

    live = data_names & root_idents(conclusion)
    changed = True
    while changed:
        changed = False
        for p in parts:
            names = data_names & root_idents(p)
            if names & live and not names <= live:
                live |= names
                changed = True

    found = []
    for names, bty in props:
        why = bad_premise(bty, live, own_name)
        if why:
            found.append(f"`({names} : {normalize(bty)})`, which {why}")
    for p in premises:
        why = bad_premise(p, live, own_name)
        if why:
            found.append(f"`{normalize(strip_parens(p))} → …`, which {why}")
    return found


def spec_binder_premises(binders, own_name):
    """The types of the Prop binders headed by a spec: premises in binder
    clothing, which `vacuous` compares against the conclusion."""
    return [bty for _, bty in binder_groups(binders)
            if is_prop(bty, own_name) and spec_headed(bty, own_name)]


def normalize(s):
    return " ".join(s.split())


def idents(text):
    """Every qualified identifier in `text`, as written."""
    return [x.group(0) for x in QUALIFIED.finditer(text)]


def last(name):
    return name.rsplit(".", 1)[-1]


def alias_uses(names, aliases, own=None):
    """The aliases the qualified identifiers `names` reach, through ANY
    component: `fixture_arm.admits` applies the value `fixture_arm` holds
    (generalized field notation) as surely as `fixture_arm` names it, so an
    alias is reached from every component and not the last one only."""
    hit = set()
    for a in names:
        for p in a.split("."):
            if p in aliases and p != own:
                hit.add(p)
    return hit


# ------------------------------------------------------------- PIN-5 .. PIN-8

def conjuncts(prop):
    """The depth-0 `∧` parts of a proposition, each without its outer
    parentheses; the whole proposition when there is no `∧`."""
    core = strip_parens(prop)
    cuts = top_level(core, "∧")
    parts, start = [], 0
    for i in cuts:
        parts.append(core[start:i])
        start = i + 1
    parts.append(core[start:])
    return [strip_parens(p) for p in parts]


def model_predicates(root):
    """name -> (file, line) of every `def`/`abbrev` in the model whose
    result type ends in `Bool` or `Prop`: the decision procedures PIN-6
    refuses on a pin's kernel side.  `*_spec` names are left to PIN-1."""
    files = []
    for rel in MODEL_ROOTS:
        if os.path.isfile(os.path.join(root, rel + ".lean")):
            files.append(rel + ".lean")
        if os.path.isdir(os.path.join(root, rel)):
            files += lean_files(root, rel)
    out = {}
    for rel in files:
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            clean = blank_comments_and_strings(f.read())
        for m in DEF.finditer(clean):
            _, sig = statement_span(clean, m.start(1), m.end(1))
            nm = re.match(r"\s*(\S+)", sig[len(m.group(1)):])
            if not nm:
                continue
            name = last(nm.group(1))
            if SPEC_NAME.search(name):
                continue
            rest = sig[len(m.group(1)) + nm.end():]
            colons = top_level(rest, ":")
            if not colons:
                continue
            result = rest[colons[-1] + 1:]
            arrows = top_level(result, "→")
            target = strip_parens(result[arrows[-1] + 1:] if arrows else result)
            if target in ("Bool", "Prop"):
                out.setdefault(name, (rel, line_of(clean, m.start(1))))
    if not out:
        sys.exit(f"{MODEL_ROOTS[0]}: read no `def … : Bool` or `… : Prop` in the "
                 "model's base files. PIN-6's predicate rule would then pass "
                 "every pin vacuously; the model defines such predicates, so "
                 "this is a reader that is no longer reading them.")
    return out


class Pin:
    """A declaration under Checks/Cases that mentions a spec, classified."""

    def __init__(self, rel, line, name, specs, positive, negative, sysnos):
        self.rel, self.line, self.name = rel, line, name
        self.specs, self.positive, self.negative = specs, positive, negative
        self.sysnos = sysnos


# `mkSpecArm N <spec>`: the arm's spec argument (PIN-5, PIN-7).  An arm NAMES
# its spec to say which arm it is, and that name is the table's wiring rather
# than a side of a pin -- `arm.ca_arm = SpecArm.mkSpecArm 93 (fun i =>
# exit_spec (in_arg i 0) i)` says which spec the arm carries and claims
# nothing about what Linux answers.  Reading it as a pin's spec asks PIN-5 for
# an outcome the theorem was never about, and makes every `def` holding an arm
# a PIN-7 alias, so every structural fact about the table becomes a pin too:
# that is the twelve findings K2's Checks/Cases/Checks/Sys/Dispatch.lean took
# when its arm-identity and checker-obligation theorems met these rules.
#
# The exemption is by POSITION, not by spelling.  The wiring is exempt where
# the arm is used as an identity -- compared, listed, looked up, wrapped in
# `some`, read for its number or its checker -- and nowhere else: an arm that
# is OPENED (`arm.2 i m o`, `match arm with | ⟨_, s⟩ => …`), APPLIED (`arm i m
# o`: an arm is a value, not a function) or handed to a function this reader
# does not know (`spec_of arm`, `dispatch [arm]`) applies its spec, and a
# theorem doing that is a pin on that spec whatever the spelling.  A `def`
# holding an arm is a HOLDER: its lookups stay structural, and a statement
# that opens the holder owes the outcome the spec would owe.  An identity
# leaks the arm to its PARTNER: `(h : arm = SpecArm.mkSpecArm 222 s)` hands
# the spec to `s`, `lookup_arm t 222 = some a` hands the arm to `a`, `[a] =
# [arm]` too, and each of those local names is read as the arm from then on
# (partner_names); a partner this reader cannot place makes the identity an
# opening.  Unknown shapes fail closed to "the spec is read".
ARM_CTOR = re.compile(r"\bmkSpecArm\b")
# Relations an arm may stand beside without being read: the identity shapes.
IDENTITY_OPS = {"=", "≠", "∈", "∉", "<", "≤", ">", "≥"}
# Heads that hand the arm on unopened, with the number of arguments each
# takes: the table's own lookups, the constructor of a checked arm, `some`.
# The arity matters because `some arm i m o` is `some arm` APPLIED, and an
# argument past the arity is an application of whatever the head built.  A
# head not here is assumed to open the arm.
WRAPPER_ARITY = {"some": 1, "mkCheckedArm": 6, "lookup_arm": 2, "lookup_ca": 2}
ARM_WRAPPERS = set(WRAPPER_ARITY)
# Heads that read an arm's number, or compare arms, and return neither an arm
# nor a spec.  `dispatch` is deliberately absent: it APPLIES the spec.
# Both lists are matched by NAME, which is only safe while no Cases file
# defines one of these names itself; check_pins refuses that collision at the
# definition rather than trusting the name at each use.
ARM_READERS = {"ca_no", "arms_agree", "arm_numbers", "length"}
# The namespaces a wrapper or reader may be spelled under.  `Fx.some` is not
# `some`: a head qualified by any other namespace is a head this reader does
# not know, and opens the arm.
ARM_NAMESPACES = {"Option", "SpecArm", "CheckedArm", "Dispatch", "Table", "List", "_root_"}
# Projections.  The number and the checker fields end the arm's reach; the
# arm inside a checked arm carries it on; the spec field IS the spec.
NUMBER_PROJ = {"sa_no", "length", "isSome", "isNone"}
CHECKER_PROJ = {"ca_check", "ca_witness", "ca_sound_ok", "ca_sound_unmodeled",
                "ca_complete_ok"}
ARM_PROJ = {"1", "ca_arm"}
# The checker's dispatch over a TABLE of checked arms, from
# Checks/ExecutableSpecs.lean (the twin of Rocq's Checks/ExecutableSpecs.v):
# `check_syscall_in t i eff m` answers with the `ca_check` of the arm
# `lookup_ca` finds, `check_syscall_for_run_in` wraps that in the run's
# accounting, and `lookups_agree_in t n` is an identity between `lookup_arm
# spec_table n` and `(lookup_ca t n).map CheckedArm.ca_arm`.  None reads
# `sa_spec`, so a table a Cases file builds and hands to one of them is not
# opened, exactly as `arm.ca_check i eff m` is not.  Trusted by name like
# ARM_READERS, and on that premise about the model's own body, which
# trusted_heads_keep_their_premise re-reads on every run.
# The same argument over the rest of the checker's readers of an arm or a
# table of them, from `Checks/Progress.lean`, `Checks/DispatchSurface.lean`
# and `Checks/VmMapsDisjoint.lean`: `table_witness t i m` is the
# `ca_witness` of the arm `lookup_ca` finds, `probe_answers_in t n` is that
# witness being an answer rather than the decline, and `arm_preserves_vm c`
# quantifies over `c.ca_check`.  Each reads the checker's own fields and
# none reads `sa_spec`, so an arm handed to one is not opened.
# `arm_preserves inv c` (`Checks/Invariants.lean`) is `arm_preserves_vm`
# with the preserved property a parameter -- the same quantification over
# `c.ca_check`, with `inv.holds` where the VM reading spells `vm_wf
# (m_vmmaps ·)` -- so it is here for the reason its special case is, and
# for a second one the special case does not need: an invariant is a
# property of the MODEL's state on both sides of the implication, so no
# statement of this shape can name what Linux answers to a call, and
# asking it for an outcome (PIN-5) asks for something a preservation lemma
# never has.  What stops that from becoming an escape is the same premise
# as the rest of this list: the body must read `ca_check` and never
# `sa_spec`, which trusted_heads_keep_their_premise re-reads.
CHECKER_READERS = {"check_syscall_in", "check_syscall_for_run_in", "lookups_agree_in",
                   "table_witness", "probe_answers_in", "arm_preserves_vm",
                   "arm_preserves"}
# WHERE each reader takes the arm, or the table of arms: the argument's
# index counted from the head.  Every one of them but `arm_preserves` takes
# it first, which is why the reader below could read the head off the token
# standing immediately before the arm; `arm_preserves inv c` takes it second
# and has to be found by stepping back over the argument in between.  The
# position is part of the trust, not a detail of the walk: the premise each
# comment above states is about the argument the model's `def` binds as the
# arm, so the SAME head with the arm somewhere else is a shape this reader
# cannot place, and falls through to "the spec is read".  The assertion
# keeps the two facts together -- a reader added to either list without a
# position is refused here rather than silently defaulting to first.
READER_ARM_AT = {"ca_no": 0, "arms_agree": 0, "arm_numbers": 0, "length": 0,
                 "check_syscall_in": 0, "check_syscall_for_run_in": 0,
                 "lookups_agree_in": 0, "table_witness": 0, "probe_answers_in": 0,
                 "arm_preserves_vm": 0, "arm_preserves": 1}
assert set(READER_ARM_AT) == ARM_READERS | CHECKER_READERS, \
    "every trusted reader owes the argument position it takes the arm at"
# The checker's WITNESS for a call, whose value is an `outcome
# SyscallEffect`.  Two readings rest on that: a statement applying one names
# an outcome (PIN-5), and the name is not a spec however it is spelled --
# `syscall_spec_witness` has `_spec` as a segment and is `table_witness` over
# `checked_table`, so counting it as a spec makes `syscall_spec_witness i m =
# Unmodeled ↔ …` a pin whose "non-spec side" is the other half of an iff.
# Both are premises about the model's own declaration, which
# `witness_readers_are_outcomes` re-reads: the name must be declared there
# with `outcome` as its result, and `trusted_heads_keep_their_premise`
# refuses a body that comes to reach a spec.
WITNESS_READERS = {"ca_witness", "table_witness", "syscall_spec_witness"}
# A structure field, for reading `ca_witness`'s declared type: it is a field
# of `CheckedArm` rather than a `def`, so the result the trust rests on is on
# its declaration line.
FIELD_DECL = re.compile(r"^[ \t]+([A-Za-z_][\w']*)[ \t]*:([^\n]*)$", re.M)


def is_spec_name(w):
    """Whether the identifier `w` names a spec: `_spec` as a segment, minus
    the witness readers.  The exception is not a spelling exemption -- a name
    is off this list only while the model declares it with an `outcome`
    result, which is not a spec's type."""
    return SPEC_NAME.search(w) is not None and last(w) not in WITNESS_READERS
# Every field the projection chain trusts, plus `map` and `sa_spec`: the
# chain reads `arm.isSome` as the number field, and a Cases `def
# SpecArm.isSome (a : SpecArm) : Sys SyscallEffect := a.2` is what that
# spelling would reach instead.  check_pins refuses such a helper at its
# definition, as it does one named after a wrapper or a reader.
TRUSTED_FIELDS = NUMBER_PROJ | CHECKER_PROJ | ARM_PROJ | {"map", "sa_spec"}
ARM_MAPPER = re.compile(r"^(?:(?:\w+\.)*ca_arm|·\.ca_arm|fun\s+(\w+)\s*=>\s*\1\.ca_arm)$")
# `ca_no` stands beside `sa_no` here because it is ARM_READERS' number
# reader on a CHECKED arm -- `Checks/Sys/Dispatch.lean` defines it as
# `c.ca_arm.sa_no` -- so `t.map ca_no` reads the same number one level up,
# and `(t.map ca_no).all …` is the table's numbers, never its specs.
NUMBER_MAPPER = re.compile(
    r"^(?:(?:\w+\.)*(?:sa_no|ca_no)|·\.(?:sa_no|ca_no)"
    r"|fun\s+(\w+)\s*=>\s*\1\.(?:sa_no|ca_no))$")
# The spellings of the arm constructor an identity's partner may take.
CTOR_HEAD = re.compile(r"^(?:SpecArm\.)?(?:mkSpecArm|mk)\b|^\.(?:mkSpecArm|mk)\b")
# Words that take an arm apart wherever they stand in a statement.
EXTRACTION = re.compile(r"⟨|\bmatch\b")
QUANTIFIERS = {"∀", "∃", "∃!", "Σ", "Π"}
KEYWORDS = {"fun", "λ", "match", "with", "then", "else", "if", "let", "have", "show",
            "from", "by", "do", "in", "at", "where", "deriving", "extends", "of"}
IDENT_CHAR = re.compile(r"[\w'!?₀-₉]")


def argument_span(text, i):
    """(start, end) of the argument beginning at or after `i`: a balanced
    bracket group, else a run of identifier characters.  None when there is
    no argument there, when a group does not close, or when the run is one
    of Lean's keywords."""
    j = i
    while j < len(text) and text[j].isspace():
        j += 1
    if j >= len(text):
        return None
    if text[j] in OPENERS:
        k = matching_bracket(text, j)
        return None if k is None else (j, k + 1)
    if text[j] == "·":
        return (j, j + 1)
    k = j
    while k < len(text) and (IDENT_CHAR.match(text[k]) or text[k] == "."):
        k += 1
    if k == j or text[j:k] in KEYWORDS:
        return None
    return (j, k)


def line_indent(text, i):
    """(line start, indentation) of the line holding offset `i`."""
    j = text.rfind("\n", 0, i) + 1
    k = j
    while k < len(text) and text[k] in " \t":
        k += 1
    return j, k - j


def next_argument(text, e, s):
    """The argument that continues the application whose span starts at `s`
    and ends at `e`, or None.  Lean's `where` fields and a `def`'s next line
    are separated by nothing but a line break, so a token on a LATER line is
    an argument only when its line is indented deeper than the span's own:
    `ca_arm := arm` followed by `ca_check := …` at the same indent is two
    fields, `spec_of` followed by a deeper-indented `arm` is one call."""
    arg = argument_span(text, e)
    if arg is None:
        return None
    if "\n" in text[e:arg[0]]:
        _, own = line_indent(text, s)
        _, theirs = line_indent(text, arg[0])
        if theirs <= own:
            return None
    return arg


def matching_opener(text, j):
    """Offset of the opener matching the closer at `j`, or -1 when the text
    before it holds none."""
    depth = 0
    for i in range(j, -1, -1):
        if text[i] in CLOSERS:
            depth += 1
        elif text[i] in OPENERS:
            depth -= 1
            if depth == 0:
                return i
    return -1


def matching_bracket(text, i):
    """Offset of the closer matching the opener at `i`, over every bracket
    kind at once; None when it never closes."""
    stack = []
    for j in range(i, len(text)):
        c = text[j]
        if c in OPENERS:
            stack.append(OPENERS[c])
        elif c in CLOSERS:
            if not stack or c != stack[-1]:
                return None
            stack.pop()
            if not stack:
                return j
    return None


def opening_bracket(text, i):
    """Offset of the opener matching the closer at `i`, or None."""
    depth = 0
    for j in range(i, -1, -1):
        c = text[j]
        if c in CLOSERS:
            depth += 1
        elif c in OPENERS:
            depth -= 1
            if depth == 0:
                return j
    return None


def enclosing_group(text, s):
    """Offset of the innermost bracket left open at `s`, or None."""
    depth = 0
    j = s - 1
    while j >= 0:
        c = text[j]
        if c in CLOSERS:
            depth += 1
        elif c in OPENERS:
            if depth == 0:
                return j
            depth -= 1
        j -= 1
    return None


def token_before(text, s):
    """(kind, token, start) of the token ending before `s`; kind is
    "ident", "op", "open", "close" or "" at the start of the text."""
    j = s
    while j > 0 and text[j - 1].isspace():
        j -= 1
    if j == 0:
        return "", "", 0
    c = text[j - 1]
    if IDENT_CHAR.match(c) or c == ".":
        k = j
        while k > 0 and (IDENT_CHAR.match(text[k - 1]) or text[k - 1] == "."):
            k -= 1
        return "ident", text[k:j], k
    if c in OPENERS:
        return "open", c, j - 1
    if c in CLOSERS:
        return "close", c, j - 1
    k = j
    while k > 0 and not text[k - 1].isspace() and not IDENT_CHAR.match(text[k - 1]) \
            and text[k - 1] not in OPENERS and text[k - 1] not in CLOSERS:
        k -= 1
    return "op", text[k:j], k


def token_after(text, e):
    """(kind, token, end) of the token beginning at or after `e`."""
    j = e
    while j < len(text) and text[j].isspace():
        j += 1
    if j >= len(text):
        return "", "", len(text)
    c = text[j]
    if IDENT_CHAR.match(c):
        k = j
        while k < len(text) and (IDENT_CHAR.match(text[k]) or text[k] == "."):
            k += 1
        return "ident", text[j:k], k
    if c in OPENERS:
        return "open", c, j + 1
    if c in CLOSERS:
        return "close", c, j + 1
    k = j
    while k < len(text) and not text[k].isspace() and not IDENT_CHAR.match(text[k]) \
            and text[k] not in OPENERS and text[k] not in CLOSERS:
        k += 1
    return "op", text[j:k], k


def applied_head(text, s):
    """(head, index) of the application the span at `s` is an argument of:
    step left over whole arguments -- a bare identifier or a bracketed group
    -- to the leftmost one, which is the head, counting how many arguments
    stand between it and the span.  (None, 0) where the span is not in
    argument position, or where the head is anything but a plain identifier:
    `(f x) y` is an application this reader cannot place, and the caller
    reads that as the arm being opened."""
    j, idx, head = s, 0, None
    while True:
        kind, tok, at = token_before(text, j)
        if kind == "close":
            o = matching_opener(text, at)
            if o < 0:               # a closer with no opener: not a group
                return None, 0
            j, idx, head = o, idx + 1, None
            continue
        if kind == "ident" and tok not in KEYWORDS and tok not in QUANTIFIERS:
            head, j, idx = tok, at, idx + 1
            continue
        break
    return (head, idx - 1) if head is not None else (None, 0)


def arm_head(tok):
    """The name a head token stands for, when it is bare or qualified only by
    ARM_NAMESPACES; None for a head under any other namespace."""
    parts = tok.strip(".").split(".")
    if len(parts) > 1 and not set(parts[:-1]) <= ARM_NAMESPACES:
        return None
    return parts[-1]


def header_binders_end(text):
    """Offset where a declaration's header binders end: the first depth-0
    `:` that is not a `:=`, read past the keyword; the first depth-0 `:=`
    when there is none; else the end.  A `(x : T)` group before it declares
    `x`; the same group after it is an ascription."""
    m = re.match(r"\s*(?:[^\n]*?\bin[ \t]+)?(?:@\[[^\]]*\][ \t]*)*(?:[\w'!?]+[ \t]+)*?"
                 r"(?:theorem|lemma|example|def|abbrev)\b", text)
    i = m.end() if m else 0
    depth, first_assign = 0, None
    for j in range(i, len(text)):
        c = text[j]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == ":" and depth == 0:
            if text[j + 1:j + 2] == "=":
                if first_assign is None:
                    first_assign = j
            else:
                return j
    return first_assign if first_assign is not None else len(text)


def def_value_at(text):
    """Offset of the `:=` that binds a `def`'s value, or None for the
    `where` form (whose fields bind their own)."""
    depth = 0
    for j in range(len(text) - 1):
        c = text[j]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text[j:j + 2] == ":=":
            return None if re.search(r"\bwhere\b", text[:j]) else j
    return None


def partner_after(text, i):
    """(start, end) of the operand beginning at `i`: a head with its
    arguments, each with its projection chain, up to the next operator;
    None when nothing readable is there."""
    j = i
    while j < len(text) and text[j].isspace():
        j += 1
    start, end = j, None
    while True:
        arg = argument_span(text, j)
        if arg is None:
            break
        j = arg[1]
        while j < len(text) and text[j] == ".":
            k = j + 1
            while k < len(text) and IDENT_CHAR.match(text[k]):
                k += 1
            if k == j + 1:
                break
            j = k
        end = j
    return (start, end) if end is not None else None


def partner_before(text, i):
    """(start, end) of the operand ending before `i`: bracket groups and
    identifier chains read backwards until an operator, an opener or the
    start of the text; None when nothing readable is there."""
    j = i
    while j > 0 and text[j - 1].isspace():
        j -= 1
    end, start = j, None
    while j > 0:
        c = text[j - 1]
        if c in CLOSERS:
            k = opening_bracket(text, j - 1)
            if k is None:
                return None
            j = k
        elif IDENT_CHAR.match(c) or c == ".":
            k = j
            while k > 0 and (IDENT_CHAR.match(text[k - 1]) or text[k - 1] == "."):
                k -= 1
            j = k
        else:
            break
        start = j
        while j > 0 and text[j - 1].isspace():
            j -= 1
    return (start, end) if start is not None else None


def split_top(text, sep=","):
    """`text` split at each depth-0 `sep`."""
    parts, depth, last_cut = [], 0, 0
    j = 0
    while j < len(text):
        c = text[j]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(sep, j):
            parts.append(text[last_cut:j])
            j += len(sep)
            last_cut = j
            continue
        j += 1
    parts.append(text[last_cut:])
    return parts


def top_ascription(text):
    """Index of the depth-0 `:` that ascribes a type to `text` (`arm :
    SpecArm`), None when there is none: `::` and `:=` are not one."""
    depth = 0
    for j, c in enumerate(text):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == ":" and depth == 0:
            if text[j + 1:j + 2] in (":", "=") or text[j - 1:j] == ":":
                continue
            return j
    return None


def partner_names(text, holders):
    """What an identity hands the arm to, read from its partner operand:
    (known, arm_locals, spec_locals).  `known` is False for a partner this
    reader cannot place, which makes the identity an opening.  A bare local
    name (with `.1`/`.ca_arm` projections) is in `arm_locals`: it IS the arm
    from then on.  A constructor whose spec argument names no `_spec` --
    `SpecArm.mkSpecArm 222 s`, `⟨222, s⟩`, `{ sa_no := 222, sa_spec := s }` --
    puts the names in that argument in `spec_locals`: each is the arm's spec
    from then on, and applying it is applying the spec.  `some`, a list, a
    cons chain and a tuple are read component by component; a holder, a
    numeral, `none`, `[]`, a constructor with a closed spec argument and an
    application of a known wrapper or reader hand nothing on."""
    p = text.strip()
    while True:
        q = strip_parens(p).strip()
        if q == p:
            break
        p = q
    if not p or p in ("none", "[]") or NUMERAL.fullmatch(p) or p in holders:
        return True, set(), set()

    def spec_argument(st):
        if any(SPEC_NAME.search(w) for w in idents(st)):
            return True, set(), set()           # closed wiring: the spec is named, and seen
        return True, set(), {w for w in idents(st) if w not in KEYWORDS and "." not in w}

    def combine(parts):
        arms, specs = set(), set()
        for part in parts:
            ok, a, sp = partner_names(part, holders)
            if not ok:
                return False, set(), set()
            arms |= a
            specs |= sp
        return True, arms, specs

    # `<partner>.map CheckedArm.ca_arm`, `.map (·.ca_arm)`: the same arms, so
    # the partner under it; `.map SpecArm.sa_no`: their numbers, nothing
    # handed on; any other mapper opens what it maps.
    for mm in re.finditer(r"\.map\b", p):
        if bracket_depth(p, 0, mm.start()) != 0:
            continue
        arg = argument_span(p, mm.end())
        if arg is None or p[arg[1]:].strip():
            continue
        inner = strip_parens(p[arg[0]:arg[1]]).strip()
        if NUMBER_MAPPER.match(inner):
            return True, set(), set()
        if ARM_MAPPER.match(inner):
            return partner_names(p[:mm.start()], holders)
        return False, set(), set()
    # `(group).ca_arm`, `(group).sa_no`: the group with a projection chain.
    m = re.match(r"^(\(.*\))((?:\.[\w'!?]+)+)$", p, re.S)
    if m and matching_bracket(p, 0) == len(m.group(1)) - 1:
        fields = m.group(2).split(".")[1:]
        if set(fields) <= ARM_PROJ:
            return partner_names(m.group(1), holders)
        if fields[-1] in NUMBER_PROJ or fields[-1] in CHECKER_PROJ:
            return True, set(), set()
        return False, set(), set()
    m = CTOR_HEAD.match(p)
    if m:
        number = argument_span(p, m.end())
        spec = argument_span(p, number[1]) if number else None
        if spec is None or p[spec[1]:].strip():
            return False, set(), set()
        return spec_argument(p[spec[0]:spec[1]])
    if p.startswith("⟨") and matching_bracket(p, 0) == len(p) - 1:
        parts = split_top(p[1:-1])
        return spec_argument(parts[1]) if len(parts) == 2 else (False, set(), set())
    if p.startswith("{") and matching_bracket(p, 0) == len(p) - 1:
        m = re.search(r"\bsa_spec\s*:=\s*", p)
        if m is None:
            return False, set(), set()
        field = split_top(p[m.end():-1])[0]
        return spec_argument(field)
    if p.startswith("[") and matching_bracket(p, 0) == len(p) - 1:
        return combine(split_top(p[1:-1]))
    colon = top_ascription(p)
    if colon is not None:
        return partner_names(p[:colon], holders)      # `(arm : SpecArm)`: the arm
    if len(split_top(p)) > 1:
        return combine(split_top(p))
    if len(split_top(p, "::")) > 1:
        return combine(split_top(p, "::"))
    m = QUALIFIED.match(p)
    if m is None:
        return False, set(), set()
    if m.end() == len(p):
        parts = p.split(".")
        if SPEC_NAME.search(p) or parts[0] in holders:
            return True, set(), set()
        if set(parts[1:]) <= ARM_PROJ:
            return True, {parts[0]}, set()
        if parts[-1] in NUMBER_PROJ or parts[-1] in CHECKER_PROJ:
            return True, set(), set()
        return False, set(), set()
    head = arm_head(m.group(0))
    if head in ("some",):
        return partner_names(p[m.end():], holders)
    if head in ARM_WRAPPERS or head in ARM_READERS or head in CHECKER_READERS:
        return True, set(), set()
    return False, set(), set()


def number_is_used_on(text, k, s, projection=True):
    """Whether the number the projection ending at `k` yields is applied to
    an argument or projected further.  A number can be neither, so the
    field was not the field this reader knows: `arm.isSome i m o` and
    `arm.isSome.2 i m o` typecheck only through a `SpecArm.isSome` of the
    tree's own, and are read as opening the arm.

    A bracket that CLOSES a group opened before the span does not end the
    use: `(arm.isSome) i m o` is the same application with the wrapping
    free, and a reader that stopped at the `)` would take the parenthesis
    for a defence.  Step past every such closer first.

    `projection` is False where the value is a LIST of numbers rather than
    one -- `t.map ca_no`, whose `(t.map ca_no).all (…)` is `List.all` over
    `List Int` and is how the DispatchSurface twin states its check.
    Applying that list to arguments is still no more typeable than applying
    a number."""
    while True:
        j = k
        while j < len(text) and text[j].isspace():
            j += 1
        if j < len(text) and text[j] in CLOSERS and matching_opener(text, j) < s:
            k = j + 1
            continue
        k = j
        break
    if k < len(text) and text[k] == "." and k + 1 < len(text) and IDENT_CHAR.match(text[k + 1]):
        return projection
    arg = next_argument(text, k, s)
    return arg is not None and (text[arg[0]] not in OPENERS or text[arg[0]] == "(")


def judge_arm_use(text, s, e, binder_end=0, value_at=None, statement=True):
    """How the arm written at text[s:e] is used: ("terminal", …) when it
    stands as an identity and its spec is never read, ("binder", …) when
    the span is a local name being declared rather than used, ("flows", …)
    when it is the value a `def` binds, ("reach", …) when its spec is
    applied, extracted, or handed to a function this reader does not know.
    The second and third items are the span the judgement was made on; for
    a terminal identity the fourth is the (start, end) of the operand the
    arm was compared with, False when that operand could not be read, and
    None when there is no partner to read.  `binder_end` is where the
    declaration's header binders end (header_binders_end); `value_at` the
    `def`'s own `:=` (def_value_at); in a `statement` no `:=` binds the
    arm."""
    for _ in range(64):
        # 0. A projection chain right after the span.
        while e < len(text) and text[e] == ".":
            k = e + 1
            while k < len(text) and IDENT_CHAR.match(text[k]):
                k += 1
            field = text[e + 1:k]
            if field == "sa_spec":
                return "terminal", s, e, None   # the projection is itself the pin
            if field in NUMBER_PROJ:
                # A number is applied to nothing and projected no further.
                # An argument or a field after it is a Cases `SpecArm.isSome`
                # standing where the number field would (refused at its
                # definition too): fail closed here as well.
                if number_is_used_on(text, k, s):
                    return "reach", s, k, None
                return "terminal", s, k, None   # the arm does not come through
            if field in CHECKER_PROJ:
                return "terminal", s, k, None   # the checker's answer, not the spec
            if field in ARM_PROJ:
                e = k
                continue
            if field == "map":
                arg = argument_span(text, k)
                inner = strip_parens(text[arg[0]:arg[1]]) if arg else ""
                if arg and NUMBER_MAPPER.match(inner):
                    if number_is_used_on(text, arg[1], s, projection=False):
                        return "reach", s, arg[1], None
                    return "terminal", s, arg[1], None
                if arg and ARM_MAPPER.match(inner):
                    e = arg[1]
                    continue
            return "reach", s, k, None      # `.2`, or a field this reader does not know
        kind, tok, at = token_before(text, s)
        # 1. The span DECLARED as a binder -- `(c : CheckedArm)` in the header,
        #    `∀ c,`, `fun c =>` -- is not a use of the arm a local name holds.
        #    The same group past the header is an ascription: judge where the
        #    group stands.
        quantified = (kind == "op" and tok in QUANTIFIERS) or (kind == "ident" and tok in ("fun", "λ"))
        if quantified or (kind == "open" and tok in "({⦃["):
            e1 = e
            while True:
                arg = argument_span(text, e1)
                if arg is None or not IDENT_CHAR.match(text[arg[0]]):
                    break
                e1 = arg[1]
            akind, atok, aend = token_after(text, e1)
            if quantified and akind == "op" and atok in (":", ",", "=>"):
                return "binder", s, e1, None
            if not quantified and akind == "op" and atok == ":":
                q = matching_bracket(text, at)
                if q is not None:
                    bkind, btok, _ = token_before(text, at)
                    if at < binder_end or (bkind == "op" and btok in QUANTIFIERS) \
                            or (bkind == "ident" and btok in ("fun", "λ")):
                        return "binder", at, q + 1, None
                    s, e = at, q + 1          # an ascription in expression position
                    continue
        # 2. A head applied to the span: a wrapper's result stands where the
        #    head does, over exactly the arguments the wrapper takes.
        if kind == "ident":
            head = arm_head(tok)
            if head in ARM_WRAPPERS:
                j = at + len(tok)
                for _ in range(WRAPPER_ARITY[head]):
                    arg = next_argument(text, j, at)
                    if arg is None:
                        break
                    j = arg[1]
                s, e = at, max(e, j)
                continue
            if (head in ARM_READERS or head in CHECKER_READERS) \
                    and READER_ARM_AT[head] == 0:
                return "terminal", at, e, None
        # A reader that takes the arm past its first argument: the token
        # before the span is that earlier argument -- a name, or the closer
        # of a bracketed one, `arm_preserves (mkInvariant v p) c` -- so find
        # the head by stepping back over it.  Both kinds have to reach this
        # step: as first written only an identifier did, and a bracketed
        # argument fell through to "the spec is read" although
        # `applied_head` walks brackets (the deep review of #813, round 5).
        if kind in ("ident", "close"):
            outer, idx = applied_head(text, s)
            if outer is not None:
                outer = arm_head(outer)
                if (outer in ARM_READERS or outer in CHECKER_READERS) \
                        and READER_ARM_AT[outer] == idx:
                    return "terminal", s, e, None
            if kind == "ident":
                return "reach", s, e, None
        # 3. The span applied to an argument: an arm is a value, not a
        #    function, so this applies what it carries.
        arg = next_argument(text, e, s)
        if arg is not None and (text[arg[0]] not in OPENERS or text[arg[0]] == "("):
            return "reach", s, arg[1], None
        # 4. Exactly enclosed by parentheses: widen and read on.
        akind, atok, aend = token_after(text, e)
        if kind == "open" and tok == "(" and akind == "close" and atok == ")" \
                and matching_bracket(text, at) == aend - 1:
            s, e = at, aend
            continue
        # 5. A cons chain: `a :: arm :: rest` is one list.
        widened = False
        while akind == "op" and atok == "::":
            arg = argument_span(text, aend)
            if arg is None:
                break
            e = arg[1]
            akind, atok, aend = token_after(text, e)
            widened = True
        while kind == "op" and tok == "::":
            j = at
            while j > 0 and text[j - 1].isspace():
                j -= 1
            k = j
            while k > 0 and (IDENT_CHAR.match(text[k - 1]) or text[k - 1] == "."):
                k -= 1
            if k == j:
                break
            s = k
            kind, tok, at = token_before(text, s)
            widened = True
        if widened:
            continue
        # 6. An identity: compared, or a member.  The partner is read by the
        #    caller (partner_names); one that cannot be read is False.
        if akind == "op" and atok in IDENTITY_OPS:
            partner = partner_after(text, aend)
            return "terminal", s, e, (partner if partner is not None else False)
        if kind == "op" and tok in IDENTITY_OPS:
            partner = partner_before(text, at)
            return "terminal", s, e, (partner if partner is not None else False)
        # 7. The value a `def` binds: its own `:=`, or the `ca_arm` field of
        #    a checked arm it builds.  Any other `:=` -- a `let`, a `have`,
        #    another field, a structure update, anything in a statement --
        #    binds the arm to a name this reader will not follow: fail closed.
        if kind == "op" and tok == ":=":
            bkind, btok, _ = token_before(text, at)
            if not statement and (at == value_at or (bkind == "ident" and last(btok) == "ca_arm")):
                return "flows", s, e, None
            return "reach", s, e, None
        # 8. Inside a list or a tuple, or under a type ascription: the group
        #    is the value; judge where IT stands.
        if (kind == "op" and tok == ",") or (kind == "open" and tok == "[") \
                or (akind == "op" and atok in (",", ":")) or (akind == "close" and atok == "]"):
            g = enclosing_group(text, s)
            if g is None or text[g] not in "([":
                return "reach", s, e, None
            q = matching_bracket(text, g)
            if q is None:
                return "reach", s, e, None
            s, e = g, q + 1
            continue
        return "reach", s, e, None
    return "reach", s, e, None


def read_arms(text, holders, statement=True):
    """Read every arm in `text` -- each `mkSpecArm` group, each name in
    `holders` (a Cases `def` that holds an arm, mapped to the specs its
    wiring names) and each local name a statement equates with one, or
    hands one's spec to -- and judge how it is used.  In a `statement`, an
    anonymous constructor or a `match` anywhere takes the arm apart and
    every arm in it is read; a `def` body carries its proofs, which build
    and destructure freely, so there only the position of each arm is
    judged.

    Returns (wired, reach_specs, reach_idents, flow_specs).  `wired` is
    `text` with the spec argument of every arm that stands as an identity
    blanked, offsets and line breaks preserved: that argument is the
    table's wiring, not a side of a pin.  An arm that is opened or handed
    on keeps its spec visible, and a holder opened that way contributes
    its specs to `reach_specs` and its written name to `reach_idents`;
    `flow_specs` are the specs of arms a `def` body binds as its value.  A
    shape this reader cannot walk -- a group that never closes, an
    unknown head, an unknown field, a partner it cannot read -- fails
    closed: the spec stays visible and the statement is a pin."""
    out = list(text)
    occurrences = []     # (s, e, specs, blank, ident)
    for m in ARM_CTOR.finditer(text):
        number = argument_span(text, m.end())
        if number is None:
            continue
        spec = argument_span(text, number[1])
        if spec is None:
            continue
        s = m.start()
        while s > 0 and (IDENT_CHAR.match(text[s - 1]) or text[s - 1] == "."):
            s -= 1
        specs = {w for w in idents(text[spec[0]:spec[1]]) if SPEC_NAME.search(w)}
        occurrences.append((s, spec[1], specs, spec, None))
    inside = [(o[3][0], o[3][1]) for o in occurrences]

    def in_wiring(i):
        return any(a <= i < b for a, b in inside)

    def holder_occurrences(names):
        found = []
        for q in QUALIFIED.finditer(text):
            if in_wiring(q.start()):
                continue
            parts = q.group(0).split(".")
            for j, p in enumerate(parts):
                if p in names:
                    e = q.start() + len(".".join(parts[:j + 1]))
                    found.append((q.start(), e, set(names[p]), None, q.group(0)))
                    break
        return found

    occurrences += holder_occurrences(holders)
    if not occurrences:
        return text, set(), set(), set()
    reach_specs, reach_idents, flow_specs = set(), set(), set()
    torn = statement and \
        EXTRACTION.search("".join(" " if in_wiring(i) else c for i, c in enumerate(text)))
    binder_end = header_binders_end(text)
    value_at = None if statement else def_value_at(text)
    local, seen = {}, set()
    while occurrences:
        s, e, specs, blank, ident = occurrences.pop(0)
        if (s, e) in seen:
            continue
        seen.add((s, e))
        verdict, _, _, partner = judge_arm_use(text, s, e, binder_end, value_at, statement)
        if torn:
            verdict = "reach"
        if verdict == "terminal" and specs and partner is not None:
            if partner is False:
                verdict = "reach"
            else:
                known, arm_locals, spec_locals = partner_names(text[partner[0]:partner[1]], holders)
                if not known:
                    verdict = "reach"
                for name in arm_locals | spec_locals:
                    if name in holders or name[0].isdigit():
                        continue
                    if name not in local:
                        local[name] = set()
                        occurrences += [o for o in holder_occurrences({name: specs})
                                        if o[:2] not in seen]
                    local[name] |= specs
        if verdict == "reach":
            if blank is None:
                reach_specs |= specs
                reach_idents.add(ident)
            continue                          # an inline arm stays visible
        if verdict == "flows":
            flow_specs |= specs
        if blank is not None:
            for q in range(*blank):
                if not out[q].isspace():
                    out[q] = " "
    return "".join(out), reach_specs, reach_idents, flow_specs


# A Cases def that handles arms: a `SpecArm` or `CheckedArm` anywhere in
# its signature (a parameter it may open by any eliminator, or the arm it
# builds), or the direct opening forms in its value.  Such a def is not an
# outcome helper (PIN-5) whatever its text names.
ARM_TYPE = re.compile(r"\b(?:SpecArm|CheckedArm)\b")
ARM_OPENING = re.compile(r"\bsa_spec\b|\.2(?![\w])|\bdispatch\b")


def handles_arms(body):
    v = def_value_at(body)
    sig = body if v is None else body[:v]
    return ARM_TYPE.search(sig) is not None or ARM_OPENING.search(body) is not None


def declared_target(sig):
    """The result type a `def` signature declares, as written after its
    last top-level colon and last `→`, outer parentheses off; None when the
    signature declares no type."""
    colons = top_level(sig, ":")
    if not colons:
        return None
    result = sig[colons[-1] + 1:]
    arrows = top_level(result, "→")
    return strip_parens(result[arrows[-1] + 1:] if arrows else result)


def prop_heads(root, defs):
    """The names whose application is a proposition although no token says
    so: every `def`/`abbrev` under the model (Checks/Cases excluded) and
    every Cases helper whose declared result is `Prop`.  `(h : never)` over
    `def never : Prop := (1 : Int) = 2` is a closed hypothesis, and read by
    its shape alone it is a data binder named `h` (the deep review of #813,
    round 5).  An `inductive … : Prop` is not read: a binder typed by one is
    still data to PIN-3."""
    names = set()
    for rel in lean_files(root, LEAN_MODEL):
        if rel.startswith(CASES_DIR + "/"):
            continue
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            clean = blank_comments_and_strings(f.read())
        for m in DEF.finditer(clean):
            _, sig = statement_span(clean, m.start(1), m.end(1))
            nm = re.match(r"\s*(\S+)", sig[len(m.group(1)):])
            if nm and declared_target(sig[len(m.group(1)) + nm.end():]) == "Prop":
                names.add(last(nm.group(1)))
    for _rel, _line, name, _mentioned, body in defs:
        v = def_value_at(body)
        if declared_target(body if v is None else body[:v]) == "Prop":
            names.add(name)
    return names


def cases_helpers(root, files):
    """(aliases, builders): the Cases defs whose text mentions a spec, each
    mapped to the specs it resolves to (PIN-7), and the input builders
    mapped to the syscall number their `mkInput` names (PIN-8).  Also the
    PIN-1 findings on the defs themselves, and the HOLDERS: the defs that
    bind an arm as their value, mapped to the specs its wiring names,
    which a statement opening the holder is a pin on."""
    texts = {}
    for rel in files:
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            texts[rel] = blank_comments_and_strings(f.read())
    defs, builders, direct = [], {}, {}
    outcome_helpers, ok_helpers, arm_handlers = set(), set(), set()
    bodies = []
    for rel, clean in texts.items():
        for m in DEF.finditer(clean):
            e = COMMAND.search(clean, m.end())
            body = clean[m.start():e.start() if e else len(clean)]
            nm = re.match(r"\s*(\S+)", body[m.end() - m.start():])
            if not nm:
                continue
            name = last(nm.group(1))
            if name in (":=", "where", "|"):
                continue
            line = line_of(clean, m.start(1))
            bodies.append((rel, line, name, body))
            # An outcome helper BUILDS an outcome for a pin's kernel side to
            # name.  A def that takes an arm, builds one, or opens one --
            # `def admits (c : CheckedArm) … : Prop := c.1.2 i m o ∧ …` --
            # is what PIN-5 is guarding the side against, and its text
            # naming `Unmodeled` does not make it the outcome: read as one,
            # the helper the arm is handed to supplied the outcome the pin
            # owed for opening it (the deep review of #813, round 5).
            if handles_arms(body):
                arm_handlers.add(name)
            elif OUTCOME.search(body):
                outcome_helpers.add(name)
                if re.search(r"\bOk\b", body):
                    ok_helpers.add(name)
    # A def that binds an arm as its value HOLDS the arm's specs without
    # mentioning them (fixpoint: a table of holders is a holder); one that
    # opens an arm, or hands it on, mentions them.  A holder that mentions a
    # spec on its own is an alias, and read as one.
    holders, wired_of = {}, {}
    changed, passes = True, 0
    while changed and passes <= len(bodies) + 1:
        changed, passes = False, passes + 1
        for rel, line, name, body in bodies:
            # The def's own name -- its header, a recursive call -- is not
            # a use of the arm it holds; read as one it would open itself
            # and flip between holder and alias forever.
            others = {k: v for k, v in holders.items() if k != name}
            wired, reach_specs, _, flow_specs = read_arms(body, others, statement=False)
            mentioned = {w for w in idents(wired) if is_spec_name(w) and w != name} | reach_specs
            wired_of[(rel, line)] = (wired, mentioned)
            held = flow_specs if not mentioned else set()
            if held and holders.get(name) != held:
                holders[name] = held
                changed = True
            elif not held and name in holders:
                del holders[name]
                changed = True
    for rel, line, name, body in bodies:
        wired, mentioned = wired_of[(rel, line)]
        mentioned = sorted(mentioned)
        defs.append((rel, line, name, mentioned, body))
        if mentioned:
            direct[name] = set(mentioned)
    # A holder is not an outcome helper: the `Unmodeled` in a checked arm's
    # witness is the arm's checker, not an outcome the holder builds for a
    # pin to name, and a pin reached by opening the holder would otherwise
    # satisfy PIN-5 by naming the holder.
    outcome_helpers -= set(holders)
    ok_helpers -= set(holders)
    # A helper built from another helper carries its outcome (fixpoint).
    changed = True
    while changed:
        changed = False
        for rel, line, name, mentioned, body in defs:
            if name in holders:
                continue
            used = {last(a) for a in idents(body)} - {name} - set(holders)
            if name not in arm_handlers:
                if name not in outcome_helpers and used & outcome_helpers:
                    outcome_helpers.add(name); changed = True
                if name not in ok_helpers and used & ok_helpers:
                    ok_helpers.add(name); changed = True
            b = INPUT_BUILDER.search(body)
            if b:
                n = MK_INPUT.search(b.group(1))
                num = int(n.group(1)) if n else None
                if num is None:
                    # A builder whose value is ANOTHER builder applied --
                    # `def faccessat2_in bs mode flags := faccessat2_in'
                    # AT_FDCWD 8192 mode flags …`, where only the primed one
                    # writes `mkInput 439` -- names its number a level down,
                    # and this loop is already the fixpoint that resolves a
                    # chain of them.  Only when the builders in the value
                    # agree: two numbers in one value is an input this reader
                    # cannot place, and an unplaced builder reaches no arm,
                    # which is the fail-closed direction (PIN-8 then reports
                    # the arm as unpinned rather than passing it).
                    nums = {builders[u] for u in
                            {last(a) for a in idents(b.group(1))} if u in builders}
                    num = nums.pop() if len(nums) == 1 else None
                if num is not None and builders.get(name) != num:
                    builders[name] = num
                    changed = True
    # Resolve aliases through each other until nothing changes.
    aliases = {k: set(v) for k, v in direct.items()}
    changed = True
    while changed:
        changed = False
        for rel, line, name, mentioned, body in defs:
            for a in alias_uses(idents(wired_of[(rel, line)][0]), aliases, name):
                before = len(aliases.setdefault(name, set()))
                aliases[name] |= aliases[a]
                changed |= len(aliases[name]) != before
    findings = []
    for rel, line, name, mentioned, body in defs:
        names = set(mentioned)
        for a in alias_uses(idents(wired_of[(rel, line)][0]), aliases, name):
            names |= aliases[a]
        if len(names) > 1:
            findings.append((rel, line, name, sorted(names)))
    return aliases, builders, findings, texts, outcome_helpers, ok_helpers, defs, holders


# What a trusted head's body must not reach: the spec field, a `.2`
# projection, the dispatcher that applies the spec, a `*_spec` name.
PREMISE_BREAK = re.compile(r"\bsa_spec\b|\.2(?![\w])|\bdispatch\b|\w*_spec\w*")
LEAN_MODEL = "lean/LinuxProcessSemantics/LinuxProcessSem"


def trusted_heads_keep_their_premise(root, findings):
    """The heads the arm reader trusts by name (ARM_WRAPPERS, ARM_READERS,
    CHECKER_READERS) are trusted on one premise: none applies an arm's spec.
    Re-read the model's own `def` of each name that has one and refuse a
    body that reaches a spec in a direct form -- `sa_spec`, a `.2`
    projection, `dispatch`, a `*_spec` name -- so the trust ends the day the
    body grows one, instead of widening silently.  A name the model does not
    define is inert (no pin can apply it), `mkCheckedArm` is a constructor
    with no body, and a reach through a helper the body calls is not seen:
    the lists' own comments carry the argument per name, and this pins the
    body each argument was made about."""
    trusted = ARM_WRAPPERS | ARM_READERS | CHECKER_READERS | WITNESS_READERS
    for rel in lean_files(root, LEAN_MODEL):
        if rel.startswith(CASES_DIR + "/"):
            continue
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            clean = blank_comments_and_strings(f.read())
        for m in DEF.finditer(clean):
            e = COMMAND.search(clean, m.end())
            body = clean[m.start():e.start() if e else len(clean)]
            nm = re.match(r"\s*(\S+)", body[m.end() - m.start():])
            if not nm or last(nm.group(1)) not in trusted:
                continue
            hit = PREMISE_BREAK.search(body, m.end() - m.start() + nm.end())
            if hit is not None:
                findings.add(rel, line_of(clean, m.start(1)), "PIN-5",
                             f"`{last(nm.group(1))}` is a head the arm reader trusts to hand "
                             "an arm on unopened, and the model's definition of it reaches a "
                             f"spec (`{hit.group(0)}`): the trust rests on the body never "
                             "applying `sa_spec`, so the body or the reader's list has to "
                             "change.")


def witness_reader_declarations(root):
    """name -> [(file, line, result type)] for every WITNESS_READERS name the
    model declares: a `def`'s result type, and a structure field's type read
    off its line (`ca_witness` is a field of `CheckedArm`, not a `def`)."""
    out = {}
    for rel in lean_files(root, LEAN_MODEL):
        if rel.startswith(CASES_DIR + "/"):
            continue
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            clean = blank_comments_and_strings(f.read())
        for m in DEF.finditer(clean):
            _, sig = statement_span(clean, m.start(1), m.end(1))
            nm = re.match(r"\s*(\S+)", sig[len(m.group(1)):])
            if not nm or last(nm.group(1)) not in WITNESS_READERS:
                continue
            rest = sig[len(m.group(1)) + nm.end():]
            colons = top_level(rest, ":")
            out.setdefault(last(nm.group(1)), []).append(
                (rel, line_of(clean, m.start(1)), rest[colons[-1] + 1:] if colons else ""))
        for m in FIELD_DECL.finditer(clean):
            if m.group(1) in WITNESS_READERS:
                out.setdefault(m.group(1), []).append(
                    (rel, line_of(clean, m.start()), m.group(2)))
    return out


def witness_readers_are_outcomes(root, findings):
    """WITNESS_READERS is trusted for two readings at once -- a statement
    applying one NAMES an outcome, and the name is not a spec however it is
    spelled -- and both rest on the model declaring the name with `outcome`
    as its result.  Re-read that declaration and refuse one that is not, so
    the trust cannot outlive what it was granted for.

    A name the model declares NOWHERE is inert, for `trusted_heads_keep_
    their_premise`'s reason: nothing under Checks/Cases can apply a name
    nothing declares, and a Cases file defining one is refused at the
    definition.  The residue is a name some DEPENDENCY declares, which this
    reader does not see; none of the three is a name Lean's own library
    carries, and `test_check_lean_pins.py` pins each against the real tree's
    declaration so a rename does not quietly leave the list trusting a name
    the model no longer defines.

    A field can only establish the premise, never break it: the line reader
    would otherwise take any `name : …` it met -- a binder, a `where` clause
    -- for a declaration."""
    for nm, places in sorted(witness_reader_declarations(root).items()):
        if any("outcome" in result for _, _, result in places):
            continue
        for rel, line, result in places:
            findings.add(rel, line, "PIN-5",
                         f"`{nm}` is read as the checker's witness -- a statement "
                         "applying it names an outcome, and the name is not counted as "
                         f"a spec -- and the model declares it `{normalize(result)}`, "
                         "which is not an outcome. Either the definition moved or the "
                         "reader's list has to.")


def predicate_wrappers(defs, predicates):
    """name -> (file, line, model predicate) of every Checks/Cases def or
    abbrev whose body applies a model predicate, or another wrapper
    (fixpoint): `def rfree maps lo n : Bool := region_free maps lo n` is
    `region_free` under a Cases name, and PIN-6 reads through it."""
    out = {}
    changed = True
    while changed:
        changed = False
        for rel, line, name, mentioned, body in defs:
            if name in out or name in predicates:
                continue
            used = {last(a) for a in idents(body)} - {name}
            hit = sorted(used & (set(predicates) | set(out)))
            if hit:
                base = hit[0] if hit[0] in predicates else out[hit[0]][2]
                out[name] = (rel, line, base)
                changed = True
    return out


BINDER_HEAD = re.compile(r"[∃∀λ]|\bfun\b")


def binder_names(binders, ty):
    """Every name a statement binds: the header's bracket groups (`(o :
    outcome SyscallEffect)`, `{x : T}`, `[inst : C]`, `⦃y : T⦄`) and, inside
    the type, what stands between `∃`/`∀`/`fun`/`λ` and its `,` or `=>`.
    A group's names are the words before its first top-level colon; a bare
    `∃ a b, …` has none and yields both words."""
    names = set()

    def group(seg):
        cols = top_level(seg, ":")
        for w in (seg[:cols[0]] if cols else seg).split():
            if re.fullmatch(IDENT, w):
                names.add(w)

    def groups(text):
        i, bare = 0, []
        while i < len(text):
            if text[i] in OPENERS:
                j = matching_bracket(text, i)
                if j is None:
                    break
                group(text[i + 1:j])
                i = j + 1
                continue
            bare.append(text[i])
            i += 1
        group("".join(bare))

    groups(binders)
    for h in BINDER_HEAD.finditer(ty):
        k, depth = h.end(), 0
        while k < len(ty):
            c = ty[k]
            if c in OPENERS:
                depth += 1
            elif c in CLOSERS:
                depth -= 1
            elif depth == 0 and (c == "," or c == "↦" or ty.startswith("=>", k)):
                break
            k += 1
        groups(ty[h.end():k])
    return names


def check_pins(root, findings):
    """PIN-1 .. PIN-7 over Checks/Cases; returns (declarations read, pins)."""
    files = lean_files(root, CASES_DIR)
    aliases, builders, def_findings, texts, outcome_helpers, ok_helpers, defs, holders = \
        cases_helpers(root, files)
    # name -> body of every Cases `def`, Tactic.lean included, for the
    # read-only walk a command elaborator's exemption rests on.
    helpers = {name: body for _rel, _line, name, _mentioned, body in defs}
    # Two passes.  A `macro_rules` is exempt only for tokens an exempt
    # HEADER declared, and those headers are collected first so that the
    # verdict cannot depend on which file the glob walked first, or on
    # whether the header stands above or below the block it justifies.
    tactic_tokens, pending, raws = set(), [], {}
    for rel in files:
        if rel in (TACTIC_FILE, TACTIC_CORE_FILE):
            continue
        for m in NOTATION.finditer(texts[rel]):
            if rel not in raws:
                with open(os.path.join(root, rel), encoding="utf-8") as f:
                    raws[rel] = f.read()
            if m.group(1) in CATEGORY_KEYWORDS and \
                    declares_tactic_syntax(texts[rel], m.start(1)):
                tok = tactic_token(texts[rel], raws[rel], m.start(1))
                if tok is not None:
                    tactic_tokens.add(tok)
                    continue
            # The command category, exempt on `command_emission`'s argument.
            # `tactic_token` reads the token any syntax header binds, and a
            # header binding none extends one declared elsewhere: refused
            # here as it is there.  The token is NOT added to
            # `tactic_tokens`: a `macro_rules` may not ride on a command.
            if m.group(1) in CATEGORY_KEYWORDS \
                    and declares_command_syntax(texts[rel], m.start(1)) \
                    and tactic_token(texts[rel], raws[rel], m.start(1)) is not None \
                    and command_emission(texts[rel], m.start(1)) is None \
                    and command_reads_only(command_block(texts[rel], m.start(1)),
                                           helpers) is None:
                continue
            pending.append((rel, m))
    for rel, m in pending:
        line = line_of(texts[rel], m.start(1))
        kw = m.group(1)
        if kw in RULES_KEYWORDS:
            toks = tactic_rule_tokens(texts[rel], m.start(1))
            if toks and toks <= tactic_tokens:
                continue
            unknown = sorted(toks - tactic_tokens) if toks else []
            findings.add(rel, line, "PIN-7",
                         f"`{kw}` in a Cases file "
                         + (f"extends {', '.join('`' + u + '`' for u in unknown)}, which "
                            "no exempt header in a Cases file declares as tactic syntax"
                            if unknown else
                            "and this reader read no tactic alternative in it -- every "
                            "alternative has to be a `` `(tactic| token …) `` pattern")
                         + ". It binds no token in its header, so the exemption is read "
                         "from its alternatives and fails closed: a term alternative, or "
                         "a token declared nowhere, is a name no `def` reader follows and "
                         "a pin stated through it escapes PIN-1 and PIN-7.")
            continue
        if kw in CATEGORY_KEYWORDS and declares_command_syntax(texts[rel], m.start(1)):
            emits = command_emission(texts[rel], m.start(1))
            unknown = None
            if emits is None and tactic_token(texts[rel], raws[rel], m.start(1)) is not None:
                unknown = command_reads_only(command_block(texts[rel], m.start(1)), helpers)
            if emits is not None:
                why = (f"beside `{emits}`, which can put a declaration into "
                       "the environment: a generated helper is a name a pin's "
                       "statement may use and no reader here resolves, which is "
                       "a silent miss rather than a finding")
            elif unknown is not None:
                why = (f"and runs `{unknown[0]}`"
                       + (f" (in {unknown[1]})" if unknown[1] else "")
                       + ", a name not on READ_ONLY_API: the exemption is for a "
                       "command known to only READ, and a name this reader does not "
                       "know is refused rather than trusted -- `elabCommandTopLevel` "
                       "on a parsed string and `Meta.mkAuxDefinition` each declared a "
                       "helper with the old blacklist silent")
            else:
                why = ("but binds no token of its own -- it extends one declared "
                       "elsewhere, and this reader read no header for it")
            findings.add(rel, line, "PIN-7",
                         f"`{kw}` in a Cases file declares command syntax {why}. A "
                         "command that only READS is exempt; see `command_reads_only` "
                         "and `command_emission`.")
            continue
        if kw in CATEGORY_KEYWORDS and declares_tactic_syntax(texts[rel], m.start(1)):
            findings.add(rel, line, "PIN-7",
                         f"`{kw}` in a Cases file declares tactic syntax "
                         "but binds no token of its own -- it extends one declared "
                         "elsewhere, which this reader could not then keep out of "
                         "statements and helpers. Only `macro \"name\" … : tactic`, "
                         "`syntax \"name\" … : tactic` and `elab \"name\" … : tactic` "
                         "are exempt.")
            continue
        findings.add(rel, line, "PIN-7",
                     f"`{kw}` in a Cases file: a name bound this way is an "
                     "alias no `def` reader follows, so a pin stated through it "
                     "escapes PIN-1 and PIN-7. Cases helpers are `def`s; term "
                     f"syntax lives in {TACTIC_FILE}. A declaration whose header "
                     "names its token and ends `: tactic` is exempt -- a tactic "
                     "block is refused in every statement and every helper, so "
                     "none stands in a pin -- and so is one ending `: command` "
                     "whose body emits no declaration, since a command has no term "
                     "position at all. Every other category, or none, is not.")
    for rel in files:
        for r in RUNS_AT_BUILD.finditer(texts[rel]):
            findings.add(rel, line_of(texts[rel], r.start()), "PIN-7",
                         f"`{r.group(1)}` in a Cases file runs elaborator code where it "
                         "stands, with no syntax declaration for the command exemption to "
                         "read: `run_cmd` and `#eval` of a `CommandElabM` action each "
                         "declared a helper from a Cases file under Lean v4.34.0, a name a "
                         "pin's statement may then use and no reader here resolves. A "
                         "check the build must run is a `: command` elaborator that only "
                         "reads, invoked once.")
        for r in EMITTER.finditer(texts[rel]):
            findings.add(rel, line_of(texts[rel], r.start()), "PIN-7",
                         f"`{r.group(0)}` in a Cases file: a function of the family that "
                         "puts a declaration into the environment, or runs syntax that "
                         "does. Nothing under Checks/Cases declares except by writing the "
                         "declaration, whatever command stands beside this name or none; "
                         "a generated helper is a silent miss for every reader here.")
        g = GUILLEMET.search(texts[rel])
        if g is not None:
            findings.add(rel, line_of(texts[rel], g.start()), "PIN-7",
                         "a guillemet-quoted name (`«…»`) in a Cases file: no identifier "
                         "reader here resolves it, so a helper or holder spelled that way "
                         "is invisible to PIN-1 and PIN-7. Spell the name plainly.")
        r = RENAMING.search(texts[rel])
        if r is not None:
            findings.add(rel, line_of(texts[rel], r.start()), "PIN-7",
                         "`open … renaming` in a Cases file gives a definition a second "
                         "name, and the arm reader trusts heads by name: `renaming opened "
                         "→ length` hands an arm's spec to `opened` under the reader's own "
                         "`length`. Write the definition's name.")

    # The exemption's premise, enforced on the helper side: a Cases `def` that
    # runs an exempt tactic is a term this reader cannot follow (`def rocq_term
    # … : Prop := by rocq i m o` is `mmap_spec_rocq …` under a name), proof
    # fields included, which the real tree never does.
    if tactic_tokens:
        token_re = re.compile(r"(?<![\w'])(?:" + "|".join(re.escape(tk) for tk in sorted(tactic_tokens))
                              + r")(?![\w'])")
        for rel, line, name, _mentioned, body in defs:
            hit = token_re.search(body)
            if hit is not None:
                findings.add(rel, line, "PIN-7",
                             f"`{name}` runs the tactic `{hit.group(0)}`, declared in this "
                             "Cases tree: a Cases helper is a term the `def` reader follows, "
                             "and what a tactic elaborates to it cannot follow, so the "
                             "helper could stand for a spec it never names. Write the term, "
                             "or move the pin's proof to the pin.")

    def names_outcome(text):
        return OUTCOME.search(text) is not None or \
            any(last(w) in outcome_helpers or last(w) in WITNESS_READERS
                for w in idents(text))

    def names_ok(text):
        return re.search(r"\bOk\b", text) is not None or \
            any(last(w) in ok_helpers for w in idents(text))
    for rel, line, name, names in def_findings:
        findings.add(rel, line, "PIN-1",
                     f"helper `{name}` mentions {len(names)} specs: "
                     + ", ".join(f"`{s}`" for s in names)
                     + " -- a pin stated on it compares one spec to another "
                     "through a name (PIN-7 reads helpers for this).")
    # The arm reader trusts WRAPPER_ARITY and ARM_READERS by NAME: `length
    # arm` hands nothing on because `length` is the table's own reader.  A
    # Cases file defining one of those names takes that trust over, and a
    # local `def length (a : SpecArm) : Sys SyscallEffect := a.2` would hand
    # the spec on with the reader silent -- the same fail-OPEN mistake as
    # exempting an arm's wiring by its spelling.  The reader cannot tell the
    # two apart at the use site, so the collision is refused at the
    # definition, which also covers every use of it.
    for rel, line, name, _names, _body in defs:
        if name in ARM_WRAPPERS or name in ARM_READERS or name in CHECKER_READERS \
                or name in TRUSTED_FIELDS or name in WITNESS_READERS:
            findings.add(rel, line, "PIN-5",
                         f"a Cases helper named `{name}`: the arm reader trusts that "
                         "name to hand an arm on unopened (it is one of the table's own "
                         "wrappers or readers, the checker's dispatch over a table, or a "
                         "field the projection chain ends at -- `arm.isSome` reaches a "
                         "Cases `SpecArm.isSome`), so a local definition of it would pass "
                         "an arm's spec through unread and a pin stated on the result "
                         "would not be read as a pin at all. Rename the helper.")
    trusted_heads_keep_their_premise(root, findings)
    witness_readers_are_outcomes(root, findings)
    predicates = model_predicates(root)
    wrappers = predicate_wrappers(defs, predicates)
    propositions = prop_heads(root, defs)
    pins, decls = [], 0
    for rel in files:
        clean = texts[rel]
        for m in DECL.finditer(clean):
            decls += 1
            line = line_of(clean, m.start(1))
            _, stmt = statement_span(clean, m.start(1), m.end(1))
            name, binders, ty = split_header_binders(stmt)
            label = name or f"example at line {line}"
            if BY_BLOCK.search(stmt) is not None:
                findings.add(rel, line, "PIN-7",
                             f"the statement of `{label}` runs a tactic block (`by …`): a "
                             "tactic elaborates to a term no reader here follows, so an "
                             "exempt tactic macro puts a spec in the statement unseen -- "
                             "`(by rocq i m o : Prop)` is `mmap_spec_rocq …` and PIN-1 "
                             "counts one spec. Write the term.")
            ty, forall_binders = strip_foralls_binders(ty)
            binders = binders + " " + forall_binders
            # PIN-5 reads outcome NAMES, and a binder shadows one: `∃ Ok :
            # outcome SyscallEffect, o = Ok` is `∃ x, o = x`, true of every
            # outcome, and it read as naming `Ok`; the witness readers
            # (`ca_witness`) are lower-case and read as ordinary binder
            # names.  Refused at the binder, in every statement.
            for bound in sorted(binder_names(binders, ty)):
                if OUTCOME.fullmatch(bound) or bound in WITNESS_READERS \
                        or bound in outcome_helpers or bound in ok_helpers:
                    findings.add(rel, line, "PIN-5",
                                 f"`{label}` binds `{bound}` as a variable, and PIN-5 reads "
                                 "that name as an outcome the kernel side names: the binder "
                                 "shadows it, so `∃ Ok : outcome SyscallEffect, o = Ok` "
                                 "holds of every outcome and read as naming `Ok`. Rename "
                                 "the binder.")

            wired, reach_specs, reach_idents, _ = read_arms(stmt, holders)
            written = sorted({w for w in idents(wired) if is_spec_name(w) and w != name})
            via = alias_uses(idents(wired), aliases, name)
            resolved = set(written) | reach_specs
            for a in via:
                resolved |= aliases[a]
            if len(resolved) > 1:
                shown = sorted(resolved) if via or reach_specs else written
                findings.add(rel, line, "PIN-1",
                             f"statement of `{label}` mentions {len(shown)} specs: "
                             + ", ".join(f"`{s}`" for s in shown)
                             + " -- a pin compares ONE spec to a concrete kernel outcome; "
                             "two specs agreeing is not evidence about Linux. If both "
                             "spell the same definition, write it one way.")

            # PIN-2 and the `True` half of PIN-4 are about the shape of any
            # declaration, pin or not, so they are read before the gate below.
            v = vacuous(ty, spec_binder_premises(binders, name) if resolved else ())
            if v:
                findings.add(rel, line, "PIN-2",
                             f"statement of `{label}` is `A {v[0]} A` with A = "
                             f"`{v[1]}` -- vacuous, it pins nothing.")
            if re.search(r"\bTrue\b", ty) or re.search(r"\bTrue\b", binders):
                findings.add(rel, line, "PIN-4",
                             f"statement of `{label}` mentions `True` -- a disjoined or "
                             "conjoined `True` is closed by `trivial` and pins nothing.")

            if not resolved:
                continue  # not a pin: a fixture lemma, a closed fact
            spec_names = set(written) | via | reach_idents

            # PIN-3: a hypothesis that cannot be about the call, and the
            # `False` half of PIN-4, which a pin never needs.
            for h in hypotheses(binders, ty, name, propositions):
                findings.add(rel, line, "PIN-3",
                             f"pin `{label}` takes the hypothesis {h} -- such a "
                             "premise is not about the call: false, it makes "
                             "every proof close and the pin pins nothing; true, "
                             "the pin never needed it. State the case on a fixture.")
            if re.search(r"\bFalse\b", ty) or re.search(r"\bFalse\b", binders):
                findings.add(rel, line, "PIN-4",
                             f"pin `{label}` mentions `False` -- refute an outcome "
                             "as `¬ spec … (Ok …)`, never through `False`.")

            split = top_level_split(ty)

            # PIN-5: the kernel side names an outcome.  A spec that sits in
            # a hypothesis binder, not in the type, is the implication
            # shape: the whole statement is the side to read.
            side, exempt = None, False
            if split:
                lhs_spec = any(w in spec_names for w in idents(split[1]))
                rhs_spec = any(w in spec_names for w in idents(split[2]))
                if lhs_spec and rhs_spec:
                    exempt = True  # the argument-ignored shape PIN-1 permits
                elif lhs_spec or rhs_spec:
                    side = split[2] if lhs_spec else split[1]
            if reach_specs:
                # A spec reached by opening an arm has no side of its own:
                # the name it travels under (`s` in `∃ s, arm = mk 222 s ∧ (s
                # i m o ↔ True)`) is declared on one side and applied on the
                # other, which the two-sided exemption above would read as
                # the argument-ignored shape.  The whole statement owes the
                # outcome.
                side, exempt = None, False
            if not exempt:
                text = side if side is not None else stmt
                where = "non-spec side" if side is not None else "statement"
                if not names_outcome(text):
                    opened = ""
                    if reach_specs:
                        opened = (" The spec is reached by opening an arm (`"
                                  + "`, `".join(sorted(reach_idents)) + "`): an arm's "
                                  "wiring is exempt only where the arm is compared, listed, "
                                  "looked up or read for its number or checker; `.2`, "
                                  "`match`, or handing it to a function applies its spec.")
                    findings.add(rel, line, "PIN-5",
                                 f"the {where} of `{label}` is `{normalize(text)}`, which "
                                 "names no kernel outcome -- a pin's other side is an "
                                 "`Ok` outcome, an errno, or the decline `o = Unmodeled`, "
                                 "directly or through a Checks/Cases helper that builds one."
                                 + opened)


            # PIN-6: a model predicate on the kernel side.
            if side is not None:
                used = sorted({last(w) for w in idents(side)} & (set(predicates) | set(wrappers)))
                for p in used:
                    if p in predicates:
                        prel, pline = predicates[p]
                        via = ""
                    else:
                        prel, pline, base = wrappers[p]
                        via = f", a Checks/Cases wrapper of the model predicate `{base}`"
                    findings.add(rel, line, "PIN-6",
                                 f"the non-spec side of `{label}` applies the model "
                                 f"predicate `{p}` ({prel}:{pline}{via}) -- that side is the "
                                 "kernel's answer, and restating the spec's own decision "
                                 "procedure there is PIN-1 in miniature; spell the "
                                 "decision as arithmetic or a concrete value.")

            # Classification for PIN-8.  Negative: `¬ …` or `… → False`
            # with no other True/False in it.  Positive: the kernel side of
            # an iff names `Ok` and no True/False, or the statement is the
            # bare application `spec … (Ok …)`.  An implication is neither:
            # `spec … → o = Ok … ∨ True` and `(h : spec … (Ok …)) : True`
            # are provable of a spec that admits nothing.
            core = strip_parens(ty)
            negative = core.startswith("¬") or re.search(r"→\s*False\s*$", core) is not None
            if negative:
                negative = TRUE_FALSE.search(re.sub(r"→\s*False\s*$", "", core)) is None
            positive = False
            if not negative:
                if side is not None:
                    positive = names_ok(side) and TRUE_FALSE.search(side) is None
                elif split is None and not top_level(core, "→∨↔¬"):
                    positive = any(w in spec_names for w in idents(core)) and names_ok(core)
            sysnos = set()
            for b, n in builders.items():
                if re.search(rf"\bsyscall_spec\s*\(?\s*{re.escape(b)}\b", ty):
                    sysnos.add(n)
            for n in SYSCALL_MK_INPUT.findall(ty):
                sysnos.add(int(n))
            pins.append(Pin(rel, line, label, resolved, positive, negative, sysnos))
    return decls, pins


def check_table(root, findings, pins):
    """PIN-8: every registered arm has a positive and a negative pin."""
    arms = read_table(root)
    for arm in arms.values():
        pos = [p for p in pins if p.positive and (arm.spec in p.specs or arm.number in p.sysnos)]
        neg = [p for p in pins if p.negative and (arm.spec in p.specs or arm.number in p.sysnos)]
        for kind, have in (("positive", pos), ("negative", neg)):
            if not have:
                findings.add(arm.rel, arm.line, "PIN-8",
                             f"arm {arm.number} ({arm.name}) dispatches `{arm.spec}` and "
                             f"no {kind} pin under {CASES_DIR} reaches it -- "
                             + ("no theorem admits an `Ok` outcome of it"
                                if kind == "positive" else
                                "no theorem refutes an outcome of it (`¬ spec …` or "
                                "`spec … → False`)")
                             + "; a pin reaches an arm by its spec name or by "
                             "`syscall_spec` on an input naming its number.")
    return len(arms)


# --------------------------------------------------------------- DIV-1/DIV-2

def closed_literal_value(expr):
    """int value of a closed literal expression, or None if it is not one."""
    inner = expr
    m = TYPE_ASCRIPTION.match(inner)
    if m:
        inner = m.group(1)
    if not CLOSED_LITERAL.match(inner) or not NUMERAL.search(inner):
        return None
    py = inner.replace("^", "**").replace("_", "")
    py = re.sub(r"\b0[oO]", "0o", py)
    try:
        return int(eval(py, {"__builtins__": {}}, {}))  # noqa: S307 -- charset checked above
    except Exception:
        return None


_definition_cache = {}

# `import A.B.Stem.Part` alone on its line, as a re-export spells its parts.
IMPORT_LINE = re.compile(r"^import\s+([A-Za-z_][\w.]*)\s*$", re.M)


def reexport_parts(root, rel, clean):
    """The parts `rel` re-exports, in import order.  A split twin keeps its
    definitions in `<dir>/<Stem>/<Part>.lean` and `<dir>/<Stem>.lean` is a
    re-export that imports each part and defines nothing; that is the rule
    check_lean_spec_parity.twin_parts states for the parity checker, applied
    here with the file's own `import <...>.<Stem>.<Part>` lines so this lint
    needs nothing from that module.  Only a file that exists counts: an
    import of a module elsewhere is not a part, and a file under the parts
    directory that the re-export does not import is not read.  The entry in
    POSITIVE_DIVISORS may still name a part directly; then this is not
    consulted.  Since A15 split `State.lean` (PR #779) every divisor named
    there lives in a part, and the day tip's copy of this lint has to read
    that tree before the split lands."""
    stem = os.path.splitext(os.path.basename(rel))[0]
    parts = []
    for m in IMPORT_LINE.finditer(clean):
        mod = m.group(1).split(".")
        if len(mod) >= 2 and mod[-2] == stem:
            part = os.path.join(os.path.dirname(rel), stem, mod[-1] + ".lean")
            if part not in parts and os.path.isfile(os.path.join(root, part)):
                parts.append(part)
    return parts


def allowlisted_positive(root, name):
    """Why `name` is a positive divisor, or a reason it is not.  The verdict
    names the file the definition was read from: the entry's file, or the
    part of a re-export that holds it."""
    key = (root, name)
    if key in _definition_cache:
        return _definition_cache[key]
    rel = POSITIVE_DIVISORS[name]
    path = os.path.join(root, rel)
    if not os.path.isfile(path):
        verdict = (False, f"`{name}` is in POSITIVE_DIVISORS but {rel} does not exist here")
    else:
        with open(path, encoding="utf-8") as f:
            clean = blank_comments_and_strings(f.read())
        definition = re.compile(rf"^\s*def\s+{re.escape(name)}\s*:\s*(?:Int|Nat|ℤ|ℕ)\s*:=(.*)$", re.M)
        where, m = rel, definition.search(clean)
        parts = [] if m else reexport_parts(root, rel, clean)
        for part in parts:
            with open(os.path.join(root, part), encoding="utf-8") as f:
                m = definition.search(blank_comments_and_strings(f.read()))
            if m:
                where = part
                break
        if not m:
            why = (f"`{name}` is in POSITIVE_DIVISORS but {rel} has no "
                   f"`def {name} : Int := …` on one line")
            if parts:
                why += ", nor does any part it re-exports (" + ", ".join(parts) + ")"
            verdict = (False, why)
        else:
            v = closed_literal_value(m.group(1))
            if v is None:
                verdict = (False, f"`{name}` is in POSITIVE_DIVISORS but its definition "
                                  f"in {where} is not a closed literal: `{m.group(1).strip()}`")
            elif v <= 0:
                verdict = (False, f"`{name}` is in POSITIVE_DIVISORS but {where} defines it "
                                  f"as {v}, which is not positive")
            else:
                verdict = (True, f"{where} defines `{name}` as {v}")
    _definition_cache[key] = verdict
    return verdict


def matching_paren(text, i):
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    return None


def read_primary(root, clean, i):
    """Judge the primary expression at offset i: (ok, reason, end offset)."""
    if i >= len(clean):
        return False, "end of file where a divisor should be", i
    c = clean[i]
    if c == "(":
        j = matching_paren(clean, i)
        if j is None:
            return False, "unbalanced parenthesis in the divisor", i + 1
        inner = clean[i + 1:j]
        v = closed_literal_value(inner)
        if v is None:
            return False, f"parenthesized divisor `({normalize(inner)})` is not a closed literal", j + 1
        if v <= 0:
            return False, f"divisor `({normalize(inner)})` is {v}, not positive", j + 1
        return True, "", j + 1
    m = NUMERAL.match(clean, i)
    if m:
        v = closed_literal_value(m.group(0))
        if v is None or v <= 0:
            return False, f"divisor literal `{m.group(0)}` is not positive", m.end()
        return True, "", m.end()
    m = QUALIFIED.match(clean, i)
    if m:
        name = m.group(0)
        if name not in POSITIVE_DIVISORS:
            return False, (f"divisor `{name}` is not a literal and not in POSITIVE_DIVISORS "
                           "-- Rocq's Z.div/Z.modulo (floor) and Lean's Int `/`,`%` "
                           "(Euclidean) agree only for a positive divisor"), m.end()
        ok, why = allowlisted_positive(root, name)
        if not ok:
            return False, why, m.end()
        nxt = clean[m.end():m.end() + 1]
        rest = clean[m.end():].lstrip(" ")
        if rest[:1] and (rest[0] == "(" or rest[0].isalnum() or rest[0] == "_") and nxt == " ":
            return False, f"`{name}` is applied to an argument, so the divisor is not the constant", m.end()
        return True, "", m.end()
    return False, f"divisor starts with `{c}`, which this lint does not read", i + 1


def judge_divisor(root, clean, i):
    """The right operand of the operator ending at offset i-1.  `^` binds
    tighter than `/` and `%`, so `x % 2 ^ 32` divides by 2 ^ 32: every
    primary in the `^` chain must be positive."""
    j = i
    while j < len(clean) and clean[j] in " \t\n":
        j += 1
    ok, why, j = read_primary(root, clean, j)
    if not ok:
        return False, why
    while True:
        k = j
        while k < len(clean) and clean[k] in " \t":
            k += 1
        if clean[k:k + 1] != "^":
            return True, ""
        k += 1
        while k < len(clean) and clean[k] in " \t":
            k += 1
        ok, why, j = read_primary(root, clean, k)
        if not ok:
            return False, "in the exponent: " + why


def check_specs(root, findings):
    sites = 0
    for rel in lean_files(root, SPECS_DIR):
        with open(os.path.join(root, rel), encoding="utf-8") as f:
            text = f.read()
        clean = blank_comments_and_strings(text)
        for m in re.finditer(r"[/%]", clean):
            sites += 1
            ok, why = judge_divisor(root, clean, m.end())
            if not ok:
                findings.add(rel, line_of(clean, m.start()), "DIV-1",
                             f"`{m.group(0)}` at `{normalize(clean[m.start():m.start() + 40])}`: {why}")
        for m in NAMED_DIVISION.finditer(clean):
            sites += 1
            findings.add(rel, line_of(clean, m.start()), "DIV-2",
                         f"`{m.group(0)}`: spell Euclidean division as `/`/`%` with a "
                         "positive divisor so DIV-1 can read it; the truncating forms "
                         "differ from Rocq's floor division even then. `Int.fdiv`/"
                         "`Int.fmod` are the floor forms and pass.")
    return sites


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=".", help="repository root (default: .)")
    args = ap.parse_args()
    root = args.root

    findings = Findings(root)
    decls, pins = check_pins(root, findings)
    arms = check_table(root, findings, pins)
    sites = check_specs(root, findings)

    for line in findings.lines:
        print(line, file=sys.stderr)
    if findings.lines:
        sys.exit(f"check_lean_pins.py: {len(findings.lines)} finding(s) over {decls} "
                 f"declaration(s) in {CASES_DIR}, {arms} registered arm(s) and {sites} "
                 f"division site(s) in {SPECS_DIR}")
    print(f"check_lean_pins.py: {decls} declaration(s) in {CASES_DIR} ({len(pins)} pins), "
          f"{arms} registered arm(s) each pinned both ways, and {sites} "
          f"division site(s) in {SPECS_DIR}, no findings")


if __name__ == "__main__":
    main()
