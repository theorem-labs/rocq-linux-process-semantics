import LinuxProcessSemantics.LinuxProcessSem.Specs

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Witness.Prelude — the witnesses' shared helpers and tactics

Mirrors `theories/LinuxProcessSem/Checks/Witness/Prelude.v`: the
infrastructure every progress witness under `Checks/Witness/` shares.  It
mirrors no kernel source and holds nothing syscall-specific.  Not part of
the trusted specification: a witness exhibits one outcome a spec in the
matching `Sys` module admits, its `*_witness_ok` lemma proves the
admission, and `Checks/Progress.lean` is what consumes both.

The baseline is the one `Checks/Sys/Dispatch.lean`'s header explains: the
Rocq file is byte-identical there to `f44244ad6b80`, the commit BRIEF.md
names, which stopped being an ancestor of any branch when that day's work
was rebase-merged.  The Rocq file ends in a section comment left behind by
the split that created `Checks/Witness/Uaccess.v`; it describes the `read`
witness and a three-way `access_ok_zero_witness` with a fail-closed arm,
which the definition it names no longer has, so it is not transcribed —
the two-answer argument is on `Checks/Witness/Uaccess.lean`.

Spellings that differ from Rocq without changing a value, said once: `In`
is `∈`, and `srw` is a macro, as it is in `Checks/Sys/Prelude.lean`.  Rocq
defines the tactic once per file, and so does this tree.  A `macro` is not
scoped by its namespace: a file that imports both definitions —
`Checks/Progress.lean` does, and so does any witness check file that also
imports the checker prelude — parses `srw h` as a choice of the two and
elaborates ONE of them, the alternative the parser lists first, and never
compares them; an ordinary failure inside that alternative is reported,
not a reason to try the other.  So the two expansions are kept identical
by hand, and the file where only this one is in scope,
`Checks/Cases/Checks/Witness/Uaccess.lean`, is where its expansion is
pinned; `Checks/Cases/Checks/Witness/Prelude.lean` pins that the text still
parses and closes with both in scope. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- Rewrite a scrutinee equation, then re-reduce the `match`/`if` it
unblocks.  Rocq's `srw H` is `rewrite H; cbv beta iota zeta`; Lean's
`dsimp only` is that reduction (beta, iota, zeta, projections, no lemmas),
under `try` because `dsimp only` fails where `cbv` merely does nothing.
`srw E at h` is the same on a hypothesis. -/
macro "srw " e:term loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (rw [$e:term] $[$loc]?; try dsimp only $[$loc]?))

/-- A bind step whose first component contributes no events (it may still
update the model), propagating EITHER outcome shape of the continuation.
Every step in a witness proof is of this form except `emit`, which has
`emit_pure_ok`. -/
theorem bind_step {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (x : A) (m1 : Model) (o : outcome B)
    (hc : c i m (Ok x m1 [])) (hk : k x i m1 o) : bind c k i m o := by
  cases o with
  | Ok y m2 evs => exact bind_ok c k i m x m1 [] y m2 evs hc hk
  | Unmodeled => exact bind_unmodeled2 c k i m x m1 [] hc hk

/-- `emit` followed by `pure`: the whole program's events are exactly the
emitted ones. -/
theorem emit_pure_ok {A : Type} (evs : List event) (x : A) (i : SyscallInput) (m : Model) :
    (emit evs ;; Monad.pure x) i m (Ok x m evs) :=
  ⟨(), m, evs, [], rfl, rfl, (List.append_nil evs).symm⟩

/-- Every injectable-errno set is inhabited, so the failure branch is
always available: a member of the set is a witness. -/
theorem errno_from_witness (es : List Int) (e : Int) (i : SyscallInput) (m : Model)
    (h : e ∈ es) : errno_from es i m (Ok e m []) :=
  choose_ok (fun e => e ∈ es) e i m h

/-- The head of the set is a member, which is how a witness picks the
errno it fails with. -/
theorem errno_head_witness (e : Int) (es : List Int) (i : SyscallInput) (m : Model) :
    errno_from (e :: es) i m (Ok e m []) :=
  errno_from_witness (e :: es) e i m (List.Mem.head es)

/-- ENOMEM, the errno the mmap and mprotect witnesses fail with: `ENOMEM`
(include/uapi/asm-generic/errno-base.h, Linux v6.18.46) is 12.  It is the
head of the injectable sets those arms draw from, which is what lets
`errno_head_witness` supply the failure outcome; the value and the two
heads are pinned in `Checks/Cases/Checks/Witness/Prelude.lean`, with the
heads of `openat_errnos` and `dup_errnos`, whose Rocq witnesses draw it
the same way; which other witnesses fail with it is each twin's to say as
it lands, and `getrandom`'s draws EINTR instead. -/
def witness_errno : Int := ENOMEM

/-- Shorthand for the "return `r`, change nothing, emit nothing" outcome:
the shape `Checks/Sys/Prelude.lean`'s `check_ret_only` accepts, so a
witness built from it is one the acceptor admits. -/
def ret_outcome (r : word) (m : Model) : outcome SyscallEffect :=
  Ok (mkEffect r [] []) m []

/-- `bind_ok` with the event concatenation as an explicit equation, so a
witness proof can hand over the events it computed rather than the
`evs1 ++ evs2` the lemma builds. -/
theorem witness_bind_ok_eq {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput)
    (m : Model) (x : A) (m1 : Model) (evs1 : List event) (y : B) (m2 : Model)
    (evs2 evs : List event)
    (hc : c i m (Ok x m1 evs1)) (hk : k x i m1 (Ok y m2 evs2)) (hevs : evs = evs1 ++ evs2) :
    bind c k i m (Ok y m2 evs) := by
  subst hevs
  exact bind_ok c k i m x m1 evs1 y m2 evs2 hc hk

end LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
