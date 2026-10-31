import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Signal — the rt_sigaction (134) and rt_sigprocmask (135) checkers and witnesses, and their proofs

Mirrors the rt_sigaction and rt_sigprocmask half of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Signal.v` (the two executable
checkers, the `oset` copy-out acceptor they share, and their soundness and
completeness proofs) and the same half of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Signal.v` (the two
receptiveness witnesses, the copy-out witness they share, and their
proofs), in that order, as two sections of one module.  Both answer to
Linux `kernel/signal.c`.  Not part of the trusted specification: the
specs are `Sys/Kernel/Signal.lean`'s, and every theorem here relates an
executable checker, or a witness, to one of them.  The pins are
`Checks/Cases/Checks/Sys/Kernel/Signal.lean`.

The Rocq checker file is split out of `Checks/ExecutableSpecs.v`, which
keeps the dispatcher and the four top-level theorems and re-exports it;
the Rocq witness file is split out of `Checks/Progress.v` the same way.

TWO TICKETS WROTE THIS FILE, IN TWO HALVES.  The first half — rt_sigaction
and rt_sigprocmask, everything down to `rt_sigprocmask_witness_ok` — is the
mask/action ticket's (C-Kernel-Signal-mask-action).  The OTHER HALF of the
two Rocq files — `check_sigaltstack`, `check_send_sigabrt`,
`check_tkill_self`, `check_tkill` and `check_tgkill` with their lemmas and
`check_tkill_frame` and `check_tgkill_frame`, and the witnesses
`sigaltstack_witness`, `send_sigabrt_witness`, `tkill_self_witness`,
`tkill_witness` and `tgkill_witness` — is the sigaltstack/tkill/tgkill
ticket's (C-Kernel-Signal-altstack-kill), appended below the first in three
marked sections after the first ticket had merged; neither half depends on
the other and neither restates the other.  Three names in the second half
have no Rocq twin: `check_send_sigabrt_ok_iff`, the delivery acceptor's
effect destruct as an iff, and `check_send_sigabrt_frame` and
`check_tkill_self_frame`, the halves of the two frame lemmas that Rocq's
`repeat match` walks in place.  One name a reader may look for is not here
on purpose: Rocq states `check_sigaltstack_frame` in
`Checks/VmMapsDisjoint.v` beside the alternation, not in the checker file,
so its twin is the registration's.

WHAT IS NOT HERE, AND WHOSE IT IS.  The REGISTRATION: the arm each checker
becomes — the `CheckedArm` built from its four lemmas and its witness's
`_ok`, the row that carries its number in the checked table, the
`arm_unfold` lemmas that open it, and the alternative the VM-ledger
invariant's alternation takes for it — is the conformance ticket's
registration step, not this file's (BRIEF.md section 5, CHECK).  That
split is what lets this file build on the two preludes and the spec alone,
and a `lean: checks:` PR carries none of those hunks.

The header's baseline is a71fd38a, the squash that landed the 2026-09-11
work on main; both Rocq files are byte-identical there to the port's
common baseline f44244ad, from which the brief quotes them, and to
8589c1245, the `nightly/09-14-2026` tip this twin was written against on
2026-09-19.

WHAT A CHECKER HERE DECIDES.  Each checker is its spec's branch
structure, branch for branch, with the relational `ret_only r` replaced
by `check_ret_only eff r m []` — the executable test that the recorded
effect is exactly a return of `r` with no writes, no zero-fills, no
copy-in ledger and no model change — the spec's `unmodeled` replaced by
`CheckUnmodeled`, and, for rt_sigprocmask alone, two more executable
tests: `check_one_write`, the same test for an effect that is exactly one
store, which is what the `oset` copy-out produces, and the `_copyins`
forms, which strip the copy-in ledger before the test and compare it
afterwards, the way `Checks/Sys/Prelude.lean`'s `check_ret_only_copyins`
does for a bare return.  The second half adds one more, `check_send_sigabrt`:
the bare-return test for the SIGABRT delivery, whose model is the
delivery's own — the pending bit or the kill — in place of the one given.  Nothing is decided here that the spec does not
decide, and the lemmas say so in both directions: what a checker accepts
its spec admits (`*_sound_ok`), what it declines its spec declines
(`*_sound_unmodeled`), and conversely (`*_complete_ok`,
`*_complete_unmodeled`).  Read `Sys/Kernel/Signal.lean` for the kernel
order the branches are in; the docstrings below name the line each
branch answers to, and the argument for each decline is on the spec.

WHY THE MODEL IS THE CHECKER'S OUTPUT AND NEVER ITS INPUT TO COMPARE.  A
trace shows the checker an input and an effect; the model after the call
is what the checker computes, `CheckOk m' evs`, and three arms here return
a model other than the one they were given: rt_sigprocmask's install,
sigaltstack's install, and the SIGABRT delivery under tkill and tgkill.  So
a lie about the mask installed, the alternate-stack bit or the pending bit
is not a `CheckReject` — there is no offered model to refuse — but a
`CheckOk` with the RIGHT model, which the pins state by refuting the wrong
one.  The facts a consumer needs about those models are stated where
Rocq states them: `check_rt_sigprocmask_keeps_mask_launchable`, the
whole-run half of `Run.valid_sigmask`, and `check_rt_sigprocmask_frame`,
`check_tkill_frame` and `check_tgkill_frame`, the VM-ledger halves, at
the end of their checker sections — sigaltstack's frame excepted, which
Rocq states in `Checks/VmMapsDisjoint.v` beside the alternation (above).
A frame lemma is HERE and not the registration's exactly when Rocq's
proof needs a lemma that lives beside the checker: `check_write_oset_ok_iff`
for rt_sigprocmask's copy-out, the destruct of the delivery's effect
(`check_send_sigabrt_ok_iff`) for tkill and tgkill.  Changing the model
is not by itself the reason — `check_sigaltstack` changes it too, and
Rocq's generic VM-ledger tactic walks that arm unaided.  The
registration's alternative for each names the lemma and adds nothing.
The Rocq `check_rt_sigprocmask_inert` it replaced, and why it went, is on
Rocq's `check_rt_sigprocmask_frame`.

THE PROOFS keep Rocq's shape.  Where Rocq writes `destruct b eqn:H; cbv
beta iota`, a Lean proof writes `cases hb : b with | true => simp only
[hb, …, ↓reduceIte] at h ⊢ | false => …` — `cases hb : e` substitutes the
goal alone, so `hb` is spelled in the set for the hypothesis and the
goal's `if` is reduced by the same pass.  Where Rocq's completeness proofs
write `inv_ok` on an `err_ret`, a Lean proof coerces the hypothesis to
the `Ok = Ok` equation it unfolds to (`have h' : Ok eff m' evs = Ok … m []
:= h`) and cases on it, which substitutes the effect, model and events at
once.  Rocq's completeness proof for rt_sigprocmask ends in
`check_write_oset_efault` and `check_write_oset_stored`, the two accepted
shapes of the copy-out; those are ported by name.  Its soundness proof
destructs `check_write_oset … (clear_copyins eff) …` in place; the Lean
proof factors that destruct into `check_write_oset_copyins_ok_iff` and
`check_write_oset_copyins_no_ok_unmodeled`, two lemmas Rocq does not
have, because three proofs (soundness, the launchable mask and the frame)
would otherwise spell the same scrutinee three times.
Rocq's `check_write_oset_copyins_ok` is the `mpr` half of the first at
`evs = []`, and is ported by name beside it.  The second half keeps the
same shape with two additions: the one Prop gate in the file,
sigaltstack's `MINSIGSTKSZ` comparison, is split by `cases` on its
`decide` where the Bool gates are split by `cases` on the Bool — never by
`by_cases`, whose `dite` makes the elaborator take the weak head normal
form of a goal headed by that `ite`, and the `Int` comparison's
`Decidable` instance does not have one within the recursion depth — and
the two in-place destructs of the delivery's effect Rocq makes, in
`check_send_sigabrt_sound_ok` and `check_send_sigabrt_no_unmodeled`, are
factored into one lemma, `check_send_sigabrt_ok_iff`, which `sound_ok`,
`complete_ok` and `check_send_sigabrt_frame` read (the tkill and tgkill
frames reach it through that one); `no_unmodeled` still destructs in
place, because the iff's `CheckOk` side does not by itself give
`≠ CheckUnmodeled`, and `complete_unmodeled` opens neither — it refutes
its spec-side hypothesis. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Signal

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## rt_sigaction (134) -/

/-- rt_sigaction: nothing is recorded, so every admissible outcome is a
bare return, and the declining arms are the ones whose answer would need a
stored disposition (see `Signal.rt_sigaction_spec`).  The gates are the
kernel's, in the kernel's order: `if (sigsetsize != sizeof(sigset_t))
return -EINVAL;` (`SYSCALL_DEFINE4(rt_sigaction)`, kernel/signal.c:4647-4648,
Linux v6.18.46), then the `oact` decline — the one place the spec is
EARLIER than the kernel, which copies `act` in first (:4650-4651) — then
`act`'s copy-in (-EFAULT, :4650-4651), then `do_sigaction`'s guard
`if (!valid_signal(sig) || sig < 1 || (act && sig_kernel_only(sig)))
return -EINVAL;` (kernel/signal.c:4317-4318, Linux v6.18.46), then the flags and the
signal's acceptance (`Signal.sa_flags_ok`, `Signal.sigaction_accepted`),
where Linux answers 0 (:4660) and the model answers 0 or declines.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigaction`. -/
def check_rt_sigaction (i : SyscallInput) (sig act oact ss : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(bv_eqb ss (Z_to_bv 64 8)) then check_ret_only eff (errno_ret EINVAL) m []
  else if !(w_is0 oact) then CheckUnmodeled
  else if w_is0 act
  then (if sig_valid sig then check_ret_only eff (Z_to_bv 64 0) m []
        else check_ret_only eff (errno_ret EINVAL) m [])
  else
    match sigaction_flags i.in_mem act with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some fl =>
        if !(sig_valid sig) then check_ret_only eff (errno_ret EINVAL) m []
        else if sig_kernel_only sig then check_ret_only eff (errno_ret EINVAL) m []
        else if !(sa_flags_ok fl) then CheckUnmodeled
        else if sigaction_accepted sig then check_ret_only eff (Z_to_bv 64 0) m []
        else CheckUnmodeled

/-- Every `CheckOk` the checker returns is a run the spec admits.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigaction_sound_ok`. -/
theorem check_rt_sigaction_sound_ok (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs) :
    rt_sigaction_spec sig act oact ss i m (Ok eff m' evs) := by
  unfold check_rt_sigaction at h
  unfold rt_sigaction_spec
  cases hss : bv_eqb ss (Z_to_bv 64 8) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hoact : w_is0 oact with
  | false =>
    simp only [hoact, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoact, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hact : w_is0 act with
  | true =>
    simp only [hact, ↓reduceIte] at h ⊢
    cases hv : sig_valid sig with
    | true =>
      simp only [hv, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
  | false =>
  simp only [hact, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
  cases hfl : sigaction_flags i.in_mem act with
  | none =>
    simp only [hfl] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some fl =>
  simp only [hfl] at h ⊢
  cases hv : sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hk : sig_kernel_only sig with
  | true =>
    simp only [hk, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | false =>
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfo : sa_flags_ok fl with
  | false =>
    simp only [hfo, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hfo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ha : sigaction_accepted sig with
  | true =>
    simp only [ha, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | false =>
    simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `Checks.Sys.Kernel.Signal.check_rt_sigaction_sound_unmodeled`. -/
theorem check_rt_sigaction_sound_unmodeled (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_rt_sigaction i sig act oact ss eff m = CheckUnmodeled) :
    rt_sigaction_spec sig act oact ss i m Unmodeled := by
  unfold check_rt_sigaction at h
  unfold rt_sigaction_spec
  cases hss : bv_eqb ss (Z_to_bv 64 8) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hoact : w_is0 oact with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hoact, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hact : w_is0 act with
  | true =>
    simp only [hact, ↓reduceIte] at h
    cases hv : sig_valid sig with
    | true =>
      simp only [hv, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hact, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
  cases hfl : sigaction_flags i.in_mem act with
  | none =>
    simp only [hfl] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some fl =>
  simp only [hfl] at h ⊢
  cases hv : sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hk : sig_kernel_only sig with
  | true =>
    simp only [hk, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfo : sa_flags_ok fl with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hfo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ha : sigaction_accepted sig with
  | true =>
    simp only [ha, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- Every run the spec admits is one the checker accepts, with the same
model and the same (empty) event list.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigaction_complete_ok`. -/
theorem check_rt_sigaction_complete_ok (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : rt_sigaction_spec sig act oact ss i m (Ok eff m' evs)) :
    check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs := by
  unfold rt_sigaction_spec at h
  unfold check_rt_sigaction
  cases hss : bv_eqb ss (Z_to_bv 64 8) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hoact : w_is0 oact with
  | false =>
    simp only [hoact, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hoact, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hact : w_is0 act with
  | true =>
    simp only [hact, ↓reduceIte] at h ⊢
    cases hv : sig_valid sig with
    | true =>
      simp only [hv, ↓reduceIte] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hact, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_ok_inv _ i m _ _ _ h
  cases hfl : sigaction_flags i.in_mem act with
  | none =>
    simp only [hfl] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some fl =>
  simp only [hfl] at h ⊢
  cases hv : sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hk : sig_kernel_only sig with
  | true =>
    simp only [hk, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfo : sa_flags_ok fl with
  | false =>
    simp only [hfo, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hfo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ha : sigaction_accepted sig with
  | true =>
    simp only [ha, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
    simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigaction_complete_unmodeled`. -/
theorem check_rt_sigaction_complete_unmodeled (i : SyscallInput) (sig act oact ss : word)
    (m : Model) (eff : SyscallEffect)
    (h : rt_sigaction_spec sig act oact ss i m Unmodeled) :
    check_rt_sigaction i sig act oact ss eff m = CheckUnmodeled := by
  unfold rt_sigaction_spec at h
  unfold check_rt_sigaction
  cases hss : bv_eqb ss (Z_to_bv 64 8) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hoact : w_is0 oact with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hoact, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hact : w_is0 act with
  | true =>
    simp only [hact, ↓reduceIte] at h
    cases hv : sig_valid sig with
    | true =>
      simp only [hv, ↓reduceIte] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      cases h'
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
  | false =>
  simp only [hact, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_unmodeled_inv _ i m h
  cases hfl : sigaction_flags i.in_mem act with
  | none =>
    simp only [hfl] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
  | some fl =>
  simp only [hfl] at h ⊢
  cases hv : sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hk : sig_kernel_only sig with
  | true =>
    simp only [hk, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | false =>
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfo : sa_flags_ok fl with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hfo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ha : sigaction_accepted sig with
  | true =>
    simp only [ha, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]

/-! ## The `oset` copy-out acceptor, shared by rt_sigprocmask's two writing arms -/

/-- An effect that is exactly one write and nothing else, in the shape
`check_ret_only` has for an effect that is nothing at all.  Local to this
file because Rocq defines it here, beside `check_write_oset`, rather than
in its Prelude — other Rocq checkers that owe exactly one store spell the
match inline — and the port keeps the file-for-file layout instead of
hoisting.  Rocq: `Checks.Sys.Kernel.Signal.check_one_write`. -/
def check_one_write (eff : SyscallEffect) (r a : word) (bs : List byte) (m' : Model)
    : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret ws [] [] [] [] =>
      if bv_eqb ret r && writes_eqb ws [(a, bs)] then CheckOk m' [] else CheckReject
  | _ => CheckReject

/-- Rocq: `Checks.Sys.Kernel.Signal.check_one_write_ok_iff`. -/
theorem check_one_write_ok_iff (eff : SyscallEffect) (r a : word) (bs : List byte)
    (m1 m' : Model) (evs : List event) :
    check_one_write eff r a bs m1 = CheckOk m' evs ↔
    (eff = mkEffect r [(a, bs)] [] ∧ m' = m1 ∧ evs = []) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases zs with
  | cons z zs =>
    simp only [check_one_write, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases us with
  | cons u us =>
    simp only [check_one_write, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases cs with
  | cons c cs =>
    simp only [check_one_write, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases copyins with
  | cons c copyins =>
    simp only [check_one_write, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  simp only [check_one_write, mkEffect, SyscallEffect.mkEffectU.injEq, and_true]
  cases hE : (bv_eqb ret r && writes_eqb ws [(a, bs)]) with
  | true =>
    rw [Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq] at hE
    obtain ⟨rfl, rfl⟩ := hE
    simp only [↓reduceIte, check_result.CheckOk.injEq, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    rintro ⟨rfl, rfl⟩ - -
    rw [bv_eqb_refl, (writes_eqb_eq _ _).mpr rfl] at hE
    exact absurd hE (by simp only [Bool.and_self, reduceCtorEq, not_false_eq_true])

/-- The `oset` copy-out acceptor, mirroring `Kernel.Signal.write_oset` arm
for arm and testing the same booleans in the same order —
`State.access_okb` BEFORE the `in_wmem` walk, because the walk wraps at
2^64 and the range test does not.  `copy_to_user(oset, &old_set,
sizeof(sigset_t))` (`SYSCALL_DEFINE4(rt_sigprocmask)`,
kernel/signal.c:3349-3351, Linux v6.18.46) is -EFAULT when
`access_ok` refuses the range — `__access_ok`, include/asm-generic/access_ok.h:31-41,
Linux v6.18.46 — and the model DECLINES a range inside the address space
whose eight bytes are not all writable, because the store may be partial
there and the model does not track how much of it landed.

Both answering arms demand an empty copy-in ledger, which is what
`write_oset` itself produces; the callers that run it under a
`Syscall.record_copyins` use `check_write_oset_copyins` below.  Rocq:
`Checks.Sys.Kernel.Signal.check_write_oset`. -/
def check_write_oset (i : SyscallInput) (oset old : word) (eff : SyscallEffect) (m' : Model)
    : check_result :=
  if !(access_okb oset NSIG_BYTES) then check_ret_only eff (errno_ret EFAULT) m' []
  else
    match read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
    | none => CheckUnmodeled
    | some _ =>
        check_one_write eff (Z_to_bv 64 0) oset
          (Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old)) m'

/-- The same, under a recorded copy-in ledger.  `check_ret_only_copyins`
stands to `check_ret_only` exactly as this stands to `check_write_oset`,
and for the same reason: the ledger is attached outside the arm that
produced the effect.  Rocq: `Checks.Sys.Kernel.Signal.check_write_oset_copyins`. -/
def check_write_oset_copyins (reads : List (word × Nat)) (i : SyscallInput) (oset old : word)
    (eff : SyscallEffect) (m' : Model) : check_result :=
  match check_write_oset i oset old (clear_copyins eff) m' with
  | CheckOk m'' evs =>
      if access_ranges_eqb eff.eff_copyins reads then CheckOk m'' evs else CheckReject
  | result => result

/-- Rocq: `Checks.Sys.Kernel.Signal.check_write_oset_ok_iff`. -/
theorem check_write_oset_ok_iff (i : SyscallInput) (oset old : word) (eff : SyscallEffect)
    (m1 m' : Model) (evs : List event) :
    check_write_oset i oset old eff m1 = CheckOk m' evs ↔
    (m' = m1 ∧ evs = [] ∧ eff.eff_copyins = [] ∧ write_oset oset old i m1 (Ok eff m1 [])) := by
  unfold check_write_oset write_oset
  cases ha : access_okb oset NSIG_BYTES with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, check_ret_only_ok_iff]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, pure_ok _ i _⟩
    · rintro ⟨hm, rfl, -, hs⟩
      have h' : Ok eff m1 [] = Ok (mkEffect (errno_ret EFAULT) [] []) m1 [] := hs
      cases h'
      exact ⟨rfl, hm, rfl⟩
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
  | some bs =>
    simp only [check_one_write_ok_iff]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, rfl, rfl, ?_⟩
      refine bind_ok0 _ _ i _ i _ _ _ _ (input_ok i _) ?_
      simp only [hw]
      exact pure_ok _ i _
    · rintro ⟨hm, rfl, -, hs⟩
      have hs := input_bind_ok_inv _ i m1 _ _ _ hs
      simp only [hw] at hs
      have h' : Ok eff m1 [] = Ok (mkEffect (Z_to_bv 64 0)
          [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))] []) m1 [] := hs
      cases h'
      exact ⟨rfl, hm, rfl⟩
  | none =>
    simp only [reduceCtorEq, false_iff, not_and]
    rintro hm rfl - hs
    have hs := input_bind_ok_inv _ i m1 _ _ _ hs
    simp only [hw] at hs
    have h' : Ok eff m1 [] = Unmodeled := hs
    cases h'

/-- Rocq: `Checks.Sys.Kernel.Signal.check_write_oset_no_ok_unmodeled`. -/
theorem check_write_oset_no_ok_unmodeled (i : SyscallInput) (oset old : word)
    (eff : SyscallEffect) (m1 : Model)
    (h : check_write_oset i oset old eff m1 = CheckUnmodeled) :
    ∀ m, write_oset oset old i m Unmodeled := by
  intro m
  unfold check_write_oset at h
  unfold write_oset
  cases ha : access_okb oset NSIG_BYTES with
  | false =>
    simp only [ha, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
  | some bs =>
    simp only [hw] at h
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    cases zs with
    | cons z zs => simp only [check_one_write, reduceCtorEq] at h
    | nil =>
    cases us with
    | cons u us => simp only [check_one_write, reduceCtorEq] at h
    | nil =>
    cases cs with
    | cons c cs => simp only [check_one_write, reduceCtorEq] at h
    | nil =>
    cases copyins with
    | cons c copyins => simp only [check_one_write, reduceCtorEq] at h
    | nil =>
    simp only [check_one_write] at h
    cases hE : (bv_eqb ret (Z_to_bv 64 0) &&
        writes_eqb ws [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))]) with
    | true => simp only [hE, ↓reduceIte, reduceCtorEq] at h
    | false => simp only [hE, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | none =>
    refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
    simp only [hw]
    exact unmodeled_intro i m

/-- The copy-out acceptor under a ledger, read at `CheckOk`: the arm's own
verdict on the effect with its ledger cleared, and the ledger equal to
`reads`.  Not in Rocq, whose soundness proof destructs
`check_write_oset … (clear_copyins eff) …` in place; here three proofs
need the same reading (the header says which), so it is stated once.
`check_write_oset_copyins_ok` below is its `mpr` half at `evs = []`, the
shape Rocq names. -/
theorem check_write_oset_copyins_ok_iff (reads : List (word × Nat)) (i : SyscallInput)
    (oset old : word) (eff : SyscallEffect) (m1 m' : Model) (evs : List event) :
    check_write_oset_copyins reads i oset old eff m1 = CheckOk m' evs ↔
    (m' = m1 ∧ evs = [] ∧ eff.eff_copyins = reads ∧
     write_oset oset old i m1 (Ok (clear_copyins eff) m1 [])) := by
  unfold check_write_oset_copyins
  cases hcw : check_write_oset i oset old (clear_copyins eff) m1 with
  | CheckOk m2 evs2 =>
    rw [check_write_oset_ok_iff] at hcw
    obtain ⟨rfl, rfl, -, hspec⟩ := hcw
    cases hled : access_ranges_eqb eff.eff_copyins reads with
    | true =>
      rw [access_ranges_eqb_eq] at hled
      simp only [↓reduceIte, check_result.CheckOk.injEq, hled, hspec, and_true]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro _ _ hr
      rw [hr, access_ranges_eqb_refl] at hled
      exact absurd hled (by simp only [reduceCtorEq, not_false_eq_true])
  | CheckReject =>
    simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl rfl - hspec
    have hok := (check_write_oset_ok_iff i oset old (clear_copyins eff) _ _ []).mpr
      ⟨rfl, rfl, rfl, hspec⟩
    rw [hok] at hcw
    exact absurd hcw (by simp only [reduceCtorEq, not_false_eq_true])
  | CheckUnmodeled =>
    simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl rfl - hspec
    have hok := (check_write_oset_ok_iff i oset old (clear_copyins eff) _ _ []).mpr
      ⟨rfl, rfl, rfl, hspec⟩
    rw [hok] at hcw
    exact absurd hcw (by simp only [reduceCtorEq, not_false_eq_true])

/-- The copy-out acceptor under a ledger declines only where the copy-out
itself does — on every model, since the decline reads the input alone.
Not in Rocq, for the reason on `check_write_oset_copyins_ok_iff`. -/
theorem check_write_oset_copyins_no_ok_unmodeled (reads : List (word × Nat))
    (i : SyscallInput) (oset old : word) (eff : SyscallEffect) (m1 : Model)
    (h : check_write_oset_copyins reads i oset old eff m1 = CheckUnmodeled) :
    ∀ m, write_oset oset old i m Unmodeled := by
  unfold check_write_oset_copyins at h
  cases hcw : check_write_oset i oset old (clear_copyins eff) m1 with
  | CheckOk m2 evs2 =>
    simp only [hcw] at h
    cases hled : access_ranges_eqb eff.eff_copyins reads with
    | true => simp only [hled, ↓reduceIte, reduceCtorEq] at h
    | false => simp only [hled, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | CheckReject =>
    simp only [hcw, reduceCtorEq] at h
  | CheckUnmodeled =>
    exact check_write_oset_no_ok_unmodeled i oset old (clear_copyins eff) m1 hcw

/-! ## rt_sigprocmask (135) -/

/-- rt_sigprocmask's acceptor, mirroring `Kernel.Signal.rt_sigprocmask_spec`
gate for gate in the kernel's order (`SYSCALL_DEFINE4(rt_sigprocmask)`,
kernel/signal.c:3327-3355, Linux v6.18.46): `if (sigsetsize !=
sizeof(sigset_t)) return -EINVAL;` (:3334-3335); `old_set =
current->blocked` (:3337), the snapshot `oset` reports whatever follows;
`if (nset)` (:3339) — a NULL set skips the copy-in, `sigdelsetmask` and
`sigprocmask` alike, so `how` is never looked at; `copy_from_user`
(:3340-3341), -EFAULT with nothing recorded; `sigprocmask(how, &new_set,
NULL)` (:3344), whose `switch (how)` (kernel/signal.c:3253-3264, Linux
v6.18.46) answers
-EINVAL on `default` (:3263-3264) AFTER the copy, so that -EINVAL carries
the eight-byte ledger; the install (`__set_current_blocked`, :3267) and
its delivery of a pending SIGABRT the new mask unblocks
(`Signal.sigmask_deliver_model`); then `if (oset)` `copy_to_user`
(:3349-3351), with the install already committed — the no-rollback -EFAULT.

The arms that answer WITHOUT touching `oset` still use `check_ret_only`,
which demands all five effect lists be empty — so an effect claiming a
write on the bad-size -EINVAL, or on the `nset` -EFAULT, is rejected
rather than accepted as an inert errno.  That is what separates the two
-EFAULTs this syscall can return: the one raised by `copy_from_user`
writes nothing and RECORDS nothing, and the one raised by `copy_to_user`
writes nothing and records the eight bytes it had already read.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigprocmask`. -/
def check_rt_sigprocmask (i : SyscallInput) (how nset oset ss : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(bv_eqb ss (Z_to_bv 64 NSIG_BYTES)) then check_ret_only eff (errno_ret EINVAL) m []
  else
    let old := m_sigmask m
    if w_is0 nset then
      (if w_is0 oset then check_ret_only eff (Z_to_bv 64 0) m []
       else check_write_oset i oset old eff m)
    else
      match sigset_at i.in_mem nset with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some raw =>
          if !(how_valid how) then
            check_ret_only_copyins [(nset, NSIG_BYTES.toNat)] eff (errno_ret EINVAL) m []
          else
            let m' := sigmask_deliver_model (sigmask_apply how old (sigmask_strip raw)) m
            if w_is0 oset then
              check_ret_only_copyins [(nset, NSIG_BYTES.toNat)] eff (Z_to_bv 64 0) m' []
            else check_write_oset_copyins [(nset, NSIG_BYTES.toNat)] i oset old eff m'

/-- The two shapes `write_oset` can produce, accepted.  They are what the
completeness proof's leaves reduce to, and naming them keeps that proof
readable.  Rocq: `Checks.Sys.Kernel.Signal.check_write_oset_efault`. -/
theorem check_write_oset_efault (i : SyscallInput) (oset old : word) (m : Model)
    (ha : (!(access_okb oset NSIG_BYTES)) = true) :
    check_write_oset i oset old (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  unfold check_write_oset
  rw [ha]
  simp only [↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Kernel.Signal.check_write_oset_stored`. -/
theorem check_write_oset_stored (i : SyscallInput) (oset old : word) (m : Model) (bs : List byte)
    (ha : (!(access_okb oset NSIG_BYTES)) = false)
    (hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) = some bs) :
    check_write_oset i oset old
      (mkEffect (Z_to_bv 64 0) [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))] []) m
    = CheckOk m [] := by
  unfold check_write_oset
  rw [ha, hw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (check_one_write_ok_iff _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- `check_write_oset_copyins` discharged from its two parts: the arm's own
verdict and the ledger.  The same shape `check_ret_only_copyins` has, and
it exists so the completeness proof never has to reduce through
`clear_copyins` by hand.  Rocq:
`Checks.Sys.Kernel.Signal.check_write_oset_copyins_ok`. -/
theorem check_write_oset_copyins_ok (reads : List (word × Nat)) (i : SyscallInput)
    (oset old : word) (eff : SyscallEffect) (m : Model)
    (h : check_write_oset i oset old (clear_copyins eff) m = CheckOk m [])
    (hc : eff.eff_copyins = reads) :
    check_write_oset_copyins reads i oset old eff m = CheckOk m [] := by
  unfold check_write_oset_copyins
  rw [h, hc, access_ranges_eqb_refl]
  simp only [↓reduceIte]

/-- Every `CheckOk` the checker returns is a run the spec admits.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigprocmask_sound_ok`. -/
theorem check_rt_sigprocmask_sound_ok (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs) :
    rt_sigprocmask_spec how nset oset ss i m (Ok eff m' evs) := by
  unfold check_rt_sigprocmask at h
  unfold rt_sigprocmask_spec
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h ⊢
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, -, hspec⟩ := (check_write_oset_ok_iff _ _ _ _ _ _ _).mp h
      exact hspec
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some raw =>
  simp only [hr] at h ⊢
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    refine record_copyins_ok_empty _ _ i m _ _ _ rfl ?_
    unfold set_sigmask_deliver
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, hled, hspec⟩ := (check_write_oset_copyins_ok_iff _ _ _ _ _ _ _ _).mp h
    refine record_copyins_clear_ok _ _ i m eff _ _ hled ?_
    unfold set_sigmask_deliver
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact hspec

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `Checks.Sys.Kernel.Signal.check_rt_sigprocmask_sound_unmodeled`. -/
theorem check_rt_sigprocmask_sound_unmodeled (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_rt_sigprocmask i how nset oset ss eff m = CheckUnmodeled) :
    rt_sigprocmask_spec how nset oset ss i m Unmodeled := by
  unfold check_rt_sigprocmask at h
  unfold rt_sigprocmask_spec
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h ⊢
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_write_oset_no_ok_unmodeled _ _ _ _ _ h m
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some raw =>
  simp only [hr] at h ⊢
  apply record_copyins_unmodeled
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h
    exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold set_sigmask_deliver
    refine bind_unmodeled2 _ _ i m () _ [] (modify_ok _ i m) ?_
    exact check_write_oset_copyins_no_ok_unmodeled _ _ _ _ _ _ h _

/-- Every run the spec admits is one the checker accepts.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigprocmask_complete_ok`. -/
theorem check_rt_sigprocmask_complete_ok (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : rt_sigprocmask_spec how nset oset ss i m (Ok eff m' evs)) :
    check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs := by
  unfold rt_sigprocmask_spec at h
  unfold check_rt_sigprocmask
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h ⊢
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold write_oset at h
      cases ha : access_okb oset NSIG_BYTES with
      | false =>
        simp only [ha, Bool.not_false, ↓reduceIte] at h
        have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
        cases h'
        exact check_write_oset_efault i oset _ m (by rw [ha]; rfl)
      | true =>
        simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have h := input_bind_ok_inv _ i m _ _ _ h
        cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
        | some bs =>
          simp only [hw] at h
          have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0)
              [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned (m_sigmask m)))] []) m [] := h
          cases h'
          exact check_write_oset_stored i oset _ m bs (by rw [ha]; rfl) hw
        | none =>
          simp only [hw] at h
          have h' : Ok eff m' evs = Unmodeled := h
          cases h'
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_ok_inv _ i m _ _ _ h
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some raw =>
  simp only [hr] at h ⊢
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ _ _ h
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at hcore ⊢
    have h' : Ok core m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hcore
    cases h'
    exact check_ret_only_copyins_refl _ _ _ _
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
  unfold set_sigmask_deliver at hcore
  rw [bind_modify_iff] at hcore
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at hcore ⊢
    have h' : Ok core m' evs = Ok (mkEffect (Z_to_bv 64 0) [] [])
        (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := hcore
    cases h'
    exact check_ret_only_copyins_refl _ _ _ _
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
    unfold write_oset at hcore
    cases ha : access_okb oset NSIG_BYTES with
    | false =>
      simp only [ha, Bool.not_false, ↓reduceIte] at hcore
      have h' : Ok core m' evs = Ok (mkEffect (errno_ret EFAULT) [] [])
          (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := hcore
      cases h'
      exact check_write_oset_copyins_ok _ i oset _ _ _
        (check_write_oset_efault i oset _ _ (by rw [ha]; rfl)) rfl
    | true =>
      simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcore
      have hcore := input_bind_ok_inv _ i _ _ _ _ hcore
      cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
      | some bs =>
        simp only [hw] at hcore
        have h' : Ok core m' evs = Ok (mkEffect (Z_to_bv 64 0)
            [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned (m_sigmask m)))] [])
            (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) []
          := hcore
        cases h'
        exact check_write_oset_copyins_ok _ i oset _ _ _
          (check_write_oset_stored i oset _ _ bs (by rw [ha]; rfl) hw) rfl
      | none =>
        simp only [hw] at hcore
        have h' : Ok core m' evs = Unmodeled := hcore
        cases h'

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigprocmask_complete_unmodeled`. -/
theorem check_rt_sigprocmask_complete_unmodeled (i : SyscallInput) (how nset oset ss : word)
    (m : Model) (eff : SyscallEffect)
    (h : rt_sigprocmask_spec how nset oset ss i m Unmodeled) :
    check_rt_sigprocmask i how nset oset ss eff m = CheckUnmodeled := by
  unfold rt_sigprocmask_spec at h
  unfold check_rt_sigprocmask
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h ⊢
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      cases h'
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold write_oset at h
      unfold check_write_oset
      cases ha : access_okb oset NSIG_BYTES with
      | false =>
        simp only [ha, Bool.not_false, ↓reduceIte] at h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
        cases h'
      | true =>
        simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have h := input_bind_unmodeled_inv _ i m h
        cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
        | some bs =>
          simp only [hw] at h
          have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0)
              [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned (m_sigmask m)))] []) m [] := h
          cases h'
        | none => rfl
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_unmodeled_inv _ i m h
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
  | some raw =>
  simp only [hr] at h ⊢
  have h := record_copyins_unmodeled_inv _ _ i m h
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  unfold set_sigmask_deliver at h
  rw [bind_modify_iff] at h
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] [])
        (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := h
    cases h'
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold write_oset at h
    unfold check_write_oset_copyins check_write_oset
    cases ha : access_okb oset NSIG_BYTES with
    | false =>
      simp only [ha, Bool.not_false, ↓reduceIte] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EFAULT) [] [])
          (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := h
      cases h'
    | true =>
      simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := input_bind_unmodeled_inv _ i _ h
      cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
      | some bs =>
        simp only [hw] at h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0)
            [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned (m_sigmask m)))] [])
            (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := h
        cases h'
      | none => rfl

/-- `Kernel.Signal.mask_launchable` carried across a whole run, which is
what makes `Run.valid_sigmask` a property of every reachable state and not
only of the entry one.  Its two halves are proved where the arithmetic
lives (`Signal.sigmask_apply_launchable`, `Signal.sigmask_strip_launchable`);
this is the step that says the checker has no other way to move the
field.

It matters because `oset` copies the mask out verbatim: a reachable state
with SIGKILL or SIGSTOP set would put a trace in the model that Linux
cannot produce — `rt_sigprocmask` strips the two from the set itself
(kernel/signal.c:3342, Linux v6.18.46) before `sigprocmask` (:3244-3269)
installs it at :3267 through `__set_current_blocked` (:3220-3234), which
strips nothing; the in-kernel writer that does strip,
`set_current_blocked` (:3214-3218), is not on this arm's path — which is
the second of the three priorities rather than the first.  Rocq:
`Checks.Sys.Kernel.Signal.check_rt_sigprocmask_keeps_mask_launchable`. -/
theorem check_rt_sigprocmask_keeps_mask_launchable (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hm : mask_launchable (m_sigmask m))
    (h : check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs) :
    mask_launchable (m_sigmask m') := by
  unfold check_rt_sigprocmask at h
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact hm
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h
      obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact hm
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, -, -, -⟩ := (check_write_oset_ok_iff _ _ _ _ _ _ _).mp h
      exact hm
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact hm
  | some raw =>
  simp only [hr] at h
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact hm
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  have hinst : mask_launchable (m_sigmask (sigmask_deliver_model
      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m)) := by
    rw [m_sigmask_sigmask_deliver_model]
    exact sigmask_apply_launchable how _ _ hm (sigmask_strip_launchable raw)
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact hinst
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, -, -, -⟩ := (check_write_oset_copyins_ok_iff _ _ _ _ _ _ _ _).mp h
    exact hinst

/-- The framing statement in the shape `Checks.VmMapsDisjoint`'s
`check_syscall_preserves_vm_wf` cascade consumes, so the arm can be
discharged there by naming this lemma and nothing else.  It is stated
HERE rather than with the alternation because the arm CHANGES the model,
so the cascade's generic tactic cannot close it, and the proof needs
`check_write_oset_ok_iff`, which lives here (the header says what this
replaced and why the VM half is still true by construction: the model
changes only inside `ProcState`, through `State.with_sigmask` and, on
the delivery branch, `State.with_killed` over it, and
`Kernel.Signal.m_vmmaps_sigmask_deliver_model` carries the ledger
across).  Rocq: `Checks.Sys.Kernel.Signal.check_rt_sigprocmask_frame`. -/
theorem check_rt_sigprocmask_frame (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_rt_sigprocmask at h
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h
      obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, -, -, -⟩ := (check_write_oset_ok_iff _ _ _ _ _ _ _).mp h
      rfl
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | some raw =>
  simp only [hr] at h
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    rfl
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact m_vmmaps_sigmask_deliver_model _ m
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, -, -, -⟩ := (check_write_oset_copyins_ok_iff _ _ _ _ _ _ _ _).mp h
    exact m_vmmaps_sigmask_deliver_model _ m

/-! ## The witnesses

Each spec is deterministic — no `choose`, no `alt` — so its witness is the
spec's own arm structure read as a function; `ret_outcome r m` is the
"return `r`, change nothing" outcome `Checks/Witness/Prelude.lean`
names, and the `oset` copy-out is factored out the way the spec factors
it, so the two stay in step arm for arm.  Rocq keeps these in
`theories/LinuxProcessSem/Checks/Witness/Kernel/Signal.v`; the argument
order is Rocq's, arguments first and the input and model last. -/

/-- Rocq: `Checks.Witness.Kernel.Signal.rt_sigaction_witness`. -/
def rt_sigaction_witness (sig act oact ss : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 8)) then ret_outcome (errno_ret EINVAL) m
  else if !(w_is0 oact) then Unmodeled
  else if w_is0 act
  then (if sig_valid sig then ret_outcome (Z_to_bv 64 0) m
        else ret_outcome (errno_ret EINVAL) m)
  else
    match sigaction_flags i.in_mem act with
    | none => ret_outcome (errno_ret EFAULT) m
    | some fl =>
        if !(sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if sig_kernel_only sig then ret_outcome (errno_ret EINVAL) m
        else if !(sa_flags_ok fl) then Unmodeled
        else if sigaction_accepted sig then ret_outcome (Z_to_bv 64 0) m
        else Unmodeled

/-- The witness is a run of the spec: rt_sigaction is receptive on every
input and model.  Rocq: `Checks.Witness.Kernel.Signal.rt_sigaction_witness_ok`. -/
theorem rt_sigaction_witness_ok (sig act oact ss : word) (i : SyscallInput) (m : Model) :
    rt_sigaction_spec sig act oact ss i m (rt_sigaction_witness sig act oact ss i m) := by
  unfold rt_sigaction_spec rt_sigaction_witness ret_outcome
  cases hss : bv_eqb ss (Z_to_bv 64 8) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hoact : w_is0 oact with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hact : w_is0 act with
  | true =>
    simp only [↓reduceIte]
    cases hv : sig_valid sig with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m i m _ (input_ok i m) ?_
  cases hfl : sigaction_flags i.in_mem act with
  | none =>
    dsimp only
    exact pure_ok _ i m
  | some fl =>
  dsimp only
  cases hv : sig_valid sig with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hk : sig_kernel_only sig with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hfo : sa_flags_ok fl with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases ha : sigaction_accepted sig with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Kernel.Signal.write_oset_witness`. -/
def write_oset_witness (oset old : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if !(access_okb oset NSIG_BYTES) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
    | none => Unmodeled
    | some _ =>
        Ok (mkEffect (Z_to_bv 64 0) [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))] [])
          m []

/-- Rocq: `Checks.Witness.Kernel.Signal.write_oset_witness_ok`. -/
theorem write_oset_witness_ok (oset old : word) (i : SyscallInput) (m : Model) :
    write_oset oset old i m (write_oset_witness oset old i m) := by
  unfold write_oset write_oset_witness ret_outcome
  cases ha : access_okb oset NSIG_BYTES with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m i m _ (input_ok i m) ?_
  cases hw : read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
  | some bs =>
    dsimp only
    exact pure_ok _ i m
  | none =>
    dsimp only
    exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Kernel.Signal.rt_sigprocmask_witness`. -/
def rt_sigprocmask_witness (how nset oset ss : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 NSIG_BYTES)) then ret_outcome (errno_ret EINVAL) m
  else
    let old := m_sigmask m
    if w_is0 nset then
      (if w_is0 oset then ret_outcome (Z_to_bv 64 0) m else write_oset_witness oset old i m)
    else
      match sigset_at i.in_mem nset with
      | none => ret_outcome (errno_ret EFAULT) m
      | some raw =>
          outcome_copyins [(nset, NSIG_BYTES.toNat)]
            (if !(how_valid how) then ret_outcome (errno_ret EINVAL) m
             else
               let m' := sigmask_deliver_model (sigmask_apply how old (sigmask_strip raw)) m
               if w_is0 oset then ret_outcome (Z_to_bv 64 0) m'
               else write_oset_witness oset old i m')

/-- The witness is a run of the spec: rt_sigprocmask is receptive on every
input and model.  Rocq: `Checks.Witness.Kernel.Signal.rt_sigprocmask_witness_ok`. -/
theorem rt_sigprocmask_witness_ok (how nset oset ss : word) (i : SyscallInput) (m : Model) :
    rt_sigprocmask_spec how nset oset ss i m (rt_sigprocmask_witness how nset oset ss i m) := by
  unfold rt_sigprocmask_spec rt_sigprocmask_witness
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hn : w_is0 nset with
  | true =>
    simp only [↓reduceIte]
    cases ho : w_is0 oset with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact write_oset_witness_ok oset _ i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m i m _ (input_ok i m) ?_
  cases hr : sigset_at i.in_mem nset with
  | none =>
    dsimp only
    exact pure_ok _ i m
  | some raw =>
  dsimp only
  apply record_copyins_outcome
  cases hh : how_valid how with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold set_sigmask_deliver
  refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
  cases ho : w_is0 oset with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact write_oset_witness_ok oset _ i _


/-! ## sigaltstack (132) — the second half of this file begins here

Appended by C-Kernel-Signal-altstack-kill after the mask/action half above
had merged; nothing below is used above and nothing above is restated
below.  The kernel path, Linux v6.18.46, commit 1f99e9ab748f:
`SYSCALL_DEFINE2(sigaltstack)` (kernel/signal.c:4455-4467) copies the new
record in — `copy_from_user`, -EFAULT (:4459-4460) — and calls
`do_sigaltstack` (:4397-4453) with `MINSIGSTKSZ` (:4461-4463), whose order
the arms keep: the mode test on `ss_flags & ~SS_FLAG_BITS`, -EINVAL
(:4421-4424), the `SS_DISABLE` shortcut that zeroes `ss_size` and `ss_sp`
(:4436-4438), `ss_size < min_ss_size`, -ENOMEM (:4440-4441), and the store
under `if (!ret)` (:4445-4448).  Every decline below is the spec's, in the
spec's place; the argument for each is on `Sys/Kernel/Signal.lean`'s
`sigaltstack_spec`. -/

/-- No arm touches user memory, so every admissible outcome is a bare
return; exactly one of them carries the model forward with the
alternate-stack bit set, the install.  SS_DISABLE succeeds and does NOT set
it: the kernel zeroes `ss_size` before the store (`do_sigaltstack`,
kernel/signal.c:4436-4438, Linux v6.18.46, commit 1f99e9ab748f), so the
record stays in the shape the arms below can answer from.  The declining
arms are the ones whose answer would need the user stack pointer, or the
stored flags word (see `Sys.Kernel.Signal.sigaltstack_spec`).  Rocq:
`Checks.Sys.Kernel.Signal.check_sigaltstack`. -/
def check_sigaltstack (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if m_sigaltstack_installed m then CheckUnmodeled
  else if !(w_is0 uoss) then CheckUnmodeled
  else if w_is0 uss then check_ret_only eff (Z_to_bv 64 0) m []
  else
    match sigaltstack_at i.in_mem uss with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some bs =>
        if !(ss_mode_ok (ss_flags_of bs)) then check_ret_only eff (errno_ret EINVAL) m []
        else if ss_disabling (ss_flags_of bs) then check_ret_only eff (Z_to_bv 64 0) m []
        else if w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs) then CheckUnmodeled
        else if bv_unsigned (ss_size_of bs) < MINSIGSTKSZ
        then check_ret_only eff (errno_ret ENOMEM) m []
        else check_ret_only eff (Z_to_bv 64 0) (with_sigaltstack_installed m) []

/-- What the checker accepts, the spec admits.  The one Prop gate, the
`MINSIGSTKSZ` comparison, is split with `cases` on its `decide` where the
Bool gates are split with `cases` on the Bool, and both sides — `h` and
the goal — are reduced before anything is unified against the goal;
the install arm ends in `modify_ok`, the spec's
`set_sigaltstack_installed` read as one step.  Rocq:
`Checks.Sys.Kernel.Signal.check_sigaltstack_sound_ok`. -/
theorem check_sigaltstack_sound_ok (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_sigaltstack i uss uoss eff m = CheckOk m' evs) :
    sigaltstack_spec uss uoss i m (Ok eff m' evs) := by
  unfold check_sigaltstack at h
  unfold sigaltstack_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hw : m_sigaltstack_installed m with
  | true =>
    simp only [hw, ↓reduceIte] at h
    cases h
  | false =>
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 uoss with
  | false =>
    simp only [ho, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hu : w_is0 uss with
  | true =>
    simp only [hu, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | false =>
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
  cases hbs : sigaltstack_at i.in_mem uss with
  | none =>
    simp only [hbs] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some bs =>
  simp only [hbs] at h ⊢
  cases hmode : ss_mode_ok (ss_flags_of bs) with
  | false =>
    simp only [hmode, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hmode, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hdis : ss_disabling (ss_flags_of bs) with
  | true =>
    simp only [hdis, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | false =>
  simp only [hdis, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hz : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) with
  | true =>
    simp only [hz, ↓reduceIte] at h
    cases h
  | false =>
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hsz : decide (bv_unsigned (ss_size_of bs) < MINSIGSTKSZ) with
  | true =>
    simp only [of_decide_eq_true hsz, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | false =>
    simp only [of_decide_eq_false hsz, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    unfold set_sigaltstack_installed
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _

/-- What the checker declines, the spec declines: the three `CheckUnmodeled`
arms are the spec's three `unmodeled`, and no answering arm can produce one
(`check_ret_only_no_unmodeled`).  Rocq:
`Checks.Sys.Kernel.Signal.check_sigaltstack_sound_unmodeled`. -/
theorem check_sigaltstack_sound_unmodeled (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_sigaltstack i uss uoss eff m = CheckUnmodeled) :
    sigaltstack_spec uss uoss i m Unmodeled := by
  unfold check_sigaltstack at h
  unfold sigaltstack_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hw : m_sigaltstack_installed m with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 uoss with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hu : w_is0 uss with
  | true =>
    simp only [hu, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
  cases hbs : sigaltstack_at i.in_mem uss with
  | none =>
    simp only [hbs] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some bs =>
  simp only [hbs] at h ⊢
  cases hmode : ss_mode_ok (ss_flags_of bs) with
  | false =>
    simp only [hmode, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hmode, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hdis : ss_disabling (ss_flags_of bs) with
  | true =>
    simp only [hdis, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hdis, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hz : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
  cases hsz : decide (bv_unsigned (ss_size_of bs) < MINSIGSTKSZ) with
  | true =>
    simp only [of_decide_eq_true hsz, ↓reduceIte] at h ⊢
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
    simp only [of_decide_eq_false hsz, ↓reduceIte] at h ⊢
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- What the spec admits, the checker accepts, with the same model and no
events.  Rocq: `Checks.Sys.Kernel.Signal.check_sigaltstack_complete_ok`. -/
theorem check_sigaltstack_complete_ok (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : sigaltstack_spec uss uoss i m (Ok eff m' evs)) :
    check_sigaltstack i uss uoss eff m = CheckOk m' evs := by
  unfold sigaltstack_spec at h
  unfold check_sigaltstack
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  cases hw : m_sigaltstack_installed m with
  | true =>
    simp only [hw, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | false =>
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 uoss with
  | false =>
    simp only [ho, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hu : w_is0 uss with
  | true =>
    simp only [hu, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_ok_inv _ i m _ _ _ h
  cases hbs : sigaltstack_at i.in_mem uss with
  | none =>
    simp only [hbs] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some bs =>
  simp only [hbs] at h ⊢
  cases hmode : ss_mode_ok (ss_flags_of bs) with
  | false =>
    simp only [hmode, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hmode, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hdis : ss_disabling (ss_flags_of bs) with
  | true =>
    simp only [hdis, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hdis, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hz : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) with
  | true =>
    simp only [hz, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | false =>
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hsz : decide (bv_unsigned (ss_size_of bs) < MINSIGSTKSZ) with
  | true =>
    simp only [of_decide_eq_true hsz, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
    simp only [of_decide_eq_false hsz, ↓reduceIte] at h ⊢
    rw [bind_set_sigaltstack_installed_iff] at h
    have h' : Ok eff m' evs
        = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_sigaltstack_installed m) [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- What the spec declines, the checker declines, whatever effect it is
shown.  Rocq: `Checks.Sys.Kernel.Signal.check_sigaltstack_complete_unmodeled`. -/
theorem check_sigaltstack_complete_unmodeled (i : SyscallInput) (uss uoss : word) (m : Model)
    (eff : SyscallEffect) (h : sigaltstack_spec uss uoss i m Unmodeled) :
    check_sigaltstack i uss uoss eff m = CheckUnmodeled := by
  unfold sigaltstack_spec at h
  unfold check_sigaltstack
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hw : m_sigaltstack_installed m with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ho : w_is0 uoss with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hu : w_is0 uss with
  | true =>
    simp only [hu, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
  | false =>
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h := input_bind_unmodeled_inv _ i m h
  cases hbs : sigaltstack_at i.in_mem uss with
  | none =>
    simp only [hbs] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := h
    cases h'
  | some bs =>
  simp only [hbs] at h ⊢
  cases hmode : ss_mode_ok (ss_flags_of bs) with
  | false =>
    simp only [hmode, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hmode, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hdis : ss_disabling (ss_flags_of bs) with
  | true =>
    simp only [hdis, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
  | false =>
  simp only [hdis, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hz : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
  cases hsz : decide (bv_unsigned (ss_size_of bs) < MINSIGSTKSZ) with
  | true =>
    simp only [of_decide_eq_true hsz, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := h
    cases h'
  | false =>
    simp only [of_decide_eq_false hsz, ↓reduceIte] at h
    rw [bind_set_sigaltstack_installed_iff] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_sigaltstack_installed m) [] := h
    cases h'

/-! ## tkill (130) and tgkill (131)

The acceptors mirror the specs' branches — read `Sys/Kernel/Signal.lean`'s
`tkill_self`, `tkill_spec` and `tgkill_spec` for the kernel order, Linux
v6.18.46, commit 1f99e9ab748f: `SYSCALL_DEFINE2(tkill)`
(kernel/signal.c:4192-4199) and `SYSCALL_DEFINE3(tgkill)` (:4176-4183)
ahead of `do_send_specific` (:4127-4155).  Two things are worth naming
rather than reading off the code.

THE EFFECT SHAPE IS EMPTY on every branch: neither call writes user
memory, zeroes or unmaps anything, or copies anything in.  A claimed write
is therefore a reject rather than a decline, which is what makes a mutated
probe that forges one fail.

THE FATAL BRANCH STILL CLAIMS 0.  The syscall's own return value is what a
kernel would have put in a0 had the process lived; the process does not,
and `Run.sstep_killed` discards the effect.  Requiring the 0 here rather
than admitting anything keeps the acceptor total on the shape and costs
nothing: no trace can distinguish the two. -/

/-- The delivery acceptor: a bare return of 0, and the model the delivery
leaves — the pending bit when the mask covers SIGABRT (`wants_signal`
returns false for a blocked signal, kernel/signal.c:946-949, Linux
v6.18.46, commit 1f99e9ab748f, so `__send_signal_locked`'s `sigaddset`
at :1137 is all that happens), the kill when it does not (`get_signal`
finds SIG_DFL at :2942 and takes the coredump branch at :3016-3043).  Rocq:
`Checks.Sys.Kernel.Signal.check_send_sigabrt`. -/
def check_send_sigabrt (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if !(bv_eqb ret (Z_to_bv 64 0)) then CheckReject
      else if sigabrt_blocked (m_sigmask m) then CheckOk (with_sigabrt_pending m) []
      else CheckOk (with_killed (Z_to_bv 64 SIGABRT) m) []
  | _ => CheckReject

/-- The destruct of the effect the delivery acceptor needs, as an iff:
it accepts exactly a bare return of 0, with no events and the delivery's
own model.  Rocq destructs `eff` in place in two of the four lemmas below
(`sound_ok` and `no_unmodeled`); Lean factors it into this lemma, the way
`Checks/Sys/Prelude.lean`'s `check_ret_only_ok_iff` does for the bare
return, and `sound_ok`, `complete_ok` and `check_send_sigabrt_frame` read
it (the tkill and tgkill frames through the latter).  `no_unmodeled`
still destructs in place: the `CheckOk` side of the iff does not by
itself give `≠ CheckUnmodeled`; `complete_unmodeled` refutes its
spec-side hypothesis and opens neither.  Lean-only; no Rocq twin. -/
theorem check_send_sigabrt_ok_iff (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_send_sigabrt eff m = CheckOk m' evs ↔
    (eff = mkEffect (Z_to_bv 64 0) [] [] ∧ evs = [] ∧
     m' = (if sigabrt_blocked (m_sigmask m) then with_sigabrt_pending m
           else with_killed (Z_to_bv 64 SIGABRT) m)) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws =>
    simp only [check_send_sigabrt, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq,
      false_and, and_false]
  | nil =>
  cases zs with
  | cons z zs =>
    simp only [check_send_sigabrt, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq,
      false_and, and_false]
  | nil =>
  cases us with
  | cons u us =>
    simp only [check_send_sigabrt, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq,
      false_and, and_false]
  | nil =>
  cases cs with
  | cons c cs =>
    simp only [check_send_sigabrt, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq,
      false_and, and_false]
  | nil =>
  cases copyins with
  | cons c copyins =>
    simp only [check_send_sigabrt, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq,
      false_and, and_false]
  | nil =>
  simp only [check_send_sigabrt, mkEffect, SyscallEffect.mkEffectU.injEq, and_true]
  cases hE : bv_eqb ret (Z_to_bv 64 0) with
  | true =>
    rw [bv_eqb_eq] at hE
    subst hE
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases hb : sigabrt_blocked (m_sigmask m) with
    | true =>
      simp only [↓reduceIte, check_result.CheckOk.injEq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, check_result.CheckOk.injEq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩⟩
  | false =>
    simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    intro hret
    subst hret
    rw [bv_eqb_refl] at hE
    exact absurd hE (by simp only [reduceCtorEq, not_false_eq_true])

/-- Rocq: `Checks.Sys.Kernel.Signal.check_send_sigabrt_sound_ok`. -/
theorem check_send_sigabrt_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_send_sigabrt eff m = CheckOk m' evs) :
    send_sigabrt i m (Ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_send_sigabrt_ok_iff _ _ _ _).mp h
  unfold send_sigabrt
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hb : sigabrt_blocked (m_sigmask m) with
  | true =>
    simp only [↓reduceIte]
    unfold set_sigabrt_pending
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold set_killed
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _

/-- The delivery never declines: every effect is accepted or rejected.
Rocq: `Checks.Sys.Kernel.Signal.check_send_sigabrt_no_unmodeled`. -/
theorem check_send_sigabrt_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_send_sigabrt eff m ≠ CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_send_sigabrt, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases zs with
  | cons z zs => simp only [check_send_sigabrt, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases us with
  | cons u us => simp only [check_send_sigabrt, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases cs with
  | cons c cs => simp only [check_send_sigabrt, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_send_sigabrt, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  simp only [check_send_sigabrt]
  cases (!bv_eqb ret (Z_to_bv 64 0)) with
  | true => simp only [↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases sigabrt_blocked (m_sigmask m) with
    | true => simp only [↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
    | false => simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Rocq: `Checks.Sys.Kernel.Signal.check_send_sigabrt_complete_ok`. -/
theorem check_send_sigabrt_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : send_sigabrt i m (Ok eff m' evs)) :
    check_send_sigabrt eff m = CheckOk m' evs := by
  unfold send_sigabrt at h
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  refine (check_send_sigabrt_ok_iff _ _ _ _).mpr ?_
  cases hb : sigabrt_blocked (m_sigmask m) with
  | true =>
    simp only [hb, ↓reduceIte] at h ⊢
    rw [bind_set_sigabrt_pending_iff] at h
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_sigabrt_pending m) [] := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_killed_iff] at h
    have h' : Ok eff m' evs
        = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_killed (Z_to_bv 64 SIGABRT) m) [] := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩

/-- Vacuous, as in Rocq: the delivery admits no `Unmodeled`.  Rocq:
`Checks.Sys.Kernel.Signal.check_send_sigabrt_complete_unmodeled`. -/
theorem check_send_sigabrt_complete_unmodeled (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (h : send_sigabrt i m Unmodeled) : check_send_sigabrt eff m = CheckUnmodeled := by
  unfold send_sigabrt at h
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hb : sigabrt_blocked (m_sigmask m) with
  | true =>
    simp only [hb, ↓reduceIte] at h
    rw [bind_set_sigabrt_pending_iff] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_sigabrt_pending m) [] := h
    cases h'
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_set_killed_iff] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_killed (Z_to_bv 64 SIGABRT) m) [] := h
    cases h'

/-- Everything `tkill` and `tgkill` share once the caller has named a
positive `pid`, with the declaration tested here too, as the spec tests
it (`Sys.Kernel.Signal.tkill_self`).  Rocq:
`Checks.Sys.Kernel.Signal.check_tkill_self`. -/
def check_tkill_self (pid sig : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(m_abort_terminal m) then CheckUnmodeled
  else
    match m_tid m with
    | none => CheckUnmodeled
    | some t =>
        if !(bv_eqb pid t) then CheckUnmodeled
        else if !(tkill_sig_valid sig) then check_ret_only eff (errno_ret EINVAL) m []
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then check_send_sigabrt eff m
        else CheckUnmodeled

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_self_sound_ok`. -/
theorem check_tkill_self_sound_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_tkill_self pid sig eff m = CheckOk m' evs) :
    tkill_self pid sig i m (Ok eff m' evs) := by
  unfold check_tkill_self at h
  unfold tkill_self
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    cases h
  | some t =>
  simp only [ht] at h ⊢
  cases hp : bv_eqb pid t with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [hs, ↓reduceIte] at h ⊢
    exact check_send_sigabrt_sound_ok _ _ _ _ i h
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_self_sound_unmodeled`. -/
theorem check_tkill_self_sound_unmodeled (pid sig : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_tkill_self pid sig eff m = CheckUnmodeled) :
    tkill_self pid sig i m Unmodeled := by
  unfold check_tkill_self at h
  unfold tkill_self
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some t =>
  simp only [ht] at h ⊢
  cases hp : bv_eqb pid t with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [hs, ↓reduceIte] at h
    exact absurd h (check_send_sigabrt_no_unmodeled _ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_self_complete_ok`. -/
theorem check_tkill_self_complete_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : tkill_self pid sig i m (Ok eff m' evs)) :
    check_tkill_self pid sig eff m = CheckOk m' evs := by
  unfold tkill_self at h
  unfold check_tkill_self
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | some t =>
  simp only [ht] at h ⊢
  cases hp : bv_eqb pid t with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [hs, ↓reduceIte] at h ⊢
    exact check_send_sigabrt_complete_ok _ _ _ _ i h
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_self_complete_unmodeled`. -/
theorem check_tkill_self_complete_unmodeled (pid sig : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : tkill_self pid sig i m Unmodeled) :
    check_tkill_self pid sig eff m = CheckUnmodeled := by
  unfold tkill_self at h
  unfold check_tkill_self
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hoff : m_abort_terminal m with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none => dsimp only
  | some t =>
  simp only [ht] at h ⊢
  cases hp : bv_eqb pid t with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [hs, ↓reduceIte] at h
    exact check_send_sigabrt_complete_unmodeled m i eff h
  | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- `tkill pid sig`: the declaration, then `SYSCALL_DEFINE2(tkill)`'s
`pid <= 0` (kernel/signal.c:4195-4196, Linux v6.18.46, commit
1f99e9ab748f), then the shared tail.  Rocq:
`Checks.Sys.Kernel.Signal.check_tkill`. -/
def check_tkill (pid sig : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(m_abort_terminal m) then CheckUnmodeled
  else if !(pid_positive pid) then check_ret_only eff (errno_ret EINVAL) m []
  else check_tkill_self pid sig eff m

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_sound_ok`. -/
theorem check_tkill_sound_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_tkill pid sig eff m = CheckOk m' evs) :
    tkill_spec pid sig i m (Ok eff m' evs) := by
  unfold check_tkill at h
  unfold tkill_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : pid_positive pid with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_sound_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_sound_unmodeled`. -/
theorem check_tkill_sound_unmodeled (pid sig : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_tkill pid sig eff m = CheckUnmodeled) :
    tkill_spec pid sig i m Unmodeled := by
  unfold check_tkill at h
  unfold tkill_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : pid_positive pid with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_sound_unmodeled _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_complete_ok`. -/
theorem check_tkill_complete_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : tkill_spec pid sig i m (Ok eff m' evs)) :
    check_tkill pid sig eff m = CheckOk m' evs := by
  unfold tkill_spec at h
  unfold check_tkill
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : pid_positive pid with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_complete_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tkill_complete_unmodeled`. -/
theorem check_tkill_complete_unmodeled (pid sig : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : tkill_spec pid sig i m Unmodeled) :
    check_tkill pid sig eff m = CheckUnmodeled := by
  unfold tkill_spec at h
  unfold check_tkill
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hoff : m_abort_terminal m with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : pid_positive pid with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_complete_unmodeled _ _ m i eff h

/-- `tgkill tgid pid sig`: the declaration, `SYSCALL_DEFINE3(tgkill)`'s
`pid <= 0 || tgid <= 0` (kernel/signal.c:4179-4180, Linux v6.18.46,
commit 1f99e9ab748f), then the one test `tgkill` adds over `tkill`, the
seeded -ESRCH of `do_send_specific` when `task_tgid_vnr(p) == tgid` fails
(:4131, :4135), decidable here for the caller's own tid alone.  Rocq:
`Checks.Sys.Kernel.Signal.check_tgkill`. -/
def check_tgkill (tgid pid sig : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(m_abort_terminal m) then CheckUnmodeled
  else if !(pid_positive pid && pid_positive tgid) then check_ret_only eff (errno_ret EINVAL) m []
  else
    match m_tid m with
    | none => CheckUnmodeled
    | some t =>
        if !(bv_eqb pid t) then CheckUnmodeled
        else if !(bv_eqb tgid t) then check_ret_only eff (errno_ret ESRCH) m []
        else check_tkill_self pid sig eff m

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tgkill_sound_ok`. -/
theorem check_tgkill_sound_ok (tgid pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_tgkill tgid pid sig eff m = CheckOk m' evs) :
    tgkill_spec tgid pid sig i m (Ok eff m' evs) := by
  unfold check_tgkill at h
  unfold tgkill_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    cases h
  | some t =>
  simp only [ht] at h ⊢
  cases hpt : bv_eqb pid t with
  | false =>
    simp only [hpt, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hpt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [hg, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_sound_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tgkill_sound_unmodeled`. -/
theorem check_tgkill_sound_unmodeled (tgid pid sig : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_tgkill tgid pid sig eff m = CheckUnmodeled) :
    tgkill_spec tgid pid sig i m Unmodeled := by
  unfold check_tgkill at h
  unfold tgkill_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some t =>
  simp only [ht] at h ⊢
  cases hpt : bv_eqb pid t with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hpt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [hg, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_sound_unmodeled _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tgkill_complete_ok`. -/
theorem check_tgkill_complete_ok (tgid pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : tgkill_spec tgid pid sig i m (Ok eff m' evs)) :
    check_tgkill tgid pid sig eff m = CheckOk m' evs := by
  unfold tgkill_spec at h
  unfold check_tgkill
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | some t =>
  simp only [ht] at h ⊢
  cases hpt : bv_eqb pid t with
  | false =>
    simp only [hpt, Bool.not_false, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  | true =>
  simp only [hpt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [hg, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret ESRCH) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_complete_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Signal.check_tgkill_complete_unmodeled`. -/
theorem check_tgkill_complete_unmodeled (tgid pid sig : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : tgkill_spec tgid pid sig i m Unmodeled) :
    check_tgkill tgid pid sig eff m = CheckUnmodeled := by
  unfold tgkill_spec at h
  unfold check_tgkill
  have h := get_model_bind_unmodeled_inv _ i m h
  cases hoff : m_abort_terminal m with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : m_tid m with
  | none => dsimp only
  | some t =>
  simp only [ht] at h ⊢
  cases hpt : bv_eqb pid t with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hpt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [hg, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret ESRCH) [] []) m [] := h
    cases h'
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_tkill_self_complete_unmodeled _ _ m i eff h

/-- The delivery changes `ProcState` alone: `State.with_sigabrt_pending`
and `State.with_killed` both leave the VM ledger where it was.  Lean-only
helper for the two frame lemmas below; Rocq unfolds the delivery in place. -/
theorem check_send_sigabrt_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_send_sigabrt eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  obtain ⟨-, -, rfl⟩ := (check_send_sigabrt_ok_iff _ _ _ _).mp h
  cases sigabrt_blocked (m_sigmask m) with
  | true =>
    simp only [↓reduceIte]
    exact m_vmmaps_with_sigabrt_pending m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact m_vmmaps_with_killed _ m

/-- Lean-only helper for the two frame lemmas below, the shared tail's
half of each; Rocq's `repeat match` walks through it in place. -/
theorem check_tkill_self_frame (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_tkill_self pid sig eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_tkill_self at h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    cases h
  | some t =>
  simp only [ht] at h
  cases hp : bv_eqb pid t with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [hv, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | true =>
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [hs, ↓reduceIte] at h
    exact check_send_sigabrt_frame _ _ _ _ h
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- The framing statement `Checks.VmMapsDisjoint`'s cascade consumes, in
the shape the rt_sigprocmask one above has, and HERE for the same reason:
the arm changes the model, on one branch each — the pending bit and the
kill — and neither touches the address space, since `State.with_killed`
and `State.with_sigabrt_pending` rebuild `ProcState` alone.  The
registration's alternative for 130 names this lemma and adds nothing.
Rocq: `Checks.Sys.Kernel.Signal.check_tkill_frame`. -/
theorem check_tkill_frame (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_tkill pid sig eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_tkill at h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hp : pid_positive pid with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact check_tkill_self_frame _ _ _ _ _ _ h

/-- The same for 131.  Rocq: `Checks.Sys.Kernel.Signal.check_tgkill_frame`. -/
theorem check_tgkill_frame (tgid pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_tgkill tgid pid sig eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_tgkill at h
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [hoff, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hoff, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ht : m_tid m with
  | none =>
    simp only [ht] at h
    cases h
  | some t =>
  simp only [ht] at h
  cases hpt : bv_eqb pid t with
  | false =>
    simp only [hpt, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [hpt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [hg, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact check_tkill_self_frame _ _ _ _ _ _ h

/-! ## The witnesses, continued: sigaltstack, the delivery, tkill and tgkill

The same reading as above: each spec is deterministic, so its witness is
the spec's arm structure as a function, `ret_outcome` on every answering
arm and `Unmodeled` on every declining one — including the declaration
gate at the head of the two kill arms, so with the declaration off every
shape is `Unmodeled` — the witness the dispatcher's progress theorem
wants for a number the model declines.  The delivery's witness takes the
model alone, as the spec's `send_sigabrt` reads nothing else.  Rocq keeps
these in `theories/LinuxProcessSem/Checks/Witness/Kernel/Signal.v`. -/

/-- Rocq: `Checks.Witness.Kernel.Signal.sigaltstack_witness`. -/
def sigaltstack_witness (uss uoss : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if m_sigaltstack_installed m then Unmodeled
  else if !(w_is0 uoss) then Unmodeled
  else if w_is0 uss then ret_outcome (Z_to_bv 64 0) m
  else
    match sigaltstack_at i.in_mem uss with
    | none => ret_outcome (errno_ret EFAULT) m
    | some bs =>
        if !(ss_mode_ok (ss_flags_of bs)) then ret_outcome (errno_ret EINVAL) m
        else if ss_disabling (ss_flags_of bs) then ret_outcome (Z_to_bv 64 0) m
        else if w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs) then Unmodeled
        else if bv_unsigned (ss_size_of bs) < MINSIGSTKSZ then ret_outcome (errno_ret ENOMEM) m
        else ret_outcome (Z_to_bv 64 0) (with_sigaltstack_installed m)

/-- The witness is a run of the spec: sigaltstack is receptive on every
input and model.  Rocq: `Checks.Witness.Kernel.Signal.sigaltstack_witness_ok`. -/
theorem sigaltstack_witness_ok (uss uoss : word) (i : SyscallInput) (m : Model) :
    sigaltstack_spec uss uoss i m (sigaltstack_witness uss uoss i m) := by
  unfold sigaltstack_spec sigaltstack_witness ret_outcome
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hw : m_sigaltstack_installed m with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases ho : w_is0 uoss with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hu : w_is0 uss with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m i m _ (input_ok i m) ?_
  cases hbs : sigaltstack_at i.in_mem uss with
  | none =>
    dsimp only
    exact pure_ok _ i m
  | some bs =>
  dsimp only
  cases hmode : ss_mode_ok (ss_flags_of bs) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hdis : ss_disabling (ss_flags_of bs) with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hz : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hsz : decide (bv_unsigned (ss_size_of bs) < MINSIGSTKSZ) with
  | true =>
    simp only [of_decide_eq_true hsz, ↓reduceIte]
    exact pure_ok _ i m
  | false =>
    simp only [of_decide_eq_false hsz, ↓reduceIte]
    unfold set_sigaltstack_installed
    refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Kernel.Signal.send_sigabrt_witness`. -/
def send_sigabrt_witness (m : Model) : outcome SyscallEffect :=
  if sigabrt_blocked (m_sigmask m) then ret_outcome (Z_to_bv 64 0) (with_sigabrt_pending m)
  else ret_outcome (Z_to_bv 64 0) (with_killed (Z_to_bv 64 SIGABRT) m)

/-- Rocq: `Checks.Witness.Kernel.Signal.send_sigabrt_witness_ok`. -/
theorem send_sigabrt_witness_ok (i : SyscallInput) (m : Model) :
    send_sigabrt i m (send_sigabrt_witness m) := by
  unfold send_sigabrt send_sigabrt_witness ret_outcome
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hb : sigabrt_blocked (m_sigmask m) with
  | true =>
    simp only [↓reduceIte]
    unfold set_sigabrt_pending
    refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold set_killed
    refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Kernel.Signal.tkill_self_witness`. -/
def tkill_self_witness (pid sig : word) (m : Model) : outcome SyscallEffect :=
  if !(m_abort_terminal m) then Unmodeled
  else
    match m_tid m with
    | none => Unmodeled
    | some t =>
        if !(bv_eqb pid t) then Unmodeled
        else if !(tkill_sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then send_sigabrt_witness m
        else Unmodeled

/-- Rocq: `Checks.Witness.Kernel.Signal.tkill_self_witness_ok`. -/
theorem tkill_self_witness_ok (pid sig : word) (i : SyscallInput) (m : Model) :
    tkill_self pid sig i m (tkill_self_witness pid sig m) := by
  unfold tkill_self tkill_self_witness ret_outcome
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases ht : m_tid m with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some t =>
  dsimp only
  cases hp : bv_eqb pid t with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hv : tkill_sig_valid sig with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hs : bv_eqb sig (Z_to_bv 64 SIGABRT) with
  | true =>
    simp only [↓reduceIte]
    exact send_sigabrt_witness_ok i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Kernel.Signal.tkill_witness`. -/
def tkill_witness (pid sig : word) (m : Model) : outcome SyscallEffect :=
  if !(m_abort_terminal m) then Unmodeled
  else if !(pid_positive pid) then ret_outcome (errno_ret EINVAL) m
  else tkill_self_witness pid sig m

/-- The witness is a run of the spec: tkill is receptive on every input and
model, the declaration off included.  Rocq:
`Checks.Witness.Kernel.Signal.tkill_witness_ok`. -/
theorem tkill_witness_ok (pid sig : word) (i : SyscallInput) (m : Model) :
    tkill_spec pid sig i m (tkill_witness pid sig m) := by
  unfold tkill_spec tkill_witness ret_outcome
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hp : pid_positive pid with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact tkill_self_witness_ok pid sig i m

/-- Rocq: `Checks.Witness.Kernel.Signal.tgkill_witness`. -/
def tgkill_witness (tgid pid sig : word) (m : Model) : outcome SyscallEffect :=
  if !(m_abort_terminal m) then Unmodeled
  else if !(pid_positive pid && pid_positive tgid) then ret_outcome (errno_ret EINVAL) m
  else
    match m_tid m with
    | none => Unmodeled
    | some t =>
        if !(bv_eqb pid t) then Unmodeled
        else if !(bv_eqb tgid t) then ret_outcome (errno_ret ESRCH) m
        else tkill_self_witness pid sig m

/-- Rocq: `Checks.Witness.Kernel.Signal.tgkill_witness_ok`. -/
theorem tgkill_witness_ok (tgid pid sig : word) (i : SyscallInput) (m : Model) :
    tgkill_spec tgid pid sig i m (tgkill_witness tgid pid sig m) := by
  unfold tgkill_spec tgkill_witness ret_outcome
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hoff : m_abort_terminal m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hp : (pid_positive pid && pid_positive tgid) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases ht : m_tid m with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some t =>
  dsimp only
  cases hpt : bv_eqb pid t with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hg : bv_eqb tgid t with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact tkill_self_witness_ok pid sig i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Signal
