import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.DPath — the getcwd (17) checker and witness

Mirrors two Rocq files, name for name and in their order:
`theories/LinuxProcessSem/Checks/Sys/Fs/DPath.v` — `check_getcwd` and
the four lemmas that tie it to `Sys.Fs.DPath.getcwd_spec` — and
`theories/LinuxProcessSem/Checks/Witness/Fs/DPath.v` — `getcwd_witness`
and `getcwd_witness_ok`.  One Lean file rather than two is the port's
shape for every checker, not a choice made here: the Lean tree's
`Checks/Witness/` holds the prelude alone, and each checker file carries
its witness because the dispatcher takes a `CheckedArm` record that reads
the checker and the witness from one place, so the two halves are written
where that arm reads them (`Checks/Sys/Fs/Timerfd.lean`'s header carries
the argument).  Every definition keeps its Rocq name.

THE BASELINE NAMED ABOVE is the squash that carries this history's Rocq
tree and the commit the spec twin `Sys/Fs/DPath.lean` names.  The port
plan's baseline, `f44244ad6b80`, stopped being an ancestor of this
history when that day's work was rebase-merged, and BRIEF.md section 3
asks for an ancestor; the two Rocq files mirrored here and the spec's are
byte-identical at both commits and at this head, so the header names the
one `git merge-base --is-ancestor` accepts and loses nothing by it.

Not part of the trusted specification: the checker is what the twin of
`theories/LinuxProcessSem/Checks/ExecutableSpecs.v` will run against a
trace, and the five lemmas here are what make its answer the
specification's — soundness and
completeness on both the accepting and the fail-closed side, and the
witness's admission.  Every proof goes through the spec's own
definition; the checker is not a second reading of the kernel, and the
kernel citations below say which statement of `SYSCALL_DEFINE2(getcwd)`
each SHAPE of the checker answers to, so that a reader can check the
shape against the source without going through `Sys/Fs/DPath.lean`
first.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq builds `arm_getcwd` and lists it
in `checked_table` (`Checks/Sys/Dispatch.v`), registers the `arm_unfold`
equations `ca_check_arm_getcwd`, `ca_witness_arm_getcwd` and
`sa_spec_arm_getcwd` and proves `ca_no_arm_getcwd` beside them, and
proves `check_getcwd_frame` in `Checks/VmMapsDisjoint.v` — `m_vmmaps m' =
m_vmmaps m` on every `CheckOk`, which is immediate here because the
checker hands back the model it was given.  In the Lean port those are
the registration step of the conformance ticket for this arm, not this
file's (BRIEF.md section 5, the CHECK and VERIFY blocks): the checker
lands on the preludes and the spec alone, and the checked table's row,
the `arm_unfold` lemmas, the frame lemma and the ledger's per-arm
alternative are written when the arm is registered.  So a `lean: checks:`
PR touches neither `Checks/Sys/Table.lean` nor `Checks/VmMapsDisjoint.lean`
— by the ticket's shape, not by a guard's refusal:
`tools/check_lean_port_scope.py` freezes the second but takes additions
to the first, so a table row added here would pass it and be wrong only
against the brief.  Its pins are `Checks/Cases/Checks/Sys/Fs/DPath.lean`.

One spelling differs from Rocq without changing a value: the `Z.ltb`
size test is Lean's decidable `<` on `Int`, as in the spec twin.
`ret_outcome` comes from `Checks.Witness.Prelude`, as in Rocq.  Nothing
is left unported. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.DPath

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- `check_getcwd size eff m`: `-ERANGE` or one of the three injectable
errnos when `size` is 0 or 1, `CheckUnmodeled` for every larger buffer,
`CheckReject` for anything else.  Rocq: `check_getcwd`.

The size test comes FIRST, before the effect is opened, because the
model's answer above the band is the decline whatever the trace says:
`getcwd_spec` is `unmodeled` there, and a checker that read the effect
first could only reject what the spec declines.  Inside the band the
four admitted answers share one shape, a bare return with FIVE EMPTY
ledgers: `SYSCALL_DEFINE2(getcwd)` (fs/d_path.c, Linux v6.18.46, commit
1f99e9ab748f) reaches its single `copy_to_user` (line 441) only after
the `len > size` comparison (line 439) has passed, and at `size ≤ 1` it
never does — the spec twin carries the argument that `len ≥ 2` on every
path that reaches the comparison — so no admitted outcome writes, zeroes,
unmaps, copies or reads a byte of user memory.  Any ledger entry beside
an admitted errno is therefore a lie, and the `match` refuses it before
the return is looked at; a return outside the four is refused by the two
tests after it.  The `-EFAULT` Linux could return from that
`copy_to_user` (line 442) is not among the four for the same reason: at
`size ≤ 1` the copy is never reached.  That is Linux's answer and not
every supported implementation's — qemu-user checks the buffer before any
size test and answers `-EFAULT` at size 1 on a buffer that is not guest
memory and at size 0 on an address above `reserved_va` under `-R` — so
refusing it is a Linux behavior the spec proves certain where another
implementation differs; `bugs/getcwd-erange-band-admits-linux-alone.md`
records the cost, the spec twin's docstring the shapes, and the checker
follows the spec.

The two return tests are separate rather than one membership test on a
four-element list because they mirror the spec's `alt`: `errno_ret_in
getcwd_errnos` is the injected arm, `bv_eqb ret (errno_ret ERANGE)` the
arm the model derives from `size`, in the spec's order. -/
def check_getcwd (size : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if 1 < bv_unsigned size then CheckUnmodeled
  else
    match eff with
    | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
        if errno_ret_in getcwd_errnos ret then CheckOk m []
        else if bv_eqb ret (errno_ret ERANGE) then CheckOk m []
        else CheckReject
    | _ => CheckReject

/-! ## Soundness and completeness

The four lemmas are Rocq's, with Rocq's names and hypothesis order.  The
effect's five ledgers are opened by hand, one `cases` at a time, rather
than through the prelude's `check_ret_only_ok_iff`: that lemma is about a
checker that accepts ONE return, and `check_getcwd` accepts a set, so a
proof through it would need a helper of a shape Rocq does not have — and
Rocq's own proofs destruct the ledgers by hand (BRIEF.md section 3: a
helper that changes shape is a divergence). -/

/-- A `CheckOk` answer is an outcome the spec admits.  Rocq:
`check_getcwd_sound_ok`. -/
theorem check_getcwd_sound_ok (size : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_getcwd size eff m = CheckOk m' evs) :
    getcwd_spec size i m (Ok eff m' evs) := by
  unfold check_getcwd at h
  unfold getcwd_spec
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte, reduceCtorEq] at h
  · simp only [hs, ↓reduceIte] at h ⊢
    obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
    cases ws with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases zs with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases us with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases cs with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases cis with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases he : errno_ret_in getcwd_errnos ret with
    | true =>
      simp only [he, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true getcwd_errnos ret).mp he
      exact alt_l _ _ i m _
        (bind_ok0 _ _ i m e m _ m [] (choose_ok _ e i m hin) (pure_ok _ i m))
    | false =>
      simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : bv_eqb ret (errno_ret ERANGE) with
      | true =>
        simp only [hr, ↓reduceIte, check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bv_eqb_eq] at hr
        subst hr
        exact alt_r _ _ i m _ (pure_ok _ i m)
      | false =>
        simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- A `CheckUnmodeled` answer is a decline the spec makes: the checker
declines exactly above the band, where the spec is `unmodeled`.  Rocq:
`check_getcwd_sound_unmodeled`. -/
theorem check_getcwd_sound_unmodeled (size : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getcwd size eff m = CheckUnmodeled) :
    getcwd_spec size i m Unmodeled := by
  unfold check_getcwd at h
  unfold getcwd_spec
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte]
    exact unmodeled_intro i m
  · exfalso
    simp only [hs, ↓reduceIte] at h
    obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
    cases ws with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases zs with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases us with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases cs with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases cis with
    | cons _ _ => simp only [reduceCtorEq] at h
    | nil =>
    cases he : errno_ret_in getcwd_errnos ret with
    | true => simp only [he, ↓reduceIte, reduceCtorEq] at h
    | false =>
      cases hr : bv_eqb ret (errno_ret ERANGE) with
      | true => simp only [he, hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | false => simp only [he, hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Every outcome the spec admits is one the checker accepts, with the
model and the events the spec hands back.  Rocq:
`check_getcwd_complete_ok`. -/
theorem check_getcwd_complete_ok (size : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : getcwd_spec size i m (Ok eff m' evs)) :
    check_getcwd size eff m = CheckOk m' evs := by
  unfold getcwd_spec at h
  unfold check_getcwd
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte] at h
    rw [unmodeled_iff] at h
    cases h
  · simp only [hs, ↓reduceIte] at h ⊢
    rw [alt_iff] at h
    rcases h with h | h
    · unfold errno_from at h
      rw [bind_choose_iff] at h
      obtain ⟨e, hin, h⟩ := h
      unfold err_ret ret_only at h
      rw [pure_iff] at h
      injection h with heff hm hevs
      subst heff hm hevs
      simp only [errno_ret_in_intro getcwd_errnos e hin, ↓reduceIte]
    · unfold err_ret ret_only at h
      rw [pure_iff] at h
      injection h with heff hm hevs
      subst heff hm hevs
      have hno : errno_ret_in getcwd_errnos (errno_ret ERANGE) = false := by decide
      simp only [hno, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl]

/-- Where the spec declines, the checker declines whatever effect the
trace offers.  Rocq: `check_getcwd_complete_unmodeled`. -/
theorem check_getcwd_complete_unmodeled (size : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : getcwd_spec size i m Unmodeled) :
    check_getcwd size eff m = CheckUnmodeled := by
  unfold getcwd_spec at h
  unfold check_getcwd
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte]
  · exfalso
    simp only [hs, ↓reduceIte] at h
    rw [alt_iff] at h
    rcases h with h | h
    · unfold errno_from at h
      rw [bind_choose_iff] at h
      obtain ⟨_, _, h⟩ := h
      unfold err_ret ret_only at h
      rw [pure_iff] at h
      cases h
    · unfold err_ret ret_only at h
      rw [pure_iff] at h
      cases h

/-! ## The witness

Mirrors `theories/LinuxProcessSem/Checks/Witness/Fs/DPath.v`. -/

/-- One outcome `getcwd_spec size` admits: the decline above the band,
`-ERANGE` inside it.  Rocq: `getcwd_witness`.

The witness takes `-ERANGE` rather than an injected errno because it is
the answer the model DERIVES from `size`: at 0 or 1 the `len > size`
test of `SYSCALL_DEFINE2(getcwd)` (fs/d_path.c, Linux v6.18.46) holds
for every working directory, where `-ENOMEM`, `-ENOENT` and
`-ENAMETOOLONG` each rest on an allocator, dcache or depth condition the
model does not carry.  Above the band the spec is `unmodeled` and so is
the only outcome a witness can exhibit. -/
def getcwd_witness (size : word) (m : Model) : outcome SyscallEffect :=
  if 1 < bv_unsigned size then Unmodeled
  else ret_outcome (errno_ret ERANGE) m

/-- The witness is admitted, at every size.  Rocq: `getcwd_witness_ok`. -/
theorem getcwd_witness_ok (size : word) (i : SyscallInput) (m : Model) :
    getcwd_spec size i m (getcwd_witness size m) := by
  unfold getcwd_spec getcwd_witness
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hs, ↓reduceIte]
    unfold err_ret ret_only ret_outcome
    exact alt_r _ _ i m _ (pure_ok _ i m)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.DPath
