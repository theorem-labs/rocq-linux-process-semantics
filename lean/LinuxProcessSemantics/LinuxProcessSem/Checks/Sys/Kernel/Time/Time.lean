import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Time.Time — the gettimeofday (169) checker, its proofs, and its witness

Twin of `theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Time.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Time/Time.v`, read at the
baseline above.  Both mirror `Sys/Kernel/Time/Time.v`, which answers to
Linux `kernel/time/time.c`: this file holds the executable checker for
`gettimeofday_spec` (`Sys/Kernel/Time/Time.lean`), its two soundness and
two completeness lemmas, and the witness that makes the arm receptive, and
no other syscall.  The witness lives here rather than at its own mirror
path because `Checks/Witness/Prelude.lean` and `Checks/Sys/Prelude.lean`
are both imported anyway and a second module would carry only the one
definition, its constant and its proof; nothing else the tree reads
depends on the split.  Not part of the trusted specification: the trusted
definitions are `Sys/Kernel/Time/Time.lean`'s, and every theorem here
relates an executable to them.

Every kernel line named below was read at Linux v6.18.46 (commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), which is AGENTS.md's citation
baseline.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq registers this checker in
`Checks/Sys/Dispatch.v`'s `checked_table` and proves its frame lemma,
`check_gettimeofday_frame`, in `Checks/VmMapsDisjoint.v`; the Lean tree
does neither here.  Since PR #904 a checker ticket ships the checker, its
theorems and its witness, and the V ticket's registration step adds the
`checked_table` row, the `arm_unfold` lemmas, the `CheckedArm` and the
frame lemma in one change, against the shared files this ticket may not
touch.  So the theorems below stand alone against `Checks/Sys/Prelude.lean`,
`Checks/Witness/Prelude.lean` and the `Sys` twin, and are what that step
will wire in.  The pins on this checker are in
`Checks/Cases/Checks/Sys/Kernel/Time/Time.lean`.

Its own definitions are cited as `Time.<ident>`, not
`Kernel.Time.Time.<ident>`, for the reason the Sys twin's header gives: a
module path with a repeated segment is what `tools/check_module_refs.py`
reports as malformed in the Rocq and Markdown prose it scans, and the Lean
files keep the same spelling by convention.

The Rocq files were first read at f44244ad6b80 and the baseline above is
the day tip they were re-read at: both are byte-identical between the two
commits (`git diff` is empty).  The baseline should be an ancestor of the
branch, and f44244ad is not one here; nothing mechanical holds THIS
file's header to that — `tools/check_lean_spec_parity.py` sweeps the
`Sys/` twins and the base twins, not `Checks/` — so it was checked by
hand with `git merge-base --is-ancestor`.

Only Rocq spellings change, and nothing else does: `negb (w_is0 tz)` is
`!(w_is0 tz)`, `Some _`/`None` are `some _`/`none`, `in_wmem i` is
`i.in_wmem` and `mkEffectU` is `SyscallEffect.mkEffectU`.

THREE HELPERS HAVE NO ROCQ TWIN and say so in place:
`check_gettimeofday_ok_inv` and `check_gettimeofday_delivered_ne_unmodeled`
on the checker, `timeval_zero_ok` on the witness.  Rocq destructs the
effect inline in its two soundness lemmas (the completeness pair takes
`eff` whole and resolves it by `inv_ok`); Lean destructs it in the two
helpers, one per soundness twin — `check_gettimeofday_sound_ok` reads the
inversion, `check_gettimeofday_sound_unmodeled` the `≠ CheckUnmodeled`
fact — and the completeness pair works from the spec hypothesis.
Rocq closes the witness's well-formedness by `vm_compute` inside
`gettimeofday_witness_ok`; Lean states it once and reads it there.  None
of the three is a claim about the kernel: each is the executable's own
case analysis, and the theorems that are twins are what tie it to the
spec. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Time

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-- The gettimeofday (169) checker: given the input, the two pointer
arguments and the effect a kernel reported, say whether `gettimeofday_spec`
admits that effect.  Mirrors Rocq's `Time.check_gettimeofday`; the
decisions are the spec's, restated so that they COMPUTE, and each is the
spec's own gate in the spec's own order:

- a non-NULL `tz`: `CheckUnmodeled`, whatever the effect.  The kernel
  copies a mutable file-scope `struct timezone` there (kernel/time/time.c,
  `gettimeofday`, :151-154 at v6.18.46) and the model carries no value for
  it, so the spec declines and the checker cannot do otherwise — an
  effect it accepted or rejected here would be an answer the spec does not
  give.
- a NULL `tv`: `CheckUnmodeled`, for the same reason: the spec declines
  (the Sys twin's docstring says why), so neither `CheckOk` nor
  `CheckReject` is available.
- a `tv` whose 16 bytes `copy_bytes_map` will not read: `access_okb tv 8`
  false means the FIRST `put_user` (kernel/time/time.c, `gettimeofday`,
  :147 at v6.18.46; riscv's `put_user` is arch/riscv/include/asm/uaccess.h:408-415,
  its `access_ok` at :412) is refused before anything is stored and the
  call is -EFAULT (:149), so the checker demands exactly that: the errno
  and NO write, zero, unmap, copy or copy-in beside it, which is what
  `check_ret_only` checks.  `access_okb tv 8` true is the torn band or a
  destination not wholly mapped, where the kernel may have stored
  `tv_sec` before failing; the spec declines, and so does the checker.
- a readable `tv`: the kernel answers the literal 0 (:155) having written
  the two fields (:147-148) and nothing else, so the checker demands a
  return of 0, EXACTLY ONE write, at `tv`, whose bytes pass
  `timeval_ok_b`, and no other effect.  The `CheckOk` carries the model
  unchanged and no events, because the spec's `pure` does.

What it does NOT check is the VALUE the kernel wrote beyond
`timeval_ok_b`: the spec `choose`s it afresh per call, so any normalized
timeval below `KTIME_SEC_MAX` is admitted, and the Sys twin's docstring
carries the argument that there is nothing to relate it to. -/
def check_gettimeofday (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(w_is0 tz) then CheckUnmodeled
  else if w_is0 tv then CheckUnmodeled
  else
    match copy_bytes_map i.in_wmem tv 16 with
    | none =>
        if !(access_okb tv 8) then check_ret_only eff (errno_ret EFAULT) m []
        else CheckUnmodeled
    | some _ =>
        match eff with
        | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs
            then CheckOk m [] else CheckReject
        | _ => CheckReject

/-- Everything a `CheckOk` from `check_gettimeofday` tells you, in one
inversion: the model and events are the input's, both gates were passed
(`tz` NULL, `tv` not), and the effect is one of the two shapes the checker
accepts — the bare -EFAULT on a `tv` whose first store is refused, or the
zero return with one well-formed 16-byte write at `tv` on a readable one.

NO ROCQ TWIN: Rocq destructs the effect inline in each soundness lemma
(`Time.check_gettimeofday_sound_ok` and `Time.check_gettimeofday_sound_unmodeled`).  Lean does the
destruct here for `check_gettimeofday_sound_ok`, which reads it, as will
the frame lemma the V ticket's registration step states from `m' = m`;
`check_gettimeofday_delivered_ne_unmodeled` below carries the other
soundness twin's half. -/
theorem check_gettimeofday_ok_inv (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_gettimeofday i tv tz eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] ∧ w_is0 tz = true ∧ w_is0 tv = false ∧
      ((copy_bytes_map i.in_wmem tv 16 = none ∧ access_okb tv 8 = false ∧
          eff = mkEffect (errno_ret EFAULT) [] []) ∨
       (∃ w bs, copy_bytes_map i.in_wmem tv 16 = some w ∧
          eff = mkEffect (Z_to_bv 64 0) [(tv, bs)] [] ∧ timeval_ok_b bs = true)) := by
  unfold check_gettimeofday at h
  cases htz : w_is0 tz with
  | false => simp only [htz, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
    simp only [htz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases htv : w_is0 tv with
    | true => simp only [htv, ↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [htv, Bool.false_eq_true, ↓reduceIte] at h
      cases hc : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        simp only [hc] at h
        cases ha : access_okb tv 8 with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte] at h
          rw [check_ret_only_ok_iff] at h
          obtain ⟨rfl, hm, rfl⟩ := h
          exact ⟨hm, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
        | true => simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | some w =>
        simp only [hc] at h
        obtain ⟨r, ws, zs, us, cs, cis⟩ := eff
        rcases zs with _ | ⟨z, zs⟩ <;> rcases us with _ | ⟨u, us⟩ <;>
          rcases cs with _ | ⟨c, cs⟩ <;> rcases cis with _ | ⟨ci, cis⟩ <;>
          rcases ws with _ | ⟨⟨a, bs⟩, _ | ⟨w2, ws⟩⟩ <;>
          simp only [reduceCtorEq] at h
        cases hok : (bv_eqb r (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs) with
        | false => simp only [hok, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hok, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨hm, rfl⟩ := h
          simp only [Bool.and_eq_true, bv_eqb_eq] at hok
          obtain ⟨⟨rfl, rfl⟩, hbs⟩ := hok
          exact ⟨hm.symm, rfl, rfl, rfl, Or.inr ⟨w, bs, rfl, rfl, hbs⟩⟩

/-- On a readable `tv` the checker answers `CheckOk` or `CheckReject` and
never `CheckUnmodeled`: the delivery branch has no decline in it.

NO ROCQ TWIN: this is the `Some` half of Rocq's
`Time.check_gettimeofday_sound_unmodeled`, destructed inline there. -/
theorem check_gettimeofday_delivered_ne_unmodeled (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model) (w : List byte)
    (htz : w_is0 tz = true) (htv : w_is0 tv = false)
    (hc : copy_bytes_map i.in_wmem tv 16 = some w) :
    check_gettimeofday i tv tz eff m ≠ CheckUnmodeled := by
  unfold check_gettimeofday
  simp only [htz, htv, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r, ws, zs, us, cs, cis⟩ := eff
  rcases zs with _ | ⟨z, zs⟩ <;> rcases us with _ | ⟨u, us⟩ <;>
    rcases cs with _ | ⟨c, cs⟩ <;> rcases cis with _ | ⟨ci, cis⟩ <;>
    rcases ws with _ | ⟨⟨a, bs⟩, _ | ⟨w2, ws⟩⟩ <;>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  cases hok : (bv_eqb r (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs) with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, not_false_eq_true]
  | true => simp only [↓reduceIte, reduceCtorEq, not_false_eq_true]

/-- Soundness on the accepting side: a `CheckOk` is a spec run.  Mirrors
Rocq's `Time.check_gettimeofday_sound_ok`. -/
theorem check_gettimeofday_sound_ok (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_gettimeofday i tv tz eff m = CheckOk m' evs) :
    gettimeofday_spec tv tz i m (Ok eff m' evs) := by
  obtain ⟨hm, hevs, htz, htv, hcase⟩ := check_gettimeofday_ok_inv i tv tz eff m m' evs h
  rw [hm, hevs]
  unfold gettimeofday_spec
  simp only [htz, htv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
  rcases hcase with ⟨hc, ha, rfl⟩ | ⟨w, bs, hc, rfl, hbs⟩
  · simp only [hc, ha, Bool.not_false, ↓reduceIte]
    unfold err_ret ret_only
    exact pure_ok _ _ _
  · simp only [hc]
    refine bind_ok0 _ _ i m bs m _ _ _ (choose_ok _ bs i m hbs) ?_
    exact pure_ok _ _ _

/-- Soundness on the declining side: a `CheckUnmodeled` is a spec decline.
Mirrors Rocq's `Time.check_gettimeofday_sound_unmodeled`. -/
theorem check_gettimeofday_sound_unmodeled (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_gettimeofday i tv tz eff m = CheckUnmodeled) :
    gettimeofday_spec tv tz i m Unmodeled := by
  unfold gettimeofday_spec
  cases htz : w_is0 tz with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro _ _
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases htv : w_is0 tv with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro _ _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
      cases hc : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        unfold check_gettimeofday at h
        simp only [htz, htv, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases ha : access_okb tv 8 with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro _ _
      | some w =>
        exact absurd h (check_gettimeofday_delivered_ne_unmodeled i tv tz eff m w htz htv hc)

/-- Completeness on the accepting side: a spec run is a `CheckOk`.  Mirrors
Rocq's `Time.check_gettimeofday_complete_ok`. -/
theorem check_gettimeofday_complete_ok (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : gettimeofday_spec tv tz i m (Ok eff m' evs)) :
    check_gettimeofday i tv tz eff m = CheckOk m' evs := by
  unfold gettimeofday_spec at h
  unfold check_gettimeofday
  cases htz : w_is0 tz with
  | false => simp only [htz, Bool.not_false, ↓reduceIte, Monad.unmodeled, reduceCtorEq] at h
  | true =>
    simp only [htz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases htv : w_is0 tv with
    | true => simp only [htv, ↓reduceIte, Monad.unmodeled, reduceCtorEq] at h
    | false =>
      simp only [htv, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := input_bind_ok_inv _ i m _ _ _ h
      cases hc : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        simp only [hc] at h ⊢
        cases ha : access_okb tv 8 with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte] at h ⊢
          simp only [err_ret, ret_only, Monad.pure, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        | true =>
          simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Monad.unmodeled,
            reduceCtorEq] at h
      | some w =>
        simp only [hc] at h ⊢
        rw [bind_choose_iff] at h
        obtain ⟨bs, hbs, hk⟩ := h
        simp only [Monad.pure, outcome.Ok.injEq] at hk
        obtain ⟨rfl, rfl, rfl⟩ := hk
        simp only [bv_eqb_refl, Bool.true_and, hbs, ↓reduceIte]

/-- Completeness on the declining side: a spec decline is a `CheckUnmodeled`,
whatever effect is offered.  Mirrors Rocq's
`Time.check_gettimeofday_complete_unmodeled`. -/
theorem check_gettimeofday_complete_unmodeled (i : SyscallInput) (tv tz : word) (m : Model)
    (eff : SyscallEffect)
    (h : gettimeofday_spec tv tz i m Unmodeled) :
    check_gettimeofday i tv tz eff m = CheckUnmodeled := by
  unfold gettimeofday_spec at h
  unfold check_gettimeofday
  cases htz : w_is0 tz with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
    simp only [htz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases htv : w_is0 tv with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [htv, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := input_bind_unmodeled_inv _ i m h
      cases hc : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        simp only [hc] at h ⊢
        cases ha : access_okb tv 8 with
        | false =>
          simp only [ha, Bool.not_false, ↓reduceIte, err_ret, ret_only, Monad.pure,
            reduceCtorEq] at h
        | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      | some w =>
        simp only [hc] at h
        rw [bind_choose_iff] at h
        obtain ⟨bs, _, hk⟩ := h
        simp only [Monad.pure, reduceCtorEq] at hk

/-! ## The witness — `Checks/Witness/Kernel/Time/Time.v`

One outcome `gettimeofday_spec` admits on every input and model, and the
lemma saying so.  It is what makes the arm RECEPTIVE — the spec is never
empty where the checker would have to answer — and it is the `ca_witness`
field of the `CheckedArm` the V ticket's registration step builds, with
`ca_receptive` the proof field that carries `gettimeofday_witness_ok`.
The witness picks an answer; `gettimeofday_witness_ok` is what says the
spec agrees, and a wrong pick fails that lemma rather than passing quietly.

The pick is the spec's own gate order and, on a readable `tv`, the epoch:
the spec `choose`s any well-formed timeval, so a constant one is enough,
and a NULL `tz` lets the whole call be exhibited without a `sys_tz` value
the model does not carry. -/

/-- The timeval the witness writes: the epoch, `tv_sec = 0` and `tv_usec = 0`
as sixteen little-endian bytes.  Mirrors Rocq's `Time.timeval_zero`.  It
passes `timeval_ok_b` — sixteen bytes, `tv_usec` below 10^6, `tv_sec` below
`KTIME_SEC_MAX` — so the spec admits it.  The witness does not claim any
kernel WILL report it, only that the spec admits it, which is all
receptiveness needs. -/
def timeval_zero : List byte := Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0

/-- `timeval_zero` is a well-formed reading.  No Rocq twin: Rocq closes this
by `vm_compute` inside `gettimeofday_witness_ok`. -/
theorem timeval_zero_ok : timeval_ok_b timeval_zero = true := by decide

/-- One outcome `gettimeofday_spec tv tz` admits on `i` and `m`, gate for
gate: `Unmodeled` where the spec declines (a non-NULL `tz`, a NULL `tv`, a
`tv` in the torn band or not wholly mapped), the bare -EFAULT where the
first `put_user`'s own range test refuses `tv`
(arch/riscv/include/asm/uaccess.h, `put_user`, :412 at v6.18.46, answering
-EFAULT at :414 without storing), and on a readable `tv` the zero return
(kernel/time/time.c, `gettimeofday`, :155 at v6.18.46) with one 16-byte
write of `timeval_zero` at `tv`.  Mirrors Rocq's
`Time.gettimeofday_witness`.  Every branch is the spec's own answer on that
branch, which is what `gettimeofday_witness_ok` checks. -/
def gettimeofday_witness (tv tz : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if !(w_is0 tz) then Unmodeled
  else if w_is0 tv then Unmodeled
  else
    match copy_bytes_map i.in_wmem tv 16 with
    | none =>
        if !(access_okb tv 8) then ret_outcome (errno_ret EFAULT) m
        else Unmodeled
    | some _ => Ok (mkEffect (Z_to_bv 64 0) [(tv, timeval_zero)] []) m []

/-- The witness is a spec run: the arm is receptive.  Mirrors Rocq's
`Time.gettimeofday_witness_ok`. -/
theorem gettimeofday_witness_ok (i : SyscallInput) (tv tz : word) (m : Model) :
    gettimeofday_spec tv tz i m (gettimeofday_witness tv tz i m) := by
  unfold gettimeofday_spec gettimeofday_witness
  cases htz : w_is0 tz with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro _ _
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases htv : w_is0 tv with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro _ _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine bind_step _ _ i m i m _ (input_ok i m) ?_
      cases hc : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        dsimp only
        cases ha : access_okb tv 8 with
        | false =>
          simp only [Bool.not_false, ↓reduceIte]
          unfold err_ret ret_only ret_outcome
          exact pure_ok _ _ _
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro _ _
      | some w =>
        dsimp only
        refine bind_step _ _ i m timeval_zero m _ (choose_ok _ timeval_zero i m timeval_zero_ok) ?_
        exact pure_ok _ _ _

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Time
