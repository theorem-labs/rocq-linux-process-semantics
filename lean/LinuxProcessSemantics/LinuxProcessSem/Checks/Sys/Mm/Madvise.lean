import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Mm.Madvise — the madvise (233) checker and witness

Mirrors two Rocq files at once: `theories/LinuxProcessSem/Checks/Sys/Mm/Madvise.v`
(`check_madvise` and its soundness/completeness lemmas) and
`theories/LinuxProcessSem/Checks/Witness/Mm/Madvise.v` (`madvise_witness`
and `madvise_witness_ok`).  Every definition and lemma keeps its Rocq name
and statement shape.  Not part of the trusted specification: the checker
is an executable reading of `Sys.Mm.Madvise.madvise_spec`, and the lemmas
here are what relate the two — a `CheckOk` is exactly an `Ok` the spec
accepts, a `CheckUnmodeled` exactly the spec's `Unmodeled`, in both
directions.  What the spec says of Linux, and why, is argued on the spec
twin and on `theories/LinuxProcessSem/Sys/Mm/Madvise.v`; nothing of that
argument is repeated here, and no kernel behaviour is claimed here that the
spec does not already claim.

The checker walks the spec's gates in the spec's order, because the order
is behaviour.  Which kernel line forces each gate, and why nothing but the
0 and the whole-range zero-fill is admissible past them, is argued on the
spec twin's header and pinned, input by input, in
`Checks/Cases/Checks/Sys/Mm/Madvise.lean`; it is not restated here.

The baseline named above is a71fd38a, the squash that landed the
2026-09-11 work on `main` (#794), and not the brief's f44244ad6: that
commit is no longer an ancestor of the day branch, and the two mirrored
Rocq files and `Checks/Cases/Mm/Madvise.v` are byte-identical at the two.

Rocq states more about this checker than the two mirrored files hold, and
this file carries one piece of it: `check_madvise_frame`, the
`Checks/VmMapsDisjoint.v` lemma that an accepted `madvise` leaves `vm_maps`
where they were.  It depends on nothing but `check_madvise`, so it is
stated here as every merged checker twin states its own
(`Checks/Sys/Fs/Sync.lean`'s `check_fsync_frame` says why), although the
C-ticket acceptance in `tools/lean_port_graph.py` assigns it to the
registration step.  The rest is not here, for two different reasons.
`ca_check_arm_madvise` and `ca_witness_arm_madvise` (`Checks/Sys/Dispatch.v`)
and the `checked_table` row are the V ticket's registration, so that a
checker lands on the preludes and its spec alone, ahead of the
checked-table chain; the `arm_madvise_preserves_vm` alternative that step
adds beside the VM invariant's alternation is derived from the frame lemma
below, not re-proved.  `check_syscall_madvise` and `syscall_witness_madvise`
(`Checks/Sys/DispatchCompute.v`) are ported by no ticket: that file is
declined for the port's duration in `tools/lean_port_graph.py`'s register,
its two lemmas per arm serving the simulation proofs of the Rocq examples'
common layer, which no Lean example needs yet. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome)

/-! ## The checker -/

/-- `check_madvise addr len advice eff m`: the executable reading of
`madvise_spec addr len advice`, gate for gate; which gate answers what,
and why, is on the spec twin.  Rocq: `Checks.Sys.Mm.Madvise.check_madvise`. -/
def check_madvise (addr len advice : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
  else if !(madvise_dontneed_b advice) then CheckUnmodeled
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      match eff with
      | SyscallEffect.mkEffectU r [] zs [] [] [] =>
          if w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (madvise_dontneed_next m addr n) []
          else CheckReject
      | _ => CheckReject
    else CheckUnmodeled

/-! ## Soundness and completeness

The four lemmas are the five `CheckedArm` obligations minus receptivity,
which the witness below discharges.  Each walks the same gates as the
definitions, so a gate moved in one and not the other stops the proof
closing: that is the whole point of stating them.

The wrap gate is split as `cases hbig : decide (two_pow_64 ≤ …)` and
handed back as a hypothesis by `of_decide_eq_true` / `of_decide_eq_false`,
so that the `Int` order on `two_pow_64` is named and never evaluated; the
pins file's header says what evaluating it costs the elaborator. -/

/-- A `CheckOk` is an `Ok` the spec accepts.
Rocq: `Checks.Sys.Mm.Madvise.check_madvise_sound_ok`. -/
theorem check_madvise_sound_ok (addr len advice : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_madvise addr len advice eff m = CheckOk m' evs) :
    madvise_spec addr len advice i m (Ok eff m' evs) := by
  unfold check_madvise at h
  unfold madvise_spec
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hadv : madvise_dontneed_b advice
  · simp only [hadv, Bool.not_false, ↓reduceIte] at h
    cases h
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h ⊢
      refine bind_ok0 get_model _ i m m m _ _ _ (get_model_ok i m) ?_
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
        cases h
      simp only [hok, ↓reduceIte] at h ⊢
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      cases ws <;> cases us <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
      split at h
      · rename_i hc
        simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Bool.and_eq_true, w_is0, bv_eqb_eq, listNN_eqb_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)
      · simp only [reduceCtorEq] at h
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · simp only [hlen, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- A `CheckUnmodeled` is the spec's `Unmodeled`.
Rocq: `Checks.Sys.Mm.Madvise.check_madvise_sound_unmodeled`. -/
theorem check_madvise_sound_unmodeled (addr len advice : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_madvise addr len advice eff m = CheckUnmodeled) :
    madvise_spec addr len advice i m Unmodeled := by
  unfold check_madvise at h
  unfold madvise_spec
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hadv : madvise_dontneed_b advice
  · simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h ⊢
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · refine bind_unmodeled2 get_model _ i m m m [] (get_model_ok i m) ?_
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      simp only [hok, ↓reduceIte] at h
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      cases ws <;> cases us <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
      split at h <;> simp only [reduceCtorEq] at h
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h ⊢
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hlen, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Every `Ok` the spec accepts is the checker's `CheckOk`, with the same
post-model and events.  Rocq: `Checks.Sys.Mm.Madvise.check_madvise_complete_ok`. -/
theorem check_madvise_complete_ok (addr len advice : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : madvise_spec addr len advice i m (Ok eff m' evs)) :
    check_madvise addr len advice eff m = CheckOk m' evs := by
  unfold madvise_spec at h
  unfold check_madvise
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h ⊢
    simp only [err_ret, ret_only, Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hadv : madvise_dontneed_b advice
  · simp only [hadv, Bool.not_false, ↓reduceIte] at h
    simp only [unmodeled, reduceCtorEq] at h
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h ⊢
      have h2 := get_model_bind_ok_inv _ i m eff m' evs h
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h2
        simp only [unmodeled, reduceCtorEq] at h2
      simp only [hok, ↓reduceIte, bind_modify_iff, Monad.pure, outcome.Ok.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      have hr : w_is0 (Z_to_bv 64 0) = true := bv_eqb_refl _
      have hz : listNN_eqb [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
          [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] = true :=
        (listNN_eqb_eq _ _).mpr rfl
      simp only [hr, hz, Bool.and_self, ↓reduceIte]
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h ⊢
    simp only [err_ret, ret_only, Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · simp only [hlen, ↓reduceIte] at h ⊢
    simp only [ret_only, Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩

/-- The spec's `Unmodeled` is the checker's `CheckUnmodeled`, whatever
effect the trace offers.
Rocq: `Checks.Sys.Mm.Madvise.check_madvise_complete_unmodeled`. -/
theorem check_madvise_complete_unmodeled (addr len advice : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : madvise_spec addr len advice i m Unmodeled) :
    check_madvise addr len advice eff m = CheckUnmodeled := by
  unfold madvise_spec at h
  unfold check_madvise
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h
    simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hadv : madvise_dontneed_b advice
  · simp only [Bool.not_false, ↓reduceIte]
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h ⊢
      have h2 := get_model_bind_unmodeled_inv _ i m h
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [hok, ↓reduceIte, bind_modify_iff, Monad.pure, reduceCtorEq] at h2
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h
    simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
  · simp only [hlen, ↓reduceIte] at h
    simp only [ret_only, Monad.pure, reduceCtorEq] at h

/-- An accepted `madvise` leaves `vm_maps` where they were: three of the
four `CheckOk`s hand back the model they were given, and the fourth,
`madvise_dontneed_next`, moves the materialized ledger alone
(`m_vmmaps_with_vm_backing`).  This is the fact the VM invariant's
alternation consumes for the arm, stated here so that it does not wait on
the alternation's file; Rocq keeps it in `VmMapsDisjoint.v` under the same
name.  Rocq: `VmMapsDisjoint.check_madvise_frame`. -/
theorem check_madvise_frame (addr len advice : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_madvise addr len advice eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_madvise at h
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hadv : madvise_dontneed_b advice
  · simp only [hadv, Bool.not_false, ↓reduceIte] at h
    cases h
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
        cases h
      simp only [hok, ↓reduceIte] at h
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      cases ws <;> cases us <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
      split at h
      · simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl
      · simp only [reduceCtorEq] at h
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · simp only [hlen, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl

/-! ## The witness

One outcome the spec accepts at every input and model: what makes the arm
receptive.  It is the checker's accepting answer written out, so a gate the
checker declines is a gate the witness declines, and a proof that the
witness is accepted (`madvise_witness_ok`) is a second, independent walk of
the spec's gates. -/

/-- Rocq: `Checks.Witness.Mm.Madvise.madvise_witness`. -/
def madvise_witness (addr len advice : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
  else if !(madvise_dontneed_b advice) then Unmodeled
  else if w_is0 len then ret_outcome (Z_to_bv 64 0) m
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
  then ret_outcome (errno_ret EINVAL) m
  else
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) []
    else Unmodeled

/-- The witness is accepted by the spec.
Rocq: `Checks.Witness.Mm.Madvise.madvise_witness_ok`. -/
theorem madvise_witness_ok (addr len advice : word) (i : SyscallInput) (m : Model) :
    madvise_spec addr len advice i m (madvise_witness addr len advice m) := by
  unfold madvise_spec madvise_witness
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i _
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hadv : madvise_dontneed_b advice
  · simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hlen : w_is0 len
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte]
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine bind_unmodeled2 get_model _ i m m m [] (get_model_ok i m) ?_
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      simp only [↓reduceIte]
      refine bind_ok0 get_model _ i m m m _ _ _ (get_model_ok i m) ?_
      simp only [hok, ↓reduceIte]
      exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) := of_decide_eq_true hbig
    simp only [hb, ↓reduceIte]
    exact pure_ok _ i _
  · simp only [↓reduceIte]
    exact pure_ok _ i _

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise
