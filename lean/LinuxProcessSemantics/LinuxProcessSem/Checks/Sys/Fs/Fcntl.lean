import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Fcntl — the fcntl (25) checker, witness, and their proofs

Mirrors two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Fs/Fcntl.v`,
which holds `check_fcntl` and the soundness and completeness lemmas
relating it to
`Sys/Fs/Fcntl.v`'s `fcntl_spec`, and
`theories/LinuxProcessSem/Checks/Witness/Fs/Fcntl.v`, which holds
`fcntl_witness` and `fcntl_witness_ok`.  They are one file here because the
port's per-syscall checker ticket owns one module, and because the two
Rocq files both import `Specs` and re-export their own prelude chain
(`Checks/Sys/Prelude` with `Fs.ReadWrite`, and the Witness pair), and
neither imports the other.  Not part of the trusted
specification.  What is trusted is `Sys/Fs/Fcntl.lean`; the checker is
believed only through the proofs below, which are the proof fields
the `CheckedArm` for this syscall is built from once it is registered.  Its
pins are `Checks/Cases/Checks/Sys/Fs/Fcntl.lean`.

THE BASELINE NAMED ABOVE is the commit the two Rocq files mirrored here
were read at and the one the spec twin `Sys/Fs/Fcntl.lean` names.  The
port's common baseline, `f44244ad` — `docs/lean-port/BRIEF.md` section 1's
`Rocq commit to read specs at`, which the ticket brief prints — is not an
ancestor of this history; between it and `a71fd38a` the two checker files did not
change, and the spec file gained the twelve lines the spec twin already
carries, so the header names the commit the whole surface was read at
rather than one the tree cannot reach.

THE ORDER IS THE KERNEL'S, and it is the one thing the checker's shape
says that its arms do not spell: `SYSCALL_DEFINE3(fcntl, …)`
(fs/fcntl.c:574-592, Linux v6.18.46, commit 1f99e9ab748f) resolves the
descriptor and returns -EBADF on `fd_empty` before `do_fcntl`
(fs/fcntl.c:444-557) ever switches on `cmd`, and `setfl` (fs/fcntl.c:39-89)
is what an F_SETFL reaches.  The argument for each arm, and for each
decline, is on the spec twin's definitions, not here: the checker decides
by the spec's own predicates and adds no kernel claim of its own.

THE ARGUMENTS ARRIVE DECODED.  `check_fcntl` takes the three words the
kernel's `unsigned int fd`, `unsigned int cmd` and `unsigned long arg`
hold, and never reads a register: the narrowing of a0 and a1 to 32 bits
is `fd32` and `cmd32` (`Sys/Syscall.lean`), applied by the arm that
registers this checker — Rocq's `Dispatch.arm_fcntl` writes
`check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)` — and
the pins that are about the narrowing apply the two explicitly.

THE PROOFS are Rocq's, arm for arm.  Rocq's `destruct (…) eqn:H` is
`cases h : …`, which rewrites the goal and leaves hypotheses alone, so each
case opens with one `simp only [h, …] at h ⊢` that puts the same
constructor in both; Rocq's `srw` on the spec side is then not needed,
because the remaining `ite`s and `match`es carry literal conditions and
`exact pure_ok _ _ _` closes them by definitional unfolding.  Rocq's
`inv_ok` on a spec-side `Ok` is the `have h' : Ok … = Ok … := h;
injection h'` step, and its `discriminate` is `cases h'` on the
constructor mismatch.  `check_ret_only_ok_iff` and
`check_ret_only_no_unmodeled` are `Checks/Sys/Prelude.lean`'s.

WHAT THIS FILE HOLDS, AND WHAT WAITS.  The checker, its soundness and
completeness lemmas, the witness with its proof and the frame lemma need
only the two preludes and the spec, and are here.  The rest of the Rocq surface for this syscall is
the registration step of the ticket that adds the arm, and cannot be here:

- the arm `arm_fcntl`, its `checked_table` row and its `arm_unfold`
  lemmas are a `CheckedArm` value (`Checks/Sys/Dispatch.v`; the Lean
  record is `Checks/Sys/Dispatch.lean`'s) and go in `Checks/Sys/Table.lean`
  when the V ticket registers it; that file imports each checker it
  registers, so a checker's file cannot see its own arm;
- the ledger fact the VM invariant's alternation consumes is, in the Lean
  shape, one `arm_fcntl_preserves_vm` theorem and one alternative beside
  the alternation in `Checks/VmMapsDisjoint/Arms.lean` (Rocq's alternation
  names `check_fcntl_frame` directly, `Checks/VmMapsDisjoint.v`).  That
  file imports the table, which imports this file, so importing it back
  is a cycle.  It is DERIVED from `check_fcntl_frame` below, not re-proved;
- the per-arm facts `Checks/Invariants.lean`'s `registry_preserves`
  demands go with the arm too — one `arm_preserves inv arm_fcntl` theorem
  for every invariant that file's registry holds, on the pattern of
  `vm_wf_arm_mmap`, since `inv_arm_uncovered` refuses the registration
  without them; which invariants those are is the registry's to say, not
  this header's.  Each follows from the frame lemma below read through
  the arm: the checker returns the model it was handed, so every
  invariant of that model is an invariant of the result.

The frame lemma is stated here, ahead of the registration that consumes
it, because it depends on nothing but `check_fcntl`, and a lemma provable
where its subject is defined should not wait on a file that cannot import
it; `Checks/Sys/Fs/Sync.lean` states its `check_fsync_frame` the same
way. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- Rocq: `Checks.Sys.Fs.Fcntl.check_fcntl`. -/
def check_fcntl (fd cmd arg : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if bv_eqb cmd F_SETFD then check_ret_only eff (Z_to_bv 64 0) m []
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg then check_ret_only eff (Z_to_bv 64 0) m []
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => check_ret_only eff fl m []
        | none => CheckUnmodeled
      else CheckUnmodeled

/-- Rocq: `Checks.Sys.Fs.Fcntl.check_fcntl_sound_ok`. -/
theorem check_fcntl_sound_ok (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_fcntl fd cmd arg eff m = CheckOk m' evs) :
    fcntl_spec fd cmd arg i m (Ok eff m' evs) := by
  unfold check_fcntl at h
  unfold fcntl_spec
  rw [bind_get_model_iff]
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst heff hm' hevs
    exact pure_ok _ i _
  | some e =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h ⊢
      obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      subst heff hm' hevs
      exact pure_ok _ _ _
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h ⊢
        obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        subst heff hm' hevs
        exact pure_ok _ _ _
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h ⊢
            obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            subst heff hm' hevs
            exact pure_ok _ _ _
          | none =>
            simp only [hgf] at h
            cases h
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          cases h

/-- Rocq: `Checks.Sys.Fs.Fcntl.check_fcntl_sound_unmodeled`. -/
theorem check_fcntl_sound_unmodeled (fd cmd arg : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_fcntl fd cmd arg eff m = CheckUnmodeled) :
    fcntl_spec fd cmd arg i m Unmodeled := by
  unfold check_fcntl at h
  unfold fcntl_spec
  rw [bind_get_model_iff]
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          | none =>
            simp only
            exact unmodeled_intro _ _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro _ _

/-- Rocq: `Checks.Sys.Fs.Fcntl.check_fcntl_complete_ok`. -/
theorem check_fcntl_complete_ok (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : fcntl_spec fd cmd arg i m (Ok eff m' evs)) :
    check_fcntl fd cmd arg eff m = CheckOk m' evs := by
  unfold fcntl_spec at h
  rw [bind_get_model_iff] at h
  unfold check_fcntl
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    have h' : (Ok eff m' evs : outcome SyscallEffect) = Ok (mkEffect (errno_ret EBADF) [] []) m [] := h
    injection h' with heff hm' hevs
    subst heff hm' hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h ⊢
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      injection h' with heff hm' hevs
      subst heff hm' hevs
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h ⊢
        have h' : (Ok eff m' evs : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
        injection h' with heff hm' hevs
        subst heff hm' hevs
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h ⊢
            have h' : (Ok eff m' evs : outcome SyscallEffect) = Ok (mkEffect fl [] []) m [] := h
            injection h' with heff hm' hevs
            subst heff hm' hevs
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          | none =>
            simp only [hgf] at h
            have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
            cases h'
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
          cases h'

/-- Rocq: `Checks.Sys.Fs.Fcntl.check_fcntl_complete_unmodeled`. -/
theorem check_fcntl_complete_unmodeled (fd cmd arg : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : fcntl_spec fd cmd arg i m Unmodeled) :
    check_fcntl fd cmd arg eff m = CheckUnmodeled := by
  unfold fcntl_spec at h
  rw [bind_get_model_iff] at h
  unfold check_fcntl
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EBADF) [] []) m [] := h
    cases h'
  | some e =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
      cases h'
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
        cases h'
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h
            have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect fl [] []) m [] := h
            cases h'
          | none =>
            simp only
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]

/-! ## The witness -/

/-- Rocq: `Checks.Witness.Fs.Fcntl.fcntl_witness`. -/
def fcntl_witness (fd cmd arg : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if bv_eqb cmd F_SETFD then ret_outcome (Z_to_bv 64 0) m
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg then ret_outcome (Z_to_bv 64 0) m
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => ret_outcome fl m
        | none => Unmodeled
      else Unmodeled

/-- Rocq: `Checks.Witness.Fs.Fcntl.fcntl_witness_ok`. -/
theorem fcntl_witness_ok (fd cmd arg : word) (i : SyscallInput) (m : Model) :
    fcntl_spec fd cmd arg i m (fcntl_witness fd cmd arg m) := by
  unfold fcntl_spec fcntl_witness
  rw [bind_get_model_iff]
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only
    exact pure_ok _ i _
  | some e =>
    simp only
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [↓reduceIte]
        exact pure_ok _ i _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [↓reduceIte]
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only
            exact pure_ok _ i _
          | none =>
            simp only
            exact unmodeled_intro _ _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro _ _

/-! ## The frame lemma -/

/-- An accepted `fcntl` leaves the VM ledger where it was: every accepting
arm is a `check_ret_only` that hands back the model it was given, and the
two declining arms accept nothing.  This is the fact the ledger
invariant's alternation consumes for this arm, stated here so that it does
not wait on the alternation's file; Rocq keeps it in `VmMapsDisjoint.v`
under the same name.  Rocq: `VmMapsDisjoint.check_fcntl_frame`. -/
theorem check_fcntl_frame (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_fcntl fd cmd arg eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_fcntl at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | some e =>
    simp only [hfd] at h
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h
      obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h
        obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        rfl
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h
            obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            rfl
          | none =>
            simp only [hgf] at h
            cases h
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          cases h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
