-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Sched/Syscalls.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Witness/Kernel/Sched/Syscalls.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/VmMapsDisjoint.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude


-- The `rocq-baseline` below is the upstream port's own; this file's source
-- of truth is the `Ports` line at the top.
/-! rocq-baseline: 6e7c0d18ddbaa2d453318f0af4665958350a1871 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) checkers and witnesses, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Sched/Syscalls.v` — the
three checkers and their soundness and completeness lemmas — and, in the
same file, `theories/LinuxProcessSem/Checks/Witness/Kernel/Sched/
Syscalls.v` — the three witnesses and their `*_witness_ok` lemmas.  Both
answer to Linux `kernel/sched/syscalls.c` (v6.18.46): this file holds the
checkers and witnesses for the syscalls defined there, and no others.  Not
part of the trusted specification: the checkers and witnesses are
executable, and the lemmas are what carry the trust — each checker lemma
relates its checker to the relational spec in
`Sys/Kernel/Sched/Syscalls.lean` in one direction on one outcome shape,
and each witness lemma says the spec admits the outcome its witness
exhibits, which is what progress is proved from.

WHY TWO ROCQ FILES MEET IN ONE LEAN FILE.  Rocq splits by role: the
checkers in a file `Checks/ExecutableSpecs.v` re-exports, the witnesses in
one `Checks/Progress.v` re-exports.  The Lean tree keeps one file per Rocq
checker file because the arm a registration builds wants both at once —
checker, witness and the five proofs are the fields of one record — and
because the witness half is a few lines that would otherwise sit alone in
a file whose header is longer than its content.  The pins over this file
are in `Checks/Cases/Checks/Sys/Kernel/Sched/Syscalls.lean`, where every
pin in this tree lives.

The arm file registers these checkers and witnesses in the checked table.
The proofs below supply the arm fields.

WHAT ELSE IS HERE.  The frame lemmas, Rocq's
`VmMapsDisjoint.check_sched_getaffinity_frame`,
`check_sched_setscheduler_frame` and `check_sched_yield_frame`: no checker
here moves `m_vmmaps`.  Rocq
states them in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside
the alternation that consumes them, and the C ticket's acceptance text
assigns them to the registration step; this file states them anyway, for
the reason `Checks/Sys/Kernel/Groups.lean` gives for its two: each
depends on nothing but its checker and one prelude lemma, and a lemma
provable where its subject is defined should not wait on a file that
cannot import it.  The arm-level facts the alternation consumes are
DERIVED from them at registration, not re-proved.  They are the section
before the witnesses.

THE BASELINE is 6e7c0d18d, the day-branch commit that added the
`sched_yield` arm, and an ancestor of the day branch, which a twin's
baseline has to be.  It moved from a71fd38a with that arm and accepts
exactly it: the three Rocq definitions this file gained
(`check_sched_yield`, `sched_yield_witness` and the frame lemma) are the
whole of what the two Rocq files this file mirrors, and the Cases file the
pins restate, changed between a71fd38a and 6e7c0d18d.  The older note is
still why a71fd38a was the baseline rather than f44244ad, the commit the
ticket named: f44244ad is not an ancestor — that day's work was
rebase-merged — and everything here read the same at either.
The ancestor rule, and why a day-branch commit fails it once the day
integrates, is `linux-process-semantics@ff0313ba4f:tools/check_lean_spec_parity.py`'s docstring (WHICH
COMMITS SURVIVE THAT TEST).  The `Checks/VmMapsDisjoint.v` the frame
lemmas mirror differs between f44244ad and the tip, in arms that are not
the first two of these: the `sched_getaffinity` and `sched_setscheduler`
lemmas read the same at either.  What it gained between a71fd38a and the baseline is
`check_sched_yield_frame` and the one `erewrite` alternative that consumes
it, and nothing else.

Every definition and every lemma keeps its Rocq name and statement.  The
kernel argument for each branch is on the Sys twin and is not repeated:
the checkers mirror the specs branch for branch, and what a branch means
is said once, where the spec makes the decision.  Spellings that differ
from Rocq without changing a value: `Z.ltb` on `sint32` is the decidable
`<` on `Int`, `negb` is `!`, `orb` is `||`, `option` is `Option`, and the
`cbv iota` steps of the Rocq proofs are `simp only [↓reduceIte]` on the
`if` a `cases` has just decided. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## sched_getaffinity (123) -/

/-- `sched_getaffinity` (123): -EINVAL on a length either gate of
`SYSCALL_DEFINE3(sched_getaffinity)` refuses (kernel/sched/syscalls.c:1335-1338,
Linux v6.18.46), and `CheckUnmodeled` on every length they let through.
Mirrors `sched_getaffinity_spec` branch for branch — read that spec for
why neither `pid` nor `user_mask_ptr` is an argument here either, and for
what the decline costs.
Rocq: `Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity`. -/
def check_sched_getaffinity (len : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if affinity_len_einval_b len then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled

theorem check_sched_getaffinity_sound_ok (len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_sched_getaffinity len eff m = CheckOk m' evs) :
    sched_getaffinity_spec len i m (Ok eff m' evs) := by
  unfold check_sched_getaffinity at h
  unfold sched_getaffinity_spec
  cases hlen : affinity_len_einval_b len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [hlen, ↓reduceIte] at h
    simp only [↓reduceIte]
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _

/-- The one decline is every length the gates let through: the answer
there depends on `nr_cpu_ids` and `cpumask_size()`
(kernel/sched/syscalls.c:1335 and :1345, `SYSCALL_DEFINE3(sched_getaffinity)`,
Linux v6.18.46), which this model does not carry. -/
theorem check_sched_getaffinity_sound_unmodeled (len : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_sched_getaffinity len eff m = CheckUnmodeled) :
    sched_getaffinity_spec len i m Unmodeled := by
  unfold check_sched_getaffinity at h
  unfold sched_getaffinity_spec
  cases hlen : affinity_len_einval_b len
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hlen, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_sched_getaffinity_complete_ok (len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : sched_getaffinity_spec len i m (Ok eff m' evs)) :
    check_sched_getaffinity len eff m = CheckOk m' evs := by
  unfold sched_getaffinity_spec at h
  unfold check_sched_getaffinity
  cases hlen : affinity_len_einval_b len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, unmodeled, reduceCtorEq] at h
  · simp only [hlen, ↓reduceIte, err_ret, ret_only, Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [↓reduceIte]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem check_sched_getaffinity_complete_unmodeled (len : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : sched_getaffinity_spec len i m Unmodeled) :
    check_sched_getaffinity len eff m = CheckUnmodeled := by
  unfold sched_getaffinity_spec at h
  unfold check_sched_getaffinity
  cases hlen : affinity_len_einval_b len
  · rfl
  · simp only [hlen, ↓reduceIte, err_ret, ret_only, Monad.pure, reduceCtorEq] at h

/-! ## sched_setscheduler (119) -/

/-- `sched_setscheduler` (119).  Mirrors `sched_setscheduler_spec` branch
for branch, and shares `sched_setscheduler_answer` with it rather than
transcribing the kernel's ordered chain a second time — read that spec for
the envelope, for what the SCHED_IDLE answer assumes, and for why the model
carries no scheduling state.

The `i` is here for the four bytes at `param`: the `copy_from_user` of
`do_sched_setscheduler` (kernel/sched/syscalls.c:887-888, Linux v6.18.46)
runs before the task lookup (:890), so its ledger rides on every path past
it.
Rocq: `Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler`. -/
def check_sched_setscheduler (i : SyscallInput) (pid policy param : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if decide (sint32 policy < 0) then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 param || decide (sint32 pid < 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else
    match read_bytes_map i.in_mem param (Z_to_bv 64 4) with
    | none =>
        if !(access_okb param 4) then check_ret_only eff (errno_ret EFAULT) m []
        else CheckUnmodeled
    | some bs =>
        if !(sched_targets_self_b pid m) then CheckUnmodeled
        else
          match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                  (bv_unsigned (le_bytes_to_word bs)) with
          | some r => check_ret_only_copyins [(param, 4)] eff r m []
          | none => CheckUnmodeled

/-! ### Crossing the negative-policy gate

The gate is `decide (sint32 policy < 0)`, and reducing it against a
symbolic `policy` exceeds the recursion limit: `sint32` opens into a
comparison and a subtraction against `2 ^ 31` and `2 ^ 32`
(`Sys/Syscall.lean`), and `Int.decLt` sends those literals into `Nat.sub`'s
structural recursion.  The second gate is safe, for the reason upstream's
Lean was safe by accident: `w_is0 param || decide (sint32 pid < 0)` has
`Bool.or` at the head and stops at once on the symbolic `w_is0`.  The first
gate has nothing in front of the `decide`, so anything that asks for its
value pays — `by_cases` on the `Prop` under the `decide` among them,
because the elaborator reduces the goal through the gate to find its head,
and `Lean.Linter.constructorNameAsVariable`, which runs `whnf` on the type
of every bound variable it sees and so walks into the gate of
`check_sched_setscheduler_complete_ok` and
`check_sched_setscheduler_complete_unmodeled`, whose hypothesis IS the
spec, before a tactic runs at all.

The attribute below stops every one of those at the root, which is the
reading and not the gate.  No proof in this file evaluates a signed
reading: each crosses both gates from a hypothesis, by `simp only` keyed on
it, which is the discipline the header of
`Checks/Sys/Kernel/Time/PosixTimers.lean` states for the recorded-clock
gate.  The attribute is `local`, so the pins in `Checks/Cases/`, which DO
evaluate closed readings, are untouched.  It changes no definition: the
gate still reads `decide (sint32 policy < 0)`, still comes first, and still
answers what it answered. -/

attribute [local irreducible] sint32

theorem check_sched_setscheduler_sound_ok (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_sched_setscheduler i pid policy param eff m = CheckOk m' evs) :
    sched_setscheduler_spec pid policy param i m (Ok eff m' evs) := by
  unfold check_sched_setscheduler at h
  unfold sched_setscheduler_spec
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
      try dsimp only
      refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
      try dsimp only
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | some bs =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hself : sched_targets_self_b pid m
        · simp only [hself, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hans : sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at h
            dsimp only at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            exact record_copyins_ok_empty _ _ i _ _ _ [] rfl (pure_ok _ i _)
          | none =>
            rw [hans] at h
            dsimp only at h
            exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [hearly, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

theorem check_sched_setscheduler_sound_unmodeled (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_sched_setscheduler i pid policy param eff m = CheckUnmodeled) :
    sched_setscheduler_spec pid policy param i m Unmodeled := by
  unfold check_sched_setscheduler at h
  unfold sched_setscheduler_spec
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte] at h ⊢
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
      try dsimp only
      refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
      try dsimp only
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro i m
      | some bs =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hself : sched_targets_self_b pid m
        · simp only [Bool.not_false, ↓reduceIte]
          exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hans : sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at h
            dsimp only at h
            exact absurd h (check_ret_only_copyins_no_unmodeled [(param, 4)] eff r m [])
          | none =>
            dsimp only
            exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    · simp only [hearly, ↓reduceIte] at h ⊢
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

theorem check_sched_setscheduler_complete_ok (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : sched_setscheduler_spec pid policy param i m (Ok eff m' evs)) :
    check_sched_setscheduler i pid policy param eff m = CheckOk m' evs := by
  unfold check_sched_setscheduler
  unfold sched_setscheduler_spec at h
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := bind_input_model_inv _ i m _ h
      try dsimp only at h
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, Monad.pure,
            outcome.Ok.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unmodeled,
            reduceCtorEq] at h
      | some bs =>
        rw [hread] at h
        dsimp only at h ⊢
        obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
        cases hself : sched_targets_self_b pid m
        · simp only [hself, Bool.not_false, ↓reduceIte, unmodeled, reduceCtorEq] at hcore
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
          cases hans : sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at hcore
            simp only [ret_only, Monad.pure, outcome.Ok.injEq] at hcore
            obtain ⟨rfl, rfl, rfl⟩ := hcore
            dsimp only
            exact check_ret_only_copyins_refl [(param, 4)] r _ []
          | none =>
            rw [hans] at hcore
            simp only [unmodeled, reduceCtorEq] at hcore
    · simp only [hearly, ↓reduceIte] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem check_sched_setscheduler_complete_unmodeled (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m : Model)
    (h : sched_setscheduler_spec pid policy param i m Unmodeled) :
    check_sched_setscheduler i pid policy param eff m = CheckUnmodeled := by
  unfold check_sched_setscheduler
  unfold sched_setscheduler_spec at h
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte] at h ⊢
    simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := bind_input_model_inv _ i m _ h
      try dsimp only at h
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h ⊢
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, Monad.pure,
            reduceCtorEq] at h
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      | some bs =>
        rw [hread] at h
        dsimp only at h ⊢
        have hcore := record_copyins_unmodeled_inv _ _ i m h
        cases hself : sched_targets_self_b pid m
        · simp only [Bool.not_false, ↓reduceIte]
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
          cases hans : sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at hcore
            simp only [ret_only, Monad.pure, reduceCtorEq] at hcore
          | none => rfl
    · simp only [hearly, ↓reduceIte] at h ⊢
      simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h

/-! ## The witnesses

One outcome each spec admits on every input and model, or `Unmodeled`
where it admits none; `*_witness_ok` is the proof, and is what progress
is proved from once the arm is registered.  Mirrors
`theories/LinuxProcessSem/Checks/Witness/Kernel/Sched/Syscalls.v`
definition for definition. -/

/-! ### The frame lemmas

Rocq keeps every arm's frame lemma inside
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, next to the alternation
that uses it; the header says why these two are here instead, and what
the registration step derives from them.

The argument is the trivial one: neither checker builds a model.  Every
`CheckOk` either checker returns is a `check_ret_only` or
`check_ret_only_copyins` verdict, and the middle conjunct of each `_ok_iff`
says the model handed back is the one handed in, so `m_vmmaps m'` is
`m_vmmaps m` by substitution; the `CheckUnmodeled` and `CheckReject`
branches never reach a `CheckOk` and are closed by the constructor
mismatch. -/

/-- sched_getaffinity answers an errno or declines; it never reaches user
memory, let alone the mappings.
Rocq: `VmMapsDisjoint.check_sched_getaffinity_frame`. -/
theorem check_sched_getaffinity_frame (len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_sched_getaffinity len eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_sched_getaffinity at h
  cases hlen : affinity_len_einval_b len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [hlen, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl

/-- sched_setscheduler answers an errno or a 0 that changes no model state
at all, or declines.  It READS four bytes of user memory and writes none,
so it cannot reach the mappings either.
Rocq: `VmMapsDisjoint.check_sched_setscheduler_frame`. -/
theorem check_sched_setscheduler_frame (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_sched_setscheduler i pid policy param eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_sched_setscheduler at h
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          rfl
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | some bs =>
        rw [hread] at h
        dsimp only at h
        cases hself : sched_targets_self_b pid m
        · simp only [hself, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hans : sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at h
            dsimp only at h
            obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            rfl
          | none =>
            rw [hans] at h
            dsimp only at h
            exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [hearly, ↓reduceIte] at h
      obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl

/-! ### The sched_getaffinity witness -/

/-- `sched_getaffinity` (123) is deterministic on both branches, so the
witness is the branch itself: the -EINVAL, or the `Unmodeled` every length
the two gates of `SYSCALL_DEFINE3(sched_getaffinity)`
(kernel/sched/syscalls.c:1335-1338, Linux v6.18.46) let through answers.
Failing closed is an admissible outcome, which is what makes progress hold
on the second.
Rocq: `Checks.Witness.Kernel.Sched.Syscalls.sched_getaffinity_witness`. -/
def sched_getaffinity_witness (len : word) (m : Model) : outcome SyscallEffect :=
  if affinity_len_einval_b len then ret_outcome (errno_ret EINVAL) m else Unmodeled

theorem sched_getaffinity_witness_ok (len : word) (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec len i m (sched_getaffinity_witness len m) := by
  unfold sched_getaffinity_spec sched_getaffinity_witness
  cases affinity_len_einval_b len
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [↓reduceIte]
    exact pure_ok _ i m

/-! ### The sched_setscheduler witness -/

/-- The witness follows the spec's decisions without drawing a value or changing model state.
`SYSCALL_DEFINE3(sched_setscheduler)` refuses a negative policy
(kernel/sched/syscalls.c:962-968, Linux v6.18.46) and `do_sched_setscheduler`
refuses a NULL `param` or a negative pid (:885-886), both before the copy,
so those two witnesses are the -EINVAL with an empty ledger.
Linux copies four bytes before the task lookup in `do_sched_setscheduler` (:887-892).
Every witness answer after that copy carries its ledger.
The `Unmodeled` outcome supplies the progress witness for each decline.
Rocq: `Checks.Witness.Kernel.Sched.Syscalls.sched_setscheduler_witness`. -/
def sched_setscheduler_witness (pid policy param : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if decide (sint32 policy < 0) then ret_outcome (errno_ret EINVAL) m
  else if w_is0 param || decide (sint32 pid < 0) then ret_outcome (errno_ret EINVAL) m
  else
    match read_bytes_map i.in_mem param (Z_to_bv 64 4) with
    | none =>
        if !(access_okb param 4) then ret_outcome (errno_ret EFAULT) m
        else Unmodeled
    | some bs =>
        if !(sched_targets_self_b pid m) then Unmodeled
        else
          match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                  (bv_unsigned (le_bytes_to_word bs)) with
          | some r => Ok (with_copyins [(param, 4)] (mkEffect r [] [])) m []
          | none => Unmodeled

theorem sched_setscheduler_witness_ok (i : SyscallInput) (pid policy param : word) (m : Model) :
    sched_setscheduler_spec pid policy param i m
      (sched_setscheduler_witness pid policy param i m) := by
  unfold sched_setscheduler_spec sched_setscheduler_witness
  by_cases hpolneg : sint32 policy < 0
  · simp only [hpolneg, decide_true, ↓reduceIte]
    exact pure_ok _ i m
  · simp only [hpolneg, decide_false, Bool.false_eq_true, ↓reduceIte]
    cases hearly : (w_is0 param || decide (sint32 pid < 0))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine bind_step _ _ i m i m _ (input_ok i m) ?_
      try dsimp only
      refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
      try dsimp only
      cases read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        dsimp only
        cases access_okb param 4
        · simp only [Bool.not_false, ↓reduceIte]
          exact pure_ok _ i m
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro i m
      | some bs =>
        dsimp only
        cases sched_targets_self_b pid m
        · simp only [Bool.not_false, ↓reduceIte]
          exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
              (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            dsimp only
            exact record_copyins_ok_empty _ _ i m _ m [] rfl (pure_ok _ i m)
          | none =>
            dsimp only
            exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    · simp only [↓reduceIte]
      exact pure_ok _ i m

/-! ## sched_yield (124)

The whole of it: the checker, its four obligations, the frame lemma and
the witness.  This is the one arm here with no fail-closed branch at all,
which is what the two `_unmodeled` obligations come to — `sound_unmodeled`
is vacuous because `check_ret_only` never answers `CheckUnmodeled`, and
`complete_unmodeled` is vacuous because the spec is a bare `ret_only`
that is never `Unmodeled`.  Neither is padding: they are the fields the
record wants, and a reader who expects a decline somewhere is told here
that there is none. -/

/-- `sched_yield` (124): 0, no writes, no state change, no events, and
nothing else admitted.  Mirrors
`Kernel.Sched.Syscalls.sched_yield_spec`, which carries the reading of
`SYSCALL_DEFINE0(sched_yield)` — above all why ignoring every argument
word is exact here rather than an approximation.  Rocq:
`Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield`. -/
def check_sched_yield (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only eff (Z_to_bv 64 0) m []

/-- Rocq: `Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_sound_ok`. -/
theorem check_sched_yield_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_sched_yield eff m = CheckOk m' evs) :
    sched_yield_spec i m (Ok eff m' evs) := by
  unfold check_sched_yield at h
  unfold sched_yield_spec
  rw [check_ret_only_ok_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact pure_ok _ i _

/-- Vacuously: the checker never declines, so there is no answer to carry
over.  Rocq:
`Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_sound_unmodeled`. -/
theorem check_sched_yield_sound_unmodeled (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_sched_yield eff m = CheckUnmodeled) :
    sched_yield_spec i m Unmodeled := by
  unfold check_sched_yield at h
  exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_complete_ok`. -/
theorem check_sched_yield_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : sched_yield_spec i m (Ok eff m' evs)) :
    check_sched_yield eff m = CheckOk m' evs := by
  unfold sched_yield_spec at h
  unfold check_sched_yield
  have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
  cases h'
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The spec has no `Unmodeled` outcome either, so this side is the one
that says so: the hypothesis is the impossibility.  Rocq:
`Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_complete_unmodeled`. -/
theorem check_sched_yield_complete_unmodeled (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : sched_yield_spec i m Unmodeled) :
    check_sched_yield eff m = CheckUnmodeled := by
  unfold sched_yield_spec at h
  have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
  cases h'

/-- Rocq: `VmMapsDisjoint.check_sched_yield_frame`.  The checker hands
back the model it was given, so the mappings are the same list. -/
theorem check_sched_yield_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_sched_yield eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_sched_yield at h
  rw [check_ret_only_ok_iff] at h
  obtain ⟨-, rfl, -⟩ := h
  rfl

/-- `sched_yield` (124) has one outcome and no branch at all, so the
witness is that outcome.  It is the only witness here that is never
`Unmodeled`: the spec has no fail-closed branch to exhibit.  Rocq:
`Checks.Witness.Kernel.Sched.Syscalls.sched_yield_witness`. -/
def sched_yield_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) m

/-- Rocq: `Checks.Witness.Kernel.Sched.Syscalls.sched_yield_witness_ok`. -/
theorem sched_yield_witness_ok (i : SyscallInput) (m : Model) :
    sched_yield_spec i m (sched_yield_witness m) := by
  unfold sched_yield_spec sched_yield_witness
  exact pure_ok _ i _

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls
