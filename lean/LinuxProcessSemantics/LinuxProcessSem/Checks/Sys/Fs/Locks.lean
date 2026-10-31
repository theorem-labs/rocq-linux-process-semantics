import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Locks — the flock (32) checker, witness, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Locks.v` — the executable
checker `check_flock` and its four proofs — and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Fs/Locks.v` — the progress
witness `flock_witness` and `flock_witness_ok` — and the frame lemma Rocq
states in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
(`check_flock_frame`), which every checker file of this tree carries
beside its checker so that the registration can derive the arm's
`*_preserves` obligation from it.  All answer to the relational spec in
`Sys/Fs/Locks.lean`, which answers to Linux `fs/locks.c`.  Not part of
the trusted specification: the checker's proofs relate it to the spec,
and the proofs are what carry the trust.  This file stops at those
theorems.  The `CheckedArm` built from them, its `checked_table` row and
its `arm_unfold` lemmas are V-Fs-Locks's: a checker ticket owes none of
them since #904 re-cut the C tickets' edges, so that it depends on K1, K5
and its spec alone rather than on the checked-table chain (BRIEF.md, the
CHECK and VERIFY templates).  The pins over what this file computes are
`Checks/Cases/Checks/Sys/Fs/Locks.lean`.

Every kernel claim below is read at Linux v6.18.46 (commit
1f99e9ab748f); the definition-level arguments are on `Sys/Fs/Locks.lean`
and on Rocq's `Locks.flock_spec`, and are not repeated here.  What this
file adds is the ACCEPTOR reading of each arm: which `(effect, model,
events)` triple the checker admits, which it rejects, and where it
declines.

`FdUrandom` is declined by the spec and the checker alike, as Rocq's are
at the baseline (the arm arrived with #794, which is why the baseline is
that commit and not the day's earlier one), and every arm is named rather
than wildcarded so that the build stops here when a constructor is added.
Both matches below are wildcard-free for that reason.

Spellings that differ from Rocq without changing a value: `negb` is `!`,
written `!(flock_cmd_ok_b cmd)` exactly as the spec writes it, so the
checker's `if` and the spec's are the same term; `None`/`Some` are
`none`/`some`.  The proofs do not mirror Rocq's scripts tactic for tactic:
Rocq's `destruct … eqn:` is `cases h : …`, which substitutes in the goal
only (a hypothesis still holds the term and is rewritten by name), and
Rocq's `cbv beta iota` after a rewrite is the `↓reduceIte` simproc or a
`dsimp only`, chosen per arm so that every `simp only` argument is used. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- The flock acceptor.  Rocq: `Locks.check_flock`.

Every modeled answer is a bare return — `check_ret_only`: the effect must
be exactly the return word with every ledger empty, the post-model the
model handed in, and no event — because nothing the model carries moves
on any flock the kernel answers: `SYSCALL_DEFINE2(flock)` (fs/locks.c,
Linux v6.18.46, commit 1f99e9ab748f) writes no user memory, and the lock
it takes or drops lives in the inode's `struct file_lock_context`
(include/linux/filelock.h, Linux v6.18.46), which the model does not
carry.  What each arm RETURNS is the spec's business — `flock_spec`'s
docstring in `Sys/Fs/Locks.lean` argues it arm by arm — and is not
restated here.  The acceptor's pins rest on two arguments that the spec's
docstring does not make, every line of fs/locks.c below read at Linux
v6.18.46.

The `LOCK_UN` arm accepts the 0 on any open descriptor, whatever its
kind, and rejects -EAGAIN: on an unlock `flock_lock_inode`
(fs/locks.c:1074-1144, Linux v6.18.46) walks the inode's flock list
only to drop the caller's own entry (:1101-1109) and leaves at the
`lock_is_unlock` exit (:1111-1115) with `error` still 0 — the
-ENOENT there needs `FL_EXISTS`, which `flock_make_lock` (:465-475)
does not set — and with no lock context answers 0 at :1084-1088.
Other files' locks are walked past, never read into the answer.

A lock request on an open descriptor DECLINES — `CheckUnmodeled`, never
`CheckReject` — whatever its kind and however many openers its path has
(T202).  A sole opener's grant is not certain: `flock_spec`'s header
gives the AFS `LOCK_SH` and the CIFS `LOCK_EX` relock, which a
filesystem with its own `.flock` answers with -EACCES, or under CIFS
without `LOCK_NB` does not answer at all.  On a second opener the
decline has a second reason: the model has no lock table to say what a
conflicting holder makes the kernel answer: `flock_lock_inode`
(fs/locks.c:1074-1144, Linux v6.18.46) returns -EAGAIN at :1121-1123
only when the request lacks `FL_SLEEP`, which `SYSCALL_DEFINE2(flock)`
sets exactly when `LOCK_NB` is clear (fs/locks.c:2170-2172, Linux
v6.18.46); otherwise it defers (:1124-1126) and `flock_lock_inode_wait`
(fs/locks.c:2079-2093, Linux v6.18.46) loops until a later
`flock_lock_inode` grants, 0, or `wait_event_interruptible`
(include/linux/wait.h:501-508, Linux v6.18.46) is interrupted, which
is -ERESTARTSYS (`prepare_to_wait_event`, kernel/sched/wait.c:309,
Linux v6.18.46), never -EINTR inside the kernel.  `flock` returns that
word (fs/locks.c:2179-2182, Linux v6.18.46) into a0, where
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396-463, Linux
v6.18.46) reads it (:407) and restarts the syscall (:417-423) unless a
handler without SA_RESTART is delivered, when a0 becomes -EINTR
(:437-444).  So, on the `locks_lock_file_wait` path a file without an
`.flock` of its own takes (fs/locks.c:2178-2179, Linux v6.18.46), a
conflicting shape shows the process 0 or -EAGAIN under `LOCK_NB`,
and 0 or -EINTR without it; the decline is on the SHAPE, before any
answer is read, and the pins offer every declined shape the 0 and
the -EAGAIN, the probe's `ro_sh` and `wo_ex` modes and their nonblocking
pin shapes the -EACCES, and the two-opener table's blocking `LOCK_EX` and
`LOCK_SH` the -EINTR as well.

The two arguments arrive as 64-bit words but are read as the kernel's
`unsigned int`s (fs/locks.c:2135, Linux v6.18.46): the narrowing is the
dispatcher's — `fd32` and `cmd32` on the `CheckedArm` V-Fs-Locks builds,
as Rocq's `arm_flock` applies them before calling `check_flock`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and as the spec's own
row in `Sys/SyscallTable.lean` applies them before `flock_spec` — so
this checker assumes `fd` and `cmd` already below 2^32 and states
nothing about the upper word. -/
def check_flock (fd cmd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none =>
      if flock_mand_b cmd then CheckUnmodeled
      else if !(flock_cmd_ok_b cmd) then CheckUnmodeled
      else check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if flock_mand_b cmd then CheckUnmodeled
      else if !(flock_cmd_ok_b cmd) then check_ret_only eff (errno_ret EINVAL) m []
      else
        if flock_unlock_b cmd then check_ret_only eff (Z_to_bv 64 0) m []
        else
          match e with
          | .FdFile _ _ => CheckUnmodeled
          | .FdFileW _ _ => CheckUnmodeled
          | .FdFileA _ _ => CheckUnmodeled
          | .FdFileRW _ _ => CheckUnmodeled
          | .FdChannel _ => CheckUnmodeled
          | .FdDir => CheckUnmodeled
          | .FdSocket _ => CheckUnmodeled
          | .FdPipe _ _ => CheckUnmodeled
          | .FdDevNull _ _ => CheckUnmodeled
          | .FdUrandom => CheckUnmodeled

/-! ## Soundness: what the checker accepts, the spec admits

The two cmd-only tests (`flock_mand_b`, `flock_cmd_ok_b`) do not mention the model the bind
introduces, so a `cases` on them settles both the hypothesis and the goal;
`fd_lookup`, which reads `m`, does too, once the model has been bound by
`get_model`.  Each arm names the equation it substitutes, so that the
`simp only` that follows uses every argument it is given. -/

/-- Rocq: `Locks.check_flock_sound_ok`. -/
theorem check_flock_sound_ok (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_flock fd cmd eff m = CheckOk m' evs) :
    flock_spec fd cmd i m (Ok eff m' evs) := by
  unfold check_flock at h
  unfold flock_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | some e =>
  simp only [hfd] at h ⊢
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [hmand, ↓reduceIte, reduceCtorEq] at h
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h ⊢
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases e with
  | FdFile _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileA _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileRW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdChannel c => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDir => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdSocket sk => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdPipe id w => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDevNull rd wr =>
    dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdUrandom => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- Rocq: `Locks.check_flock_sound_unmodeled`. -/
theorem check_flock_sound_unmodeled (fd cmd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_flock fd cmd eff m = CheckUnmodeled) :
    flock_spec fd cmd i m Unmodeled := by
  unfold check_flock at h
  unfold flock_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
    · exact unmodeled_intro i m
    · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · exact unmodeled_intro i m
    · exact unmodeled_intro i m
  | some e =>
  simp only [hfd] at h ⊢
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h ⊢
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases e with
  | FdFile _ _ => exact unmodeled_intro i m
  | FdFileW _ _ => exact unmodeled_intro i m
  | FdFileA _ _ => exact unmodeled_intro i m
  | FdFileRW _ _ => exact unmodeled_intro i m
  | FdChannel c => exact unmodeled_intro i m
  | FdDir => exact unmodeled_intro i m
  | FdSocket sk => exact unmodeled_intro i m
  | FdPipe id w => exact unmodeled_intro i m
  | FdDevNull rd wr => exact unmodeled_intro i m
  | FdUrandom => exact unmodeled_intro i m

/-! ## Completeness: what the spec admits, the checker accepts

The spec is `get_model` followed by a body; `bind_model_inv` strips the
bind, and each modeled arm is a `ret_only`, which `pure_iff` reads as an
equation on the outcome.  The declining arms are `unmodeled`, which
`unmodeled_iff` reads as `o = Unmodeled`, refuting the `Ok` case and
closing the `Unmodeled` one. -/

/-- Rocq: `Locks.check_flock_complete_ok`. -/
theorem check_flock_complete_ok (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : flock_spec fd cmd i m (Ok eff m' evs)) :
    check_flock fd cmd eff m = CheckOk m' evs := by
  unfold flock_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_flock
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
    all_goals first
      | exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
      | unfold err_ret ret_only at h
        rw [pure_iff] at h
        injection h with heff hm' hevs
        subst heff hm' hevs
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
  simp only [hfd] at h ⊢
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [hmand, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h ⊢
    unfold err_ret ret_only at h
    rw [pure_iff] at h
    injection h with heff hm' hevs
    subst heff hm' hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h ⊢
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h ⊢
    unfold ret_only at h
    rw [pure_iff] at h
    injection h with heff hm' hevs
    subst heff hm' hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases e with
  | FdFile _ _ =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileW _ _ =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileA _ _ =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileRW _ _ =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdChannel c =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDir =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdSocket sk =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdPipe id w =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDevNull rd wr =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | FdUrandom =>
    dsimp only at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])

/-- Rocq: `Locks.check_flock_complete_unmodeled`. -/
theorem check_flock_complete_unmodeled (fd cmd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : flock_spec fd cmd i m Unmodeled) :
    check_flock fd cmd eff m = CheckUnmodeled := by
  unfold flock_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_flock
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
    unfold err_ret ret_only at h
    rw [pure_iff] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | some e =>
  simp only [hfd] at h ⊢
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [↓reduceIte]
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h
    unfold err_ret ret_only at h
    rw [pure_iff] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h ⊢
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h
    unfold ret_only at h
    rw [pure_iff] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases e with
  | FdFile _ _ => rfl
  | FdFileW _ _ => rfl
  | FdFileA _ _ => rfl
  | FdFileRW _ _ => rfl
  | FdChannel c => rfl
  | FdDir => rfl
  | FdSocket sk => rfl
  | FdPipe id w => rfl
  | FdDevNull rd wr => rfl
  | FdUrandom => rfl

/-! ## The frame

Rocq states this one in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
beside the other arms' frame lemmas, where
`check_syscall_preserves_vm_wf` consumes it; here it sits with the
checker it is about, as every checker file of this tree places it, and
V-Fs-Locks's `arm_preserves` is derived from it.  Every accepting arm is
a `check_ret_only`, whose `CheckOk` hands back the model it was given,
so the post-model's mappings are the pre-model's; the declining arms
accept nothing.  The script is `check_flock_sound_ok`'s with the goal
side dropped. -/

/-- An accepted flock leaves the mappings alone.  Rocq:
`VmMapsDisjoint.check_flock_frame`. -/
theorem check_flock_frame (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_flock fd cmd eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_flock at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  | some e =>
  simp only [hfd] at h
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [hmand, ↓reduceIte, reduceCtorEq] at h
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h
  cases e with
  | FdFile _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileA _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileRW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdChannel c => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDir => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdSocket sk => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdPipe id w => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDevNull rd wr =>
    dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdUrandom => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-! ## The witness

Rocq: `Checks/Witness/Fs/Locks.v`.  Every modeled arm is deterministic —
the spec draws no errno and chooses nothing — so the witness is the answer
itself, `ret_outcome` where the checker has `check_ret_only`, and
`Unmodeled` on the shapes the spec declines, where the spec admits exactly
that outcome. -/

/-- The one outcome `flock_spec` admits at each input, as data.  Rocq:
`Locks.flock_witness`.  `Checks/Cases/Checks/Sys/Fs/Locks.lean` pins the
outcome per arm and that `check_flock` accepts it. -/
def flock_witness (fd cmd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none =>
      if flock_mand_b cmd then Unmodeled
      else if !(flock_cmd_ok_b cmd) then Unmodeled
      else ret_outcome (errno_ret EBADF) m
  | some e =>
      if flock_mand_b cmd then Unmodeled
      else if !(flock_cmd_ok_b cmd) then ret_outcome (errno_ret EINVAL) m
      else
        if flock_unlock_b cmd then ret_outcome (Z_to_bv 64 0) m
        else
          match e with
          | .FdFile _ _ => Unmodeled
          | .FdFileW _ _ => Unmodeled
          | .FdFileA _ _ => Unmodeled
          | .FdFileRW _ _ => Unmodeled
          | .FdChannel _ => Unmodeled
          | .FdDir => Unmodeled
          | .FdSocket _ => Unmodeled
          | .FdPipe _ _ => Unmodeled
          | .FdDevNull _ _ => Unmodeled
          | .FdUrandom => Unmodeled

/-- The spec admits its witness at every input: `flock` is receptive.
Rocq: `Locks.flock_witness_ok`. -/
theorem flock_witness_ok (fd cmd : word) (i : SyscallInput) (m : Model) :
    flock_spec fd cmd i m (flock_witness fd cmd m) := by
  unfold flock_spec flock_witness
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact pure_ok _ i _ | exact unmodeled_intro i m
  | some e =>
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
  simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases e with
  | FdFile _ _ => exact unmodeled_intro i m
  | FdFileW _ _ => exact unmodeled_intro i m
  | FdFileA _ _ => exact unmodeled_intro i m
  | FdFileRW _ _ => exact unmodeled_intro i m
  | FdChannel c => exact unmodeled_intro i m
  | FdDir => exact unmodeled_intro i m
  | FdSocket sk => exact unmodeled_intro i m
  | FdPipe id w => exact unmodeled_intro i m
  | FdDevNull rd wr => exact unmodeled_intro i m
  | FdUrandom => exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks
