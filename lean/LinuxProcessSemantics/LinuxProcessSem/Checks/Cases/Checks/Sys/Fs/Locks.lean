-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Locks.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Locks

/-! # Checks.Cases.Checks.Sys.Fs.Locks — the flock checker, exercised

Pins over `Checks.Sys.Fs.Locks`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Locks.v` and
`theories/LinuxProcessSem/Checks/Witness/Fs/Locks.v`.  Not part of the
trusted specification.

WHAT IS UNDER TEST is the ACCEPTOR, not the spec: `Checks/Cases/Fs/Locks.lean`
already reads `flock_spec` off `fs/locks.c` at every arm, and the four
proofs in the checker's file tie `check_flock` to that spec at every
input.  What those proofs cannot say is which concrete answer the checker
gives — a checker that accepted everything and a spec that admitted
everything would satisfy all four — so each pin here offers the checker
one concrete effect and pins the verdict: `CheckOk` with the model handed
back and no event, `CheckReject`, or `CheckUnmodeled`.  Every accepting
pin is paired with the rejection of a different return, so that "the
model accepts this" is not the vacuous reading of a checker that accepts
everything. Rocq's
`theories/LinuxProcessSem/Checks/Cases/Fs/Locks.v` provides the matching
examples. `Checks/Cases/Fs/Locks.lean` carries their cases register and
spec pins; the acceptor-level twins are here, with dispatcher-level pins
in `V_Fs_Locks` below.  Rocq's
`flock_every_file_kind_counts_as_an_opener` is covered here arm by arm:
a sole opener of each file kind is accepted at 0, and a second
descriptor on the same name declines;
`Checks/Cases/Fs/Locks.lean` pins the same answers on the spec.

The fixtures are `Checks/Cases/Fs/Locks.lean`'s, imported rather than
copied, so that the spec pins and the checker pins read the same tables.
Every ground pin is `rfl`: the checker is executable and the inputs are
literals.  The two lemmas of `Witness` that quantify over the input
compose the checker's own theorems instead.  Every kernel line is read at
Linux v6.18.46 (commit 1f99e9ab748f); the citations are the ones the spec
pins carry for the same arm, and the claim each pin adds is about the
checker's answer. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Locks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Locks

section SuccessIsInert

/-! ## Success is inert

Rocq: `flock_success_is_inert`.  A probe sees only the 0.  That the
descriptors' offsets and the files' contents came back UNCHANGED, and
that no event was emitted, is a statement about the model's own state,
and the `CheckOk flock_model []` below is the whole of it: the accepted
post-model is the SAME model, and the event list is empty. -/

/-- The sole opener of "g" is accepted at 0: the lock's owner is the
`struct file`, so a sole opener has nothing to conflict with.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_opener_accepts_zero :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and the -EAGAIN of a conflicting holder is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_opener_rejects_eagain :
    check_flock 4 2 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- LOCK_UN on a directory reference: 0 without consulting the fd kind.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_dir_is_inert :
    check_flock 5 8 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and `LOCK_UN` is an operation `flock_translate_cmd` recognizes, so
-EINVAL is refused there.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_un_on_dir_rejects_einval :
    check_flock 5 8 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- `LOCK_MAND` is answered 0 before the descriptor is resolved.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_on_open_fd_is_zero :
    check_flock 1 32 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and -EBADF is refused on it.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_on_open_fd_rejects_ebadf :
    check_flock 1 32 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

end SuccessIsInert

section OrderIsBehavior

/-! ## The order of the checks, at the acceptor

The versioned command-order argument is on the spec's closed-fd arm. -/

/-- An unrecognized operation on the open fd 1 is -EINVAL:
`flock_translate_cmd` falls off its `switch`, which every ordering
reaches once the lookup has found the fd.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_bad_op_on_open_fd_is_einval :
    check_flock 1 0 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] :=
  rfl

/-- …and -EBADF, the closed-descriptor answer, is refused on it.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_bad_op_on_open_fd_rejects_ebadf :
    check_flock 1 0 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- A recognized operation on a closed fd is -EBADF, from `fd_empty`.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ex_on_closed_fd_is_ebadf :
    check_flock 9999 2 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckOk flock_model [] :=
  rfl

/-- A closed descriptor cannot be locked: the lie no kernel tells, and
the negative that shows the -EBADF arm is not "accept anything".
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ex_on_closed_fd_rejects_success :
    check_flock 9999 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_UN` on a closed fd is -EBADF: the `fd_empty` test
(include/linux/file.h:45, Linux v6.18.46) that `flock` makes right after
the lookup (fs/locks.c:2158-2159, Linux v6.18.46) fires before the
`type != F_UNLCK` test at fs/locks.c:2161 could skip anything, so the
acceptor's unlock arm sits behind the lookup.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_un_on_closed_fd_is_ebadf :
    check_flock 9999 8 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and the 0 an acceptor testing the unlock before the lookup would take
is refused.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_un_on_closed_fd_rejects_success :
    check_flock 9999 8 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- Every unrecognized word on a closed fd is -EINVAL, not operation 0
alone: `LOCK_SH|LOCK_EX` is translated before the lookup, so the -EBADF
of the lookup is refused.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- combinedclosed
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_combined_op_on_closed_fd_is_einval :
    check_flock 9999 3 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 9999 3 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject ∧
    check_flock 9999 3 (mkEffect (errno_ret EBADF) [] []) flock_model ≠ CheckOk flock_model [] := by
  refine ⟨rfl, rfl, ?_⟩
  intro h; cases h

/-- `LOCK_UN|LOCK_EX` on a closed fd: the same, -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_unlock_ex_on_closed_fd_is_einval :
    check_flock 9999 10 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 9999 10 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- `LOCK_EX` with bit 31 set on a closed fd: unrecognized whole, so
-EINVAL.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- highcmdclosed
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_sign_bit_op_on_closed_fd_is_einval :
    check_flock 9999 0x80000002 (mkEffect (errno_ret EINVAL) [] []) flock_model
      = CheckOk flock_model [] ∧
    check_flock 9999 0x80000002 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject ∧
    check_flock 9999 0x80000002 (mkEffect (errno_ret EBADF) [] []) flock_model ≠ CheckOk flock_model [] := by
  refine ⟨rfl, rfl, ?_⟩
  intro h; cases h

/-- `LOCK_NB` changes no answer: the nonblocking take on the sole opener
is accepted at 0.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_nb_on_sole_opener_accepts_zero :
    check_flock 4 6 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and -EINVAL is refused there: the word is recognized.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_ex_nb_on_sole_opener_rejects_einval :
    check_flock 4 6 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_ex_nb_on_sole_opener_rejects_einval_on_unlock :
    check_flock 4 12 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- `LOCK_NB` ALONE is no operation: stripping it leaves 0, which
`flock_translate_cmd` does not recognize, so the answer is -EINVAL on an
open descriptor too.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_nb_alone_is_einval :
    check_flock 3 4 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and a kernel granting a lock for the bare modifier is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_nb_alone_rejects_success :
    check_flock 3 4 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_SH | LOCK_EX` is not one of the three cases of the switch: -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_sh_and_ex_is_einval :
    check_flock 3 3 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and a kernel granting the two-bit word a lock is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_sh_and_ex_rejects_success :
    check_flock 3 3 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_MAND | LOCK_UN` carries the bit, so it is 0 before anything
else is read.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_with_un_is_zero :
    check_flock 3 40 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_with_un_rejects_einval :
    check_flock 3 40 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- Bit 31 survives the `unsigned int` narrowing; `flock_translate_cmd`
takes an `int`, sees a negative word that is none of the three cases, and
answers -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_high_bit_operation_is_einval :
    check_flock 3 0x80000000 (mkEffect (errno_ret EINVAL) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and a grant for it is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_high_bit_operation_rejects_success :
    check_flock 3 0x80000000 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- The sole opener of "f" is accepted at 0 for a shared request too.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_opener_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and its -EAGAIN is refused.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- The grant is a bare return: a write beside the 0 is refused.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_effect_with_a_write_rejected :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [(0x10000, [0])] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_effect_with_a_write_rejected_on_unlock :
    check_flock 4 8 (mkEffect (Z_to_bv 64 0) [(0x10000, [0])] []) flock_model = CheckReject := rfl

/-- …and so is a zero-filled range.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_effect_with_a_zero_range_rejected :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] [(0x10000, 16)]) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_effect_with_a_zero_range_rejected_on_unlock :
    check_flock 4 8 (mkEffect (Z_to_bv 64 0) [] [(0x10000, 16)]) flock_model = CheckReject := rfl

/-- …and so is a copy-in: `flock` reads no user memory.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_effect_with_a_copyin_rejected :
    check_flock 4 2 (with_copyins [(0x10000, 4)] (mkEffect (Z_to_bv 64 0) [] [])) flock_model
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_effect_with_a_copyin_rejected_on_unlock :
    check_flock 4 8 (with_copyins [(0x10000, 4)] (mkEffect (Z_to_bv 64 0) [] [])) flock_model
      = CheckReject := rfl

/-- `LOCK_UN` on a file this process never locked is 0, not -ENOENT: the
-ENOENT of `flock_lock_inode` (fs/locks.c:1087 with no lock context,
:1112 with one and no entry found, Linux v6.18.46) needs `FL_EXISTS`,
and `flock_make_lock` ASSIGNS `FL_FLOCK` to the flags (:472) — the only
later change on the syscall's path is `|= FL_SLEEP` (:2172).  `FL_EXISTS`
is set by lockd, nfs4, dlm and ceph alone, each of which maps the
-ENOENT back to 0 itself.
kernel: fs/locks.c:flock,flock_make_lock,flock_lock_inode@v6.18.46 -/
theorem flock_un_never_taken_rejects_enoent :
    check_flock 3 8 (mkEffect (errno_ret ENOENT) [] []) flock_model = CheckReject := rfl

/-- …and on a closed fd the -EBADF arm refuses -ENOENT as it refuses 0:
no arm of the acceptor answers that errno.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_closed_fd_rejects_enoent :
    check_flock 9999 2 (mkEffect (errno_ret ENOENT) [] []) flock_model = CheckReject := rfl

/-- The nonblocking take on the sole opener refuses -EAGAIN as well.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_ex_nb_on_sole_opener_rejects_eagain :
    check_flock 4 6 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_ex_nb_on_sole_opener_rejects_eagain_on_unlock :
    check_flock 4 12 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- The nonblocking shared take on the sole opener is accepted at 0.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sh_nb_on_sole_opener_accepts_zero :
    check_flock 3 5 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and refuses -EAGAIN.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sh_nb_on_sole_opener_rejects_eagain :
    check_flock 3 5 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sh_nb_on_sole_opener_rejects_eagain_on_unlock :
    check_flock 3 12 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject := rfl

end OrderIsBehavior

section EveryArmIsRetOnly

/-! ## Every accepting arm is `check_ret_only`, on every ledger

`SYSCALL_DEFINE2(flock)` (fs/locks.c:2135-
2183, Linux v6.18.46) reads and writes no user memory on any path, and
neither maps nor unmaps anything. -/

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_arm_rejects_a_write :
    check_flock 1 32 (mkEffect (Z_to_bv 64 0) [(0x10000, [0])] []) flock_model = CheckReject :=
  rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_arm_rejects_a_copyin :
    check_flock 1 32 (with_copyins [(0x10000, 4)] (mkEffect (Z_to_bv 64 0) [] [])) flock_model
      = CheckReject := rfl

/-- The -EINVAL arm with a write beside its errno.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_einval_arm_rejects_a_write :
    check_flock 1 0 (mkEffect (errno_ret EINVAL) [(0x10000, [0])] []) flock_model = CheckReject :=
  rfl

/-- …and with a zero-filled range.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_einval_arm_rejects_a_zero_range :
    check_flock 1 0 (mkEffect (errno_ret EINVAL) [] [(0x10000, 16)]) flock_model = CheckReject :=
  rfl

/-- The -EBADF arm with a write beside its errno.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ebadf_arm_rejects_a_write :
    check_flock 9999 2 (mkEffect (errno_ret EBADF) [(0x10000, [0])] []) flock_model = CheckReject :=
  rfl

/-- …with an unmapped range.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ebadf_arm_rejects_an_unmap :
    check_flock 9999 2 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(0x10000, 4096)] [] [])
      flock_model = CheckReject := rfl

/-- …and with a copy.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ebadf_arm_rejects_a_copy :
    check_flock 9999 2
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 0x10000 0x11000 16] [])
      flock_model = CheckReject := rfl

/-- The unlock arm, on the directory, with a write beside its 0.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_arm_rejects_a_write :
    check_flock 5 8 (mkEffect (Z_to_bv 64 0) [(0x10000, [0])] []) flock_model = CheckReject := rfl

/-- …and with a copy-in.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_arm_rejects_a_copyin :
    check_flock 5 8 (with_copyins [(0x10000, 4)] (mkEffect (Z_to_bv 64 0) [] [])) flock_model
      = CheckReject := rfl

/-- The grant arm maps nothing: an unmap beside its 0 is refused.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_grant_rejects_an_unmap :
    check_flock 4 2 (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(0x10000, 4096)] [] [])
      flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_grant_rejects_an_unmap_on_unlock :
    check_flock 4 8 (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(0x10000, 4096)] [] [])
      flock_model = CheckReject := rfl

/-- …and copies nothing.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_grant_rejects_a_copy :
    check_flock 4 2
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [MemCopy.mkCopy 0x10000 0x11000 16] [])
      flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_grant_rejects_a_copy_on_unlock :
    check_flock 4 8
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [MemCopy.mkCopy 0x10000 0x11000 16] [])
      flock_model = CheckReject := rfl

end EveryArmIsRetOnly

section ReturnIsTheFullWord

/-! ## The return is compared as the whole 64-bit word

`errno_ret e` is `Z_to_bv 64 (-e)`, the two's complement of the errno in
all 64 bits, which is what a riscv64 kernel leaves in `a0`: the arm's
`int` return (`return -EBADF`, `return type`) becomes the `long` of the
`__do_sys_flock` wrapper `SYSCALL_DEFINE2` expands to
(`__SYSCALL_DEFINEx`, include/linux/syscalls.h:257-264, Linux v6.18.46)
and is stored whole (`syscall_handler`, arch/riscv/include/asm/syscall.h,
Linux v6.18.46).  A tracer or a lying kernel handing back the errno as a
zero-extended 32-bit word, or a 0 with a stray upper word, is refused:
`bv_eqb` reads all 64 bits, and a checker comparing the low 32 would
accept every one of these. -/

/-- -EBADF as a 32-bit word (0xFFFFFFF7) is not -EBADF.
kernel: fs/locks.c:flock; include/linux/syscalls.h:__SYSCALL_DEFINEx@v6.18.46 -/
theorem flock_ebadf_as_a_32_bit_word_is_rejected :
    check_flock 9999 2 (mkEffect (Z_to_bv 64 0xFFFFFFF7) [] []) flock_model = CheckReject := rfl

/-- -EINVAL as a 32-bit word (0xFFFFFFEA) is not -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd; include/linux/syscalls.h:__SYSCALL_DEFINEx@v6.18.46 -/
theorem flock_einval_as_a_32_bit_word_is_rejected :
    check_flock 1 0 (mkEffect (Z_to_bv 64 0xFFFFFFEA) [] []) flock_model = CheckReject := rfl

/-- A 0 with a stray upper word is not the 0 the grant arm takes.
kernel: fs/locks.c:flock; include/linux/syscalls.h:__SYSCALL_DEFINEx@v6.18.46 -/
theorem flock_success_with_an_upper_word_is_rejected :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0x100000000) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_success_with_an_upper_word_is_rejected_on_unlock :
    check_flock 4 8 (mkEffect (Z_to_bv 64 0x100000000) [] []) flock_model = CheckReject := rfl

/-- -EAGAIN as a 32-bit word is refused on the grant arm as well.
kernel: fs/locks.c:flock; include/linux/syscalls.h:__SYSCALL_DEFINEx@v6.18.46 -/
theorem flock_eagain_as_a_32_bit_word_is_rejected :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0xFFFFFFF5) [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_eagain_as_a_32_bit_word_is_rejected_on_unlock :
    check_flock 4 8 (mkEffect (Z_to_bv 64 0xFFFFFFF5) [] []) flock_model = CheckReject := rfl

end ReturnIsTheFullWord

section TheModelComesBackWhole

/-! ## The model handed back is the model handed in, mappings included

`CheckOk flock_model []` in every accepting pin says the post-model is the
pre-model — but every fixture of `Checks/Cases/Fs/Locks.lean` carries an
EMPTY mapping list, so a checker that handed back the model with its
mappings dropped would hand back a model equal to the fixture, and every
pin above would still close.  The frame lemma `check_flock_frame` is
what refuses that checker with proofs kept; these pins refuse it with
the pins alone, on a fixture that has a mapping to lose.  Kernel side:
`flock` maps and unmaps nothing (`SYSCALL_DEFINE2(flock)`,
fs/locks.c:2135-2183, Linux v6.18.46). -/

/-- `flock_model` with one anonymous mapping recorded. -/
def flock_mapped_model : Model :=
  { flock_model with
    m_vm := { flock_model.m_vm with
      vmst_maps := { flock_model.m_vm.vmst_maps with vm_maps := [(0x10000, 4096)] } } }

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_arm_keeps_the_mapping :
    check_flock 1 32 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model
      = CheckOk flock_mapped_model [] := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_arm_on_mapped_model_rejects_ebadf :
    check_flock 1 32 (mkEffect (errno_ret EBADF) [] []) flock_mapped_model = CheckReject := rfl

/-- So does the unlock arm.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_arm_keeps_the_mapping :
    check_flock 5 8 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model
      = CheckOk flock_mapped_model [] := rfl

/-- …and refuses -EINVAL, the answer to a word `flock_translate_cmd`
(fs/locks.c:452-462, Linux v6.18.46) does not recognize: `LOCK_UN` is one
it does, on the mapped fixture as on the bare one.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_un_arm_on_mapped_model_rejects_einval :
    check_flock 5 8 (mkEffect (errno_ret EINVAL) [] []) flock_mapped_model = CheckReject := rfl

/-- The grant arm keeps the mapping too.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_lock_on_mapped_model_keeps_the_mapping :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model
      = CheckOk flock_mapped_model [] := rfl

/-- …and refuses -EAGAIN on the sole opener there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_grant_on_mapped_model_rejects_eagain :
    check_flock 4 2 (mkEffect (errno_ret EAGAIN) [] []) flock_mapped_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_grant_on_mapped_model_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) flock_mapped_model = CheckReject := rfl

/-- …and the -EBADF arm.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ebadf_arm_keeps_the_mapping :
    check_flock 9999 2 (mkEffect (errno_ret EBADF) [] []) flock_mapped_model
      = CheckOk flock_mapped_model [] := rfl

/-- …and refuses a grant on the closed fd there.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ebadf_arm_on_mapped_model_rejects_success :
    check_flock 9999 2 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model = CheckReject := rfl

/-- The accepted post-model is the one handed in, mapping included: the
bare fixture is not it.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_grant_does_not_hand_back_another_model :
    ¬ (check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model
        = CheckOk flock_model []) := by
  intro h
  change CheckOk flock_mapped_model [] = CheckOk flock_model [] at h
  injection h with hm _
  have hmaps := congrArg (fun m => (m_vmmaps m).vm_maps) hm
  exact List.cons_ne_nil _ _ hmaps

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_grant_does_not_hand_back_another_model_on_unlock :
    ¬ (check_flock 4 8 (mkEffect (Z_to_bv 64 0) [] []) flock_mapped_model
        = CheckOk flock_model []) := by
  intro h
  change CheckOk flock_mapped_model [] = CheckOk flock_model [] at h
  injection h with hm _
  have hmaps := congrArg (fun m => (m_vmmaps m).vm_maps) hm
  exact List.cons_ne_nil _ _ hmaps

end TheModelComesBackWhole

section LockRequestsDecline

/-! ## Lock requests decline regardless of the effect

The decline is `CheckUnmodeled` on the success and on -EAGAIN alike, and the
pins offer both, because a decline is on the SHAPE and not on the answer:
with a second opener the model has no lock table to say whether the
request is granted, blocks, or fails.  Which of the last two a conflict
produces is the word's: `flock_lock_inode` answers -EAGAIN
(fs/locks.c:1121-1123, Linux v6.18.46) only to a request without
`FL_SLEEP`, which `flock` sets exactly when `LOCK_NB` is clear
(:2170-2172), and defers the rest (:1124-1126) to
`flock_lock_inode_wait` (:2079-2093), which loops until a later grant,
0, or an interrupting signal, -ERESTARTSYS (`wait_event_interruptible`,
include/linux/wait.h:501-508, Linux v6.18.46), which
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:417-423 and
:437-444, Linux v6.18.46) turns into a restart of the syscall or, under
a handler without SA_RESTART, into the -EINTR the process sees.  So on
the blocking `LOCK_EX` the -EAGAIN offered below is an answer the
`locks_lock_file_wait` (include/linux/filelock.h:425, Linux v6.18.46)
path, the one `flock` takes at fs/locks.c:2178-2179 for a file with no
flock method of its own, never gives; it is declined rather than refused
because the shape was declined first, and the -EINTR that path can give
is declined the same way.  `LOCK_EX | LOCK_NB` is the word on which the
-EAGAIN is real, and is declined the same way.  The unlock pins
are what keep this from reading as "the second model declines
everything": on the SH fixture, `LOCK_UN` on the very same descriptor
of the very same two-opener table answers 0 and refuses -EAGAIN. -/

/-- The second writer's mode-matching `LOCK_EX`: declined, not accepted.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_with_second_writer_declines_success :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] []) flock_two_writers_model = CheckUnmodeled := rfl

/-- …and declined, not rejected, on -EAGAIN: the decline is on the shape,
before the answer is read, so an errno this blocking word cannot produce
on the path the spec models is neither accepted nor refused.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_with_second_writer_declines_eagain :
    check_flock 4 2 (mkEffect (errno_ret EAGAIN) [] []) flock_two_writers_model
      = CheckUnmodeled := rfl

/-- …and on the -EINTR a signal delivered to a handler without SA_RESTART
makes this blocking word's answer (`arch_do_signal_or_restart`,
arch/riscv/kernel/signal.c:437-444, Linux v6.18.46, on the -ERESTARTSYS
`flock_lock_inode_wait`, fs/locks.c:2079-2093, hands up): declined the
same way, because the shape was declined first.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,flock_lock_inode,flock_lock_inode_wait; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem flock_ex_with_second_writer_declines_eintr :
    check_flock 4 2 (mkEffect (errno_ret EINTR) [] []) flock_two_writers_model
      = CheckUnmodeled := rfl

/-- `LOCK_EX | LOCK_NB` with the second writer: declined on the 0…
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_nb_with_second_writer_declines_success :
    check_flock 4 6 (mkEffect (Z_to_bv 64 0) [] []) flock_two_writers_model = CheckUnmodeled := rfl

/-- …and on the -EAGAIN that a conflicting holder makes the kernel's
answer to THIS word (`flock_lock_inode`, fs/locks.c:1121-1123, without
`FL_SLEEP`): here the model really cannot tell the two answers apart.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_nb_with_second_writer_declines_eagain :
    check_flock 4 6 (mkEffect (errno_ret EAGAIN) [] []) flock_two_writers_model
      = CheckUnmodeled := rfl

/-- `LOCK_SH` with the second opener declines too: a shared request
conflicts with a second `struct file`'s exclusive lock (`locks_conflict`,
fs/locks.c:886-893, Linux v6.18.46: either side `F_WRLCK` conflicts), and
the model does not know what the other opener holds.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_with_second_opener_declines_success :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) flock_two_openers_model = CheckUnmodeled := rfl

/-- …and the blocking `LOCK_SH` declines the -EINTR of an interrupted
wait as the blocking `LOCK_EX` does.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode,flock_lock_inode_wait; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem flock_sh_with_second_opener_declines_eintr :
    check_flock 3 1 (mkEffect (errno_ret EINTR) [] []) flock_two_openers_model
      = CheckUnmodeled := rfl

/-- …and the -EAGAIN a `LOCK_NB` request would get is declined on this
blocking word too: the decline is on the shape.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_with_second_opener_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model
      = CheckUnmodeled := rfl

/-- …and `LOCK_SH | LOCK_NB` declines the -EAGAIN a conflicting exclusive
holder gives it.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_nb_with_second_opener_declines_eagain :
    check_flock 3 5 (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model
      = CheckUnmodeled := rfl

/-- …and the 0 of a grant the same way.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_nb_with_second_opener_declines_success :
    check_flock 3 5 (mkEffect (Z_to_bv 64 0) [] []) flock_two_openers_model = CheckUnmodeled := rfl

/-- `LOCK_MAND | LOCK_EX` carries the bit, so the two-opener table is
never read: 0.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_with_ex_on_second_opener_is_zero :
    check_flock 3 34 (mkEffect (Z_to_bv 64 0) [] []) flock_two_openers_model
      = CheckOk flock_two_openers_model [] := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_with_ex_on_second_opener_rejects_eagain :
    check_flock 3 34 (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model = CheckReject :=
  rfl

/-- `LOCK_UN` on the same descriptor of the same two-opener table: 0,
because an unlock spends no premise about other holders.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem flock_un_with_second_opener_is_inert :
    check_flock 3 8 (mkEffect (Z_to_bv 64 0) [] []) flock_two_openers_model
      = CheckOk flock_two_openers_model [] := rfl

/-- …and an unlock cannot -EAGAIN.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem flock_un_with_second_opener_rejects_eagain :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model = CheckReject :=
  rfl

end LockRequestsDecline

section EveryFileKindCounts

/-! ## The opener count across file kinds

`SYSCALL_DEFINE2(flock)` reads `f_mode`
only to refuse, with -EBADF, a LOCK REQUEST on a file open with NEITHER
read nor write (`flock`, fs/locks.c:2161-2162, Linux v6.18.46): the shape
an access mode of 3 produces (`init_file`, fs/file_table.c:199, through
`OPEN_FMODE`, include/linux/fs.h:3981, Linux v6.18.46).  An `O_PATH`
descriptor never reaches that test: the fd class constructs through
`fdget` (include/linux/file.h:83), which is `__fget_light` with the
FMODE_PATH mask and hands back an empty fd for a file whose `f_mode`
carries FMODE_PATH (fs/file.c:1153-1181, Linux v6.18.46), so its -EBADF
is `fd_empty`'s (include/linux/file.h:45; fs/locks.c:2158-2159), for
`LOCK_UN` as much as for a lock — the correction #893 made to the Sys
file's prose.  The model has a constructor for neither shape
(`do_dentry_open`, fs/open.c:917, Linux v6.18.46, is where `O_PATH` sets
FMODE_PATH | FMODE_OPENED, and no modeled open passes it). -/

/-- `LOCK_EX` on fd 3, the descriptor each table below puts on "f"; the
effect claims the success, so a decline shows as `CheckUnmodeled` and a
wrong success as `CheckReject`. Rocq: `flock_ex_on_3`. -/
def flock_ex_on_3 (m : Model) : check_result :=
  check_flock 3 2 (mkEffect (Z_to_bv 64 0) [] []) m

def flock_ex_eagain_on_3 (m : Model) : check_result :=
  check_flock 3 2 (mkEffect (errno_ret EAGAIN) [] []) m

/-- One descriptor of kind `k` on "f".  Rocq: the `sole` of
`flock_every_file_kind_counts_as_an_opener`. -/
def flock_sole (k : path → word → FdEntry) : Model :=
  flock_openers_model [(3, k [102] (Z_to_bv 64 0))]

/-- Two descriptors of kind `k` on "f".  Rocq: its `pair`. -/
def flock_pair (k : path → word → FdEntry) : Model :=
  flock_openers_model [(3, k [102] (Z_to_bv 64 0)), (4, k [102] (Z_to_bv 64 5))]

/-- A descriptor of kind `k` beside an `FdFile`, both on "f".  Rocq: its
`mixed`. -/
def flock_mixed (k : path → word → FdEntry) : Model :=
  flock_openers_model [(3, k [102] (Z_to_bv 64 0)), (4, .FdFile [102] (Z_to_bv 64 5))]

/-- The sole opener is accepted at 0 on every file kind, this one an
`FdFile`.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_file_accepts_zero :
    check_flock 3 1 (mkEffect 0 [] []) (flock_sole .FdFile) = CheckOk (flock_sole .FdFile) [] := rfl

/-- …an `FdFileW`.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_filew_accepts_zero :
    flock_ex_on_3 (flock_sole .FdFileW) = CheckOk (flock_sole .FdFileW) [] := rfl

/-- …an `FdFileA`: O_APPEND is no input of the lock.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_filea_accepts_zero :
    flock_ex_on_3 (flock_sole .FdFileA) = CheckOk (flock_sole .FdFileA) [] := rfl

/-- …and an `FdFileRW`: the access mode is no input of it either.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_filerw_accepts_zero :
    flock_ex_on_3 (flock_sole .FdFileRW) = CheckOk (flock_sole .FdFileRW) [] := rfl

/-- A second descriptor of the same kind on the same name declines, on
`FdFileA`…
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_pair_filea_declines : flock_ex_on_3 (flock_pair .FdFileA) = CheckUnmodeled := rfl

/-- …and on `FdFileRW`.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_pair_filerw_declines : flock_ex_on_3 (flock_pair .FdFileRW) = CheckUnmodeled := rfl

/-- A second descriptor of a DIFFERENT kind counts as an opener too, on
`FdFileA`…
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_mixed_filea_declines : flock_ex_on_3 (flock_mixed .FdFileA) = CheckUnmodeled := rfl

/-- …and on `FdFileRW`.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_mixed_filerw_declines :
    flock_ex_on_3 (flock_mixed .FdFileRW) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_pair_file_declines : check_flock 3 1 (mkEffect 0 [] []) (flock_pair .FdFile) = CheckUnmodeled := rfl

/-- A second `FdFileW` on the same name: declined — the arm that survived
the skip mutation with the Rocq tree green until it was pinned.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_pair_filew_declines : flock_ex_on_3 (flock_pair .FdFileW) = CheckUnmodeled := rfl

/-- The lock request declines with different file kinds on the same path.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_mixed_filew_declines : flock_ex_on_3 (flock_mixed .FdFileW) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_pair_file_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_pair .FdFile) = CheckUnmodeled := rfl

/-- The `FdFileW` pair declines the -EAGAIN as the `FdFile` pair does.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_pair_filew_declines_eagain :
    flock_ex_eagain_on_3 (flock_pair .FdFileW) = CheckUnmodeled := rfl

/-- …and so does the mixed pair.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_mixed_filew_declines_eagain :
    flock_ex_eagain_on_3 (flock_mixed .FdFileW) = CheckUnmodeled := rfl

/-- The model keeps unlock under its filesystem premise even on this
two-descriptor table.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem flock_un_on_pair_filew_is_inert :
    check_flock 3 8 (mkEffect (Z_to_bv 64 0) [] []) (flock_pair .FdFileW) = CheckOk (flock_pair .FdFileW) [] :=
  rfl

/-- …and refuses -EAGAIN there, as every unlock does.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_pair_filew_rejects_eagain :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_pair .FdFileW) = CheckReject := rfl

/-- Rocq's own conjunct, on the `FdFileRW` pair: `LOCK_UN` answers 0
there too, because `flock_spec` answers an unlock before it matches on
the kind, so the read-write decline never reaches it.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem flock_un_on_pair_rdwr_is_inert :
    check_flock 3 8 (mkEffect (Z_to_bv 64 0) [] []) (flock_pair .FdFileRW) = CheckOk (flock_pair .FdFileRW) [] :=
  rfl

/-- The sole `FdFileW` opener refuses -EAGAIN: it has nothing to
conflict with.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_filew_rejects_eagain :
    flock_ex_eagain_on_3 (flock_sole .FdFileW) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_sole_filew_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_sole .FdFileW) = CheckReject := rfl

/-- …and so does the sole `FdFile` opener.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_file_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_sole .FdFile) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_sole_file_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_sole .FdFile) = CheckReject := rfl

end EveryFileKindCounts

section OtherKindsDecline

/-! ## The other descriptor kinds decline a lock and answer an unlock

Over `flock_kinds_model` (a socket, a pipe end, /dev/null, /dev/urandom)
and the channel and the directory of `flock_model`.  A lock request on
each is declined for the reason `Sys/Fs/Locks.lean` gives per kind, and
the pins offer the decline BOTH candidate answers, the 0 and the -EAGAIN,
because a decline is not a rejection: `CheckReject` on either would claim
the kernel cannot give it, and the decline is on the kind, before any
answer is read.  Which of the two a kind can really produce differs —
the socket's inode has one `struct file` and cannot conflict; the pipe's
two ends and every open of a device node share an inode and can — and
each pin says which; on this blocking word -EAGAIN is in any case the
answer of a `LOCK_NB` request (`flock_lock_inode`, fs/locks.c:1121-1123,
Linux v6.18.46, reached without `FL_SLEEP`), offered here to show the
decline does not read the answer.  `LOCK_UN` on each is answered with 0,
and -EAGAIN refused, because the kernel first branches on `F_UNLCK`
after the lookup (`flock`, fs/locks.c:2161, Linux v6.18.46) and the
unlock leaves `flock_lock_inode` before its conflict scan
(fs/locks.c:1111-1115, Linux v6.18.46): the kind of the descriptor
never enters. -/

/-- A socket: declined.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_socket_declines :
    check_flock 3 2 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- …and -EAGAIN is declined the same way, never accepted and never
refused, although no kernel gives it here: a socket's inode has exactly
one `struct file` (`sock_alloc_file`, net/socket.c:476-501, Linux
v6.18.46, the one file the socket layer allocates on the socket's inode;
a reopen through the inode fails at `no_open` (fs/inode.c:212, Linux
v6.18.46), the file operations `inode_init_always_gfp` installs at
fs/inode.c:240 and the socket allocation never replaces, and an `O_PATH`
reopen is `fd_empty` to `flock`), so `flock_locks_conflict`
(fs/locks.c:945) exempts every entry the scan could meet.  The spec
declines the kind rather than argue this about net/socket.c, and the
decline is on the kind before the answer.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict; net/socket.c:sock_alloc_file; fs/inode.c:no_open@v6.18.46 -/
theorem flock_ex_on_socket_declines_eagain :
    check_flock 3 2 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- A pipe end: declined, both ends of one pipe sharing an inode.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_pipe_declines :
    check_flock 4 2 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- …and the -EAGAIN the other end's holder gives a `LOCK_NB` request on
the shared inode is declined the same way, never accepted: the model does
not carry the other end's lock.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_on_pipe_declines_eagain :
    check_flock 4 2 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- /dev/null: declined, every open of it being a `struct file` on one
inode.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_devnull_declines :
    check_flock 5 2 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- …and the -EAGAIN another open of /dev/null holding a lock gives a
`LOCK_NB` request is declined the same way, never accepted: the model
does not record device lock state.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_on_devnull_declines_eagain :
    check_flock 5 2 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- /dev/urandom: declined, for the same reason as /dev/null.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_urandom_declines :
    check_flock 6 2 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- …and the -EAGAIN another open of /dev/urandom holding a lock gives a
`LOCK_NB` request is declined the same way, never accepted.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_on_urandom_declines_eagain :
    check_flock 6 2 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckUnmodeled := rfl

/-- A channel: declined, its object not being in the model.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_channel_declines :
    check_flock 0 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckUnmodeled := rfl

/-- …and -EAGAIN is declined the same way, never accepted: the channel's
object is not in the model, so what else holds its inode is unknown.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_on_channel_declines_eagain :
    check_flock 0 2 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckUnmodeled := rfl

/-- The directory at fd 5 of `flock_model`: a lock request is declined.
The kernel takes it — `flock` tests only `f_mode` (fs/locks.c:2161-2162,
Linux v6.18.46), which an `O_RDONLY | O_DIRECTORY` open has, and
fs/locks.c never asks `S_ISDIR` — and would answer 0 with no other
holder; the spec declines because `"."` and `".."` are one constructor
and a second reference to the same directory cannot be told from a
reference to another (`Sys/Fs/Locks.lean`).  The spec pin is
`ex_on_dir_is_unmodeled`; this is the acceptor's answer.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_ex_on_dir_declines :
    check_flock 5 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckUnmodeled := rfl

/-- …and on -EAGAIN too, the decline being on the kind.
kernel: fs/locks.c:flock,flock_lock_inode,flock_locks_conflict@v6.18.46 -/
theorem flock_ex_on_dir_declines_eagain :
    check_flock 5 2 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_dir_declines :
    check_flock 5 1 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_sh_on_dir_declines_eagain :
    check_flock 5 1 (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckUnmodeled := rfl

/-- `LOCK_UN` on the socket: 0, the unlock arm preceding the kind match.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_socket_is_inert :
    check_flock 3 8 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model
      = CheckOk flock_kinds_model [] := rfl

/-- `LOCK_UN` on the pipe end: 0.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_pipe_is_inert :
    check_flock 4 8 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model
      = CheckOk flock_kinds_model [] := rfl

/-- …and refuses -EAGAIN on the pipe end too.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_pipe_rejects_eagain :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckReject := rfl

/-- `LOCK_UN | LOCK_NB` on the channel at fd 0: the modifier is stripped
and the unlock arm answers 0 before the kind is looked at.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_un_nb_on_channel_is_inert :
    check_flock 0 12 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and the -EINVAL of a model that translated 12 before stripping the
modifier is refused, on the channel as on a file.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_un_nb_on_channel_rejects_einval :
    check_flock 0 12 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- …and the unlock refuses -EAGAIN on a socket as on a file.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_socket_rejects_eagain :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckReject := rfl

/-- `LOCK_UN` on /dev/null: 0, the unlock arm ahead of the kind match.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_devnull_is_inert :
    check_flock 5 8 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckOk flock_kinds_model [] :=
  rfl

/-- …and -EAGAIN refused there.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_devnull_rejects_eagain :
    check_flock 5 8 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckReject := rfl

/-- `LOCK_UN` on /dev/urandom: 0, for the same reason.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_urandom_is_inert :
    check_flock 6 8 (mkEffect (Z_to_bv 64 0) [] []) flock_kinds_model = CheckOk flock_kinds_model [] :=
  rfl

/-- …and -EAGAIN refused there.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_un_on_urandom_rejects_eagain :
    check_flock 6 8 (mkEffect (errno_ret EAGAIN) [] []) flock_kinds_model = CheckReject := rfl

end OtherKindsDecline

section UnrecognisedWords

/-! ## The two command words #893 added to the spec pins

`flock_translate_cmd` (fs/locks.c:461, Linux v6.18.46) falls through to
-EINVAL for a word that is not exactly one of its three cases, so
`LOCK_UN|LOCK_EX` (10) is refused; and the syscall takes the word as an
`unsigned int` (`flock`, fs/locks.c:2135, Linux v6.18.46), so a set bit 31
survives into the switch.  #893 pinned both on the spec
(`un_and_ex_together_is_einval`, `sign_bit_cmd_is_einval` in
`Checks/Cases/Fs/Locks.lean`); these are the same two claims at the
acceptor.  The spec's third pin there, `sign_bit_cmd_survives_narrowing`,
goes through `syscall_spec`, and its acceptor twin waits on the
dispatcher arm V-Fs-Locks registers. -/

/-- `LOCK_UN|LOCK_EX` is -EINVAL, and the checker accepts exactly that.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_un_and_ex_together_is_einval :
    check_flock 3 10 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and refuses the 0 a kernel reading the word as a bit set would give.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_un_and_ex_together_rejects_success :
    check_flock 3 10 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_EX` with bit 31 set is -EINVAL: the `unsigned int` keeps the bit.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_sign_bit_cmd_is_einval :
    check_flock 3 2147483650 (mkEffect (errno_ret EINVAL) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the lock a narrowing kernel would grant is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_sign_bit_cmd_rejects_success :
    check_flock 3 2147483650 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_READ` (64) is a word of the removed mandatory-locking API, not
one of `flock_translate_cmd`'s three cases: -EINVAL on an open file.
kernel: include/uapi/asm-generic/fcntl.h:LOCK_READ; fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_lock_read_is_einval :
    check_flock 3 64 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- …and a kernel that still read it as a shared request is refused.
kernel: include/uapi/asm-generic/fcntl.h:LOCK_READ; fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_lock_read_rejects_success :
    check_flock 3 64 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_RW` (192) likewise.
kernel: include/uapi/asm-generic/fcntl.h:LOCK_RW; fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_lock_rw_is_einval :
    check_flock 3 192 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] :=
  rfl

/-- …and its grant is refused.
kernel: include/uapi/asm-generic/fcntl.h:LOCK_RW; fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_lock_rw_rejects_success :
    check_flock 3 192 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_MAND | LOCK_READ` carries the bit, so it is 0 and not the
-EINVAL the word alone would get.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_mand_read_is_zero :
    check_flock 3 96 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_mand_read_rejects_einval :
    check_flock 3 96 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

end UnrecognisedWords

section HighBitDescriptor

/-! ## A descriptor word with bit 31 set

`fd` is an `unsigned int` (`flock`, fs/locks.c:2135, Linux v6.18.46), so
bit 31 is not a sign and is not narrowed away.  The lookup is `fdget`
(include/linux/file.h:83) → `__fget_light` (fs/file.c:1130-1178) →
`files_lookup_fd_raw` (include/linux/fdtable.h:72-86, Linux v6.18.46),
which masks an index at or above `max_fds` to NULL; `max_fds` is bounded
by `sysctl_nr_open_max` (fs/file.c:100-101), below 2^31.  So every such
word is a closed descriptor: -EBADF at the `fd_empty` test
(include/linux/file.h) that `flock` makes right after the lookup
(fs/locks.c:2158-2159, Linux v6.18.46) once the two cmd tests have
passed; a word carrying LOCK_MAND is 0 on such a descriptor, and a word
`flock_translate_cmd` does not recognize is -EINVAL on it.  The checker's
`fd_lookup` finds no such key in any fixture; a checker that read the fd
as a signed index, or masked bit 31, would find fd 3 under 0x80000003
and grant. -/

/-- `LOCK_EX` on 0x80000003 is -EBADF, not the grant fd 3 would get.
kernel: fs/locks.c:flock; include/linux/fdtable.h:files_lookup_fd_raw@v6.18.46 -/
theorem flock_ex_on_fd_3_with_bit_31_is_ebadf :
    check_flock 0x80000003 2 (mkEffect (errno_ret EBADF) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the grant is refused.
kernel: fs/locks.c:flock; include/linux/fdtable.h:files_lookup_fd_raw@v6.18.46 -/
theorem flock_ex_on_fd_3_with_bit_31_rejects_success :
    check_flock 0x80000003 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- The all-ones 32-bit word is -EBADF too.
kernel: fs/locks.c:flock; include/linux/fdtable.h:files_lookup_fd_raw@v6.18.46 -/
theorem flock_ex_on_all_ones_fd_is_ebadf :
    check_flock 0xFFFFFFFF 2 (mkEffect (errno_ret EBADF) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the grant fd 3 would get is refused on it.
kernel: fs/locks.c:flock; include/linux/fdtable.h:files_lookup_fd_raw@v6.18.46 -/
theorem flock_ex_on_all_ones_fd_rejects_success :
    check_flock 0xFFFFFFFF 2 (mkEffect (Z_to_bv 64 0) [] []) flock_model = CheckReject := rfl

/-- `LOCK_MAND` on the all-ones word, which no table holds: the bit is
tested before the lookup, so the answer is 0 and not -EBADF.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- mandclosed -/
theorem flock_mand_on_all_ones_fd_is_zero :
    check_flock 0xFFFFFFFF 32 (mkEffect (Z_to_bv 64 0) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the -EBADF of a lookup-first order is refused there.
Read at Linux v5.19: fs/locks.c, SYSCALL_DEFINE2(flock), performs fd lookup before command translation.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- mandclosed -/
theorem flock_mand_on_all_ones_fd_ebadf_is_rejected :
    check_flock 0xFFFFFFFF 32 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject ∧
    check_flock 0xFFFFFFFF 32 (mkEffect (errno_ret EBADF) [] []) flock_model ≠ CheckOk flock_model [] := by
  constructor
  · rfl
  · intro h; cases h

/-- An unrecognized operation on the all-ones word: `flock_translate_cmd`
falls off its switch before the descriptor is looked up, so the answer is
-EINVAL on a closed fd exactly as on an open one, and the checker accepts
it.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- badcmdclosed -/
theorem flock_bad_op_on_all_ones_fd_einval_is_accepted :
    check_flock 0xFFFFFFFF 0 (mkEffect (errno_ret EINVAL) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the -EBADF a lookup-first order would give is refused there: the
command word is translated before the fd is resolved.
Read at Linux v5.19: fs/locks.c, SYSCALL_DEFINE2(flock), performs fd lookup before command translation.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- badcmdclosed -/
theorem flock_bad_op_on_all_ones_fd_ebadf_is_rejected :
    check_flock 0xFFFFFFFF 0 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject ∧
    check_flock 0xFFFFFFFF 0 (mkEffect (errno_ret EBADF) [] []) flock_model ≠ CheckOk flock_model [] := by
  constructor
  · rfl
  · intro h; cases h

end HighBitDescriptor

section DeclinesBesideOtherKinds

/-! ## Lock requests beside other descriptor kinds

These pins check the grant and the decline with a file and a socket,
pipe, directory or device in either table order, including tables with
two file entries.  A descriptor of another kind is no opener of the
file's path, so the file stays the sole opener and the take is granted;
a second file entry on the same name declines. -/

/-- The skipped descriptor at 3, the file's sole opener at 4. -/
def flock_beside_file (e : FdEntry) : Model :=
  flock_openers_model [(3, e), (4, .FdFile [102] 0)]

/-- The file's sole opener at 3, the skipped descriptor at 4. -/
def flock_file_beside (e : FdEntry) : Model :=
  flock_openers_model [(3, .FdFile [102] 0), (4, e)]

/-- Two file openers at 3 and 5, the skipped descriptor between them. -/
def flock_file_hidden_by (e : FdEntry) : Model :=
  flock_openers_model [(3, .FdFile [102] 0), (4, e), (5, .FdFile [102] 5)]

/-- The skipped descriptor at 3, two file openers behind it at 4 and 5. -/
def flock_pair_after (e : FdEntry) : Model :=
  flock_openers_model [(3, e), (4, .FdFile [102] 0), (5, .FdFile [102] 5)]

/-- A socket is no opener of "f": the file is still the sole opener.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sole_file_beside_socket_accepts_zero :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_beside_file (.FdSocket .SkFresh))
      = CheckOk (flock_beside_file (.FdSocket .SkFresh)) [] := rfl

/-- …and -EAGAIN is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_socket_rejects_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdSocket .SkFresh))
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_socket_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdSocket .SkFresh))
      = CheckReject := rfl

/-- The same with the socket listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_socket_beside_file_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_beside (.FdSocket .SkFresh))
      = CheckOk (flock_file_beside (.FdSocket .SkFresh)) [] := rfl

/-- …and -EAGAIN is refused there too.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_socket_beside_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdSocket .SkFresh)) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_socket_beside_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdSocket .SkFresh)) = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_socket_beside_two_files_declines :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_hidden_by (.FdSocket .SkFresh)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_socket_beside_two_files_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_hidden_by (.FdSocket .SkFresh)) = CheckUnmodeled := rfl

/-- A pipe end is no opener of "f" either.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sole_file_beside_pipe_accepts_zero :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_beside_file (.FdPipe 7 false))
      = CheckOk (flock_beside_file (.FdPipe 7 false)) [] := rfl

/-- …and -EAGAIN is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_pipe_rejects_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdPipe 7 false))
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_pipe_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdPipe 7 false))
      = CheckReject := rfl

/-- The same with the pipe end listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_pipe_beside_file_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_beside (.FdPipe 7 false))
      = CheckOk (flock_file_beside (.FdPipe 7 false)) [] := rfl

/-- …and -EAGAIN is refused there too.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_pipe_beside_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdPipe 7 false)) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pipe_beside_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdPipe 7 false)) = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pipe_beside_two_files_declines :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_hidden_by (.FdPipe 7 false)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pipe_beside_two_files_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_hidden_by (.FdPipe 7 false)) = CheckUnmodeled := rfl

/-- A directory reference is no opener of "f".
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sole_file_beside_dir_accepts_zero :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_beside_file (.FdDir))
      = CheckOk (flock_beside_file (.FdDir)) [] := rfl

/-- …and -EAGAIN is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_dir_rejects_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdDir))
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_dir_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdDir))
      = CheckReject := rfl

/-- The same with the directory listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_dir_beside_file_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_beside (.FdDir))
      = CheckOk (flock_file_beside (.FdDir)) [] := rfl

/-- …and -EAGAIN is refused there too.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_dir_beside_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdDir)) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_dir_beside_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdDir)) = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_dir_beside_two_files_declines :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_hidden_by (.FdDir)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_dir_beside_two_files_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_hidden_by (.FdDir)) = CheckUnmodeled := rfl

/-- /dev/null is no opener of "f".
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sole_file_beside_devnull_accepts_zero :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_beside_file (.FdDevNull true true))
      = CheckOk (flock_beside_file (.FdDevNull true true)) [] := rfl

/-- …and -EAGAIN is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_devnull_rejects_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdDevNull true true))
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_devnull_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdDevNull true true))
      = CheckReject := rfl

/-- The same with /dev/null listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_devnull_beside_file_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_beside (.FdDevNull true true))
      = CheckOk (flock_file_beside (.FdDevNull true true)) [] := rfl

/-- …and -EAGAIN is refused there too.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_devnull_beside_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdDevNull true true)) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_devnull_beside_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdDevNull true true)) = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_devnull_beside_two_files_declines :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_hidden_by (.FdDevNull true true)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_devnull_beside_two_files_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_hidden_by (.FdDevNull true true)) = CheckUnmodeled := rfl

/-- /dev/urandom is no opener of "f".
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_sole_file_beside_urandom_accepts_zero :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_beside_file (.FdUrandom))
      = CheckOk (flock_beside_file (.FdUrandom)) [] := rfl

/-- …and -EAGAIN is refused there.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_urandom_rejects_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdUrandom))
      = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_sole_file_beside_urandom_rejects_eagain_on_unlock :
    check_flock 4 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_beside_file (.FdUrandom))
      = CheckReject := rfl

/-- The same with /dev/urandom listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_urandom_beside_file_accepts_zero :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_beside (.FdUrandom))
      = CheckOk (flock_file_beside (.FdUrandom)) [] := rfl

/-- …and -EAGAIN is refused there too.
kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem flock_urandom_beside_opener_rejects_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdUrandom)) = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_urandom_beside_opener_rejects_eagain_on_unlock :
    check_flock 3 8 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_beside (.FdUrandom)) = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_urandom_beside_two_files_declines :
    check_flock 3 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_file_hidden_by (.FdUrandom)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_urandom_beside_two_files_declines_eagain :
    check_flock 3 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_file_hidden_by (.FdUrandom)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_socket_declines :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_pair_after (.FdSocket .SkFresh)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_socket_declines_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_pair_after (.FdSocket .SkFresh)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_pipe_declines :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_pair_after (.FdPipe 7 false)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_pipe_declines_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_pair_after (.FdPipe 7 false)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_devnull_declines :
    check_flock 4 1 (mkEffect (Z_to_bv 64 0) [] []) (flock_pair_after (.FdDevNull true true)) = CheckUnmodeled := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_pair_after_devnull_declines_eagain :
    check_flock 4 1 (mkEffect (errno_ret EAGAIN) [] []) (flock_pair_after (.FdDevNull true true)) = CheckUnmodeled := rfl

end DeclinesBesideOtherKinds

section Witness

/-! ## The witness is the outcome the checker accepts

`flock_witness` is the spec's one admitted outcome per input, as data.
`flock_witness_ok` says the spec admits it and the checker's soundness
and completeness theorems say the checker and the spec agree, so the
checker accepts the witness at every input and declines exactly where it
is `Unmodeled` — the two quantified lemmas at the end compose those
theorems.  What they cannot
say is WHICH outcome the witness computes: a witness that answered 0 on
every arm is one `flock_witness_ok` would still prove, were the spec
wrong the same way.  So the ground pins name it, one per arm, with the
return the spec pins read off the kernel. -/

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_witness_mand_on_open_fd_is_zero :
    flock_witness 1 32 flock_model = Ok (mkEffect (Z_to_bv 64 0) [] []) flock_model [] := rfl

/-- The witness answers the `LOCK_MAND` word before the lookup, so a
closed descriptor gets the same 0.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_witness_mand_on_closed_fd_is_zero :
    flock_witness 9999 32 flock_model = Ok (mkEffect (Z_to_bv 64 0) [] []) flock_model [] := rfl

/-- An invalid command on a closed fd is -EINVAL, the translation
running before the lookup.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_witness_badcmd_on_closed_fd_is_einval :
    flock_witness 9999 0 flock_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := rfl

/-- …and so is every other unrecognized word, `LOCK_SH|LOCK_EX` among them.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_witness_combined_op_on_closed_fd_is_einval :
    flock_witness 9999 3 flock_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := rfl

/-- The unrecognized word's witness: -EINVAL, `LOCK_NB` alone on an open
file.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_witness_nb_alone :
    flock_witness 3 4 flock_model = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := rfl

/-- The closed descriptor's witness: -EBADF.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_witness_ex_on_closed_fd :
    flock_witness 9999 2 flock_model = Ok (mkEffect (errno_ret EBADF) [] []) flock_model [] := rfl

/-- The unlock's witness on the directory: 0.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_witness_un_on_dir :
    flock_witness 5 8 flock_model = Ok (mkEffect (Z_to_bv 64 0) [] []) flock_model [] := rfl

/-- The sole opener's witness is the grant.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_witness_ex_on_sole_opener_is_zero :
    flock_witness 4 2 flock_model = Ok (mkEffect (Z_to_bv 64 0) [] []) flock_model [] := rfl

/-- …on the shared request as well.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_witness_sh_on_sole_opener_is_zero :
    flock_witness 3 1 flock_model = Ok (mkEffect (Z_to_bv 64 0) [] []) flock_model [] := rfl

/-- With a second opener the mode-matching SH witness is `Unmodeled`.
An exclusive lock on the other opener can conflict with this shared request
(fs/locks.c, `flock_locks_conflict` and `locks_conflict`, Linux v6.18.46).
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_witness_sh_with_second_opener_is_unmodeled :
    flock_witness 3 1 flock_two_openers_model = Unmodeled := rfl

/-- …and on the directory.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_witness_ex_on_dir_is_unmodeled :
    flock_witness 5 2 flock_model = Unmodeled := rfl

/-- …and on the socket, the pipe end, /dev/null and /dev/urandom.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_witness_ex_on_other_kinds_is_unmodeled :
    flock_witness 3 2 flock_kinds_model = Unmodeled ∧ flock_witness 4 2 flock_kinds_model = Unmodeled
      ∧ flock_witness 5 2 flock_kinds_model = Unmodeled
      ∧ flock_witness 6 2 flock_kinds_model = Unmodeled := ⟨rfl, rfl, rfl, rfl⟩

/-- Wherever the witness is an outcome, the checker accepts exactly that
outcome: `flock_witness_ok` puts it in the spec and
`check_flock_complete_ok` carries it to the checker.
model: composes `flock_witness_ok` with `check_flock_complete_ok`; the ground pins above say which outcome -/
theorem flock_witness_is_accepted (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (hw : flock_witness fd cmd m = Ok eff m' evs) :
    check_flock fd cmd eff m = CheckOk m' evs := by
  have h := flock_witness_ok fd cmd i m
  rw [hw] at h
  exact check_flock_complete_ok fd cmd eff m m' evs i h

/-- …and wherever it is `Unmodeled`, the checker declines whatever effect
it is shown.
model: composes `flock_witness_ok` with `check_flock_complete_unmodeled`; the ground pins above say where -/
theorem flock_witness_decline_is_the_checkers (fd cmd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (hw : flock_witness fd cmd m = Unmodeled) :
    check_flock fd cmd eff m = CheckUnmodeled := by
  have h := flock_witness_ok fd cmd i m
  rw [hw] at h
  exact check_flock_complete_unmodeled fd cmd m i eff h

/-- T202: LOCK_EX|LOCK_UN is not a recognized operation, even on an open fd.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_witness_un_and_ex_together_is_einval :
    flock_witness 1 10 flock_model = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := rfl

end Witness

-- lean-port sentinel: ticket V-Fs-Locks
section V_Fs_Locks

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Locks — Rocq's examples through the real table

Read at f1006fe8178338a499b5e5c41be83006c4edd058 in
`theories/LinuxProcessSem/Checks/Cases/Fs/Locks.v`. The inputs below
are Rocq's, the file-kind example's four kinds included.
The fixtures are imported from `Checks/Cases/Fs/Locks.lean`.
The narrowing pins separately exercise each register, so narrowing only
one cannot satisfy them. -/

/-- The lookup ignores arguments and memory; the argument interpretation
is the arm's, from fs/locks.c:2135 (Linux v6.18.46).
model: `lookup_ca` over `checked_table` at a closed number; the table's contents -/
theorem lookup_flock_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 32 args mem wmem).in_sysno)
      = some arm_flock :=
  lookup_ca_checked_table_flock

/-- Rocq: `flock_success_is_inert`, through the real table.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_success_is_inert_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 32 [9999, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [9999, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and the same inputs with `LOCK_UN` in place of the take.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_success_is_inert_over_the_real_table_on_unlock :
    check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 32 [1, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [1, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Rocq: `flock_every_file_kind_counts_as_an_opener`, through the real
table: the sole opener of each kind is granted, a second descriptor of
the same kind or of another declines, and the unlock on the pair still
answers 0.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_every_file_kind_counts_as_an_opener_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFile [102] 0)])
      = CheckOk (flock_openers_model [(3, .FdFile [102] 0)]) []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileW [102] 0)])
      = CheckOk (flock_openers_model [(3, .FdFileW [102] 0)]) []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0)])
      = CheckOk (flock_openers_model [(3, .FdFileA [102] 0)]) []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileRW [102] 0)])
      = CheckOk (flock_openers_model [(3, .FdFileRW [102] 0)]) []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFile [102] 0), (4, .FdFile [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFileW [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0), (4, .FdFileA [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFileRW [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFile [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0), (4, .FdFile [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFile [102] 5)]) = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFileRW [102] 5)])
      = CheckOk (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFileRW [102] 5)]) []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EAGAIN) [] []) (flock_openers_model [(3, .FdFileRW [102] 0)])
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Rocq: `flock_second_opener_declines`, through the real table.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem flock_second_opener_declines_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_two_openers_model = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_two_openers_model = CheckOk flock_two_openers_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- The fd register narrows to 32 bits, so `2^32 + 3` is fd 3 and the
sole opener is granted.
kernel: fs/locks.c:flock; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem flock_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [4294967299, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [4294967299, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_fd_truncates_to_32_bits_over_the_real_table_on_unlock :
    check_syscall (SyscallInput.mkInput 32 [4294967299, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [4294967299, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- The cmd register `2^32 + 8` aliases LOCK_UN, by the unsigned-int
signature at fs/locks.c:2135 and the cast at include/linux/syscalls.h:132
through arch/riscv/include/asm/syscall_wrapper.h:88 (Linux v6.18.46).
`flock_translate_cmd` (fs/locks.c:458-459) recognizes the narrowed unlock, and
`flock_lock_inode` (fs/locks.c:1111-1115) returns zero. The -EINVAL a checker retaining
the high half would yield is refused.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem flock_cmd_truncates_to_32_bits_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [3, 4294967304, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckOk flock_model []
    ∧ check_syscall (SyscallInput.mkInput 32 [3, 4294967304, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- A count of 1 is not the 0 the grant arm takes.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem flock_shared_lock_nonzero_rejected_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) flock_model = CheckReject := rfl

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_shared_lock_nonzero_rejected_over_the_real_table_on_unlock :
    check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) flock_model = CheckReject := rfl

/-- A recognized command on a closed fd returns -EBADF before making
a lock: `flock`, fs/locks.c:2153-2164 (Linux v6.18.46). Success is a lie.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_bad_fd_success_rejected_over_the_real_table :
    check_syscall (SyscallInput.mkInput 32 [9999, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- Both registers narrow, and the witness names the answer each one
leads to: the grant on the narrowed fd, the unlock on the narrowed cmd.
kernel: fs/locks.c:flock; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem flock_witness_narrows_both_registers_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 32 [4294967299, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        flock_model = Ok (mkEffect 0 [] []) flock_model [] ∧ syscall_spec_witness
        (SyscallInput.mkInput 32 [3, 4294967304, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        flock_model = Ok (mkEffect 0 [] []) flock_model [] := ⟨rfl, rfl⟩

end V_Fs_Locks

/-- The `LOCK_MAND` arm answers, whatever effect it is shown: it accepts
the 0 and refuses everything else, and never declines.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_any_effect_is_not_unmodeled (eff : SyscallEffect) :
    check_flock 1 32 eff flock_model ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_einval_rejected :
    check_flock 1 32 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_ro_ex_any_effect_is_not_unmodeled (eff : SyscallEffect) :
    check_flock 3 2 eff flock_model ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_ro_ex_zero_accepted :
    check_flock 3 2 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_ro_ex_einval_rejected :
    check_flock 3 2 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ro_ex_ebadf_rejected :
    check_flock 3 2 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_ro_ex_nb_any_effect_is_not_unmodeled (eff : SyscallEffect) :
    check_flock 3 6 eff flock_model ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_ro_ex_nb_zero_accepted :
    check_flock 3 6 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_ro_ex_nb_einval_rejected :
    check_flock 3 6 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_ro_ex_nb_ebadf_rejected :
    check_flock 3 6 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_wo_sh_any_effect_is_not_unmodeled (eff : SyscallEffect) :
    check_flock 4 1 eff flock_model ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_wo_sh_zero_accepted :
    check_flock 4 1 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_wo_sh_einval_rejected :
    check_flock 4 1 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_wo_sh_ebadf_rejected :
    check_flock 4 1 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_wo_sh_nb_any_effect_is_not_unmodeled (eff : SyscallEffect) :
    check_flock 4 5 eff flock_model ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem flock_wo_sh_nb_zero_accepted :
    check_flock 4 5 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem flock_wo_sh_nb_einval_rejected :
    check_flock 4 5 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject := rfl

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_wo_sh_nb_ebadf_rejected :
    check_flock 4 5 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- The sole read-only opener: the 0 is accepted and -EBADF refused.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_ro_sh_accepts_zero_and_refuses_ebadf :
    check_flock 3 1 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 3 1 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_ro_sh_unlock_answers_and_refuses_ebadf :
    check_flock 3 8 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 3 8 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- The same with `LOCK_NB`.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_ro_sh_nb_accepts_zero_and_refuses_ebadf :
    check_flock 3 5 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 3 5 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_ro_sh_nb_unlock_answers_and_refuses_ebadf :
    check_flock 3 12 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 3 12 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- The sole write-only opener, exclusive request.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_wo_ex_accepts_zero_and_refuses_ebadf :
    check_flock 4 2 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 4 2 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_wo_ex_unlock_answers_and_refuses_ebadf :
    check_flock 4 8 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 4 8 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- …and with `LOCK_NB`.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem flock_wo_ex_nb_accepts_zero_and_refuses_ebadf :
    check_flock 4 6 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 4 6 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem flock_wo_ex_nb_unlock_answers_and_refuses_ebadf :
    check_flock 4 12 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] ∧
    check_flock 4 12 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := ⟨rfl, rfl⟩

/-- The `LOCK_MAND` arm answers on every descriptor kind, so it never
declines there either.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem flock_mand_any_fd_kind_any_effect_is_not_unmodeled (e : FdEntry) (eff : SyscallEffect) :
    check_flock 3 32 eff (flock_openers_model [(3, e)]) ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-- The sole opener's grant refuses -EACCES, the answer a filesystem with
its own `.flock` could give; the modeled band assumes none.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_ro_sh_eacces_rejected :
    check_flock 3 1 (mkEffect (errno_ret EACCES) [] []) flock_model = CheckReject := rfl

/-- …and the nonblocking shared request refuses it too.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_ro_sh_nb_eacces_rejected :
    check_flock 3 5 (mkEffect (errno_ret EACCES) [] []) flock_model = CheckReject := rfl

/-- …and the exclusive request on the sole writer.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_wo_ex_eacces_rejected :
    check_flock 4 2 (mkEffect (errno_ret EACCES) [] []) flock_model = CheckReject := rfl

/-- …and the same with `LOCK_NB`.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_wo_ex_nb_eacces_rejected :
    check_flock 4 6 (mkEffect (errno_ret EACCES) [] []) flock_model = CheckReject := rfl

/-- T202: Retain unlock under the recorded filesystem premise.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_unlock_on_sole_file_is_zero :
    check_flock 3 8 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- T202: Retain unlock under the recorded filesystem premise.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_unlock_on_sole_filew_is_zero :
    check_flock 4 8 (mkEffect 0 [] []) flock_model = CheckOk flock_model [] := rfl

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_sign_bit_unlock_zero_rejected :
    check_flock 3 0x80000008 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_42_zero_rejected :
    check_flock 1 0x42 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_82_zero_rejected :
    check_flock 1 0x82 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_10002_zero_rejected :
    check_flock 1 0x10002 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_48_zero_rejected :
    check_flock 1 0x48 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_88_zero_rejected :
    check_flock 1 0x88 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_10008_zero_rejected :
    check_flock 1 0x10008 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- An unrecognized word on a closed descriptor is -EINVAL: the
translation runs before the lookup.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_closed_extra_ex_einval_accepted :
    check_flock 9999 0x42 (mkEffect (errno_ret EINVAL) [] []) flock_model
      = CheckOk flock_model [] := rfl

/-- …and the -EBADF of a lookup-first order is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_closed_extra_ex_ebadf_rejected :
    check_flock 9999 0x42 (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject := rfl

/-- T202: Refute a 31-bit command mask through the real dispatcher.
kernel: fs/locks.c:flock,flock_translate_cmd; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem t202_sign_bit_unlock_zero_rejected_over_the_real_table :
    LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall (SyscallInput.mkInput 32 [3, 0x80000008] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- T202: Keep both witness narrowing controls on an answered unlock.
kernel: fs/locks.c:flock,flock_lock_inode; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem flock_witness_narrows_both_registers_over_the_real_table_on_unlock :
    LinuxProcessSemantics.LinuxProcessSem.Checks.Progress.syscall_spec_witness
        (SyscallInput.mkInput 32 [4294967299, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        flock_model = Ok (mkEffect 0 [] []) flock_model []
    ∧ LinuxProcessSemantics.LinuxProcessSem.Checks.Progress.syscall_spec_witness
        (SyscallInput.mkInput 32 [3, 4294967304, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        flock_model = Ok (mkEffect 0 [] []) flock_model [] := ⟨rfl, rfl⟩

/-- The file descriptor avoids the channel-direction premise.
Extra command bits still make this operation invalid.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_42_is_einval :
    check_flock 3 0x42 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- The invalid word cannot succeed on the file descriptor.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_42_zero_rejected :
    check_flock 3 0x42 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- The file descriptor avoids the channel-direction premise.
Extra command bits still make this operation invalid.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_48_is_einval :
    check_flock 3 0x48 (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckOk flock_model [] := rfl

/-- The invalid word cannot succeed on the file descriptor.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_48_zero_rejected :
    check_flock 3 0x48 (mkEffect 0 [] []) flock_model = CheckReject := rfl

/-- The append-mode sole opener is granted, so -EACCES is refused: the
modeled band assumes no filesystem with its own `.flock`.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_wa_ex_eacces_rejected :
    check_flock 3 2 (mkEffect (errno_ret EACCES) [] [])
      (flock_openers_model [(3, .FdFileA [102] 0)]) = CheckReject := rfl

/-- …and so is the read-write sole opener's.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem t202_rw_ex_eacces_rejected :
    check_flock 3 2 (mkEffect (errno_ret EACCES) [] [])
      (flock_openers_model [(3, .FdFileRW [102] 0)]) = CheckReject := rfl

/-- The model commits to the LOCK_UN premise recorded in
linux-process-semantics@ff0313ba4f:bugs/flock-answers-assume-no-flock-f-op.md and rejects -ENOLCK here.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem t202_unlock_on_file_rejects_enolck :
    check_flock 3 8 (mkEffect (errno_ret 37) [] []) flock_model = CheckReject := rfl

/-- The model commits to the LOCK_UN premise recorded in
linux-process-semantics@ff0313ba4f:bugs/flock-answers-assume-no-flock-f-op.md and rejects -EIO here.
kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem t202_unlock_on_file_rejects_eio :
    check_flock 3 8 (mkEffect (errno_ret 5) [] []) flock_model = CheckReject := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Locks
