-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.EventPoll — what the epoll CHECKERS accept and refuse, read off against Linux

Pins over `Checks.Sys.Fs.EventPoll.check_epoll_create1`, `check_epoll_ctl`
and `check_epoll_pwait`, the twins of
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`, and over the three
witnesses of `theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`.
Not part of the trusted specification: this file is QA on the checkers,
written to be READ, and every claim in it is a claim about what Linux
does, with the citation beside it, unless its evidence line says `model:`
and says otherwise.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f).

WHY THESE EXIST beside the twelve lemmas.  Those relate each checker to
its spec, and a mistake made in both closes every one of them.  What
separates the pair from Linux is a concrete answer from outside: offer a
checker an effect a real kernel could never produce and require
`CheckReject`, offer the one it does produce and require `CheckOk`.  The
spec's own pins are `Checks/Cases/Fs/EventPoll.lean`'s; this file is the
checker's, and it holds the row application the dispatcher performs as
well, since a checker can be right and its registration wrong.

HOW THESE ARE STATED.  The row pins apply the checker the way the
dispatcher does: `check_epoll_create1_row`, `check_epoll_ctl_row` and
`check_epoll_pwait_row` below are the argument narrowing of
`arm_epoll_create1`, `arm_epoll_ctl` and `arm_epoll_pwait`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and of the rows for
20, 21 and 22 in `Sys/SyscallTable.lean`, spelled once and proved to be
that narrowing, not merely described as it: a later section closes each
row's `CheckOk` against `dispatch spec_table` through the registered arm,
which unifies only if the row narrows every register as
`Sys/Registry/Fs/EventPoll.lean` does.  The last section exercises
`check_syscall` through the registered arms of `checked_table`.
The model is `Checks/Cases/Fs/EventPoll.lean`'s `ep_model`, imported
rather than copied, so a pin on fd 3 is a pin on a regular file and a pin
on fd 6 a pin on a socket in both files at once; the memories are that
file's `ep_mem_all` and `ep_mem_run`.  Every equality is closed by `rfl`:
on a closed input each checker reduces to a constructor by evaluation
alone, reading no field of a quantified model.

WHICH PINS CARRY A `probe:` LINE.  Some `= CheckOk` pins cite the
`conform` case of
`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/epoll_spec.c`
whose recorded run
(`linux-process-semantics@ff0313ba4f:testing/syscall-check/traces/epoll_spec/`)
issued the pin's syscall with the pin's shape and got the pin's errno:
for those, `tools/check_lean_pin_evidence.py`'s PROBE-RET holds the errno
to a return a real kernel gave, which no kernel reading can.

ONE PIN STATES A KNOWN OMISSION rather than a kernel fact, and says so
where it stands: `epoll_ctl_a_recorded_copy_in_is_rejected`.  The spec
records no copy-in for the event struct it reads
(`linux-process-semantics@ff0313ba4f:bugs/epoll-ctl-copyin-not-recorded.md`),
so the checker refuses an effect that records one; the pin exists so that
the day the spec records it, this file stops compiling at the line that
has to move.

NOTHING HERE EXECUTES THE ROCQ CHECKER.  These pins state the Lean
checkers' verdicts against the cited kernel behaviour. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventPoll

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
-- Selective: only the fixtures, so that no spec-level pin name is brought
-- into a namespace that states the checker's verdict under a like name.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
  (ep_model ep_mem_all ep_mem_run ep_in pw_in)

/-! ## The dispatcher's application of each checker -/

/-- `check_epoll_create1` as the dispatcher applies it: `flags` narrowed to
`int` by `flag32` — Rocq's `arm_epoll_create1` and the row for 20 in
`Sys/SyscallTable.lean`. -/
def check_epoll_create1_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_create1 (flag32 (in_arg i 0)) eff m

/-- `check_epoll_ctl` as the dispatcher applies it: `epfd` and `fd`
narrowed by `fd32`, `op` by `int32`, the `event` pointer as it arrives —
Rocq's `arm_epoll_ctl` and the row for 21. -/
def check_epoll_ctl_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m

/-- `check_epoll_pwait` as the dispatcher applies it: `epfd` by `fd32`,
`maxevents` by `int32`, the `events` pointer, `sigmask` and `sigsetsize`
as they arrive, and the fourth register — `timeout` — not read at all:
Rocq's `arm_epoll_pwait` and the row for 22. -/
def check_epoll_pwait_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4)
    (in_arg i 5) eff m

/-! ## The register files

What a tracer records at the `ecall`: the number in a7 and the six
argument registers, with the pre-syscall memory for the arms that read
one.  `create1_call` hands its row a memory with no byte mapped, which is
the statement that the row reads none; the other two take the memory a pin
chooses, because both arms read through it. -/

/-- `epoll_create1(flags)`: syscall 20. -/
def create1_call (flags : word) : SyscallInput :=
  SyscallInput.mkInput 20 [flags, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `epoll_ctl(epfd, op, fd, event)`: syscall 21, over the memory `mem`. -/
def ctl_call (epfd op tfd ev : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 21 [epfd, op, tfd, ev, 0, 0] mem mem

/-- `epoll_pwait(epfd, events, maxevents, timeout, sigmask, sigsetsize)`:
syscall 22, over the memory `mem`. -/
def pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 22 [epfd, events, maxevents, timeout, sigmask, sigsetsize] mem mem

/-! ## The checker's own shape: the outcome first, then the effect's ledgers -/

/-- A return-only arm rejects an effect that carries a write beside the
kernel's own errno: `epoll_ctl` stores nothing on a path that ends in
-EPERM (`do_epoll_ctl` returns at :2530-2531 before any store), so each
empty ledger `check_ret_only` demands is load-bearing.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_an_effect_with_a_write_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EPERM) [(4096, [0])] [] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and a DECLINED call is declined whatever the effect's shape: the
outcome function answers `none` before the ledgers are looked at.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_declined_call_is_declined_whatever_the_effect_shape :
    check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EPERM) [(4096, [0])] [] [] [] []) ep_model
      = CheckUnmodeled := by
  rfl

/-- A recorded copy-in is refused, and THAT IS THE MODEL'S OMISSION and
not Linux's answer: `epoll_ctl` does read 16 bytes of the event struct,
and the spec records no copy-in for them
(`linux-process-semantics@ff0313ba4f:bugs/epoll-ctl-copyin-not-recorded.md`).
model: the spec's copy-in ledger is empty on this arm; the kernel's read is real -/
theorem epoll_ctl_a_recorded_copy_in_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
      (with_copyins [(4096, 16)] (mkEffect (errno_ret EPERM) [] [])) ep_model
      = CheckReject := by
  rfl

/-- Every other ledger beside the errno is refused too.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [(4096, 16)] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- `epoll_pwait` writes nothing on any modeled path — `ep_poll` is the
only writer of the events array and no modeled path enters it — so a
zero-fill beside the right errno is refused.
kernel: fs/eventpoll.c:ep_check_params,ep_send_events@v6.18.46 -/
theorem epoll_pwait_an_effect_with_a_zero_fill_is_rejected :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and so is every other ledger.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [(4096, [0])] [] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (with_copyins [(8192, 8)] (mkEffect (errno_ret EINVAL) [] [])) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A declined `epoll_pwait` — a mask that would be installed — is
declined whatever the effect's shape.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_declined_call_is_declined_whatever_the_effect_shape :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
      = CheckUnmodeled := by
  rfl

/-! ## epoll_create1 (20): the one `if`, and the decline past it -/

/-- A well-formed create is declined whatever it is shown: the success
arm is not modeled, so no descriptor and no errno is graded.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_well_formed_create_is_declined :
    check_epoll_create1_row (create1_call 0) (mkEffect 3 [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 524288) (mkEffect 3 [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 0) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- A stray flag bit is -EINVAL and the checker accepts exactly that.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- badflags -/
theorem epoll_create1_a_stray_flag_is_einval :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- A descriptor for a stray flag is the lie `do_epoll_create` never
tells: the gate returns before `get_unused_fd_flags`.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_descriptor_for_a_stray_flag_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect 3 [] []) ep_model = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect 0 [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Another errno for the same stray bit is rejected too.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_foreign_errno_for_a_stray_flag_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- …including the two errnos the path past the gate can raise, which
this path never reaches.
kernel: fs/eventpoll.c:do_epoll_create,ep_alloc; fs/file.c:alloc_fd@v6.18.46 -/
theorem epoll_create1_enomem_and_emfile_for_a_stray_flag_are_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret ENOMEM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EMFILE) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The right errno beside a store is refused: nothing is written.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_einval_with_a_write_is_rejected :
    check_epoll_create1_row (create1_call 1)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [(4096, [0])] [] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and so is every other ledger beside it.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (with_copyins [(4096, 16)] (mkEffect (errno_ret EINVAL) [] [])) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A 32-bit truncation of the errno is not the errno: the return is a
64-bit word.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_truncated_return_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect 4294967274 [] []) ep_model = CheckReject := by
  rfl

/-- `flags` is an `int` (:2473): riscv64's `__SYSCALL_DEFINEx` narrows
the register, so bit 32 alone is the empty word and is declined, while
bit 32 over bit 0 keeps the stray bit.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_create1@v6.18.46 -/
theorem epoll_create1_bit_32_of_flags_is_dropped :
    check_epoll_create1_row (create1_call 4294967296) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 4294967297) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- Every bit of the `int` but bit 19 is a stray bit — `EPOLL_CLOEXEC` is
`O_CLOEXEC` — the sign bit included.
kernel: fs/eventpoll.c:do_epoll_create; include/uapi/linux/eventpoll.h:EPOLL_CLOEXEC@v6.18.46 -/
theorem epoll_create1_every_other_bit_is_a_stray_bit :
    check_epoll_create1_row (create1_call 2147483648) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_create1_row (create1_call 524289) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_create1_row (create1_call 4294967295) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_create1_row (create1_call 18446744073709551615)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## epoll_ctl (21): the copy, the two lookups, the target's `->poll`, -EINVAL

Every pin below that names the top of the address space reads it as
`State.TASK_SIZE`, the Sv48 top: `TASK_SIZE_MAX` is `TASK_SIZE`
(include/asm-generic/access_ok.h, Linux v6.18.46), which is 2^47 under
Sv48 and another power under Sv39 or Sv57 (arch/riscv/include/asm/pgtable.h,
Linux v6.18.46).  A run declaring another size is refused rather than
graded
(`linux-process-semantics@ff0313ba4f:bugs/va-size-declines-every-non-sv48-run.md`),
so the pins hold under the one size the spec compares against. -/

/-- -EFAULT for an unreadable event struct beats -EBADF on either
descriptor: the copy runs in the syscall entry.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem epoll_ctl_the_copy_precedes_the_lookups :
    check_epoll_ctl_row (ctl_call 4294967295 1 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- -EBADF ahead of the copy is the other order, and the checker rejects
it.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_ebadf_ahead_of_the_copy_is_rejected :
    check_epoll_ctl_row (ctl_call 4294967295 1 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  rfl

/-- Under `EPOLL_CTL_DEL` no copy runs, so the closed epfd answers
whatever the event pointer is — a wild one included.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- delbad -/
theorem epoll_ctl_del_skips_the_copy :
    check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 18446744073709551608 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- -EFAULT under `EPOLL_CTL_DEL` is rejected: no copy happens, so the
pointer is never dereferenced.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_ctl_efault_under_del_is_rejected :
    check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckReject := by
  rfl

/-- `op` is an `int`: 2^32 + 2 narrows to `EPOLL_CTL_DEL`, so the copy is
skipped and -EFAULT is refused.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
theorem epoll_ctl_the_row_narrows_op_to_int :
    check_epoll_ctl_row (ctl_call 4294967295 4294967298 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967295 4294967298 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- An unrecognised op copies, so a NULL event is -EFAULT and the -EINVAL
of the switch's fallthrough is refused.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_ctl_an_unknown_op_copies :
    check_epoll_ctl_row (ctl_call 5 7 3 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 7 3 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Twelve mapped bytes are not a `struct epoll_event` on riscv64.
kernel: fs/eventpoll.c:epoll_ctl; include/uapi/linux/eventpoll.h:EPOLL_PACKED@v6.18.46 -/
theorem epoll_ctl_twelve_mapped_bytes_are_a_fault :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 12))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- The -EPERM a twelve-byte reading would reach — an x86-64 reader's
packed struct — is rejected.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_over_a_short_struct_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 12))
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckReject := by
  rfl

/-- Sixteen mapped bytes reach the target.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- perm -/
theorem epoll_ctl_sixteen_mapped_bytes_reach_the_target :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 16))
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- The copy's range is judged before a byte is read, by `__access_ok`'s
own arithmetic: one past `TASK_SIZE` is -EFAULT, ending at it is -EPERM.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_ctl_the_struct_is_judged_against_the_address_space_top :
    check_epoll_ctl_row (ctl_call 5 1 3 140737488355313 ep_mem_all)
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 140737488355312 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …so -EPERM past the top is rejected: the range is refused before the
target is looked at.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_past_the_address_space_top_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 140737488355313 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckReject := by
  rfl

/-- A wrapping struct is -EFAULT, and the -EPERM a byte walk alone would
have reached is rejected.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_wrapping_struct_is_efault :
    check_epoll_ctl_row (ctl_call 5 1 3 18446744073709551608 ep_mem_all)
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 18446744073709551608 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A closed epfd is -EBADF after the copy, and the target's -EPERM is
rejected there.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_closed_epfd_is_ebadf_after_the_copy :
    check_epoll_ctl_row (ctl_call 99 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 99 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A closed target is -EBADF, and the epoll-ness test's -EINVAL is
rejected there.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_closed_target_is_ebadf :
    check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and so is the -EPERM of the `->poll` test.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_for_a_closed_target_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckReject := by
  rfl

/-- A file target is -EPERM and not -EINVAL: the `->poll` test precedes
the epoll-ness test.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_file_target_is_eperm_not_einval :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- A write-mode file and a directory answer the same way.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_write_file_and_a_directory_target_are_eperm :
    check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …and for those two targets the -EINVAL of the epfd test and the 0 of
a successful add are rejected.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_einval_and_success_for_a_write_file_or_a_directory_target_are_rejected :
    check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A socket target HAS a `->poll`, so the epoll-ness test answers:
-EINVAL, and -EPERM and the success are rejected.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll; net/socket.c:sock_poll@v6.18.46 -/
theorem epoll_ctl_a_socket_target_is_einval :
    check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Both pipe ends answer -EINVAL, by the same route.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem epoll_ctl_both_pipe_ends_are_einval :
    check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …and for both ends the -EPERM of a target without `->poll` and the 0
of a successful add are rejected.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem epoll_ctl_eperm_and_success_for_a_pipe_target_are_rejected :
    check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The TARGET and not the epfd is asked for its `->poll`: swap the two
and the answer swaps with them.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_the_target_not_the_epfd_is_asked_for_poll :
    check_epoll_ctl_row (ctl_call 6 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 3 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- `EPOLL_CTL_DEL` on a file target is still -EPERM: skipping the copy
does not skip the `->poll` test, while `EPOLL_CTL_ADD` with the same NULL
pointer is -EFAULT.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_del_on_a_file_target_is_eperm :
    check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none))
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- The two answers `EPOLL_CTL_DEL` has once it reaches the switch — 0 for
a deleted entry and -ENOENT for a missing one — are rejected: the switch
is past the -EINVAL this model always reaches first.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_the_del_switch_answers_are_rejected :
    check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none))
        (mkEffect (errno_ret ENOENT) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none)) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Both descriptors are narrowed to `int` by the row.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_the_row_narrows_both_fds_to_int :
    check_epoll_ctl_row (ctl_call 4294967301 1 4294967299 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967301 1 4294967299 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A 32-bit truncation of the errno is rejected here too.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_truncated_return_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) (mkEffect 4294967295 [] []) ep_model
      = CheckReject := by
  rfl

/-- A channel target is declined, because `fd_can_poll` cannot say
whether its far end has a `->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_channel_target_is_declined :
    check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- /dev/null and /dev/urandom targets are declined until each has its
own probe, though the kernel's answer for both is -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem epoll_ctl_devnull_and_urandom_targets_are_declined :
    check_epoll_ctl_row (ctl_call 5 1 9 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_ctl_row (ctl_call 5 1 10 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- A channel EPFD is judged, because the epfd's kind is read by nothing
this arm reaches: the file target's -EPERM is the answer.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_channel_epfd_is_judged :
    check_epoll_ctl_row (ctl_call 0 1 3 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-! ## epoll_pwait (22): the mask, the epfd, the count, the range, -EINVAL -/

/-- A wrong `sigsetsize` beats a closed epfd: the mask is installed
first.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem epoll_pwait_the_mask_precedes_the_epfd :
    check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 4096 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- -EBADF ahead of the mask is the other order, and the checker rejects
it.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_ebadf_ahead_of_the_mask_is_rejected :
    check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 4096 7 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  rfl

/-- An unreadable mask of the right size is -EFAULT, before the epfd.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_an_unreadable_mask_is_a_fault :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- …and a mapped events buffer does not change it: the mask is read and
the events array is not.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_mapped_events_buffer_does_not_rescue_the_mask :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8 8 (ep_mem_run 4096 16))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model [] := by
  rfl

/-- …and -EBADF for the closed epfd beside that unreadable mask is
rejected.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_ebadf_beside_an_unreadable_mask_is_rejected :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  rfl

/-- Seven mapped bytes of the mask are a fault; eight are a mask that
would be installed, which is declined.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_seven_mapped_bytes_of_the_mask_are_a_fault :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 7))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 7))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 8))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- A NULL mask installs nothing whatever size sits beside it, so the
closed epfd answers -EBADF and the size's -EINVAL is rejected.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_null_is_tested_before_the_size :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 7 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 7 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and with the right size beside the NULL the answer is the same, so
the size decides nothing when the pointer is NULL.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_a_null_mask_of_the_right_size_installs_nothing :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 8 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 0 8 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- A size of 0 beside a NON-NULL mask is the wrong size: -EINVAL.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_zero_size_beside_a_mask_is_einval :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8192 0 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8192 0 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The mask POINTER is full width: 2^32 is not NULL, so the size is
judged and -EINVAL is the answer.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_the_mask_pointer_is_full_width :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4294967296 7 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4294967296 7 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A readable mask of the right size is declined whatever it is shown:
this model has no signals to install one in.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_readable_mask_is_declined :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
        (mkEffect 0 [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The size is a `size_t`, compared full width: 2^32 + 8 is the wrong
size and the answer is -EINVAL, not the decline a size of 8 would give.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_the_size_is_compared_full_width :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 4294967304 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- The mask is read through the range test first: a mask ending past
`TASK_SIZE` is -EFAULT however its bytes are mapped.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_the_mask_is_judged_against_the_address_space_top :
    check_epoll_pwait_row
        (pwait_call 5 4096 1 0 140737488355336 8
          (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- …and one ending exactly at it is a mask that would be installed:
declined.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_mask_ending_at_the_address_space_top_is_declined :
    check_epoll_pwait_row
        (pwait_call 5 4096 1 0 140737488355320 8
          (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckUnmodeled := by
  rfl

/-- A closed epfd with a NULL mask is -EBADF, and the count's -EINVAL is
rejected: the lookup precedes `ep_check_params`.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_the_epfd_precedes_the_count :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- …and a range the test would refuse does not change it either.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_the_epfd_precedes_the_range :
    check_epoll_pwait_row (pwait_call 4294967295 140737488355329 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 140737488355329 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A non-positive `maxevents` on an OPEN epfd is -EINVAL, and the
success and the range's -EFAULT are rejected.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_non_positive_maxevents_is_einval :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 4294967295 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The bound is `INT_MAX / 16`: a count AT it passes and the range is
then judged, a count one past it is -EINVAL before the range is looked
at.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_the_bound_is_int_max_over_sixteen :
    check_epoll_pwait_row (pwait_call 5 4096 134217727 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- The bound is tested BEFORE the range: a count past it beside an
events pointer the range would refuse is -EINVAL and not -EFAULT.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_the_bound_is_tested_before_the_range :
    check_epoll_pwait_row (pwait_call 5 9223372036854775800 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 9223372036854775800 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The array test is a RANGE verdict and not a read: a pointer one past
`TASK_SIZE` is -EFAULT with no byte touched, and the epoll-ness test's
-EINVAL is rejected there.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem epoll_pwait_the_array_is_a_range_verdict_not_a_read :
    check_epoll_pwait_row (pwait_call 5 140737488355313 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 140737488355313 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 140737488355312 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- Every descriptor the fixture holds answers -EINVAL at the epoll-ness
test: none of them is an epoll instance.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem epoll_pwait_every_fixture_epfd_is_einval :
    check_epoll_pwait_row (pwait_call 0 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 3 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 6 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 7 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 9 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 10 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A success on a descriptor that is not an epoll instance is rejected:
`ep_poll` is never reached.
kernel: fs/eventpoll.c:ep_check_params,do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_success_on_a_non_epoll_fd_is_rejected :
    check_epoll_pwait_row (pwait_call 3 4096 1 0 0 0 (fun _ => none))
      (mkEffect 0 [] []) ep_model
      = CheckReject := by
  rfl

/-- The row narrows the epfd and the count to `int`: 2^32 + 5 is fd 5 and
2^32 + 1 is a count of 1, so the answer is the epoll-ness test's -EINVAL
and -EBADF is rejected.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_narrowed_epfd_and_count :
    check_epoll_pwait_row (pwait_call 4294967301 4096 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967301 4096 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and the narrowed count reaches the range test, which refuses this
pointer: -EFAULT.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_the_count_reads_as_int :
    check_epoll_pwait_row (pwait_call 5 140737488355313 4294967297 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- A 32-bit truncation of the errno is rejected.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_truncated_return_is_rejected :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect 4294967274 [] []) ep_model
      = CheckReject := by
  rfl

/-! ## Nothing declines where the spec answers

A checker that answered `CheckUnmodeled` on every input would meet its
five obligations against a spec that declined everywhere.  These pins say
it does not: at an input the spec answers, no effect whatever makes the
checker decline. -/

/-- A stray flag never declines, whatever it is shown and at every model.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_stray_flag_never_declines_for_any_model (m : Model)
    (eff : SyscallEffect) :
    check_epoll_create1_row (create1_call 1) eff m ≠ CheckUnmodeled :=
  fun h => check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [] h

/-- A file target never declines, whatever the checker is shown.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_file_target_answers_whatever_it_is_shown (eff : SyscallEffect) :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) eff ep_model ≠ CheckUnmodeled :=
  fun h => check_ret_only_no_unmodeled eff (errno_ret EPERM) ep_model [] h

/-- A non-epoll epfd never declines either: the spec answers -EINVAL
there, so the checker grades every effect.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem epoll_pwait_a_non_epoll_fd_answers_whatever_it_is_shown (eff : SyscallEffect) :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none)) eff ep_model
      ≠ CheckUnmodeled :=
  fun h => check_ret_only_no_unmodeled eff (errno_ret EINVAL) ep_model [] h

/-- The one `epoll_pwait` decline is keyed on the MASK and on nothing
else: a readable mask of the right size declines at every epfd and every
effect, because `set_user_sigmask` runs before the descriptor is
resolved.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem epoll_pwait_a_readable_mask_declines_at_every_epfd (epfd : word)
    (eff : SyscallEffect) :
    check_epoll_pwait_row (pwait_call epfd 4096 1 0 8192 8 ep_mem_all) eff ep_model
      = CheckUnmodeled := by
  rfl

/-! ## The rows are the dispatcher's

`Sys/Registry/Fs/EventPoll.lean` registers the three arms the spec's
dispatcher applies.  A row could read the right registers, narrow them to
the low 32 bits and still not be the dispatcher's application.  Each
theorem here closes the row's `CheckOk` against `dispatch spec_table`
through the registered arm, by the checker's two `Ok` lemmas; the `exact`
unifies only if the row's narrowing is the arm's, term for term. -/

/-- model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_create1_row_is_the_dispatcher_on_20 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h20 : bv_unsigned i.in_sysno = 20) :
    check_epoll_create1_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_create1_arm (by rw [h20]; rfl)]
  exact ⟨fun h => check_epoll_create1_sound_ok _ _ _ _ _ i h,
         fun h => check_epoll_create1_complete_ok _ _ _ _ _ i h⟩

/-- model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_ctl_row_is_the_dispatcher_on_21 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h21 : bv_unsigned i.in_sysno = 21) :
    check_epoll_ctl_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_ctl_arm (by rw [h21]; rfl)]
  exact ⟨fun h => check_epoll_ctl_sound_ok i _ _ _ _ _ _ _ _ h,
         fun h => check_epoll_ctl_complete_ok i _ _ _ _ _ _ _ _ h⟩

/-- model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_pwait_row_is_the_dispatcher_on_22 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h22 : bv_unsigned i.in_sysno = 22) :
    check_epoll_pwait_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_pwait_arm (by rw [h22]; rfl)]
  exact ⟨fun h => check_epoll_pwait_sound_ok i _ _ _ _ _ _ _ _ _ h,
         fun h => check_epoll_pwait_complete_ok i _ _ _ _ _ _ _ _ _ h⟩

/-- model: the number a same-file register file carries in a7 -/
theorem the_register_files_carry_their_numbers
    (flags epfd op tfd ev events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) :
    bv_unsigned (create1_call flags).in_sysno = 20
    ∧ bv_unsigned (ctl_call epfd op tfd ev mem).in_sysno = 21
    ∧ bv_unsigned (pwait_call epfd events maxevents timeout sigmask sigsetsize mem).in_sysno = 22 :=
  ⟨rfl, rfl, rfl⟩

section V_Fs_EventPoll

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-EventPoll — epoll_create1, epoll_ctl and epoll_pwait over the real table

Each pin here states a call a probe
(`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/epoll_spec.c`,
`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/scenarios/wait_slot_close_reopen.c`)
makes, through
`check_syscall` over `checked_table`, so that the arm's registration is
part of the claim: the lookup at 20, 21 or 22 must find the arm and the
arm must narrow the registers the way the row does. -/

/-- model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_create1_call (flags : word) :
    lookup_ca checked_table (bv_unsigned (create1_call flags).in_sysno)
      = some arm_epoll_create1 :=
  lookup_ca_checked_table_epoll_create1

/-- model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_create1_call (flags : word)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (create1_call flags) eff m
      = check_epoll_create1_row (create1_call flags) eff m :=
  rfl

/-- model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_ctl_call (epfd op tfd ev : word) (mem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (ctl_call epfd op tfd ev mem).in_sysno)
      = some arm_epoll_ctl :=
  lookup_ca_checked_table_epoll_ctl

/-- model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_ctl_call (epfd op tfd ev : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (ctl_call epfd op tfd ev mem) eff m
      = check_epoll_ctl_row (ctl_call epfd op tfd ev mem) eff m :=
  rfl

/-- model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) :
    lookup_ca checked_table
        (bv_unsigned (pwait_call epfd events maxevents timeout sigmask sigsetsize mem).in_sysno)
      = some arm_epoll_pwait :=
  lookup_ca_checked_table_epoll_pwait

/-- model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (pwait_call epfd events maxevents timeout sigmask sigsetsize mem) eff m
      = check_epoll_pwait_row (pwait_call epfd events maxevents timeout sigmask sigsetsize mem)
          eff m :=
  rfl

/-! ### The recorded calls, through `check_syscall` -/

/-- The probe's `conform -- badflags` calls answer -EINVAL at
`do_epoll_create` (fs/eventpoll.c:2439-2440, Linux v6.18.46), before the
allocation.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem badflags_einval_accepted_over_the_real_table (m : Model) :
    check_syscall (create1_call 1)
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (create1_call 0x80001)
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- …and the descriptors the probe's `--mutate` lines offer for them are
rejected.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem badflags_descriptors_rejected_over_the_real_table (m : Model) :
    check_syscall (create1_call 1)
      (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (create1_call 1)
      (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-- The `create` and `trunc` cases are declined: both words pass the gate
once the `int` cast has run.
kernel: fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem create_and_trunc_declined_over_the_real_table (m : Model) :
    check_syscall (create1_call 0)
      (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (create1_call (2^32))
      (mkEffect 3 [] []) m = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The probe's `fault` case: the copy runs before either lookup.
kernel: fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem fault_efault_accepted_over_the_real_table (m : Model) :
    check_syscall (ctl_call 18446744073709551615 1 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] :=
  rfl

/-- The probe's `delbad` case: `EPOLL_CTL_DEL` skips the copy, so the
closed epfd answers -EBADF and -EFAULT is rejected.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem delbad_ebadf_accepted_over_the_real_table :
    check_syscall (ctl_call 18446744073709551615 2 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 18446744073709551615 2 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `perm` case: a directory target has no `->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem perm_eperm_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and a recorded copy-in for it is rejected, which is the model's
omission and not the kernel's answer
(`linux-process-semantics@ff0313ba4f:bugs/epoll-ctl-copyin-not-recorded.md`).
model: the spec's copy-in ledger is empty on this arm; the kernel's read is real -/
theorem perm_recorded_copyin_rejected_over_the_real_table :
    check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (with_copyins [(4096, 16)] (mkEffect (errno_ret EPERM) [] [])) ep_model
      = CheckReject :=
  rfl

/-- The probe's `tgtbad` case: a closed target is -EBADF.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem tgtbad_ebadf_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 18446744073709551615 4096 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model [] := by
  simp only [check_syscall_ctl_call]
  rfl

/-- The probe's `inval` case: a socket target reaches the epoll-ness
test.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll; net/socket.c:sock_poll@v6.18.46 -/
theorem inval_einval_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 6 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 5 1 6 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `chan` case is declined: the model cannot say whether a
channel's far end has a `->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem chan_declined_over_the_real_table :
    check_syscall (ctl_call 5 1 2 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled :=
  rfl

/-- The probe's `pwbadfd` case: a closed epfd is -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwbadfd_ebadf_accepted_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwmaxev` case: a count of 0 and a count of -1 are both
-EINVAL.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwmaxev_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 4096 0 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 4096 18446744073709551615 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- The probe's `sigsize` case: a wrong `sigsetsize` beats the closed
epfd.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem sigsize_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 0 0 8192 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwinval` case: an open epfd that is no epoll instance is
-EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwinval_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwmaxhi` case: one past the bound.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwmaxhi_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 4096 0x8000000 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwsigfault` case: an unreadable mask.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwsigfault_efault_accepted_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwevfault` case: an events pointer the range test
refuses.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevfault_efault_accepted_over_the_real_table :
    check_syscall (pwait_call 5 0x7ffffffffffffff8 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `pwevtop` case: one event ending exactly at `TASK_SIZE`
passes the range test and the epoll-ness test answers.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevtop_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 (2^47 - 16) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 (2^47 - 16) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `pwevpast` case: one byte further on the range test
refuses, and the epoll-ness test's -EINVAL is rejected.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevpast_efault_accepted_over_the_real_table :
    check_syscall (pwait_call 5 (2^47 - 15) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 (2^47 - 15) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `realmask` case is declined: the mask would be installed.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem realmask_declined_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 8192 8 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled :=
  rfl

/-! ### The arm's reading of its registers -/

/-- The `badflags` gate reads a0 through `epoll_create1`'s flags parameter
(fs/eventpoll.c:2473, Linux v6.18.46): an arm reading a1 would accept the
wrong call.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create1_flags_are_a0_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 20 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 20 [1, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- Both `epoll_ctl` descriptors are narrowed to `int` by the arm.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_both_fds_are_narrowed_over_the_real_table :
    check_syscall (ctl_call (2^32 + 5) 1 (2^32 + 5) 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call (2^32 + 5) 1 (2^32 + 5) 4096 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and so is `op`, so a high half over `EPOLL_CTL_DEL` still skips the
copy.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
theorem ctl_op_is_narrowed_over_the_real_table :
    check_syscall (ctl_call 18446744073709551615 (2^32 + 2) 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall
        (ctl_call 18446744073709551615 (2^32 + 2) 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The `epoll_pwait` epfd is narrowed too: 2^32 + 5 is fd 5, which is
open, so the answer is -EINVAL and not -EBADF.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_epfd_is_narrowed_over_the_real_table :
    check_syscall (pwait_call (2^32 + 5) 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call (2^32 + 5) 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- `timeout` is not an argument of the spec at all: a3 changes no
answer.
kernel: fs/eventpoll.c:ep_timeout_to_timespec,do_epoll_wait@v6.18.46 -/
theorem pwait_timeout_is_not_a_spec_argument_over_the_real_table :
    check_syscall (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 4096 1 18446744073709551615 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …and a3 is not read as the mask either: with a3 wild and a4 NULL the
closed epfd still answers.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_timeout_is_not_the_mask_over_the_real_table :
    check_syscall
        (pwait_call 18446744073709551615 4096 1 18446744073709551615 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The mask is a4 and the size is a5: a NULL a4 installs nothing
whatever a5 holds, and a non-NULL a4 with a5 = 7 is -EINVAL.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_mask_is_a4_and_size_is_a5_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 0 7 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 18446744073709551615 4096 1 0 8 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-! ### The witness the table hands `receptive` -/

/-- The table's witnesses for `badflags` and `create` are the -EINVAL of
`do_epoll_create` and the decline past its gate.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create1_witness_over_the_real_table (m : Model) :
    syscall_spec_witness (create1_call 1) m
      = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ syscall_spec_witness (create1_call 0) m = Unmodeled :=
  ⟨rfl, rfl⟩

/-- The `fault` call's witness is its -EFAULT.
kernel: fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_witness_over_the_real_table :
    syscall_spec_witness
        (ctl_call 18446744073709551615 1 18446744073709551615 0 (fun _ => none)) ep_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] :=
  rfl

/-- The `pwinval` call's witness is its -EINVAL, and the `realmask`
call's is the decline.
kernel: fs/eventpoll.c:ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_witness_over_the_real_table :
    syscall_spec_witness (pwait_call 5 4096 1 0 0 0 (fun _ => none)) ep_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model []
    ∧ syscall_spec_witness (pwait_call 18446744073709551615 4096 1 0 8192 8 ep_mem_all) ep_model
      = Unmodeled :=
  ⟨rfl, rfl⟩

end V_Fs_EventPoll

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventPoll
