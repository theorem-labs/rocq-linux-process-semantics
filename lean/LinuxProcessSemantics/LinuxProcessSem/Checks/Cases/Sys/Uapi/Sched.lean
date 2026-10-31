import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Sched — the `Sys.Uapi.Sched` constants, read off
against Linux

Pins over `Sys/Uapi/Sched.lean`, the constants about the task itself. Not
part of the trusted specification: this file is QA on the definitions,
written to be READ, and every claim in it is a claim about a header or a
function of Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Sched

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The seven policy names are 0, 1, 2, 3, 5, 6, 7 (include/uapi/linux/sched.h:114-121)
and 4 is none of them: the header reserves it for SCHED_ISO (line 118) and
`valid_policy` (kernel/sched/sched.h, Linux v6.18.46) refuses it, so a
range test 0..7 admits a policy Linux answers -EINVAL to. -/
theorem policies :
    [SCHED_NORMAL, SCHED_FIFO, SCHED_RR, SCHED_BATCH, SCHED_IDLE, SCHED_DEADLINE, SCHED_EXT]
      = [0, 1, 2, 3, 5, 6, 7]
    ∧ (4 : Int) ∉ [SCHED_NORMAL, SCHED_FIFO, SCHED_RR, SCHED_BATCH, SCHED_IDLE, SCHED_DEADLINE,
                    SCHED_EXT] := by decide

/-- `SCHED_RESET_ON_FORK` (include/uapi/linux/sched.h:124) shares no bit
with any policy, which is what lets `_sched_setscheduler`
(kernel/sched/syscalls.c, Linux v6.18.46) strip it and still read the
policy. -/
theorem SCHED_RESET_ON_FORK_is_outside_every_policy :
    SCHED_RESET_ON_FORK = 0x40000000
    ∧ [SCHED_NORMAL, SCHED_FIFO, SCHED_RR, SCHED_BATCH, SCHED_IDLE, SCHED_DEADLINE, SCHED_EXT].all
        (fun p => (p.toNat &&& SCHED_RESET_ON_FORK.toNat : Nat) == 0) := by decide

/-- `MAX_RT_PRIO` is 100 (include/linux/sched/prio.h:16, Linux v6.18.46) and
the largest priority `__sched_setscheduler` (kernel/sched/syscalls.c:567,
Linux v6.18.46) accepts is
`MAX_RT_PRIO-1` = 99, the number `sched_get_priority_max(SCHED_FIFO)`
reports; a model refusing at 99 would reject it. -/
theorem MAX_RT_PRIO_is_one_past_the_top :
    MAX_RT_PRIO = 100 ∧ MAX_RT_PRIO - 1 = 99 ∧ MAX_RT_PRIO ≠ 99 := by decide

/-- `CLONE_VM` is bit 8 (include/uapi/linux/sched.h:11, Linux v6.18.46); bit 9
is `CLONE_FS` (line 12), sharing the filesystem information and not the address
space. -/
theorem CLONE_VM_is_bit_8 : CLONE_VM = (1 <<< 8 : Nat) ∧ CLONE_VM ≠ (1 <<< 9 : Nat) := by decide

/-- The futex words (include/uapi/linux/futex.h:11-31, Linux v6.18.46).
`FUTEX_CMD_MASK`
is `~(FUTEX_PRIVATE_FLAG | FUTEX_CLOCK_REALTIME)`, which on a 32-bit `op`
is 0xfffffe7f: it takes the private words back to their commands.  The
private flag is not decoration (`FUTEX_WAKE_PRIVATE ≠ FUTEX_WAKE`: the
two key differently in `get_futex_key`), and it is 128, not
`FUTEX_CLOCK_REALTIME`'s 256 (line 27). -/
theorem futex_words :
    FUTEX_WAIT = 0 ∧ FUTEX_WAKE = 1 ∧ FUTEX_PRIVATE_FLAG = 128
    ∧ FUTEX_WAIT_PRIVATE = 128 ∧ FUTEX_WAKE_PRIVATE = 129
    ∧ (FUTEX_WAIT_PRIVATE.toNat &&& 0xfffffe7f : Nat) = FUTEX_WAIT.toNat
    ∧ (FUTEX_WAKE_PRIVATE.toNat &&& 0xfffffe7f : Nat) = FUTEX_WAKE.toNat
    ∧ FUTEX_WAKE_PRIVATE ≠ FUTEX_WAKE ∧ FUTEX_PRIVATE_FLAG ≠ 256 := by decide

/-- A futex word is 4 bytes (`FLAGS_SIZE_32`, kernel/futex/futex.h), not a
`long`: `get_futex_key` (kernel/futex/core.c, Linux v6.18.46) refuses an
address aligned to 4 but not 8 only under an 8-byte model. -/
theorem FUTEX_WORD_SIZE_is_four : FUTEX_WORD_SIZE = 4 ∧ FUTEX_WORD_SIZE ≠ 8 := by decide

/-- `WNOHANG` is bit 0 (include/uapi/linux/wait.h:5, Linux v6.18.46); bit 1 is
`WUNTRACED` (line 6), under which wait4 also reports stopped children. -/
theorem WNOHANG_is_bit_0 : WNOHANG = 1 ∧ WNOHANG ≠ 2 := by decide

/-- `(uid_t)-1` is the 32-bit 0xffffffff after `Syscall.uid32`, not the
64-bit -1 a register carries: `setuid(-1)` reaches `make_kuid`
(include/linux/uidgid.h:139, Linux v6.18.46) as 0xffffffff. -/
theorem ID_MINUS_ONE_is_32_bits :
    bv_unsigned ID_MINUS_ONE = 2 ^ 32 - 1 ∧ ID_MINUS_ONE ≠ Z_to_bv 64 (-1) := by decide

/-- `RLIMIT_CORE` is 4 (include/uapi/asm-generic/resource.h:20, Linux v6.18.46),
not `RLIMIT_STACK`'s 3 (line 19) — the limit `State.stack_max_size` fixes. -/
theorem RLIMIT_CORE_is_four : RLIMIT_CORE = 4 ∧ RLIMIT_CORE ≠ 3 := by decide

/-- `NGROUPS_MAX` is 65536 (include/uapi/linux/limits.h:7, Linux v6.18.46):
`setgroups` (kernel/groups.c:198, Linux v6.18.46) accepts a `gidsetsize` of exactly 65536, which a
bound of 2^16 - 1 would refuse. -/
theorem NGROUPS_MAX_is_2_16 : NGROUPS_MAX = 2 ^ 16 ∧ NGROUPS_MAX ≠ 2 ^ 16 - 1 := by decide

/-- `struct new_utsname` is six `char[__NEW_UTS_LEN + 1]` members
(include/uapi/linux/utsname.h:15 and :25-32, Linux v6.18.46): 6 × 65 = 390
bytes, not the 6 × 64 = 384 of a model that dropped the terminators — under
which the last six bytes of the single `copy_to_user` in `newuname`
(kernel/sys.c:1351-1359, Linux v6.18.46) would go unchecked. -/
theorem utsname_layout :
    NEW_UTS_LEN = 64 ∧ NEW_UTSNAME_SIZE = 6 * (NEW_UTS_LEN + 1)
    ∧ NEW_UTSNAME_SIZE ≠ 6 * NEW_UTS_LEN := by decide

/-- `PR_CAPBSET_READ` is 23 (include/uapi/linux/prctl.h:71, Linux v6.18.46);
24 is `PR_CAPBSET_DROP` (line 72), which changes the bounding set rather than
reading it. -/
theorem PR_CAPBSET_READ_is_23 : PR_CAPBSET_READ = 23 ∧ PR_CAPBSET_READ ≠ 24 := by decide

/-- `CAP_LAST_CAP` is `CAP_CHECKPOINT_RESTORE` = 40 (include/uapi/linux/capability.h:421-423),
not `CAP_BPF` = 39 (line 414), the last capability before v5.9:
`cap_valid(40)` holds and `prctl(PR_CAPBSET_READ, 40)` answers. -/
theorem CAP_LAST_CAP_is_40 : CAP_LAST_CAP = 40 ∧ CAP_LAST_CAP ≠ 39 := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Sched
