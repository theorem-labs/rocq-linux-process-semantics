import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Signal — the `Sys.Uapi.Signal` constants, read off
against Linux

Pins over `Sys/Uapi/Signal.lean`, the signal constants. Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about a header or a function of
Linux v6.18.46, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the
citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Signal

open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `rt_sigprocmask`'s `how` is 0/1/2 (include/uapi/asm-generic/signal-defs.h:72-78,
Linux v6.18.46), not sparc's 1/2/4 (arch/sparc/include/uapi/asm/signal.h:145-147,
Linux v6.18.46): under
the sparc numbering `SIG_BLOCK` would be read as unblock. -/
theorem sigprocmask_how :
    SIG_BLOCK = 0 ∧ SIG_UNBLOCK = 1 ∧ SIG_SETMASK = 2 ∧ SIG_BLOCK ≠ 1 := by decide

/-- The kernel's `sigset_t` is `_NSIG / __BITS_PER_LONG` = 64 / 64 = one
word, 8 bytes (include/uapi/asm-generic/signal.h:7-9 and :61-63, Linux
v6.18.46) — not the
128 bytes of musl's or glibc's userspace `sigset_t`, which passed as
`sigsetsize` is the -EINVAL testing/syscall-check/tests/rt_sigprocmask_spec.c
pins. -/
theorem sigset_is_one_word :
    NSIG_BYTES = 8 ∧ NSIG_BYTES * 8 = 64 ∧ kernel_sigset_bytes = 8 ∧ NSIG_BYTES ≠ 128 := by
  decide

/-- `sigaltstack`'s flags (include/uapi/linux/signal.h:8-14): `SS_AUTODISARM`
is bit 31 and shares no bit with the two modes, which is what lets
`do_sigaltstack` (kernel/signal.c, Linux v6.18.46) mask it off and compare
the rest against SS_DISABLE, SS_ONSTACK and 0. -/
theorem sigaltstack_flags :
    SS_ONSTACK = 1 ∧ SS_DISABLE = 2 ∧ SS_AUTODISARM = 2 ^ 31
    ∧ (SS_AUTODISARM.toNat &&& (SS_ONSTACK.toNat ||| SS_DISABLE.toNat) : Nat) = 0 := by decide

/-- `stack_t` on riscv64 (include/uapi/asm-generic/signal.h:85-89, Linux
v6.18.46): 24 bytes with `ss_size` at 16, because the 8-byte `__kernel_size_t` is
aligned past the `int`.  A packed reading — 20 bytes, `ss_size` at 12 —
would read the padding as the size and check four bytes too few. -/
theorem sigaltstack_layout :
    SIGALTSTACK_BYTES = 24 ∧ SS_SP_OFF = 0 ∧ SS_FLAGS_OFF = 8 ∧ SS_SIZE_OFF = 16
    ∧ SIGALTSTACK_BYTES ≠ 20 ∧ SS_SIZE_OFF ≠ 12 := by decide

/-- `MINSIGSTKSZ` is the asm-generic 2048 (include/uapi/asm-generic/signal.h:56,
Linux v6.18.46), not arm64's 5120 (arch/arm64/include/uapi/asm/signal.h:23,
Linux v6.18.46): a 4096-byte
alternate stack is accepted on riscv64 and -ENOMEM under the arm64
value. -/
theorem MINSIGSTKSZ_is_generic : MINSIGSTKSZ = 2048 ∧ MINSIGSTKSZ ≠ 5120 := by decide

/-- `sigmask(sig)` is `1UL << ((sig) - 1)` (include/linux/signal.h:127, Linux
v6.18.46), so
SIGKILL (9) and SIGSTOP (19) are bits 8 and 18.  Forgetting the `- 1`
gives bits 9 and 19 — SIGUSR1 (10) and SIGTSTP (20) — and would let a
program block SIGKILL while silently unblocking two signals it asked to
block. -/
theorem sig_kernel_only_mask_is_bits_8_and_18 :
    sig_kernel_only_mask = ((1 <<< (9 - 1)) ||| (1 <<< (19 - 1)) : Nat)
    ∧ sig_kernel_only_mask ≠ ((1 <<< 9) ||| (1 <<< 19) : Nat) := by decide

/-- SIGABRT is 6 (include/uapi/asm-generic/signal.h:16, Linux v6.18.46) and its
mask bit
is `1 << 5`, by the same `sigmask` macro; `1 << 6` is SIGBUS's (7). -/
theorem SIGABRT_and_its_bit :
    SIGABRT = 6 ∧ sigabrt_mask = (1 <<< (6 - 1) : Nat) ∧ sigabrt_mask ≠ (1 <<< 6 : Nat) := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Signal
