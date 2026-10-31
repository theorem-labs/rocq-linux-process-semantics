import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Signal — the signal ABI constants

One part of `theories/LinuxProcessSem/Sys/Uapi.v` (see `Sys/Uapi.lean`
for the split).  WHAT GOES HERE: the kernel's `sigset_t` width,
`rt_sigprocmask`'s `how`, `sigaltstack`'s flags, layout and minimum, the
two unblockable signals as mask bits, and SIGABRT.

TRUST BOUNDARY: this file is part of the trusted specification.

riscv defines no uapi/asm/signal.h of its own, so the asm-generic values
are the riscv64 ABI's.  Every line below is read at Linux v6.18.46,
commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `sizeof(sigset_t)` as the KERNEL declares it: `_NSIG` is 64
(`#define _NSIG 64`, include/uapi/asm-generic/signal.h:7, Linux v6.18.46,
commit 1f99e9ab748f), so the mask is 8 bytes.  `set_user_sigmask`
(kernel/signal.c, Linux v6.18.46) rejects any other `sigsetsize` with
-EINVAL.  This is the kernel's sigset, not glibc's 128-byte one. -/
def kernel_sigset_bytes : Int := 8

/-! ## `rt_sigprocmask`'s `how` (include/uapi/asm-generic/signal-defs.h)

Byte-identical across v6.1 - v6.17 as Rocq read them; the lines below are
v6.18.46's. -/

/-- `#define SIG_BLOCK 0` (include/uapi/asm-generic/signal-defs.h:72,
Linux v6.18.46, commit 1f99e9ab748f). -/
def SIG_BLOCK : Int := 0

/-- `#define SIG_UNBLOCK 1` (include/uapi/asm-generic/signal-defs.h:75,
Linux v6.18.46, commit 1f99e9ab748f). -/
def SIG_UNBLOCK : Int := 1

/-- `#define SIG_SETMASK 2` (include/uapi/asm-generic/signal-defs.h:78,
Linux v6.18.46, commit 1f99e9ab748f). -/
def SIG_SETMASK : Int := 2

/-- `sizeof(sigset_t)`, the size `rt_sigprocmask` demands in its fourth
argument and the number of bytes it copies.  Eight, and derived rather
than asserted: `#define _NSIG 64`, `#define _NSIG_BPW __BITS_PER_LONG`,
`#define _NSIG_WORDS (_NSIG / _NSIG_BPW)` and `typedef struct { unsigned
long sig[_NSIG_WORDS]; } sigset_t` (include/uapi/asm-generic/signal.h:7-9
and :61-63, Linux v6.18.46, commit 1f99e9ab748f), and riscv64's
`__BITS_PER_LONG` is `__SIZEOF_POINTER__ * 8`
(arch/riscv/include/uapi/asm/bitsperlong.h:10), i.e. 64, so `sigset_t` is
one 64-bit word.  The same eight bytes as `kernel_sigset_bytes`, which
`set_user_sigmask`'s check on pselect6's sigmask argument names; two
specs arrived at the constant independently, and folding them is a
cleanup neither owns.  NOT musl's userspace `sigset_t`, which is 128
bytes (include/signal.h) — the 8-vs-128 confusion is what
testing/syscall-check/tests/rt_sigprocmask_spec.c pins from both
sides. -/
def NSIG_BYTES : Int := 8

/-! ## sigaltstack (include/uapi/linux/signal.h, include/uapi/asm-generic/signal.h)

SS_AUTODISARM is the whole of `SS_FLAG_BITS` — `#define SS_FLAG_BITS
SS_AUTODISARM` (include/uapi/linux/signal.h:14) — so the two are one
constant and are not spelled twice.  It is what `do_sigaltstack`
(kernel/signal.c, Linux v6.18.46) masks off its `ss_flags` before
comparing the rest against SS_DISABLE, SS_ONSTACK and 0, and what
`on_sig_stack` (include/linux/sched/signal.h, Linux v6.18.46) tests to
answer "not on the stack" without looking at the stack pointer. -/

/-- `#define SS_ONSTACK 1` (include/uapi/linux/signal.h:8, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SS_ONSTACK : Int := 1

/-- `#define SS_DISABLE 2` (include/uapi/linux/signal.h:9, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SS_DISABLE : Int := 2

/-- `#define SS_AUTODISARM (1U << 31)` (include/uapi/linux/signal.h:12,
Linux v6.18.46, commit 1f99e9ab748f), which is also `SS_FLAG_BITS`. -/
def SS_AUTODISARM : Int := 0x80000000

/-- `sizeof(stack_t)` on riscv64: `ss_sp` (8) at 0, `ss_flags` (4, an
`int`) at 8, four bytes of padding, `ss_size` (8, a `__kernel_size_t`) at
16 — 24 bytes.  The struct is the asm-generic one (`typedef struct
sigaltstack { void __user *ss_sp; int ss_flags; __kernel_size_t ss_size; }
stack_t`, include/uapi/asm-generic/signal.h:85-89, Linux v6.18.46, commit
1f99e9ab748f), which riscv does not override.
`SYSCALL_DEFINE2(sigaltstack, ...)` (kernel/signal.c:4455, Linux v6.18.46)
copies exactly `sizeof(stack_t)` out of `uss` in ONE `copy_from_user`, so
readability is all-or-nothing across the whole 24 — the padding
included. -/
def SIGALTSTACK_BYTES : Int := 24
def SS_SP_OFF : Int := 0
def SS_FLAGS_OFF : Int := 8
def SS_SIZE_OFF : Int := 16

/-- The smallest alternate stack `sigaltstack` accepts:
`SYSCALL_DEFINE2(sigaltstack, ...)` (kernel/signal.c:4455, Linux v6.18.46)
passes MINSIGSTKSZ as `do_sigaltstack`'s `min_ss_size`, and riscv takes
`#define MINSIGSTKSZ 2048` (include/uapi/asm-generic/signal.h:56, Linux
v6.18.46, commit 1f99e9ab748f, guarded by `#if !defined MINSIGSTKSZ ||
!defined SIGSTKSZ` at :55, which also sets `SIGSTKSZ 8192`; riscv
supplies no uapi/asm/signal.h to define either first).  Anything
smaller is -ENOMEM.  Not the only lower bound: `sigaltstack_size_valid`
(arch/riscv/kernel/signal.c, Linux v6.18.46, under
CONFIG_DYNAMIC_SIGFRAME) is the other, and is why
`Kernel.Signal.sigaltstack_spec`'s success arm carries a premise. -/
def MINSIGSTKSZ : Int := 2048

/-- The two signals a mask may never contain, as the bits they occupy in
a `sigset_t`: `#define sigmask(sig) (1UL << ((sig) - 1))`
(include/linux/signal.h:127, Linux v6.18.46, commit 1f99e9ab748f),
`#define SIGKILL 9` and `#define SIGSTOP 19`
(include/uapi/asm-generic/signal.h:20 and :30), so the pair is bit 8 |
bit 18.  `SYSCALL_DEFINE4(rt_sigprocmask, ...)`
(kernel/signal.c:3327, Linux v6.18.46) clears exactly these from the set
it is handed, with `sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))`
(line 3342), and answers 0: blocking either is silently ignored, NOT
-EINVAL — the opposite of `rt_sigaction`, where `sig_kernel_only` is an
error (`Kernel.Signal.sig_kernel_only`).

THE STRIP IS THE WRAPPER'S, NOT `sigprocmask`'s (kernel/signal.c): the
comment above that function says so — "Unlike the user-mode
sys_sigprocmask(), the kernel interface happily blocks 'unblockable'
signals like SIGKILL and friends."  So a claim that every path clearing
these bits runs through one function is FALSE; what is true is the
enumeration in `Run.valid_sigmask`. -/
def sig_kernel_only_mask : Int := 262400

/-- `#define SIGABRT 6` (include/uapi/asm-generic/signal.h:16, Linux
v6.18.46, commit 1f99e9ab748f).  Its default disposition is SIG_CORE —
terminate the process and dump core: `sig_kernel_coredump` over
`SIG_KERNEL_COREDUMP_MASK` (include/linux/signal.h:446 and :426, Linux
v6.18.46), which `get_signal` (kernel/signal.c) tests — and the core dump
itself is outside anything this model observes: `vfs_coredump`
(fs/coredump.c:1089, Linux v6.18.46) writes a file the process cannot see
and `do_group_exit` (kernel/exit.c) ends the process either way.  The
Rocq docstring names that entry point `do_coredump` while citing
v6.18.46; no such function exists at that version, so that citation is
stale and the name here is the one the cited tree holds.  What
reaches the trace is the DEATH and the signal number, which a waiting
parent reads through WIFSIGNALED/WTERMSIG and a shell renders as 134. -/
def SIGABRT : Int := 6

/-- `sigmask(SIGABRT)`: `1 << 5`, by the same `sigmask` macro
(include/linux/signal.h:127, Linux v6.18.46, commit 1f99e9ab748f)
`sig_kernel_only_mask` is built from. -/
def sigabrt_mask : Int := 32

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
