import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi — pins that reach across two of the Uapi parts

Not part of the trusted specification.  `Sys/Uapi.lean` is the re-export
of six subsystem files; the pins that need a name from two of them at once
live here, beside the twin that joins them, and the per-part pins live in
`Checks/Cases/Sys/Uapi/<part>.lean`.  Every claim is about Linux v6.18.46,
commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the citation beside
it, and none is about the Rocq definitions. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- riscv64 falls through to `#define SOCK_CLOEXEC O_CLOEXEC` and
`#define SOCK_NONBLOCK O_NONBLOCK` (include/linux/net.h:80 and :82, Linux
v6.18.46, commit 1f99e9ab748f), so the socket flags ARE the open flags —
a fact the two files can only state together. -/
theorem sock_flags_are_the_open_flags :
    SOCK_CLOEXEC = O_CLOEXEC ∧ SOCK_NONBLOCK = O_NONBLOCK := by decide

/-- `set_user_sigmask` and `rt_sigprocmask` (kernel/signal.c, Linux
v6.18.46) test the same `sizeof(sigset_t)`; the two constants that reached
it independently agree, and neither is the 128 bytes of a libc
`sigset_t`. -/
theorem the_two_sigset_widths_agree :
    kernel_sigset_bytes = NSIG_BYTES ∧ kernel_sigset_bytes ≠ 128 := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi
