import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.DPath — getcwd (17)

Mirrors `theories/LinuxProcessSem/Sys/Fs/DPath.v`, which answers to Linux
`fs/d_path.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Both definitions keep the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and version, every
line read in Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.

One spelling differs from Rocq without changing a value: the `Z.ltb` size
test is Lean's decidable `<` on `Int`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- getcwd's injectable failures: the three answers that depend on kernel
or file-system state this model does not carry, all decided BEFORE the
size comparison in `SYSCALL_DEFINE2(getcwd)` (fs/d_path.c, Linux v6.18.46,
commit 1f99e9ab748f), so they live on every arm of `getcwd_spec`.

- `ENOMEM`: `__getname()` is the very first statement, a `GFP_KERNEL`
  allocation out of `names_cachep` (`__getname`, include/linux/fs.h, Linux
  v6.18.46) that can fail; it is the only error returned before the RCU
  section runs.
- `ENOENT`: `d_unlinked(pwd.dentry)` (`d_unlinked`, include/linux/dcache.h,
  Linux v6.18.46: unhashed and not its own root) — the working directory
  was removed from under the caller.  NOT the unreachable case: a working
  directory outside the caller's root is a SUCCESS prefixed
  "(unreachable)".
- `ENAMETOOLONG`: the assembled path did not fit `PATH_MAX`, which
  `prepend` and `prepend_char` (fs/d_path.c, Linux v6.18.46) signal by
  driving the buffer's `len` to -1.

`EFAULT` is deliberately absent: its `copy_to_user` runs only AFTER the
size comparison, which the modeled band never gets past.  The Rocq
definition carries the argument in full. -/
def getcwd_errnos : List Int := [ENOMEM, ENOENT, ENAMETOOLONG]

/-- `getcwd buf size`: copy the caller's working directory out and return
its length INCLUDING the terminating NUL (`error = len;` in
`SYSCALL_DEFINE2(getcwd)`, fs/d_path.c, Linux v6.18.46, commit
1f99e9ab748f).

THERE IS NO WORKING DIRECTORY IN THIS MODEL: `State.Model` has no pwd
field and `Fs` is a flat map from uninterpreted names to bytes, with no
root, no directories and no resolution, so the string getcwd would return
is not a function of any modeled state.  Every outcome that would carry
it — the success return and the `-EFAULT` decided after it — is
`unmodeled`, fail closed.  The Rocq definition says when that stops being
true (directories in `Fs`, a pwd in `State.Model`).

WHAT IS LEFT IS THE BAND WHERE THE WORKING DIRECTORY CANNOT MATTER.  The
kernel's `len` is at least 2 on every path that reaches `len > size`:
`DECLARE_BUFFER(b, page, PATH_MAX)` starts `b.len` at `PATH_MAX`,
`prepend_char(&b, 0)` spends one byte on the NUL, and `prepend_path`
either overflows (`b.len` = -1, caught FIRST as `-ENAMETOOLONG` by the
`len > PATH_MAX` test) or spends at least one more — its tail
`if (b.len == p->len) prepend_char(&b, '/')` charges the "/" even for a
working directory equal to the root — and when it answered `> 0` the
caller spends thirteen more on the "(unreachable)" literal, which can
itself overflow (`prepend_path`, `prepend_char`, `prepend`, fs/d_path.c,
Linux v6.18.46).  So for `size` of 0 or 1, `len > size` holds for EVERY
working directory and the answer is `-ERANGE` or one of `getcwd_errnos`.
Why `b.len` can never RISE is argued on the Rocq definition: only a
`prepend` with a negative `namelen` could raise it, and no dentry holds a
name of 2^31 bytes, because `__d_alloc` (fs/dcache.c, Linux v6.18.46)
stores a name longer than the inline slot through a `kmalloc` sized from
`name->len`, which fails above `KMALLOC_MAX_SIZE` (include/linux/slab.h,
Linux v6.18.46: `MAX_PAGE_ORDER` 10 of include/linux/mmzone.h plus the
4 KiB page shift, so 4 MiB on riscv64).

`buf` IS NOT AN ARGUMENT.  The kernel's sequence is `-ENOMEM`, `-ENOENT`,
the path built into a KERNEL page, `-ENAMETOOLONG`, `-ERANGE`, and only
then a single `copy_to_user`; there is no `access_ok` and no probe of
`buf` earlier, so `getcwd(NULL, 0)` really is `-ERANGE` — on Linux.
QEMU's user-mode emulation, a supported implementation, locks the guest
buffer BEFORE the host call (`TARGET_NR_getcwd`, linux-user/syscall.c:12285-12286,
QEMU 11.1.1; `lock_user`, linux-user/uaccess.c:8-25) and answers -EFAULT
where Linux never reads the pointer: at size 1 for a `buf` that is not
guest memory, and at size 0 for a `buf` above `reserved_va` under `-R`.
Both are real behaviors this arm refuses — Linux's answer proved certain
where the intersection is empty.  (`getcwd(NULL, 0)` is -EFAULT there
too when `guest_base` is 0, but by a defect QEMU's own source calls one,
so the model does not owe it.)  The arm keeps Linux's answer and the pins
refuse qemu-user's; bugs/getcwd-erange-band-admits-linux-alone.md
records the shapes, what keeping them costs and what closes them.  The `-EINVAL`
POSIX documents for a zero size is glibc's own and never reaches the
kernel: glibc's sysdeps/unix/sysv/linux/getcwd.c answers a zero `size`
with a non-null `buf` before issuing the call, and substitutes `PATH_MAX`
when `buf` is null.  That half is not pinned to a glibc version because
nothing here rests on it; what does is that the syscall body has no
`-EINVAL` arm at all, which is read from the fs/d_path.c above.

Nothing is written on any admitted arm: the effect is a bare return with
five empty ledgers.  `-ERANGE` and the three injectable errnos are an
`alt` rather than a ranking because they are not a priority order over
one state: in any single run exactly one applies, decided by allocator,
dcache and directory-depth conditions the model does not carry. -/
def getcwd_spec (size : word) : Sys SyscallEffect :=
  if 1 < bv_unsigned size then unmodeled   -- the cwd would decide it: fail closed
  else alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret ERANGE)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath
