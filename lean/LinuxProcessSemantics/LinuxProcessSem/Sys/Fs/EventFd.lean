-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/EventFd.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Sys.Fs.EventFd — eventfd2 (19)

Mirrors `theories/LinuxProcessSem/Sys/Fs/EventFd.v`, which answers to
Linux `fs/eventfd.c`: it holds what the kernel defines there, and nothing
else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq header is where the version windows and the `CONFIG_EVENTFD`
premise are argued, and neither is restated here.  The walk of every
errno below the gate IS restated below, because the Rocq header's walk
omits an errno the path can produce (-ENFILE).

One spelling differs from Rocq without changing a value: the bit test on
the flag word is done on the `word` (`bv_and`, `bv_not`) where Rocq does
it on `bv_unsigned` in `Z` (`Z.ldiff`).  `EFD_FLAGS_SET` is below `2^64`,
so the two agree on every word.

THIS ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE, as the Rocq
file does and for the reason its header gives: every input that survives
the gate creates a file descriptor, and `State.FdEntry` has no eventfd
kind to put the counter behind.  The `unmodeled` arm below is Rocq's, not
a declared decline of this port. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The flag mask `eventfd2` admits, written out of the kernel's own `if`:
`if (flags & ~EFD_FLAGS_SET) return -EINVAL;` in `do_eventfd`
(fs/eventfd.c:390-391, Linux v6.18.46, commit 1f99e9ab748f).  The residue
is used directly as the `if` condition — a truthiness test, not a sign
test — so bit 31 alone is refused exactly as bit 1 is; `bv_and` with the
complemented mask is that residue, and the test is against zero.  The word
arrives already narrowed to 32 bits by `Syscall.flag32` at the table, as
`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)`
(fs/eventfd.c:423, Linux v6.18.46) declares `flags` an `int`; this
predicate must not
narrow it again.  RESTATED rather than shared with an acceptor, for the
reason on the Rocq definition `eventfd2_einval_b`: a gate every layer
imported from one place would agree with itself however wrong it was.
Rocq: `negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)`. -/
def eventfd2_einval_b (flags : word) : Bool :=
  !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0)

/-- `eventfd2 count flags`: create a descriptor holding a 64-bit counter.

No `get_model` and no `count`: the answer is a function of the flag word
alone.  The gate is the first statement of `do_eventfd` (fs/eventfd.c:379,
Linux v6.18.46, commit 1f99e9ab748f) that can fail — the three
`BUILD_BUG_ON`s before it (lines 386-388) are compile-time — and it sits
above the `kmalloc` (line 393), the `ctx->count = count` store (line 399)
and the `get_unused_fd_flags` (line 405), so the refused-word arm touches
no memory, emits no event, changes no state and reserves no descriptor,
and `count` is read by nothing this arm answers.  Everything past the
gate ends in one of four answers, walked from the source so the decline
is a named list rather than "the rest", every line at Linux v6.18.46.
-ENOMEM: from the `kmalloc` (fs/eventfd.c:393-395, Linux v6.18.46);
from `alloc_fdtable` (fs/file.c:242, Linux v6.18.46), which `alloc_fd`
(fs/file.c:596) reaches through `expand_files` (fs/file.c:315) and
`expand_fdtable` (fs/file.c:259, forwarded at :268-269, Linux v6.18.46);
from `alloc_empty_file` (fs/file_table.c:260, Linux v6.18.46) and,
inside it, from `init_file` (fs/file_table.c:180-183) forwarding
`lsm_file_alloc` (security/security.c:772-774, Linux v6.18.46, through
`security_file_alloc` at :2958-2968); or from `alloc_path_pseudo`
(fs/file_table.c:402, Linux v6.18.46).  -EMFILE: from `alloc_fd`
(fs/file.c:591, the RLIMIT_NOFILE test, Linux v6.18.46), from
`expand_files` (fs/file.c:310-311, the fs.nr_open sysctl) or from
`alloc_fdtable` (fs/file.c:197 and :213, Linux v6.18.46), all under
`get_unused_fd_flags` (fs/file.c:620), which `do_eventfd` calls at
fs/eventfd.c:405.  -ENFILE: the system-wide file table's refusal, which
`alloc_empty_file` decides at fs/file_table.c:248-255 and returns at :278
(Linux v6.18.46) for a caller without CAP_SYS_ADMIN, reached from
`do_eventfd` (fs/eventfd.c:409-410, Linux v6.18.46) through
`anon_inode_getfile_fmode` (fs/anon_inodes.c:226, calling at :232),
`__anon_inode_getfile` (fs/anon_inodes.c:134, calling at :166, Linux
v6.18.46), `alloc_file_pseudo` (fs/file_table.c:408, calling at :420)
and `alloc_file` (fs/file_table.c:386, calling at :391, Linux v6.18.46).
And the descriptor number.  All declined, fail closed, for the reason
the Rocq definition `eventfd2_spec` and its file header give.

Neither -ENOENT nor -ENODEV can arise from the path's own tests: -ENOENT
(fs/anon_inodes.c:143-144, Linux v6.18.46) needs a `fops->owner`, and
`eventfd_fops` (fs/eventfd.c:302-311, Linux v6.18.46) has none, while
-ENODEV (fs/anon_inodes.c:155-156, Linux v6.18.46) needs the shared anon
inode to be an error pointer, which `anon_inode_init` panics on
(fs/anon_inodes.c:370-372, Linux v6.18.46).

ONE PREMISE the walk rests on: that no LSM `file_alloc_security` hook
returns nonzero.  `security_file_alloc` (security/security.c:2958-2968,
Linux v6.18.46) forwards the first nonzero answer of any hook, and
`alloc_empty_file` (fs/file_table.c:262-265, Linux v6.18.46) hands it up
this chain unchanged, so a hook can make an ACCEPTED word end in any
errno at all, -ENOENT and -EINVAL included.  Every static hook in the
tree returns 0: `selinux_file_alloc_security`
(security/selinux/hooks.c:3814-3823, Linux v6.18.46),
`smack_file_alloc_security` (security/smack/smack_lsm.c:1718-1724, Linux
v6.18.46), `apparmor_file_alloc_security` (security/apparmor/lsm.c:503-512,
Linux v6.18.46) and Landlock's `hook_file_alloc_security`
(security/landlock/fs.c:1610-1622, Linux v6.18.46).  Under
CONFIG_BPF_LSM (kernel/bpf/Kconfig:92, Linux v6.18.46) a BPF program
attached to the hook may return any errno: `bpf_lsm_get_retval_range`
(kernel/bpf/bpf_lsm.c:447-467, Linux v6.18.46) admits `[-MAX_ERRNO, 0]`.
That is a kernel configuration and policy choice, so CLAUDE.md's scope
admits it.  Native riscv64 `do_eventfd` refuses words outside its mask at
fs/eventfd.c:390-391 (Linux v6.18.46) before any allocation or hook, so
nothing here turns on the list.

CONFIG_EVENTFD IS ASSUMED ON.  fs/Makefile builds eventfd.o under
obj-$(CONFIG_EVENTFD) and kernel/sys_ni.c carries
`COND_SYSCALL(eventfd2)`, so a kernel built without it answers -ENOSYS to
every input this arm calls -EINVAL; init/Kconfig gives `config EVENTFD` a
`default y` and hides its prompt behind EXPERT.  It is stated rather than
tested because no syscall argument distinguishes the two builds, and it
is the ONE premise outside this call's own arguments that the -EINVAL
rests on. -/
def eventfd2_spec (flags : word) : Sys SyscallEffect :=
  if eventfd2_einval_b flags
  then err_ret EINVAL      -- real -EINVAL, decided before anything is allocated
  else unmodeled           -- ENOMEM / EMFILE / ENFILE / the descriptor: fail closed

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
