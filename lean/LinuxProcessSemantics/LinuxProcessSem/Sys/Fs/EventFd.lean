import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
divergence: bugs/eventfd2-enosys-beside-einval-admits-mixed-runs.md -- inherited
drift-ticket: eventfd2_spec R-Fs-EventFd-rebase -- Rocq admits -ENOSYS beside -EINVAL for CONFIG_EVENTFD=n (#1354) and declines refused words accepted by sparc64, mips or parisc qemu-user hosts (#1694); baseline moves after the T169 PR lands -/

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
alternative are argued, and neither is restated here.  The walk of every
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

/-- Linux v6.18.46 include/uapi/asm-generic/errno.h `ENOSYS`. -/
def ENOSYS : Int := 38

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
admits it. Native riscv64 `do_eventfd` refuses words outside its mask at
fs/eventfd.c:390-391 (Linux v6.18.46) before any allocation or hook.
Words that can reach allocation, including guest-refused words accepted
through QEMU's host translation below, are declined whatever they return.
Nothing here turns on the list.

-ENOSYS IS ADMITTED BESIDE THE -EINVAL.  Linux v6.18.46
fs/Makefile builds eventfd.o under obj-$(CONFIG_EVENTFD);
kernel/sys_ni.c `COND_SYSCALL(eventfd2)` and riscv64's
arch/riscv/include/asm/syscall_wrapper.h `COND_SYSCALL` route the
missing syscall to kernel/sys_ni.c `sys_ni_syscall` (Linux v6.18.46),
returning -ENOSYS.
init/Kconfig's EVENTFD prompt is conditional on EXPERT and defaults
to y.  Its selectors are MEMCG (init/Kconfig), KVM_COMMON
(virt/kvm/Kconfig), MSHV_ROOT (drivers/hv/Kconfig), VFIO_VIRQFD
(drivers/vfio/Kconfig), VFIO_CDX (drivers/vfio/cdx/Kconfig),
VFIO_FSL_MC (drivers/vfio/fsl-mc/Kconfig), and ACRN_HSM
(drivers/virt/acrn/Kconfig), all Linux v6.18.46: disabling EVENTFD
requires an EXPERT configuration with every selector off too.

QEMU v11.1.1 linux-user/syscall.c `do_syscall1` compiles its
TARGET_NR_eventfd2 case only under CONFIG_EVENTFD.  meson.build sets
that from a build-time link test against host libc's eventfd, not a
host-kernel test.  Without it, the default returns -TARGET_ENOSYS;
with it, the case forwards the host answer, including -ENOSYS from
a CONFIG_EVENTFD=n host.

No example reaches eventfd2. Declining every input
would collide with Checks/DispatchSurface.v modeled_sysnos_exact and
tools/check_lean_pins.py PIN-8, which require an answered shape for
19. It costs priority 2: mixed runs with -EINVAL then -ENOSYS, or the
reverse, on refused words are admitted though no single implementation
produces both.  See
bugs/eventfd2-enosys-beside-einval-admits-mixed-runs.md.  The proper
fix is a declared run configuration (a kernel built without
CONFIG_EVENTFD), part of the coming run-environment design for
LSM/seccomp/prlimit. Retire that entry when the declaration fixes
availability for the whole run and tests reject both mixed orders
while accepting both configurations. Both answers touch no memory,
emit no event and change no state; kernel/sys_ni.c `sys_ni_syscall`
(Linux v6.18.46) touches nothing.

QEMU v11.1.1 linux-user/syscall.c `do_syscall1`:13865-13879 clears the
target's `TARGET_O_NONBLOCK_MASK | TARGET_O_CLOEXEC` bits.  It sets the
host O_NONBLOCK or O_CLOEXEC when the target's `TARGET_O_NONBLOCK` or
`TARGET_O_CLOEXEC` bit is set.  It gives the other low 32 bits to host
libc `eventfd` unchanged.  `TARGET_O_NONBLOCK_MASK` is `TARGET_O_NONBLOCK`
(syscall.c:312-313), except on hppa.  QEMU v11.1.1
linux-user/hppa/target_fcntl.h:12 adds bit 2 to the hppa mask.  Thus an
hppa layer clears bit 2 and does not translate it.  The riscv64 target
takes QEMU v11.1.1 linux-user/generic/fcntl.h:32,56.  Thus a riscv64
layer clears bits 11 and 19 and passes the other low bits unchanged.
QEMU v5.2.0 uses `TARGET_O_NONBLOCK` in place of the mask. Its
linux-user/hppa/target_fcntl.h:11 defines `TARGET_O_NONBLOCK` as
000200004. Thus bit 2 or bit 16 sets the host O_NONBLOCK there.
v0.12.0 to v1.4.2 translate nothing. Their
`do_syscall` calls `eventfd(arg1, arg2)` (QEMU v1.4.2
linux-user/syscall.c:8745-8747).
Linux v6.18.46 (commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5)
arch/sparc/include/uapi/asm/fcntl.h:11,21 gives O_NONBLOCK = 2^14 and
O_CLOEXEC = 2^22; arch/mips/include/uapi/asm/fcntl.h:16 gives
O_NONBLOCK = 2^7. include/linux/eventfd.h EFD_FLAGS_SET uses those
host values, so fs/eventfd.c do_eventfd can allocate a descriptor.
QEMU v11.1.1 configure:392-397 and :472-475 select the sparc64 host;
v11.0.0 configure:449-452 still selects the mips64 host. CLAUDE.md
pins no single QEMU version (11.1.1 is only the VM tracer's), so older
linux-user hosts count; this decline costs priority 3 only.
QEMU can itself run under qemu-user (QEMU v11.1.1 https://github.com/qemu/qemu/blob/v11.1.1/docs/user/main.rst#L59-L61).
For example, a riscv64 QEMU built for sparc64 can run under qemu-sparc64
on mips64: the inner layer passes 0x4080, and the outer layer maps
SPARC's 0x4000 to MIPS's 0x80 while passing the existing 0x80 through.
The result reaches fs/eventfd.c do_eventfd as a valid MIPS flag word.
QEMU v11.1.1 linux-user/sparc/target_fcntl.h:17,27 and
linux-user/mips/target_fcntl.h:13 give the target values.
Every layer runs a QEMU binary, so its target must itself be a QEMU host
architecture of the QEMU release that runs it.

The riscv64 layer is QEMU v2.12.0 or later: v2.12.0's configure is the
first to know the riscv64 target
(https://github.com/qemu/qemu/blob/v2.12.0/configure#L6870-L6874),
while v2.11.0's configure names no riscv target
(https://github.com/qemu/qemu/blob/v2.11.0/configure).
The layers outside it emulate its host, not riscv64, so they can be
older releases. QEMU v1.6.0 supports an hppa Linux host:
https://github.com/qemu/qemu/blob/v1.6.0/configure#L417-L419 selects hppa,
https://github.com/qemu/qemu/blob/v1.6.0/configure#L544-L548 enables linux-user,
and https://github.com/qemu/qemu/blob/v1.6.0/user-exec.c#L597 supplies its
host signal handler. Thus a riscv64 QEMU built for i386 can run under
v1.6.0 i386-linux-user on parisc, passing bit 21 through both layers.
Linux v6.18.46 arch/parisc/include/uapi/asm/fcntl.h:11,15 defines
O_NONBLOCK = 2^16 and O_CLOEXEC = 2^21.
arch/parisc/kernel/syscalls/syscall.tbl:353 routes eventfd2 to
arch/parisc/kernel/sys_parisc.c parisc_eventfd2:355-359, which calls
FIX_O_NONBLOCK:317-329 to clear the old bit 2 before sys_eventfd2.
Bits 2, 16 and 21 can reach allocation, alone or beside the SPARC/MIPS
bits above. After removing guest flags, test against the union
U = {2^2, 2^7, 2^14, 2^16, 2^21, 2^22} = 0x614084.

WHY A BIT OUTSIDE U IS ANSWERED.  Take a flag word with a bit b outside
U and outside EFD_FLAGS_SET.  Native riscv64 Linux refuses it at
fs/eventfd.c:390-391 (Linux v6.18.46).  The riscv64 qemu-user layer passes b unchanged.
An outer layer passes b unchanged too: in each surveyed QEMU release,
each target's `TARGET_O_NONBLOCK`, `TARGET_O_NONBLOCK_MASK` and
`TARGET_O_CLOEXEC` lies in U plus bits 11 and 19.  At the bottom, each
Linux arch's O_NONBLOCK and O_CLOEXEC lies in the same set.  At
v6.18.46, the values come from
arch/{alpha,mips,parisc,sparc}/include/uapi/asm/fcntl.h and from
include/uapi/asm-generic/fcntl.h for the other arches.  Linux v4.17
arch/parisc/include/uapi/asm/fcntl.h:12 (O_NONBLOCK 000200004) adds only
bit 2.  At v6.18.46 the only arch wrapper, parisc_eventfd2, clears only
bit 2.  Thus the host's do_eventfd refuses b before it allocates.
Host libc keeps b.  glibc 2.42 sysdeps/unix/sysv/linux/syscalls.list:11
makes `eventfd` the eventfd2 syscall.  Without `__ASSUME_EVENTFD2`,
glibc 2.17 sysdeps/unix/sysv/linux/eventfd.c `eventfd` turns -ENOSYS
into EINVAL for nonzero flags.  musl 1.2.5 src/linux/eventfd.c
`eventfd` calls the flagless eventfd only for zero flags.  QEMU without
CONFIG_EVENTFD answers -ENOSYS.  Thus the answer is -EINVAL or -ENOSYS.
The survey read the 190 three-part QEMU release tags v0.10.0 to
v11.1.2.  The design review also read v1.0, v2.4.0.1, v2.5.1.1,
v2.8.1.1 and v3.1.1.1.  This argument stops being true in four cases:
- a QEMU target mask, or a Linux arch O_NONBLOCK or O_CLOEXEC, gains a
  bit outside U plus bits 11 and 19;
- an eventfd2 case maps or drops a bit outside its target's masks;
- an arch wrapper rewrites another flag bit;
- a host libc drops flags, or calls the flagless eventfd with nonzero
  flags. -/
def eventfd2_spec (flags : word) : Sys SyscallEffect :=
  if eventfd2_einval_b flags
  then if (bv_unsigned (bv_and (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET)))
                    (bv_not (Z_to_bv 64 (2 ^ 2 + 2 ^ 7 + 2 ^ 14 + 2 ^ 16 + 2 ^ 21 + 2 ^ 22)))) == 0)
       -- A host can allocate here; see the source argument above.
       then unmodeled
       else alt (err_ret EINVAL) (err_ret ENOSYS) -- both return before anything is allocated
  else unmodeled           -- ENOMEM / EMFILE / ENFILE / ENOSYS / the descriptor: fail closed

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
