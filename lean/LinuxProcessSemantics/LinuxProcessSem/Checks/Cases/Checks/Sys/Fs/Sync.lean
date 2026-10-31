import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Sync
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Sync
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Sync — what the fsync checker accepts and refuses, read off against Linux

Pins over `Checks.Sys.Fs.Sync.check_fsync`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Sync.v`.  Not part of the trusted
specification: this file is QA on the checker, written to be READ, and every
claim in it is a claim about what the kernel does, with the citation beside
it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

WHAT THIS TWINS.  Rocq keeps the checker's worked examples for this syscall
in `Checks/Cases/Fs/Sync.v`, beside the spec's, as three `Example`s over
`check_syscall`: the channel arm on fd 0 for both numbers, the `fd32`
aliasing of 2^32 onto fd 0, and that success is inert on every file kind.
The Lean tree keeps spec pins and checker pins apart —
`Checks/Cases/Fs/Sync.lean` pins the spec, this file the checker — and
this file is where those three land.  Section `V_Fs_Sync` below states the table-level twins.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file
tie `check_fsync` to `fsync_spec` in both directions, and a checker that
declined every input, or accepted every one, would still meet them if the
spec were changed to match.  What the lemmas cannot see is a lie told from
OUTSIDE: an errno the kernel would not return, a ledger beside the one it
does, or a return that agrees only in its low half, offered to the checker
and required to be refused.  That is what most pins below do, beside the
answer the kernel does give required to be `CheckOk` with the model
unchanged and no event; the last pins that no fd of any kind is declined,
which is the fail-closed answer a checker of this syscall must never give.

WHAT MEASURES THESE PINS.  Nothing in the tree yet: `tools/lean_mutate.py`
builds a spec mutant against `Checks/Cases/Fs/Sync.lean` alone, so no
mutant of either twin is compiled against this file, and its kill-rate is
unmeasured until that tool lists a checker's pins beside the spec's.  The
one measurement so far is the hand-run joint mutation in the deep-review
record of the PR that landed this file: spec and checker changed the same
way with the spec pins stubbed out.  A return-value lie died on every arm
under the pins Rocq's examples suggest; a ledger or width lie died only on
the arms that carried one, which is why every arm now does.

THE FIXTURES are `Checks/Cases/Fs/Sync.lean`'s `fsync_model` (Rocq's) and
`fsync_kinds_model`, so that spec and checker are pinned on the same
tables; which fd holds which kind is that file's to say, and each pin
below names the kind it relies on.

THE WITNESS IS PINNED HERE TOO.  `fsync_witness`, in the checker's file,
is the one outcome the arm the V ticket builds over this checker offers at
every fd and model, and
`fsync_witness_ok` proves the spec admits it — through the spec, which is
also the only way the four checker lemmas tie the witness to the checker.
A spec, checker and witness changed the same wrong way keep all of that
closing, so the last section names the witness's answer on the wider
fixture kind by kind, with the kernel line beside it, and feeds the witness
back to the checker at every fd and model without opening the spec, the
way `Checks/Cases/Checks/Sys/Kernel/Exit.lean` pins `exit_witness`.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted and what is refused. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Sync

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Sync
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Sync
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome)

/-- The register file of an `fsync(fd)` call, as the tracer records it:
syscall 82, the fd in a0, the other arguments zero, no memory. -/
def fsync_in (fd : word) : SyscallInput :=
  SyscallInput.mkInput 82 [fd, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The same for `fdatasync(fd)`, syscall 83. -/
def fdatasync_in (fd : word) : SyscallInput :=
  SyscallInput.mkInput 83 [fd, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! ## The channel arm on fd 0

Rocq's first example.  The model's channels are pipes, and `pipeanon_fops`
(fs/pipe.c:1257-1266, Linux v6.18.46) has no `.fsync`, so `vfs_fsync_range`
(fs/sync.c:183-184, Linux v6.18.46) answers -EINVAL.  The second conjunct
is what makes the first non-vacuous: a kernel claiming SUCCESS on fd 0 is
refused, so this pins -EINVAL rather than merely accepting it. -/

/-- fd 0 is -EINVAL, and a kernel reporting 0 there is refused.  The
fdatasync conjuncts are the same propositions, since `check_fsync` never
reads the syscall number: that 83 reaches this checker at all is the
dispatcher's claim, restated through it in section `V_Fs_Sync`.
kernel: fs/sync.c:fsync,fdatasync,do_fsync,vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem fsync_on_a_channel_is_einval :
    check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fdatasync_in 0) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fdatasync_in 0) 0)) (mkEffect 0 [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The precedence lie: a kernel answering -EBADF on an OPEN channel has
skipped `do_fsync`'s `fd_empty` test (fs/sync.c:209-210, Linux v6.18.46),
which a live fd does not fail, and reached `vfs_fsync_range` with a file
whose table has no `.fsync` — which is -EINVAL, not -EBADF.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem channel_ebadf_rejected :
    check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
      = CheckReject :=
  rfl

/-- The channel's OTHER methods' errnos, each real on a pipe end and each
wrong here.  -ESPIPE is `vfs_llseek`'s answer when `FMODE_LSEEK` is clear
(fs/read_write.c:385-390, Linux v6.18.46): `file_init_path` sets that bit
only for a table with an `.llseek` (fs/file_table.c:364-365), which
`pipeanon_fops` lacks (fs/pipe.c:1257-1266), and `create_pipe_files` calls
`stream_open` on both ends (fs/pipe.c:966-967), which clears it regardless
(fs/open.c:1658).  -ENOTTY is NOT `vfs_ioctl`'s no-method path
(fs/ioctl.c:48-49): a pipe end HAS `.unlocked_ioctl = pipe_ioctl`
(fs/pipe.c:1262), whose `default:` answers -ENOIOCTLCMD to a foreign
command (fs/pipe.c:653-654), and `vfs_ioctl` turns that into -ENOTTY
(fs/ioctl.c:52-53).  The `.fsync` test answers -EINVAL before either
method is consulted.  The -ESPIPE half is also the probe's
(`reject --mutate fsync:ret=-ESPIPE -- chan1` in fsync_spec.c, and
stderr_channel.c on fd 2); the -ENOTTY half is refused by nothing but
this pin.
kernel: fs/sync.c:vfs_fsync_range; fs/read_write.c:vfs_llseek; fs/file_table.c:file_init_path; fs/open.c:stream_open; fs/ioctl.c:vfs_ioctl; fs/pipe.c:pipe_ioctl,create_pipe_files@v6.18.46 -/
theorem channel_other_errnos_rejected :
    check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret ESPIPE) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret ENOTTY) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## The `fd32` truncation aliases onto fd 0

Rocq's second example.  `SYSCALL_DEFINE1(fsync, unsigned int, fd)`
(fs/sync.c:215-218, Linux v6.18.46) takes the fd as `unsigned int`, and the
wrapper narrows the register to it (`__SYSCALL_DEFINEx`,
arch/riscv/include/asm/syscall_wrapper.h:82-88, through `__SC_CAST`,
include/linux/syscalls.h:132, Linux v6.18.46), so `fsync(2^32)` IS
`fsync(0)`.  What is worth pinning is that truncation ALIASES rather than
REJECTS: the third conjunct offers -EBADF, the answer of an arm that handed
the whole register to the lookup, and requires it refused.  The
first conjunct is an equation between two checker calls, so on its own it
would hold if BOTH were `CheckReject`; the second names the shared value
outright. -/

/-- 2^32 and 0 name the same fd, the shared answer is an acceptance of
-EINVAL, and -EBADF — the answer of a checker that did not truncate — is
refused.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fsync_fd_truncates_to_32_bits :
    check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (2 ^ 32))) 0))
        (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (2 ^ 32))) 0))
        (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (2 ^ 32))) 0))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
      = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Truncation onto a LIVE fd, in both directions the probe's `trunc`
selector takes: 2^32 + 3 IS fd 3 (0 accepted, -EBADF refused), and a
negative register whose low half is 4 IS fd 4 (its `fdatasync` conjunct).
And -1 — the second call of the probe's `unopened` selector, not of
`trunc`, whose own wild number is positive — truncates to 0xFFFFFFFF,
which names no fd (-EBADF accepted, 0 refused).  Truncation aliases onto
the fds there are, and invents none.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file@v6.18.46 -/
theorem fd32_aliases_onto_live_fds_and_invents_none :
    check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (2 ^ 32 + 3))) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (2 ^ 32 + 3))) 0))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (-(2 ^ 32) + 4))) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (-(2 ^ 32) + 4))) 0))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (-1))) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in (Z_to_bv 64 (-1))) 0)) (mkEffect 0 [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Success is inert, on every file kind

Rocq's third example.  A probe sees only the 0.  That the fd's offset (7
and 9 here) and the file's contents came back UNCHANGED, and that no event
was emitted, is a statement about the model's own state, and the equalities
below are the whole of it: the accepted post-model is the SAME model, and
the event list is empty.  `vfs_fsync` (fs/sync.c:199-202, Linux v6.18.46)
syncs the range `0..LLONG_MAX` and reads no position; `do_fsync`
(fs/sync.c:205-213, same version) takes an fd and returns an int, and
nothing under it copies to user space. -/

/-- 0 is accepted on the read-only file, the file opened for writing and
the directory, with the model unchanged and no event; fdatasync on the
read-only file likewise.
kernel: fs/sync.c:fsync,fdatasync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem fsync_success_is_inert_on_every_file_kind :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fdatasync_in 3) 0)) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A success that WRITES is refused, and so is one that zero-fills: the
effect the checker accepts is the return alone.
kernel: fs/sync.c:do_fsync,vfs_fsync@v6.18.46 -/
theorem success_with_a_write_rejected :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 0 [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 0 [] [(4096, 4096)]) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The three ledgers the pin above does not reach — an unmap, a copy and a
copy-in beside the 0 — on the read-only file, and the two it does, on the
write fd and the directory.  `do_fsync` takes an fd and returns an int;
nothing under it maps, unmaps, copies or reads user memory.  One conjunct
per ledger, so the acceptor cannot be widened one field at a time.
kernel: fs/sync.c:do_fsync,vfs_fsync; fs/ext4/fsync.c:ext4_sync_file@v6.18.46 -/
theorem success_with_other_ledgers_rejected :
    check_fsync (fd32 (in_arg (fsync_in 3) 0))
        (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0))
        (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0))
        (with_copyins [(4096, 1)] (mkEffect 0 [] [])) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect 0 [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect 0 [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect 0 [] [(4096, 4096)]) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Success is exactly 0: `ext4_sync_file` returns its `ret`, 0 or an
errno (fs/ext4/fsync.c:141-188, Linux v6.18.46), and `noop_fsync` returns
0 (fs/libfs.c:1629, same version); a positive return is no answer of
either.  The probe's `ret=1` case, on the model, for every file kind.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem nonzero_success_rejected :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 1 [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect 1 [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect 1 [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The confident wrong answer: `write`'s -EBADF on a read-only fd
(`vfs_write`'s `FMODE_WRITE` test, fs/read_write.c:670-671, Linux v6.18.46)
copied into an arm that has no such test — fs/sync.c consults `f_mode`
nowhere.  A kernel answering -EBADF on the read-only file is refused
outright.  -EINVAL is refused on a PREMISE the spec twin's header states
and `bugs/fsync-dirfd-premise-widened-by-dotdot.md` records: the file sits
on ext4 or tmpfs, whose regular files carry an `.fsync`
(`ext4_file_operations`, fs/ext4/file.c:963-983, the member at :975).  A
read-only image filesystem's do not — `generic_ro_fops`
(fs/read_write.c:28-33) and `squashfs_file_operations`
(fs/squashfs/file.c:774-779) have no member — and there `vfs_fsync_range`
really answers -EINVAL (fs/sync.c:183-184); only this arm, `FdFile`, can
reach it, since no write-mode open succeeds on such a mount.  So the
second conjunct refuses a real Linux answer the model excludes, not one
no Linux gives, and it is the premise made a test.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/read_write.c:vfs_write@v6.18.46 -/
theorem readonly_file_errno_rejected :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The write fd's own refutations, which no pin above states: -EBADF (a
live fd), -EINVAL (the channel answer), and the -EROFS `ext4_sync_file`
returns from `ext4_emergency_state` on an emergency-read-only mount
(fs/ext4/fsync.c:147-149 and fs/ext4/ext4.h:2336-2343, Linux v6.18.46), a
state the model has no filesystem to be in.  fdatasync agrees on the last.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/ext4/ext4.h:ext4_emergency_state; fs/ext4/fsync.c:ext4_sync_file@v6.18.46 -/
theorem write_file_errno_rejected :
    check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect (errno_ret EROFS) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fdatasync_in 4) 0)) (mkEffect (errno_ret EROFS) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A directory fd answers 0 on the filesystems a run sits on
(`ext4_dir_operations` sets `.fsync = ext4_sync_file`, fs/ext4/dir.c:682-693,
the member at :691, Linux v6.18.46; tmpfs reaches `noop_fsync`,
fs/libfs.c:1629-1632), so the -EINVAL a procfs or sysfs directory would
give — `proc_dir_operations` (fs/proc/generic.c:346-350) and
`kernfs_dir_fops` (fs/kernfs/dir.c:1924-1929) set no `.fsync`, which
`vfs_fsync_range` answers with -EINVAL (fs/sync.c:183-184) — is refused
here; `bugs/fsync-dirfd-premise-widened-by-dotdot.md` records what that
premise costs.
kernel: fs/sync.c:vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem dir_einval_rejected :
    check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = CheckReject :=
  rfl

/-- A directory fd is live, so not -EBADF, and it is not refused the way
`read` refuses one: -EISDIR is `generic_read_dir`'s (fs/libfs.c:224-226,
Linux v6.18.46), a method fs/sync.c never calls.  The probe's `dir`
rejects, on the model.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:generic_read_dir; fs/ext4/fsync.c:ext4_sync_file@v6.18.46 -/
theorem dir_wrong_errnos_rejected :
    check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect (errno_ret EISDIR) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## `do_fsync`: a closed fd is -EBADF before the file is examined

`do_fsync` (fs/sync.c:205-213, Linux v6.18.46) opens with `CLASS(fd, f)(fd)`
(:207) and returns -EBADF on `fd_empty(f)` (:209-210) before `vfs_fsync`
(:212) is entered, so a number with no open file is -EBADF, and not the
-EINVAL of the `.fsync` test a closed fd never reaches. -/

/-- fd 6 is closed in `fsync_model`: -EBADF is accepted, and 0 and -EINVAL
are refused.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_is_ebadf :
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- An errno return is as inert as a success: `do_fsync` returns before any
file is touched (fs/sync.c:209-210, Linux v6.18.46) and `vfs_fsync_range`
before `.fsync` is called (fs/sync.c:183-184), so a write, a zero-fill, an
unmap, a copy or a copy-in beside -EBADF, and a write or a zero-fill
beside -EINVAL, are refused — one conjunct per ledger.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem errno_with_a_ledger_rejected :
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EBADF) [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EBADF) [] [(4096, 4096)]) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(4096, 4096)] [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EBADF) [] [])) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The return is compared at 64 bits.  `do_fsync`'s `int` is widened to
the `long` the `SYSCALL_DEFINE1` body returns (fs/sync.c:215-218, Linux
v6.18.46), so -EBADF fills the register with ones: its zero-extended low
half, 2^32 - 9, is refused on the closed fd, -EINVAL's likewise on the
channel, and 2^32 — a word whose low 32 bits are zero — is refused as a
"success" on the file.  A checker comparing `abi_low32` of both sides
accepts all three.
kernel: fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem return_is_compared_at_full_width :
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 9)) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32)) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Two errnos this tree does not define, spelled by number: -ENOSYS (38)
is `sys_ni_syscall`'s answer for a number with no entry (kernel/sys_ni.c:20-22,
Linux v6.18.46), and 82 and 83 have one (`__NR_fsync`, `__NR_fdatasync`,
include/uapi/asm-generic/unistd.h:218-221); -EIO (5) is `ext4_emergency_state`'s
on a forced shutdown (fs/ext4/ext4.h:2336-2343, same version), a state the
model does not have.  Both are refused on a file, a closed fd and a channel.
kernel: kernel/sys_ni.c:sys_ni_syscall; include/uapi/asm-generic/errno.h:ENOSYS; include/uapi/asm-generic/errno-base.h:EIO; fs/ext4/ext4.h:ext4_emergency_state; fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem foreign_errnos_rejected_everywhere :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect (errno_ret 38) [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret 38) [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret 38) [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect (errno_ret 5) [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret 5) [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0)) (mkEffect (errno_ret 5) [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `vfs_fsync_range`: -EINVAL for every table with no `.fsync`

The kinds Rocq's examples do not reach, on the wider fixture.  Each arm
names the `file_operations` table its fd kind stands for and the fact that
the table has no `.fsync` member, which `vfs_fsync_range` (fs/sync.c:183-184,
Linux v6.18.46) answers with -EINVAL; the refusal beside it is the answer a
kernel with an `.fsync` there would give, 0. -/

/-- A socket (`socket_file_ops`, net/socket.c:156, Linux v6.18.46, no
`.fsync`), both pipe ends (`pipeanon_fops`, fs/pipe.c:1257-1266, installed
by `create_pipe_files` on both ends), /dev/null (`null_fops`,
drivers/char/mem.c:644-652) and /dev/urandom (`urandom_fops`,
drivers/char/random.c:1572-1581) are -EINVAL, and 0 is refused on each.
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files; net/socket.c:sock_alloc_file; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem no_fsync_method_is_einval_on_every_kind :
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The precedence lie on every kind without an `.fsync`: an OPEN socket,
pipe end, /dev/null or /dev/urandom passes `do_fsync`'s `fd_empty` test
(fs/sync.c:209-210, Linux v6.18.46), so -EBADF is refused on each; and the
socket is not -ENOTSOCK here, which is `sockfd_lookup`'s answer
(net/socket.c:552-565, same version) to a descriptor that is NOT a socket.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; net/socket.c:sockfd_lookup@v6.18.46 -/
theorem no_fsync_kinds_are_not_ebadf :
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret ENOTSOCK) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A ledger beside -EINVAL is refused on every kind without an `.fsync`,
one conjunct per ledger per kind.  `vfs_fsync_range` returns at its
`.fsync` test (fs/sync.c:183-184, Linux v6.18.46) before any method runs,
and `do_fsync` (fs/sync.c:205-213) takes an fd and returns an int: nothing
under it writes, zero-fills, maps, unmaps, copies or reads user memory.
The relating lemmas cannot see an acceptor widened on one arm in both
twins at once, and the prelude's own refutations pin the helper, not that
an arm uses it; a conjunct here per arm and per ledger can, which is why
each arm carries all five.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem einval_with_a_ledger_rejected_on_every_kind :
    -- fd 6, the socket: a write, a zero-fill, an unmap, a copy, a copy-in
    check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_kinds_model = CheckReject
    -- fd 7, the read end of the pipe: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_kinds_model = CheckReject
    -- fd 8, the write end of the pipe: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_kinds_model = CheckReject
    -- fd 9, /dev/null: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_kinds_model = CheckReject
    -- fd 11, /dev/urandom: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect (errno_ret EINVAL) [(4096, [0])] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect (errno_ret EINVAL) [] [(4096, 4096)]) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_kinds_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ledgers the pins above leave short on Rocq's own fixture: an
unmap, a copy and a copy-in beside -EINVAL on the channel and beside 0 on
the directory, and those three plus a zero-fill beside 0 on the write fd.
With `success_with_a_write_rejected`, `success_with_other_ledgers_rejected`
and `errno_with_a_ledger_rejected`, every arm of the checker refuses every
ledger; the kernel fact is the one those pins cite.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem remaining_ledgers_rejected_on_rocq_fixture :
    -- fd 0, the channel: an unmap, a copy, a copy-in beside -EINVAL
    check_fsync (fd32 (in_arg (fsync_in 0) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 0) 0))
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) fsync_model = CheckReject
    -- fd 4, the write fd: a zero-fill, an unmap, a copy, a copy-in beside 0
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect (Z_to_bv 64 0) [] [(4096, 4096)]) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0))
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(4096, 4096)] [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0))
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 4) 0))
        (with_copyins [(4096, 1)] (mkEffect (Z_to_bv 64 0) [] [])) fsync_model = CheckReject
    -- fd 5, the directory: an unmap, a copy, a copy-in beside 0
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0))
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(4096, 4096)] [] []) fsync_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0))
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0))
        (with_copyins [(4096, 1)] (mkEffect (Z_to_bv 64 0) [] [])) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The 64-bit comparison on the arms `return_is_compared_at_full_width`
does not reach: 2^32, whose low half is 0, is refused as a "success" on the
write fd and the directory, and 2^32 - 22, -EINVAL's zero-extended low
half, on every kind without an `.fsync`.  `do_fsync`'s `int` is widened
into the `long` the two syscall bodies return (fs/sync.c:215-223, Linux
v6.18.46), so the register a probe reads is all-ones above bit 31, and a
checker comparing `abi_low32` of both sides would accept each of these.
kernel: fs/sync.c:fsync,fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem return_width_on_every_kind :
    -- 2^32, low half 0, as a "success" on the write fd and the directory
    check_fsync (fd32 (in_arg (fsync_in 4) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32)) [] []) fsync_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 5) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32)) [] []) fsync_model
        = CheckReject
    -- 2^32 - 22, -EINVAL's zero-extended low half, on every kind without an .fsync
    ∧ check_fsync (fd32 (in_arg (fsync_in 6) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 7) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 8) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 9) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_kinds_model
        = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 11) 0)) (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) fsync_kinds_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- fd 10 is the gap in `fsync_kinds_fds`: -EBADF is accepted there, and 0
and -EINVAL are refused, as on `fsync_model`'s fd 6.  The `none` arm reads
no fixture, so this pins only that the wider table did not fill the
number — the spec pin `closed_fd_is_ebadf_on_kinds` of
`Checks/Cases/Fs/Sync.lean`, mirrored on the checker.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_on_kinds_is_ebadf :
    check_fsync (fd32 (in_arg (fsync_in 10) 0)) (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model
        = CheckOk fsync_kinds_model []
    ∧ check_fsync (fd32 (in_arg (fsync_in 10) 0)) (mkEffect 0 [] []) fsync_kinds_model = CheckReject
    ∧ check_fsync (fd32 (in_arg (fsync_in 10) 0)) (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-! ## Nothing declines

A checker that answered `CheckUnmodeled` on every input would meet its five
obligations against a spec that declined everywhere, and no lemma of the
checker's file could tell.  `fsync_spec` declines nothing
(`Checks/Cases/Fs/Sync.lean`'s `fsync_never_unmodeled_on_kinds`), and the
checker's soundness for declines carries that over: whatever the fd and
whatever the offered effect, `check_fsync` answers. -/

/-- No fd, of any kind or closed, is declined on the wider fixture.  The
proof is the spec's pin through the checker's `sound_unmodeled` lemma,
which is exactly what that lemma is for: a decline of the checker would be
a decline of the spec, and the spec has none.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem never_unmodeled_on_kinds (fd : word) (eff : SyscallEffect) :
    check_fsync fd eff fsync_kinds_model ≠ CheckUnmodeled :=
  fun h => fsync_never_unmodeled_on_kinds fd (fsync_in fd)
    (check_fsync_sound_unmodeled fd eff _ (fsync_in fd) h)

/-- The same refusal on one concrete answer, WITHOUT the checker's lemma in
the proof: the pin above dies with `check_fsync_sound_unmodeled`, this one
with the checker alone.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem file_success_never_declines_directly :
    check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 0 [] []) fsync_model ≠ CheckUnmodeled := by
  intro h
  have h0 : check_fsync (fd32 (in_arg (fsync_in 3) 0)) (mkEffect 0 [] []) fsync_model
      = CheckOk fsync_model [] := rfl
  rw [h0] at h
  cases h

/-! ## The witness

`fsync_witness` is the checker's accepting answer written out, and the
spec's admission of it (`fsync_witness_ok`) is proved beside it.  These pins
are the other half, and open no spec: the answer written out is named,
kind by kind, against the kernel functions that give it; it IS the checker's at
every fd and model; and it declines nowhere — so a witness that answered a
kind differently from the checker, or fell back to `Unmodeled`, dies here on
that kind's arm rather than passing as "some outcome the spec admits". -/

/-- The witness on the wider fixture is the checker's accepted triple, kind
by kind: -EBADF on the closed fd 10, -EINVAL on the channel, the socket,
both pipe ends, /dev/null and /dev/urandom, 0 on the read-only file, the
writable file and the directory — each with the model handed back and no
event.  The evidence is the union of what `fsync_success_is_inert_on_every_file_kind`
and `no_fsync_method_is_einval_on_every_kind` cite, since these are their
answers restated on the witness: `do_fsync` for the -EBADF, `vfs_fsync_range`
for the -EINVAL, and the tables behind each kind for which of the two, or
the 0, it gets.
kernel: fs/sync.c:fsync,fdatasync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync; fs/pipe.c:create_pipe_files; net/socket.c:sock_alloc_file; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem fsync_witness_on_kinds :
    fsync_witness (fd32 (in_arg (fsync_in 10) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 0) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 6) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 7) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 8) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 9) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 11) 0)) fsync_kinds_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 3) 0)) fsync_kinds_model
        = Ok (mkEffect 0 [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 4) 0)) fsync_kinds_model
        = Ok (mkEffect 0 [] []) fsync_kinds_model []
    ∧ fsync_witness (fd32 (in_arg (fsync_in 5) 0)) fsync_kinds_model
        = Ok (mkEffect 0 [] []) fsync_kinds_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The checker accepts its own witness at every fd and model: the
receptive field and the complete field of the arm meet on the same triple,
which is what makes the arm's `ca_receptive` a statement about
`check_fsync` and not only about the spec.  The proof opens none of the
checker's four lemmas — it is the lookup split with `check_ret_only_ok_iff`
on every arm — so a witness that answered a kind differently from the
checker fails here, on that kind's arm.
model: `fsync_witness` fed to `check_fsync`, no spec named -/
theorem check_fsync_accepts_its_witness (fd : word) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : fsync_witness fd m = Ok e m' evs) : check_fsync fd e m = CheckOk m' evs := by
  unfold fsync_witness at h
  unfold check_fsync
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    dsimp only at h ⊢
    unfold ret_outcome at h
    injection h with he hm hevs
    subst he hm hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some k =>
    cases k
    case FdFileA _ _ => cases h
    case FdFileRW _ _ => cases h
    all_goals
      (dsimp only at h ⊢
       unfold ret_outcome at h
       injection h with he hm hevs
       subst he hm hevs
       exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- …and the witness declines at no fd and no model but at an append-mode
or a read-write file, the fail-closed answer a witness of this syscall
must not give where the spec answers: `fsync_spec` declines nothing else
(its header declares those two declines, and
`fsync_never_unmodeled_on_kinds` in `Checks/Cases/Fs/Sync.lean` refutes
one on every other kind), and neither does its witness.
model: `fsync_witness`'s shape, an `Ok` on every arm of the lookup but two -/
theorem fsync_witness_is_never_unmodeled (fd : word) (m : Model)
    (ha : ∀ p pos, fd_lookup (m_fds m) fd ≠ some (.FdFileA p pos))
    (hrw : ∀ p pos, fd_lookup (m_fds m) fd ≠ some (.FdFileRW p pos)) :
    fsync_witness fd m ≠ Unmodeled := by
  unfold fsync_witness
  generalize fd_lookup (m_fds m) fd = r at ha hrw ⊢
  cases r with
  | none => exact fun h => nomatch h
  | some k =>
    cases k
    case FdFileA p pos => exact absurd rfl (ha p pos)
    case FdFileRW p pos => exact absurd rfl (hrw p pos)
    all_goals exact fun h => nomatch h

-- lean-port sentinel: ticket V-Fs-Sync
section V_Fs_Sync

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Sync — the checker and witness through the real table

The three Rocq examples and the restatements of the pins above use the existing
fixtures. Kernel lines below refer to Linux v6.18.46, commit 1f99e9ab748f.
Successful file and directory pins retain the ext4/tmpfs and absent
writeback-error premises recorded in `Sys/Fs/Sync.lean`'s docstring.

fs/sync.c:205-213 (`do_fsync`, Linux v6.18.46) resolves the live fd, and
`vfs_fsync_range` (:183-187) calls its .fsync: `ext4_file_operations`
(fs/ext4/file.c:975, Linux v6.18.46) and `ext4_dir_operations` (fs/ext4/dir.c:691, Linux v6.18.46)
use `ext4_sync_file`; tmpfs uses `noop_fsync` (fs/libfs.c:1629-1632, Linux v6.18.46;
mm/shmem.c:5263 and fs/libfs.c:572, Linux v6.18.46). The success pins use the premises
in this section's header.

The unsigned-int cast at include/linux/syscalls.h:132
(`__SC_CAST`, Linux v6.18.46), applied by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), drops the high half.
fs/sync.c:209-210 (`do_fsync`, Linux v6.18.46) tests the resulting descriptor;
`vfs_fsync_range` (:183-187) selects its method. -/

/-- The lookup is independent of the registers and memory.
model: `lookup_ca` over `checked_table` at 82 -/
theorem lookup_fsync_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 82 args mem wmem).in_sysno)
      = some arm_fsync :=
  lookup_ca_checked_table_fsync

/-- The lookup is independent of the registers and memory.
model: `lookup_ca` over `checked_table` at 83 -/
theorem lookup_fdatasync_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 83 args mem wmem).in_sysno)
      = some arm_fdatasync :=
  lookup_ca_checked_table_fdatasync

/-- fs/sync.c:183-187 (`vfs_fsync_range`) returns -EINVAL for
the missing .fsync in `pipeanon_fops` (fs/pipe.c:1257-1266).
kernel: fs/sync.c:vfs_fsync_range@v6.18.46 -/
theorem fsync_on_a_channel_is_einval_over_the_real_table :
    check_syscall (fsync_in 0) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in 0) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in 0) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fdatasync_in 0) (mkEffect 0 [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The cast aliases 2^32 onto the open channel fd 0, where
`vfs_fsync_range` (fs/sync.c:183-184) returns -EINVAL for the missing
`.fsync`.  -EBADF would require the closed-fd branch of `do_fsync`
(fs/sync.c:209-210), which this alias does not take.
kernel: include/linux/syscalls.h:__SC_CAST; fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fsync_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (fsync_in (Z_to_bv 64 (2 ^ 32)))
        (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = check_syscall (fsync_in 0) (mkEffect (errno_ret EINVAL) [] []) fsync_model
    ∧ check_syscall (fsync_in (Z_to_bv 64 (2 ^ 32)))
        (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = CheckOk fsync_model []
    ∧ check_syscall (fsync_in (Z_to_bv 64 (2 ^ 32)))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
      = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The two high-half aliases reach open files 3 and 4, whose
`.fsync` returns 0 under the section's premises (`noop_fsync`,
fs/libfs.c:1631; `ext4_sync_file`, fs/ext4/fsync.c:188), so the closed-fd
-EBADF is refused.  The -1 alias is 0xFFFFFFFF, a closed fd: `do_fsync`
(fs/sync.c:209-210) returns -EBADF before a success path is reached.
kernel: include/linux/syscalls.h:__SC_CAST; fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fd32_aliases_onto_live_fds_and_invents_none_over_the_real_table :
    check_syscall (fsync_in (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in (Z_to_bv 64 (2 ^ 32 + 3)))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in (Z_to_bv 64 (-(2 ^ 32) + 4))) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in (Z_to_bv 64 (-(2 ^ 32) + 4)))
        (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in (Z_to_bv 64 (-1))) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in (Z_to_bv 64 (-1))) (mkEffect 0 [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The read-only file, writable file and directory reach the 0
from `noop_fsync` (fs/libfs.c:1631) or `ext4_sync_file`
(fs/ext4/fsync.c:188) under the section's premises.  `vfs_fsync`
(fs/sync.c:199-202) syncs 0..LLONG_MAX without advancing the offset;
`do_fsync` (:205-213) returns the integer without a user-memory transfer.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem fsync_success_is_inert_on_every_file_kind_over_the_real_table :
    check_syscall (fsync_in 3) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in 4) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in 5) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fdatasync_in 3) (mkEffect 0 [] []) fsync_model
        = CheckOk fsync_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The writable fd 4 is open and has an `.fsync` under the
section's filesystem premise, so it bypasses the -EBADF and -EINVAL
checks (`do_fsync`, fs/sync.c:209-212; `vfs_fsync_range`, :183-187).
The -EROFS from `ext4_emergency_state` (fs/ext4/ext4.h:2336-2343),
returned by `ext4_sync_file` (fs/ext4/fsync.c:147-149), requires the
emergency-read-only state excluded by the spec docstring.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/ext4/ext4.h:ext4_emergency_state@v6.18.46 -/
theorem write_file_errno_rejected_over_the_real_table :
    check_syscall (fsync_in 4) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in 4) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in 4) (mkEffect (errno_ret EROFS) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fdatasync_in 4) (mkEffect (errno_ret EROFS) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The read-only fd 3 is open, so `do_fsync` (fs/sync.c:209-212)
bypasses -EBADF without a write-mode test.  Its regular-file operations
have an `.fsync` under the section's filesystem premise, so the
missing-method -EINVAL at `vfs_fsync_range` (:183-184) is refused too.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem readonly_file_errno_rejected_over_the_real_table :
    check_syscall (fsync_in 3) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in 3) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The directory's operations have an `.fsync` under the
section's filesystem premise.  Thus fd 5 bypasses `vfs_fsync_range`'s
missing-method -EINVAL (fs/sync.c:183-184).
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem dir_einval_rejected_over_the_real_table :
    check_syscall (fsync_in 5) (mkEffect (errno_ret EINVAL) [] []) fsync_model
      = CheckReject :=
  rfl

/-- The return 1 on either regular file or the directory is
refused because `noop_fsync` returns 0 (fs/libfs.c:1631) and
`ext4_sync_file` returns 0 or -errno (fs/ext4/fsync.c:141-188).
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem nonzero_success_rejected_over_the_real_table :
    check_syscall (fsync_in 3) (mkEffect 1 [] []) fsync_model = CheckReject
    ∧ check_syscall (fsync_in 4) (mkEffect 1 [] []) fsync_model = CheckReject
    ∧ check_syscall (fsync_in 5) (mkEffect 1 [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The closed fd takes -EBADF at fs/sync.c:209-210
(`do_fsync`), before the method test at :183-184.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_is_ebadf_over_the_real_table :
    check_syscall (fsync_in 6) (mkEffect (errno_ret EBADF) [] []) fsync_model
        = CheckOk fsync_model []
    ∧ check_syscall (fsync_in 6) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_syscall (fsync_in 6) (mkEffect (errno_ret EINVAL) [] []) fsync_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The smuggled-write and zero-fill effects inject a user-memory
change beside success on fd 3.  `vfs_fsync` (fs/sync.c:199-202) syncs a
file range; `do_fsync` (fs/sync.c:205-213) returns an integer without
that transfer.
kernel: fs/sync.c:do_fsync,vfs_fsync@v6.18.46 -/
theorem success_with_a_write_rejected_over_the_real_table :
    check_syscall (fsync_in 3) (mkEffect 0 [(4096, [0])] []) fsync_model
        = CheckReject
    ∧ check_syscall (fsync_in 3) (mkEffect 0 [] [(4096, 4096)]) fsync_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- For fdatasync, the positive and negative high-half aliases
reach open files 3 and 4: `do_fsync` (fs/sync.c:209-212) bypasses -EBADF.
Their `.fsync` returns 0 under the section's premises (`noop_fsync`,
fs/libfs.c:1631; `ext4_sync_file`, fs/ext4/fsync.c:188).
kernel: include/linux/syscalls.h:__SC_CAST; fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fdatasync_fd32_alias_over_the_real_table :
    check_syscall (fdatasync_in (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
    ∧ check_syscall (fdatasync_in (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect (errno_ret EBADF) [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in (Z_to_bv 64 (-(2 ^ 32) + 4))) (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
    ∧ check_syscall (fdatasync_in (Z_to_bv 64 (-(2 ^ 32) + 4))) (mkEffect (errno_ret EBADF) [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The stdout channel uses the channel argument of
`fsync_on_a_channel_is_einval` above: `vfs_fsync_range`
(fs/sync.c:183-184) returns -EINVAL for its missing `.fsync`, excluding
0 for either syscall.  -ESPIPE belongs to `vfs_llseek`
(fs/read_write.c:385-390), a seek path this method test does not take.
kernel: fs/sync.c:vfs_fsync_range; fs/read_write.c:vfs_llseek@v6.18.46 -/
theorem stdout_return_lies_over_the_real_table :
    check_syscall (fsync_in 1) (mkEffect (errno_ret EINVAL) [] []) fsync_model = CheckOk fsync_model []
    ∧ check_syscall (fsync_in 1) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in 1) (mkEffect 0 [] []) fsync_model = CheckReject
    ∧ check_syscall (fsync_in 1) (mkEffect (errno_ret ESPIPE) [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The writable file's return 1 is refused because `noop_fsync`
returns 0 (fs/libfs.c:1631) and `ext4_sync_file` returns 0 or -errno
(fs/ext4/fsync.c:141-188).  The file and directory have an `.fsync` under
the section's filesystem premise, bypassing the missing-method -EINVAL
(`vfs_fsync_range`, fs/sync.c:183-187); fd 3 is open, bypassing the
closed-fd -EBADF (`do_fsync`, :209-212).
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem fdatasync_probe_return_lies_over_the_real_table :
    check_syscall (fdatasync_in 4) (mkEffect 1 [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in 4) (mkEffect (errno_ret EINVAL) [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in 3) (mkEffect (errno_ret EBADF) [] []) fsync_model = CheckReject
    ∧ check_syscall (fdatasync_in 5) (mkEffect (errno_ret EINVAL) [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- -EISDIR is `generic_read_dir`'s answer (fs/libfs.c:224-226).
The directory's fsync follows its `.fsync` member through
`vfs_fsync_range` (fs/sync.c:183-187), rather than that read path.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync,generic_read_dir@v6.18.46 -/
theorem dir_eisdir_lie_over_the_real_table :
    check_syscall (fsync_in 5) (mkEffect (errno_ret EISDIR) [] []) fsync_model = CheckReject :=
  rfl

/-- fs/sync.c:209-210 (`do_fsync`) returns
-EBADF on this closed descriptor before `datasync` is consulted.
kernel: fs/sync.c:do_fsync@v6.18.46 -/
theorem fdatasync_closed_fd_over_the_real_table :
    check_syscall (fdatasync_in 6) (mkEffect (errno_ret EBADF) [] []) fsync_model = CheckOk fsync_model []
    ∧ check_syscall (fdatasync_in 6) (mkEffect 0 [] []) fsync_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The shared verdict follows the spec docstring's durability bound:
fs/sync.c:215-223 passes 0 or 1 to `do_fsync`; the early errno tests
(:209-210 and :183-184) precede the `datasync` use (:185-187).
kernel: fs/sync.c:fsync,fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sync_numbers_agree_over_the_real_table (args : List word)
    (mem wmem : word → Option byte) (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 82 args mem wmem) eff m =
      check_syscall (SyscallInput.mkInput 83 args mem wmem) eff m := rfl

/-- Both syscall witnesses use the 2^32 + 3 alias of the open
read-only file fd 3.  Its `.fsync` supplies 0 under the section's premises
(`noop_fsync`, fs/libfs.c:1631; `ext4_sync_file`, fs/ext4/fsync.c:188),
returned by `do_fsync` (fs/sync.c:212) without a user-memory transfer.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem sync_witness_over_the_real_table :
    syscall_spec_witness (fsync_in (Z_to_bv 64 (2 ^ 32 + 3))) fsync_model =
      Ok (mkEffect 0 [] []) fsync_model []
    ∧ syscall_spec_witness (fdatasync_in (Z_to_bv 64 (2 ^ 32 + 3))) fsync_model =
      Ok (mkEffect 0 [] []) fsync_model [] :=
  ⟨rfl, rfl⟩

end V_Fs_Sync

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Sync
