import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.ReadWrite — write on the checked surface

The registration of `Checks/Sys/Fs/ReadWrite.lean`'s `write` checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_write`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit.  The two Rocq texts this file
twins, `arm_write` there and `check_write_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, read the same at that
commit and at the port's common baseline f44244ad6b80.

WHY `write` IS REGISTERED HERE AND NOT BY ITS V TICKET.  The whole-program
examples that issue `write` (64) — `oob_read_bug_ns` and `alloc_join_ns`
among them, by their recording in
`testing/syscall-check/traces/examples.json` — need the row, and an E
ticket registers a row no V ticket has yet (`docs/lean-port/TESTING.md`,
tier 2).  The other arms `Checks/Sys/Fs/ReadWrite.lean` answers — `read`,
`pread64`, `pwrite64`, `lseek` — join this file when their registrations
land; nothing here depends on their absence.

THE FRAME LEMMAS ARE HERE, not beside the checker as
`Checks/Sys/Fs/EventFd.lean` places its own: the registration's files are
this one alone, as `Checks/Arms/Mm/Mmap.lean`'s descriptor-state frames
were written beside the registry by the ticket that could edit only the
registry's side.  A move to the checker file changes no statement. -/

/-! ## `read` (63), registered beside `write`

#1360 registers `read` here, and `openat` (56) and
`close` (57) in `Checks/Arms/Fs/Open.lean`, for the reason the paragraph
above gives for `write`: Rocq's `theories/Common/FileSim.v` states
`check_syscall`'s answer at each of the three numbers
(`check_syscall_56`, `check_syscall_57`, `check_syscall_63`), and the
Lean `check_syscall` answers `CheckUnmodeled` at a number
`checked_table` has no row for, so the Lean twins of those lemmas need the
rows.

THE HEADER ABOVE PREDATES THIS SECTION and is left as written, because an
arm file takes additions only (`tools/check_lean_port_scope.py`, the
paragraph on arm files).  With `read` here, four of its statements are
short by that arm:
- the title and the first sentence name `write` alone;
- each of the three sections it lists holds `read`'s declarations as well
  as `write`'s: `arm_read` and its four `arm_unfold` lemmas,
  `arm_read_preserves_vm`, and one `<invariant>_arm_read` per registered
  invariant;
- the Rocq texts this file twins are four, not two: `arm_read` in
  `theories/LinuxProcessSem/Checks/Sys/Dispatch.v` and `check_read_frame`
  in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` join `arm_write`
  and `check_write_frame`.  `arm_read` reads the same at the header's
  commit and at f44244ad6b80.  `check_read_frame` states the same at both,
  and only its proof script differs: at the header's commit it unfolds
  `check_read_urandom` as well and reduces a `let` (`cbv zeta`) before
  `vm_frame2`;
- `read` is no longer among the arms that join later. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- `lseek` narrows `a0` with `fd32` and `a2` with `whence32`, passing `a1` whole.
In Linux v6.18.46, fs/read_write.c:410's
`SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset, unsigned int, whence)`
declares both fd and whence as `unsigned int`, leaving the offset `off_t`-wide.
The ledger obligation is `check_lseek_frame` below. -/
def arm_lseek : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 62
    (fun i => Sys.Fs.ReadWrite.lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_lseek_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_lseek_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_lseek_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_lseek_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.lseek_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m

@[arm_unfold] theorem ca_check_arm_lseek (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_lseek.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_lseek (i : SyscallInput) (m : Model) :
    arm_lseek.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m := rfl
@[arm_unfold] theorem sa_spec_arm_lseek (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_lseek.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_lseek : ca_no arm_lseek = 62 := rfl
/- ### read (63) -/

/-- read (63).  THE DESCRIPTOR IS REGISTER `a0` CUT TO ITS LOW 32 BITS;
THE BUFFER AND THE COUNT ARE READ WHOLE.  riscv64's wrapper hands the
registers over in order, `orig_a0`, `a1`, `a2` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
narrows each to the type
`SYSCALL_DEFINE3(read, unsigned int, fd, char __user *, buf, size_t, count)`
(fs/read_write.c:722, Linux v6.18.46) declares through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46): the
descriptor to 32 bits, and the pointer and the `size_t` not at all on a
64-bit target.  `ksys_read` (fs/read_write.c:704) receives the three
unchanged.  `Sys.Syscall.fd32 (in_arg i 0)` is that narrowing, applied
here at the boundary as Rocq's `arm_read` applies it.  `ca_arm` is the
term `Sys/Registry/Fs/ReadWrite.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_read_frame`, below. -/
def arm_read : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 63
    (fun i => Sys.Fs.ReadWrite.read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_read_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_read_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_read_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_read_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.read_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_read (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_read.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_read (i : SyscallInput) (m : Model) :
    arm_read.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_read (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_read.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_read : ca_no arm_read = 63 := rfl

/- ### write (64) -/

/-- write (64).  THE DESCRIPTOR IS REGISTER `a0` CUT TO ITS LOW 32 BITS;
THE BUFFER AND THE COUNT ARE READ WHOLE.
`SYSCALL_DEFINE3(write, unsigned int, fd, const char __user *, buf, size_t, count)`
(fs/read_write.c:746, Linux v6.18.46) declares the descriptor
`unsigned int` and the other two pointer- and `size_t`-wide, and hands
all three to `ksys_write` (fs/read_write.c:727) unchanged, which looks the
descriptor up through `fd_pos` and passes the buffer and the count to
`vfs_write`.  `Sys.Syscall.fd32 (in_arg i 0)` is that narrowing, applied
here at the boundary as Rocq's `arm_write` applies it, so the checker and
the witness receive the narrowed descriptor.  `ca_arm` is the term
`Sys/Registry/Fs/ReadWrite.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_write_frame`, below. -/
def arm_write : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 64
    (fun i => Sys.Fs.ReadWrite.write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_write_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_write_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_write_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_write_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.write_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_write (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_write.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_write (i : SyscallInput) (m : Model) :
    arm_write.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_write (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_write.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_write : ca_no arm_write = 64 := rfl

/- ### readv (65) -/

/-- `readv` narrows `a0` with `fd32` and passes `a1` and `a2` whole.
In Linux v6.18.46, fs/read_write.c's `SYSCALL_DEFINE3(readv, …)`
calls `do_readv`, whose `CLASS(fd_pos, f)(fd)` uses the `int fd`
constructor in include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` and
fs/file.c's `fdget_pos(unsigned int fd)`. The pointer and count reach
fs/read_write.c's `vfs_readv` whole; lib/iov_iter.c's `import_iovec`
narrows `nr_segs` to unsigned, represented by the checker's `iovcnt32`.
The ledger obligation is `check_readv_frame` below. -/
def arm_readv : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 65
    (fun i => Sys.Fs.ReadWrite.readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_readv_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_readv_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_readv_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_readv_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.readv_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_readv (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_readv.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_readv (i : SyscallInput) (m : Model) :
    arm_readv.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_readv (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_readv.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_readv : ca_no arm_readv = 65 := rfl

/- ### writev (66) -/

/-- `writev` narrows `a0` with `fd32` and passes `a1` and `a2` whole.
In Linux v6.18.46, fs/read_write.c's `SYSCALL_DEFINE3(writev, …)`
calls `do_writev`, whose `CLASS(fd_pos, f)(fd)` uses the `int fd`
constructor in include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` and
fs/file.c's `fdget_pos(unsigned int fd)`. The pointer and count reach
fs/read_write.c's `vfs_writev` whole; lib/iov_iter.c's `import_iovec`
narrows `nr_segs` to unsigned, represented by the checker's `iovcnt32`.
The ledger obligation is `check_writev_frame` below. -/
def arm_writev : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 66
    (fun i => Sys.Fs.ReadWrite.writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_writev_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_writev_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_writev_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_writev_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.writev_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_writev (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_writev.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_writev (i : SyscallInput) (m : Model) :
    arm_writev.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_writev (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_writev.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_writev : ca_no arm_writev = 66 := rfl

/-- `pread64` narrows `a0` with `fd32` and passes `a1`, `a2` and `a3` whole.
In Linux v6.18.46, fs/read_write.c:768's
`SYSCALL_DEFINE4(pread64, unsigned int, fd, char __user *, buf, size_t, count, loff_t, pos)`
declares fd as `unsigned int`, leaving the buffer, count and position
pointer-, `size_t`- and `loff_t`-wide respectively.
The ledger obligation is `check_pread64_frame` below. -/
def arm_pread64 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 67
    (fun i => Sys.Fs.ReadWrite.pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_pread64_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_pread64_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_pread64_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_pread64_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.pread64_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_pread64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_pread64.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_pread64 (i : SyscallInput) (m : Model) :
    arm_pread64.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_pread64 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_pread64.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_pread64 : ca_no arm_pread64 = 67 := rfl

/-- `pwrite64` narrows `a0` with `fd32` and passes `a1`, `a2` and `a3` whole.
In Linux v6.18.46, fs/read_write.c:798's
`SYSCALL_DEFINE4(pwrite64, unsigned int, fd, const char __user *, buf, size_t, count, loff_t, pos)`
declares fd as `unsigned int`, leaving the buffer, count and position
pointer-, `size_t`- and `loff_t`-wide respectively.
The ledger obligation is `check_pwrite64_frame` below. -/
def arm_pwrite64 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 68
    (fun i => Sys.Fs.ReadWrite.pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.ReadWrite.check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.ReadWrite.pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_pwrite64_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.ReadWrite.check_pwrite64_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.ReadWrite.check_pwrite64_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.ReadWrite.check_pwrite64_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.ReadWrite.pwrite64_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_pwrite64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_pwrite64.ca_check i eff m
      = Checks.Sys.Fs.ReadWrite.check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_pwrite64 (i : SyscallInput) (m : Model) :
    arm_pwrite64.ca_witness i m
      = Checks.Sys.Fs.ReadWrite.pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_pwrite64 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_pwrite64.ca_arm.sa_spec i m o
      = Sys.Fs.ReadWrite.pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_pwrite64 : ca_no arm_pwrite64 = 68 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Rocq: `VmMapsDisjoint.check_lseek_frame`. Accepted models use the
input model or `with_fds`, preserving `m_vmmaps`. -/
theorem check_lseek_frame (fd off whence : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_lseek fd off whence eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_lseek at h
  vm_frame2 h

/-- `lseek`: the ledger fact is `check_lseek_frame` above. -/
theorem arm_lseek_preserves_vm : arm_preserves_vm arm_lseek :=
  arm_preserves_of_frame arm_lseek (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_lseek_frame _ _ _ eff m m' evs h)
/-- Rocq: `VmMapsDisjoint.check_read_frame`.  Every model `check_read`
accepts is the one it was handed, or that model with the stdin or
urandom stream advanced (`with_stdin`, `with_urandom`), the descriptor
rebound (`with_fds`: a socket's receive state, a file's offset) or a
pipe's queue consumed from the front (`with_pipes`); none of those setters
reaches `m_vmmaps`, so the ledger is what it was.  Rocq's proof unfolds
the same four definitions and runs `vm_frame2`; so does this one. -/
theorem check_read_frame (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_read i fd buf count eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_read Checks.Sys.Fs.ReadWrite.check_read_urandom
    Checks.Sys.Fs.ReadWrite.check_socket_pending_error Checks.Sys.Uaccess.check_access_ok_zero at h
  vm_frame2 h

/-- `read` (63): the ledger fact is `check_read_frame` above. -/
theorem arm_read_preserves_vm : arm_preserves_vm arm_read :=
  arm_preserves_of_frame arm_read (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_read_frame i _ _ _ eff m m' evs h)

/-- Rocq: `VmMapsDisjoint.check_write_frame`.  Every model `check_write`
accepts is the one it was handed, or that model with the descriptor table
rebound (`with_fds`), the file image rewritten (`with_fs`) or a pipe's
queue extended (`with_pipes`); none of the three setters reaches
`m_vmmaps`, so the ledger is what it was.  Rocq's proof is `unfold
check_write, check_access_ok_zero in H; vm_frame2 H`; no `vm_done`
wrapper occurs in the unfolded checker, so `vm_frame` is that loop. -/
theorem check_write_frame (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_write i fd buf count eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_write Checks.Sys.Uaccess.check_access_ok_zero at h
  vm_frame h

/-- `write` (64): the ledger fact is `check_write_frame` above. -/
theorem arm_write_preserves_vm : arm_preserves_vm arm_write :=
  arm_preserves_of_frame arm_write (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_write_frame i _ _ _ eff m m' evs h)

/-- Rocq: `VmMapsDisjoint.check_readv_gap_frame`. The gap returns
`CheckUnmodeled`; its `vm_done` rule closes a goal from a claimed successful gap. -/
theorem check_readv_gap_frame (m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv_gap = CheckOk m' evs) : False := by
  cases h

macro_rules
  | `(tactic| vm_done $h:ident) =>
    `(tactic| exact (check_readv_gap_frame _ _ $h:ident).elim)

/-- Rocq: `VmMapsDisjoint.check_writev_frame`. Accepted models use the
input model or `with_fds` over `with_fs`, which preserve `m_vmmaps`. -/
theorem check_writev_frame (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_writev i fd iov iovcnt eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_writev at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  vm_frame2 h

/-- Rocq: `VmMapsDisjoint.check_readv_imported_frame`. Accepted models use
the input model, `with_stdin` or `with_fds`, which preserve `m_vmmaps`. -/
theorem check_readv_imported_frame (i : SyscallInput) (fd : word)
    (r : Sys.Fs.ReadWrite.ReadableFd) (iovs0 : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv_imported i fd r iovs0 eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv_imported at h
  vm_frame2 h

/-- Rocq: `VmMapsDisjoint.check_readv_frame`. Import errors keep the input
model; the imported branch uses `with_stdin` or `with_fds`, preserving `m_vmmaps`. -/
theorem check_readv_frame (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv i fd iov iovcnt eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  (repeat' first
    | vm_step h
    | vm_done h
    | exact check_readv_imported_frame _ _ _ _ _ _ _ _ h) <;> rfl

/-- `readv`: the ledger fact is `check_readv_frame`. -/
theorem arm_readv_preserves_vm : arm_preserves_vm arm_readv :=
  arm_preserves_of_frame arm_readv (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_readv_frame i _ _ _ eff m m' evs h)

/-- `writev`: the ledger fact is `check_writev_frame`. -/
theorem arm_writev_preserves_vm : arm_preserves_vm arm_writev :=
  arm_preserves_of_frame arm_writev (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_writev_frame i _ _ _ eff m m' evs h)

/-- Rocq: `VmMapsDisjoint.check_pread64_frame`. Accepted models use the
input model or `with_urandom`, preserving `m_vmmaps`. -/
theorem check_pread64_frame (i : SyscallInput) (fd buf count pos : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pread64 i fd buf count pos eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_pread64 Checks.Sys.Fs.ReadWrite.check_read_urandom at h
  vm_frame2 h

/-- `pread64`: the ledger fact is `check_pread64_frame` above. -/
theorem arm_pread64_preserves_vm : arm_preserves_vm arm_pread64 :=
  arm_preserves_of_frame arm_pread64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_pread64_frame i _ _ _ _ eff m m' evs h)

/-- Rocq: `VmMapsDisjoint.check_pwrite64_frame`. Accepted models use the
input model or `with_fs`, preserving `m_vmmaps`. -/
theorem check_pwrite64_frame (i : SyscallInput) (fd buf count pos : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pwrite64 i fd buf count pos eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.ReadWrite.check_pwrite64 at h
  vm_frame2 h

/-- `pwrite64`: the ledger fact is `check_pwrite64_frame` above. -/
theorem arm_pwrite64_preserves_vm : arm_preserves_vm arm_pwrite64 :=
  arm_preserves_of_frame arm_pwrite64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_pwrite64_frame i _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## What `write` writes, and why each invariant survives it

`write` is the first registered arm that rebinds a descriptor and the
first that fills a pipe, so neither registry entry below is a frame: the
`FdFileW` arm answers with the descriptor rebound to its advanced offset,
and the `FdPipe` arm with the pipe's queue extended.  Each gets one
structural lemma over the setter it goes through, and the checker-level
lemma walks `check_write` with the `vm_frame` loop, closing each accepted
model with the hypothesis itself or with that lemma. -/

/-- `fd_insert` keeps the table's descriptors distinct, whatever it
binds: it drops every binding of `fd` and puts the new one in front.  The
`FdFileW` arm rebinds a descriptor it found, as Linux advances the open
file's position and leaves the descriptor slot alone (`ksys_write`'s
`fd_file(f)->f_pos = pos`, fs/read_write.c:740, Linux v6.18.46);
the model keeps that position in the table entry, so the rebinding is the
model's spelling of the position update, not a second descriptor. -/
theorem fd_table_unique_fd_insert (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (h : fd_table_unique fds) : fd_table_unique (fd_insert fds fd e) := by
  unfold fd_table_unique fd_insert at *
  rw [List.map_cons, List.nodup_cons]
  refine ⟨fun hm => ?_, h.sublist (List.filter_sublist.map _)⟩
  obtain ⟨p, hp, hpf⟩ := List.mem_map.mp hm
  have hne := (List.mem_filter.mp hp).2
  rw [hpf, (bv_eqb_eq fd fd).mpr rfl] at hne
  exact absurd hne (by decide)

/-- Descriptor rebinding uses `fd_insert`, preserving distinct keys. -/
theorem check_lseek_fd_table_unique (fd off whence : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_lseek fd off whence eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_lseek at h
  (repeat' vm_step h) <;> first
    | exact hu
    | exact fd_table_unique_fd_insert _ _ _ hu

/-- Accepted models keep `m_pipes`, preserving `pipes_within_capacity`. -/
theorem check_lseek_pipes_within_capacity (fd off whence : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_lseek fd off whence eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_lseek at h
  (repeat' vm_step h) <;> exact hu

/-- `vm_wf` follows from the ledger frame. -/
theorem vm_wf_arm_lseek : arm_preserves inv_vm_wf arm_lseek :=
  Arms.arm_lseek_preserves_vm

/-- `fd_table_unique` follows from the checker-level preservation fact. -/
theorem fd_table_unique_arm_lseek : arm_preserves inv_fd_table_unique arm_lseek := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_lseek_fd_table_unique _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` follows from the checker-level preservation fact. -/
theorem pipes_within_capacity_arm_lseek : arm_preserves inv_pipes_within_capacity arm_lseek := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_lseek_pipes_within_capacity _ _ _ eff m m' evs h hold

/-- `check_write` keeps the descriptor table's keys distinct. -/
theorem check_write_fd_table_unique (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_write i fd buf count eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_write Checks.Sys.Uaccess.check_access_ok_zero at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_insert _ _ _ hu

/-- A pipe the lookup answers is one the table holds. -/
theorem pipe_lookup_mem (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf)
    (h : pipe_lookup ps id = some st) : ∃ k, (k, st) ∈ ps := by
  induction ps with
  | nil => cases h
  | cons p r ih =>
    obtain ⟨k, st'⟩ := p
    simp only [pipe_lookup] at h
    by_cases hk : bv_eqb k id = true
    · rw [ite_eq_left hk, Option.some.injEq] at h
      subst h
      exact ⟨k, List.mem_cons_self⟩
    · rw [ite_eq_right hk] at h
      obtain ⟨k', hk'⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hk'⟩

/-- `pipe_insert` keeps every pipe within its page when the pipe it binds
is. -/
theorem pipes_within_capacity_pipe_insert (ps : List (word × PipeBuf)) (id : word)
    (st : PipeBuf) (hps : pipes_within_capacity ps) (hst : pipe_within_capacity st) :
    pipes_within_capacity (pipe_insert ps id st) := by
  intro p hp
  unfold pipe_insert at hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst hp
    exact hst
  · exact hps p (List.mem_filter.mp hp).1

/-- `pipe_append` behind `pipe_write_room` stays inside the page.  The
same fact is pinned as `pipe_append_under_the_gate_stays_within_capacity`
in `Checks/Cases/Invariants.lean`, which this file cannot import: that
module imports `Checks.Invariants`, whose generated coverage module
imports every arm file, this one included.  The gate admits the two
cases of `anon_pipe_write` (fs/pipe.c, Linux v6.18.46) that stay on one
page: on a nonempty queue the merge test `offset + chars <= PAGE_SIZE`
(:478-483), and on an empty one, where `was_empty` skips the merge, a
fresh page (:510-515) whose copy is bounded by `PAGE_SIZE` (:522).  A
nonempty queue whose merge test fails also takes a fresh page in the
kernel, a second one; the gate is false there and `check_write` declines,
as `pipe_write_room`'s docstring (`State/Pipes.lean`) argues. -/
theorem pipe_append_within_capacity (st : PipeBuf) (bs : List byte)
    (hcap : pipe_within_capacity st) (hroom : pipe_write_room st (bs.length : Int) = true) :
    pipe_within_capacity (pipe_append st bs) := by
  obtain ⟨q, used⟩ := st
  cases q with
  | nil =>
    simp only [pipe_write_room, decide_eq_true_eq] at hroom
    exact ⟨Int.le_refl _, hroom⟩
  | cons a r =>
    simp only [pipe_write_room, decide_eq_true_eq] at hroom
    have h1 : ((a :: r).length : Int) ≤ used := hcap.1
    refine ⟨?_, hroom⟩
    simp only [pipe_append, List.length_append]
    omega

/-- The `FdPipe` arm's accepted model, as the checker's two guards leave
it: the pipe was found, the room test passed for the requested count, and
the source read supplied exactly that many bytes, so the room test holds
of the bytes appended. -/
theorem pipes_within_capacity_write_pipe (ps : List (word × PipeBuf)) (id : word)
    (st : PipeBuf) (bs : List byte) (count : word) (hl : pipe_lookup ps id = some st)
    (hroom : ¬ (!pipe_write_room st (bv_unsigned count)) = true)
    (hlen : ¬ (!(bs.length == word_to_nat count)) = true)
    (hps : pipes_within_capacity ps) :
    pipes_within_capacity (pipe_insert ps id (pipe_append st bs)) := by
  -- `split` leaves each guard as the negation of its `!`-test; casing
  -- the tested `Bool` turns each into the fact it guards.
  have hroom' : pipe_write_room st (bv_unsigned count) = true := by
    revert hroom
    cases pipe_write_room st (bv_unsigned count) <;> decide
  have hlen' : (bs.length == word_to_nat count) = true := by
    revert hlen
    cases (bs.length == word_to_nat count) <;> decide
  have hc : (bs.length : Int) = bv_unsigned count := by
    unfold bv_unsigned
    unfold word_to_nat at hlen'
    rw [beq_iff_eq.mp hlen']
  obtain ⟨k, hk⟩ := pipe_lookup_mem ps id st hl
  refine pipes_within_capacity_pipe_insert ps id _ hps
    (pipe_append_within_capacity st bs (hps _ hk) ?_)
  rw [hc]
  exact hroom'

/-- `check_write` keeps every pipe within its page. -/
theorem check_write_pipes_within_capacity (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_write i fd buf count eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_write Checks.Sys.Uaccess.check_access_ok_zero at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | (apply pipes_within_capacity_write_pipe <;> assumption)

/-- `vm_wf` × `write`: the ledger fact above. -/
theorem vm_wf_arm_write : arm_preserves inv_vm_wf arm_write :=
  Arms.arm_write_preserves_vm

/-- `fd_table_unique` × `write`: the `FdFileW` arm rebinds the descriptor
it wrote through, and every other accepted answer leaves the table as it
was (`check_write_fd_table_unique`). -/
theorem fd_table_unique_arm_write : arm_preserves inv_fd_table_unique arm_write := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_write_fd_table_unique i _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` × `write`: the `FdPipe` arm appends only
behind the room test, and every other accepted answer leaves the pipes as
they were (`check_write_pipes_within_capacity`). -/
theorem pipes_within_capacity_arm_write : arm_preserves inv_pipes_within_capacity arm_write := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_write_pipes_within_capacity i _ _ _ eff m m' evs h hold

/-- Descriptor rebinding uses `fd_insert`, preserving distinct keys. -/
theorem check_writev_fd_table_unique (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_writev i fd iov iovcnt eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_writev at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_insert _ _ _ hu

/-- Descriptor rebinding uses `fd_insert`, preserving distinct keys. -/
theorem check_readv_imported_fd_table_unique (i : SyscallInput) (fd : word) (r : Sys.Fs.ReadWrite.ReadableFd)
    (iovs0 : List (word × word))
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv_imported i fd r iovs0 eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv_imported at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_insert _ _ _ hu

/-- Descriptor rebinding uses `fd_insert`, preserving distinct keys. -/
theorem check_readv_fd_table_unique (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv i fd iov iovcnt eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_insert _ _ _ hu
      | exact check_readv_imported_fd_table_unique _ _ _ _ _ _ _ _ h hu

/-- Accepted models keep the pipe table, preserving its capacity bound. -/
theorem check_writev_pipes_within_capacity (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_writev i fd iov iovcnt eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_writev at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  (repeat' vm_step h) <;>
    first
      | exact hu

/-- Accepted models keep the pipe table, preserving its capacity bound. -/
theorem check_readv_imported_pipes_within_capacity (i : SyscallInput) (fd : word) (r : Sys.Fs.ReadWrite.ReadableFd)
    (iovs0 : List (word × word))
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv_imported i fd r iovs0 eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv_imported at h
  (repeat' vm_step h) <;>
    first
      | exact hu

/-- Accepted models keep the pipe table, preserving its capacity bound. -/
theorem check_readv_pipes_within_capacity (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_readv i fd iov iovcnt eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_readv at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((_, len0) :: _) => Sys.Syscall.w_is0 len0
         | _ => false) = eb at h
  generalize (if bv_unsigned iovcnt == 0 then false
    else if IOV_MAX < bv_unsigned iovcnt then false
    else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovcnt then false
    else match copy_iovecs_aux i.in_mem iov (BvBase.word_to_nat iovcnt) with
         | .ImpOk ((base0, len0) :: rest) =>
             Sys.Syscall.w_is0 len0 && ((base0, len0) :: rest).all
               (fun entry => access_okb entry.1 (bv_unsigned entry.2))
         | _ => false) = eo at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact check_readv_imported_pipes_within_capacity _ _ _ _ _ _ _ _ h hu

/-- `vm_wf` follows from the ledger frame. -/
theorem vm_wf_arm_readv : arm_preserves inv_vm_wf arm_readv :=
  Arms.arm_readv_preserves_vm

/-- `fd_table_unique` follows from the checker-level preservation fact. -/
theorem fd_table_unique_arm_readv : arm_preserves inv_fd_table_unique arm_readv := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_readv_fd_table_unique i _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` follows from the checker-level preservation fact. -/
theorem pipes_within_capacity_arm_readv : arm_preserves inv_pipes_within_capacity arm_readv := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_readv_pipes_within_capacity i _ _ _ eff m m' evs h hold

/-- `vm_wf` follows from the ledger frame. -/
theorem vm_wf_arm_writev : arm_preserves inv_vm_wf arm_writev :=
  Arms.arm_writev_preserves_vm

/-- `fd_table_unique` follows from the checker-level preservation fact. -/
theorem fd_table_unique_arm_writev : arm_preserves inv_fd_table_unique arm_writev := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_writev_fd_table_unique i _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` follows from the checker-level preservation fact. -/
theorem pipes_within_capacity_arm_writev : arm_preserves inv_pipes_within_capacity arm_writev := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_writev_pipes_within_capacity i _ _ _ eff m m' evs h hold

/-! ## What `read` writes, and why each invariant survives it

`check_read` hands back the model it was given, or that model with the
stdin or urandom stream advanced, the descriptor it read through rebound
(a socket's receive state, a file's advanced offset), or one pipe's queue
consumed from the front.  The rebinding goes through `fd_insert`, as
`write`'s does, so `fd_table_unique_fd_insert` above serves it; the pipe
read gets one lemma over `pipe_consume`, beside `write`'s over
`pipe_append`. -/

/-- `pipe_consume` keeps a pipe within its page: it drops bytes off the
front of the queue and leaves the mark where it was, as `anon_pipe_read`
advances `buf->offset` and shortens `buf->len` by the same count
(fs/pipe.c:350-351, Linux v6.18.46).  The same fact is pinned as
`pipe_consume_stays_within_capacity` in `Checks/Cases/Invariants.lean`,
which this file cannot import, for the reason
`pipe_append_within_capacity` gives. -/
theorem pipe_consume_within_capacity (st : PipeBuf) (k : Nat)
    (hcap : pipe_within_capacity st) : pipe_within_capacity (pipe_consume st k) := by
  obtain ⟨q, used⟩ := st
  have h1 : (q.length : Int) ≤ used := hcap.1
  refine ⟨?_, hcap.2⟩
  show ((q.drop k).length : Int) ≤ used
  have hle : (q.drop k).length ≤ q.length := by
    simp only [List.length_drop]
    omega
  omega

/-- The `FdPipe` arm's accepted model: the pipe was found, and its queue
is consumed from the front. -/
theorem pipes_within_capacity_read_pipe (ps : List (word × PipeBuf)) (id : word)
    (st : PipeBuf) (k : Nat) (hl : pipe_lookup ps id = some st)
    (hps : pipes_within_capacity ps) :
    pipes_within_capacity (pipe_insert ps id (pipe_consume st k)) := by
  obtain ⟨key, hk⟩ := pipe_lookup_mem ps id st hl
  exact pipes_within_capacity_pipe_insert ps id _ hps
    (pipe_consume_within_capacity st k (hps _ hk))

/-- `check_read` keeps the descriptor table's keys distinct. -/
theorem check_read_fd_table_unique (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_read i fd buf count eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_read Checks.Sys.Fs.ReadWrite.check_read_urandom
    Checks.Sys.Fs.ReadWrite.check_socket_pending_error Checks.Sys.Uaccess.check_access_ok_zero at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_insert _ _ _ hu

/-- `check_read` keeps every pipe within its page. -/
theorem check_read_pipes_within_capacity (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_read i fd buf count eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_read Checks.Sys.Fs.ReadWrite.check_read_urandom
    Checks.Sys.Fs.ReadWrite.check_socket_pending_error Checks.Sys.Uaccess.check_access_ok_zero at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | (apply pipes_within_capacity_read_pipe <;> assumption)

/-- `vm_wf` × `read`: the ledger fact above. -/
theorem vm_wf_arm_read : arm_preserves inv_vm_wf arm_read :=
  Arms.arm_read_preserves_vm

/-- `fd_table_unique` × `read`: the socket and `FdFile` arms rebind the
descriptor they read through, and every other accepted answer leaves the
table as it was (`check_read_fd_table_unique`). -/
theorem fd_table_unique_arm_read : arm_preserves inv_fd_table_unique arm_read := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_read_fd_table_unique i _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` × `read`: the `FdPipe` arm consumes from the
front of the queue, and every other accepted answer leaves the pipes as
they were (`check_read_pipes_within_capacity`). -/
theorem pipes_within_capacity_arm_read : arm_preserves inv_pipes_within_capacity arm_read := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_read_pipes_within_capacity i _ _ _ eff m m' evs h hold
/-- Accepted models keep `m_fds`, preserving `fd_table_unique`. -/
theorem check_pread64_fd_table_unique (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pread64 i fd buf count pos eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_pread64 Checks.Sys.Fs.ReadWrite.check_read_urandom at h
  (repeat' vm_step h) <;> exact hu

/-- Accepted models keep `m_pipes`, preserving `pipes_within_capacity`. -/
theorem check_pread64_pipes_within_capacity (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pread64 i fd buf count pos eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_pread64 Checks.Sys.Fs.ReadWrite.check_read_urandom at h
  (repeat' vm_step h) <;> exact hu

/-- `vm_wf` follows from the ledger frame. -/
theorem vm_wf_arm_pread64 : arm_preserves inv_vm_wf arm_pread64 :=
  Arms.arm_pread64_preserves_vm

/-- `fd_table_unique` follows from the checker-level preservation fact. -/
theorem fd_table_unique_arm_pread64 : arm_preserves inv_fd_table_unique arm_pread64 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_pread64_fd_table_unique i _ _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` follows from the checker-level preservation fact. -/
theorem pipes_within_capacity_arm_pread64 : arm_preserves inv_pipes_within_capacity arm_pread64 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_pread64_pipes_within_capacity i _ _ _ _ eff m m' evs h hold

/-- Accepted models keep `m_fds`, preserving `fd_table_unique`. -/
theorem check_pwrite64_fd_table_unique (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pwrite64 i fd buf count pos eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_pwrite64 at h
  (repeat' vm_step h) <;> exact hu

/-- Accepted models keep `m_pipes`, preserving `pipes_within_capacity`. -/
theorem check_pwrite64_pipes_within_capacity (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.ReadWrite.check_pwrite64 i fd buf count pos eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.ReadWrite.check_pwrite64 at h
  (repeat' vm_step h) <;> exact hu

/-- `vm_wf` follows from the ledger frame. -/
theorem vm_wf_arm_pwrite64 : arm_preserves inv_vm_wf arm_pwrite64 :=
  Arms.arm_pwrite64_preserves_vm

/-- `fd_table_unique` follows from the checker-level preservation fact. -/
theorem fd_table_unique_arm_pwrite64 : arm_preserves inv_fd_table_unique arm_pwrite64 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_pwrite64_fd_table_unique i _ _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` follows from the checker-level preservation fact. -/
theorem pipes_within_capacity_arm_pwrite64 : arm_preserves inv_pipes_within_capacity arm_pwrite64 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_pwrite64_pipes_within_capacity i _ _ _ _ eff m m' evs h hold

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
