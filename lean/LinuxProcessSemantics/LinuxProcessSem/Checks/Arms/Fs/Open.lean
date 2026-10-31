import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp
import LinuxProcessSemantics.LinuxProcessSem.Checks.Arms.Fs.ReadWrite

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Open — ftruncate on the checked surface

The registration of `Checks/Sys/Fs/Open.lean`'s ftruncate checker in
`checked_table`, in the one file that registration writes; the shape is
`tools/gen_lean_checked.py`'s, whose docstring says what it reads.  The
file is named after the checker twin, not after a syscall, so another of
that twin's checkers is registered by adding its arm here.  The three
sections sit in the namespaces `tools/gen_lean_checked.py`'s ARM-2 to
ARM-4 require of an arm file: `Checks.Sys.Table` for the `CheckedArm` and
its `arm_unfold` lemmas, `Checks.VmMapsDisjoint.Arms` for the ledger fact
and `Checks.Invariants` for the registry facts.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

/-! openat (56) and close (57) are registered here as well, in each of
the three namespaces after ftruncate's section.  For openat and close,
the Rocq texts this file twins are `arm_openat` and `arm_close` in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`, and
`check_openat_frame` and `check_close_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`; each of the four
reads the same at b22b2a23f, the commit `Checks/Sys/Fs/Open.lean` names.

WHY THE ROWS FOR 56 AND 57.  Rocq's `theories/Common/FileSim.v` states
`check_syscall`'s answer at 56 and 57 (`check_syscall_56`,
`check_syscall_57`), and the Lean `check_syscall` answers `CheckUnmodeled`
at a number `checked_table` has no row for, so the Lean twins of those
lemmas need the rows; `read` (63) is registered beside `write` in
`Checks/Arms/Fs/ReadWrite.lean` for FileSim's `check_syscall_63`.
`faccessat` (48) and `faccessat2` (439), which the same checker twin
answers, join this file when they are registered; nothing here depends on
their absence.

THE FRAME LEMMAS FOR 56 AND 57 ARE HERE, all but the acceptor's;
ftruncate's two are beside its checker in `Checks/Sys/Fs/Open.lean`, as
its arm's docstring says.  The C ticket's
acceptance text, `docs/lean-port/BRIEF.md`'s CHECK list, asks the
checker's ticket for no frame lemma and makes registration the V
ticket's first step; the VERIFY list writes that registration in this
file, `arm_openat_preserves_vm` and `arm_close_preserves_vm` among it,
and each of those is derived from its frame lemma below.
`check_open_result_frame`, the frame of the one place openat's checker
changes the model, is in `Checks/Sys/Fs/Open.lean` with its `vm_done`
rule, because `Checks/VmMapsDisjoint.lean`'s `vm_done` docstring has the
checker twin register that rule from its own file; `check_openat_frame`
below closes the acceptor calls through it, and the invariants below
split on `check_open_result_cases` beside it.  The import of
`Checks/Arms/Fs/ReadWrite.lean` is for `fd_table_unique_fd_insert`, the
fact about `fd_insert` that `write`'s descriptor rebinding and
`openat`'s descriptor minting both rest on. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### ftruncate (46) -/

/-- ftruncate (46).  THE DESCRIPTOR IS `a0` CUT TO ITS LOW 32 BITS AND
THE LENGTH IS `a1` WHOLE.  `SYSCALL_DEFINE2(ftruncate, unsigned int, fd,
off_t, length)` (fs/open.c:213-216, Linux v6.18.46) is narrowed by
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux
v6.18.46) through `__SC_CAST` (include/linux/syscalls.h:132, Linux
v6.18.46): the `unsigned int` loses a0's high half, which `fd32` is, and
the `off_t` is the register.  `ca_arm` is the term
`Sys/Registry/Fs/Open.lean`'s `ftruncate_arm` builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_ftruncate_frame`, and the table
fact is `check_ftruncate_fd_state_frame`, both beside the checker. -/
def arm_ftruncate : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 46
    (fun i => Sys.Fs.Open.ftruncate_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Open.check_ftruncate (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Open.ftruncate_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_ftruncate_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Open.check_ftruncate_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (in_arg i 1) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_ftruncate_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Open.check_ftruncate_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (in_arg i 1) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Open.ftruncate_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_ftruncate (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_ftruncate.ca_check i eff m
      = Checks.Sys.Fs.Open.check_ftruncate (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_ftruncate (i : SyscallInput) (m : Model) :
    arm_ftruncate.ca_witness i m
      = Checks.Sys.Fs.Open.ftruncate_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) m :=
  rfl
@[arm_unfold] theorem sa_spec_arm_ftruncate (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_ftruncate.ca_arm.sa_spec i m o
      = Sys.Fs.Open.ftruncate_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_ftruncate : ca_no arm_ftruncate = 46 := rfl

/- ### openat (56) -/

/-- openat (56).  THE DIRECTORY DESCRIPTOR IS REGISTER `a0` CUT TO ITS LOW
32 BITS; THE PATHNAME POINTER AND THE FLAG WORD ARE HANDED OVER WHOLE, and
the mode in `a3` is not an argument of `openat_spec`.
`SYSCALL_DEFINE4(openat, int, dfd, const char __user *, filename, int,
flags, umode_t, mode)` (fs/open.c:1463-1464, Linux v6.18.46) declares the
descriptor and the flags `int`, so Linux reads the low 32 bits of each.
`Sys.Syscall.fd32 (in_arg i 0)` is the descriptor's narrowing, applied
here at the boundary as Rocq's `arm_openat` applies it.  The flag word
reaches `openat_spec` whole, as Rocq's row hands it, and its first gate,
`modeled_open_flags` (`Sys/Fs/Open.lean`), reads all 64 bits and answers
`unmodeled` on any bit above the interpreted ones; that docstring gives
the kernel reading behind the decline.  `ca_arm` is the term
`Sys/Registry/Fs/Open.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_openat_frame`, below. -/
def arm_openat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 56
    (fun i => Sys.Fs.Open.openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Open.check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Open.openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_openat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Open.check_openat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_openat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Open.check_openat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Open.openat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_openat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_openat.ca_check i eff m
      = Checks.Sys.Fs.Open.check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_openat (i : SyscallInput) (m : Model) :
    arm_openat.ca_witness i m
      = Checks.Sys.Fs.Open.openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_openat (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_openat.ca_arm.sa_spec i m o
      = Sys.Fs.Open.openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_openat : ca_no arm_openat = 56 := rfl

/- ### close (57) -/

/-- close (57).  THE DESCRIPTOR IS REGISTER `a0` CUT TO ITS LOW 32 BITS.
`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c:1574, Linux
v6.18.46) declares it `unsigned int`; `Sys.Syscall.fd32 (in_arg i 0)` is
that narrowing, applied here at the boundary as Rocq's `arm_close`
applies it.  `ca_arm` is the term `Sys/Registry/Fs/Open.lean`'s row
builds, which `checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_close_frame`, below. -/
def arm_close : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 57
    (fun i => Sys.Fs.Open.close_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Open.check_close (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Open.close_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_close_sound_ok (fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Open.check_close_sound_unmodeled (fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_close_complete_ok (fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Open.check_close_complete_unmodeled (fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Open.close_witness_ok (fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_close (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_close.ca_check i eff m = Checks.Sys.Fs.Open.check_close (fd32 (in_arg i 0)) eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_close (i : SyscallInput) (m : Model) :
    arm_close.ca_witness i m = Checks.Sys.Fs.Open.close_witness (fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_close (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_close.ca_arm.sa_spec i m o
      = Sys.Fs.Open.close_spec (fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_close : ca_no arm_close = 57 := rfl

/- ### faccessat (48) -/

/-- faccessat (48).  THE DIRFD IS `a0` CUT TO ITS LOW 32 BITS;
THE PATHNAME POINTER AND THE MODE ARE `a1` AND `a2` WHOLE, and the
arm passes no flag word.  `SYSCALL_DEFINE3(faccessat, int, dfd,
const char __user *, filename, int, mode)` (fs/open.c:539-542, Linux
v6.18.46) calls `do_faccessat(dfd, filename, mode, 0)`; riscv64's
`SC_RISCV_REGS_TO_ARGS` passes `orig_a0`, `a1`, `a2` in order
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46) narrows each through `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46): the `int` dfd loses
a0's high half, which `fd32` is.  The mode is an `int` too, and the arm
hands the checker all of a2 because `check_faccessat`'s mode gate
(`modeled_access_mode`) does that narrowing itself.  `ca_arm` is the
term `Sys/Registry/Fs/Open.lean`'s `faccessat_arm` builds.  The ledger
fact is `check_faccessat_frame` and the table fact
`check_faccessat_fd_state_frame`, both below. -/
def arm_faccessat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 48
    (fun i => Sys.Fs.Open.faccessat_spec
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Open.check_faccessat i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Open.faccessat_witness
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_faccessat_sound_ok i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
      eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Open.check_faccessat_sound_unmodeled i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
      eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_faccessat_complete_ok i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
      eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Open.check_faccessat_complete_unmodeled i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
      m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Open.faccessat_witness_ok
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_faccessat (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_faccessat.ca_check i eff m
      = Checks.Sys.Fs.Open.check_faccessat i
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_faccessat (i : SyscallInput) (m : Model) :
    arm_faccessat.ca_witness i m
      = Checks.Sys.Fs.Open.faccessat_witness
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m :=
  rfl
@[arm_unfold] theorem sa_spec_arm_faccessat (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_faccessat.ca_arm.sa_spec i m o
      = Sys.Fs.Open.faccessat_spec
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o :=
  rfl
@[arm_unfold] theorem ca_no_arm_faccessat : ca_no arm_faccessat = 48 := rfl

/- ### faccessat2 (439) -/

/-- faccessat2 (439).  THE DIRFD IS `a0` CUT TO ITS LOW 32 BITS;
THE PATHNAME POINTER AND THE MODE ARE `a1` AND `a2` WHOLE, and
THE FLAG WORD IS `a3` WHOLE.  `SYSCALL_DEFINE4(faccessat2, int, dfd,
const char __user *, filename, int, mode, int, flags)`
(fs/open.c:544-548, Linux v6.18.46) calls
`do_faccessat(dfd, filename, mode, flags)`; riscv64's
`SC_RISCV_REGS_TO_ARGS` passes `orig_a0`, `a1`, `a2`, `a3` in order
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46) narrows each through `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46): the `int` dfd loses
a0's high half, which `fd32` is.  The mode is an `int` too, and
`modeled_access_mode` narrows a2 itself; `check_faccessat2`'s flag
gates (`valid_access_flags`, `modeled_access_flags`) narrow a3
themselves.  `ca_arm` is the term `Sys/Registry/Fs/Open.lean`'s
`faccessat2_arm` builds.  The ledger fact is `check_faccessat2_frame`
and the table fact `check_faccessat2_fd_state_frame`, both below. -/
def arm_faccessat2 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 439
    (fun i => Sys.Fs.Open.faccessat2_spec
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Open.check_faccessat2 i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Open.faccessat2_witness
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_faccessat2_sound_ok i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Open.check_faccessat2_sound_unmodeled i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Open.check_faccessat2_complete_ok i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Open.check_faccessat2_complete_unmodeled i
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Open.faccessat2_witness_ok
      (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_faccessat2 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_faccessat2.ca_check i eff m
      = Checks.Sys.Fs.Open.check_faccessat2 i
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_faccessat2 (i : SyscallInput) (m : Model) :
    arm_faccessat2.ca_witness i m
      = Checks.Sys.Fs.Open.faccessat2_witness
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m :=
  rfl
@[arm_unfold] theorem sa_spec_arm_faccessat2 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_faccessat2.ca_arm.sa_spec i m o
      = Sys.Fs.Open.faccessat2_spec
        (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o :=
  rfl
@[arm_unfold] theorem ca_no_arm_faccessat2 : ca_no arm_faccessat2 = 439 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `ftruncate` (46): an accepted model is the one handed in or `with_fs`
over it (`check_ftruncate_ok_model`), so the ledger is what it was
(`check_ftruncate_frame`; both are stated beside the checker in
`Checks/Sys/Fs/Open.lean`).  That is sound because the ledger (`VmMaps`,
`State/Vm.lean`) records address ranges and allocator bounds, not what
backs a range, and a truncate changes no VMA's extent (below).  Not every
range is anonymous: `vm_reserved` holds the image's LOAD segments, which
Linux maps from the executable wherever they have file content —
`load_elf_binary` (fs/binfmt_elf.c:1188) hands each LOAD to `elf_load`,
whose `elf_map` (fs/binfmt_elf.c:395-399, Linux v6.18.46) maps its file
part.  On Linux a shrinking `do_truncate` (fs/open.c:39-71, Linux
v6.18.46) leaves the mappings to `notify_change`, which hands the size
to the inode's `->setattr` or, where the inode has none
(fs/attr.c:545-548, Linux v6.18.46), to `simple_setattr`
(fs/libfs.c:903-918, Linux v6.18.46); bfs's regular files have none
(`bfs_file_inops`, fs/bfs/file.c:203, Linux v6.18.46).  tmpfs's
`shmem_setattr` (mm/shmem.c:1336-1348, Linux v6.18.46), in a kernel with
CONFIG_SHMEM, and `truncate_pagecache` (mm/truncate.c:783-800, Linux
v6.18.46) zap every page past the new end with
`unmap_mapping_range(…, even_cows = 1)`.  `truncate_setsize`
(mm/truncate.c:816-824, Linux v6.18.46) calls the latter, and
`simple_setattr` calls `truncate_setsize` from line 914 of fs/libfs.c
(Linux v6.18.46).  Without CONFIG_SHMEM, tmpfs is ramfs
(mm/shmem.c:5779-5791, Linux v6.18.46), whose regular files' inode
operations set `simple_setattr` as their `setattr`
(`ramfs_file_inode_operations`, fs/ramfs/file-mmu.c:52-53, Linux
v6.18.46).  ext4, FUSE and NFS call `truncate_pagecache` directly: ext4
in `ext4_setattr` (fs/ext4/inode.c:6062), FUSE in `fuse_do_setattr`
(fs/fuse/dir.c:2100) and NFS in `nfs_vmtruncate` (fs/nfs/inode.c:832,
Linux v6.18.46).  hugetlbfs zaps through its own walk instead:
`hugetlbfs_setattr` (fs/hugetlbfs/inode.c:844-875) calls
`hugetlb_vmtruncate` (fs/hugetlbfs/inode.c:619-635), which calls
`hugetlb_vmdelete_list` (fs/hugetlbfs/inode.c:463-493, Linux v6.18.46).
kernfs ignores the size (`kernfs_iop_setattr`, fs/kernfs/inode.c:111-138,
Linux v6.18.46).  None of them changes a VMA's extent. -/
theorem arm_ftruncate_preserves_vm : arm_preserves_vm arm_ftruncate :=
  arm_preserves_of_frame arm_ftruncate (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Open.check_ftruncate_frame _ _ eff m m' evs h)

open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei

/- faccessat's and faccessat2's frame lemmas are proved here, not beside
their checker as ftruncate's are, because `Checks/Sys/Fs/Open.lean` is
the C ticket's file and this registration adds only to its arm file;
`Checks/Arms/Fs/DPath.lean` and `Checks/Arms/Fs/Timerfd.lean` do the
same. -/

/-- Lean-only: every answer the body accepts hands back the model and no
event.  Each arm returns through `check_ret_only`, at the model it was
handed and no event, or through `check_access_exists`, which accepts
with the model unchanged. -/
theorem check_faccessat_body_ok_model (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat_body i dirfd pathp eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Open.check_faccessat_body at h
  generalize read_cstr i.in_mem pathp = r at h
  cases r with
  | CstrTooLong =>
    dsimp only at h
    exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  | CstrFault =>
    dsimp only at h
    exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  | CstrOk p =>
    dsimp only at h
    generalize path_eqb p [] = b at h
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize path_eqb p dot_path = b at h
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          obtain ⟨hm, hevs, -⟩ := Checks.Sys.Fs.Open.check_access_exists_ok_inv eff m m' evs h
          exact ⟨hm, hevs⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          generalize path_eqb p dotdot_path = b at h
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            obtain ⟨hm, hevs, -⟩ := Checks.Sys.Fs.Open.check_access_exists_ok_inv eff m m' evs h
            exact ⟨hm, hevs⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            generalize path_has_slash p = b at h
            cases b with
            | true => simp only [↓reduceIte, reduceCtorEq] at h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte, reduceCtorEq] at h
              · simp only [hn, ↓reduceIte] at h
                generalize fs_under (m_fs m) p = b at h
                cases b with
                | true => simp only [↓reduceIte, reduceCtorEq] at h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  generalize fs_lookup (m_fs m) p = r at h
                  cases r with
                  | none =>
                    dsimp only at h
                    exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
                  | some _ =>
                    dsimp only at h
                    obtain ⟨hm, hevs, -⟩ :=
                      Checks.Sys.Fs.Open.check_access_exists_ok_inv eff m m' evs h
                    exact ⟨hm, hevs⟩

/-- Lean-only: the mode gate returns no event and keeps the model,
as does the shared body (`check_faccessat_body_ok_model`). -/
theorem check_faccessat_ok_model (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat i dirfd pathp mode eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Open.check_faccessat at h
  split at h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  · split at h
    · cases h
    · exact check_faccessat_body_ok_model i dirfd pathp _ m m' evs
        ((check_copyins_after_ok_iff _ _ _ _ _).mp h).2

/-- Lean-only: the mode and flag gates return no event and keep the
model, as does the shared body (`check_faccessat_body_ok_model`). -/
theorem check_faccessat2_ok_model (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Open.check_faccessat2 at h
  split at h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  · split at h
    · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
    · split at h
      · cases h
      · split at h
        · cases h
        · exact check_faccessat_body_ok_model i dirfd pathp _ m m' evs
            ((check_copyins_after_ok_iff _ _ _ _ _).mp h).2

/-- Rocq: `VmMapsDisjoint.check_faccessat_frame`.  The ledger is the
one handed in, by `check_faccessat_ok_model`; a `*_frame` rather than a
`*_preserves`: faccessat writes nothing. -/
theorem check_faccessat_frame (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat i dirfd pathp mode eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, -⟩ := check_faccessat_ok_model i dirfd pathp mode eff m m' evs h
  rfl

/-- Rocq: `VmMapsDisjoint.check_faccessat2_frame`.  The ledger is the
one handed in, by `check_faccessat2_ok_model`; a `*_frame` rather than a
`*_preserves`: faccessat2 writes nothing. -/
theorem check_faccessat2_frame (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, -⟩ := check_faccessat2_ok_model i dirfd pathp mode flags eff m m' evs h
  rfl

/-- `faccessat` (48): the accepted model is the model handed in, so the
ledger is what it was (`check_faccessat_frame`, above). -/
theorem arm_faccessat_preserves_vm : arm_preserves_vm arm_faccessat :=
  arm_preserves_of_frame arm_faccessat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_faccessat_frame _ _ _ _ eff m m' evs h)

/-- `faccessat2` (439): the accepted model is the model handed in, so the
ledger is what it was (`check_faccessat2_frame`, above). -/
theorem arm_faccessat2_preserves_vm : arm_preserves_vm arm_faccessat2 :=
  arm_preserves_of_frame arm_faccessat2 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_faccessat2_frame _ _ _ _ _ eff m m' evs h)

/-- Open, in `h`, the first of `check_openat`'s definitions below that
occurs there, in the order listed.  The three `check_openat` proofs in
this file run it as one more alternative of `vm_frame2`'s loop, so each
definition is opened only once `vm_step` has split the one that calls it,
where Rocq's `check_openat_frame` unfolds them all before its loop.
Opened all at once, the checker is one hypothesis holding the whole
decision tree, and `split at h` on its outermost `if` fails with `simp`
reporting its maximum number of steps exceeded (measured on a scratch
compile of that proof; `Checks/Arms/Mm/Mmap.lean` meets the same limit on
`check_mmap`).  No other alternative of `vm_step` applies to that
hypothesis, so the loop ends where it started.  Opened as the loop
reaches them, each split is over the body of one definition, with the
definitions it calls still folded.  The descriptor wrappers
`check_open_devnull`, `check_open_urandom` and `check_create_wronly`
have no line here: `check_open_result_frame`'s `vm_done` rule and
`check_open_result_cases`, both in `Checks/Sys/Fs/Open.lean`, take them
as they stand. -/
macro "openat_layer " h:ident : tactic => `(tactic| first
  | rw [Checks.Sys.Fs.Open.check_openat_body] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_resolved] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_sep] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_localtime] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_devnull] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_urandom] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_tmp] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_read] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_create] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_excl] at $h:ident
  | rw [Checks.Sys.Fs.Open.check_openat_dir] at $h:ident)

/-- Rocq: `VmMapsDisjoint.check_openat_frame`.  Every model `check_openat`
accepts is the one it was handed, or, through `check_open_result`, that
model with a descriptor bound (`with_fds`) and, when the descriptor is
`check_create_wronly`'s `FdFileW` (the create word on a plain or `/tmp`
name, an exclusive-create word on a plain one), the path emptied
(`with_fs`); neither setter reaches `m_vmmaps`.  Rocq's proof unfolds the
checker's arms and runs `vm_frame2`, whose `vm_done` closes each acceptor
call through `check_open_result_frame`.  This one runs `vm_frame2`'s loop
with `openat_layer` as a third alternative, which opens each arm as the
loop reaches it (that macro's docstring says why), and the `vm_done` rule
beside `check_open_result_frame` in `Checks/Sys/Fs/Open.lean` closes the
acceptor calls.  Rocq
also unfolds `check_openat_append`, `check_openat_rdwr`,
`check_openat_rdwr_excl`, `check_open_append` and `check_open_rdwr`,
which are `Checks/Sys/Fs/Open.lean`'s `unported:` lines. -/
theorem check_openat_frame (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_openat i dirfd pathp flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.Open.check_openat at h
  (repeat' first | vm_step h | vm_done h | openat_layer h) <;> (try rfl)

/-- `openat` (56): the ledger fact is `check_openat_frame` above. -/
theorem arm_openat_preserves_vm : arm_preserves_vm arm_openat :=
  arm_preserves_of_frame arm_openat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_openat_frame i _ _ _ eff m m' evs h)

/-- Rocq: `VmMapsDisjoint.check_close_frame`.  Every model `check_close`
accepts is the one it was handed, or that model with the descriptor's
bindings filtered out (`with_fds`), which does not reach `m_vmmaps`.
Rocq's proof is `unfold check_close in H; vm_frame2 H`, and so is this
one. -/
theorem check_close_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_close fd eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.Open.check_close at h
  vm_frame2 h

/-- `close` (57): the ledger fact is `check_close_frame` above. -/
theorem arm_close_preserves_vm : arm_preserves_vm arm_close :=
  arm_preserves_of_frame arm_close (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_close_frame _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `vm_wf` × `ftruncate`: the ledger fact above. -/
theorem vm_wf_arm_ftruncate : arm_preserves inv_vm_wf arm_ftruncate :=
  Arms.arm_ftruncate_preserves_vm

/-- `fd_table_unique` × `ftruncate`: the descriptor is resolved through
`fdget` (`CLASS(fd, f)`, include/linux/file.h:83, Linux v6.18.46), and an
accepted call hands back the table it was given
(`check_ftruncate_fd_state_frame`, stated beside the checker). -/
theorem fd_table_unique_arm_ftruncate : arm_preserves inv_fd_table_unique arm_ftruncate :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_ftruncate (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Fs.Open.check_ftruncate_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `ftruncate`: no pipe is touched — a pipe end
is refused -EINVAL before any change (fs/open.c:175-176, Linux v6.18.46). -/
theorem pipes_within_capacity_arm_ftruncate :
    arm_preserves inv_pipes_within_capacity arm_ftruncate :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_ftruncate (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Fs.Open.check_ftruncate_fd_state_frame _ _ eff m m' evs h))

/-- Lean-only: the descriptor subsystem is the one handed in:
`do_faccessat` (fs/open.c:467-537, Linux v6.18.46) resolves a path and
installs no descriptor. -/
theorem check_faccessat_fd_state_frame (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat i dirfd pathp mode eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_faccessat_ok_model i dirfd pathp mode eff m m' evs h
  rfl

/-- Lean-only: the descriptor subsystem is the one handed in:
`do_faccessat` (fs/open.c:467-537, Linux v6.18.46) resolves a path and
installs no descriptor. -/
theorem check_faccessat2_fd_state_frame (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_faccessat2_ok_model i dirfd pathp mode flags eff m m' evs h
  rfl

/-- `vm_wf` × `faccessat`: the ledger fact above. -/
theorem vm_wf_arm_faccessat : arm_preserves inv_vm_wf arm_faccessat :=
  Arms.arm_faccessat_preserves_vm

/-- `fd_table_unique` × `faccessat`: the descriptor-state frame above. -/
theorem fd_table_unique_arm_faccessat : arm_preserves inv_fd_table_unique arm_faccessat :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_faccessat
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table
        (check_faccessat_fd_state_frame _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `faccessat`: the descriptor-state frame above. -/
theorem pipes_within_capacity_arm_faccessat :
    arm_preserves inv_pipes_within_capacity arm_faccessat :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_faccessat
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_faccessat_fd_state_frame _ _ _ _ eff m m' evs h))

/-- `vm_wf` × `faccessat2`: the ledger fact above. -/
theorem vm_wf_arm_faccessat2 : arm_preserves inv_vm_wf arm_faccessat2 :=
  Arms.arm_faccessat2_preserves_vm

/-- `fd_table_unique` × `faccessat2`: the descriptor-state frame above. -/
theorem fd_table_unique_arm_faccessat2 : arm_preserves inv_fd_table_unique arm_faccessat2 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_faccessat2
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table
        (check_faccessat2_fd_state_frame _ _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `faccessat2`: the descriptor-state frame above. -/
theorem pipes_within_capacity_arm_faccessat2 :
    arm_preserves inv_pipes_within_capacity arm_faccessat2 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_faccessat2
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_faccessat2_fd_state_frame _ _ _ _ _ eff m m' evs h))

/-! ## What `openat` and `close` write, and why each invariant survives them

`check_openat` hands back the model it was given, or, through
`check_open_result`, that model with a descriptor bound by `fd_insert`
and, when the descriptor is `check_create_wronly`'s `FdFileW`, the path
emptied in the file image.
`check_close` hands back the model it was given, or that model with the
descriptor's bindings dropped by `fd_remove`.  Neither reaches the pipes.
So the descriptor table is the one invariant either arm moves: `openat`'s
binding is `fd_table_unique_fd_insert`'s case, and `close`'s gets one
lemma over `fd_remove`. -/

/-- `fd_remove` keeps the table's descriptors distinct: it drops bindings
and adds none. -/
theorem fd_table_unique_fd_remove (fds : List (word × FdEntry)) (fd : word)
    (h : fd_table_unique fds) : fd_table_unique (fd_remove fds fd) := by
  unfold fd_table_unique fd_remove at *
  exact h.sublist (List.filter_sublist.map _)

/-- `check_openat` keeps the descriptor table's keys distinct. -/
theorem check_openat_fd_table_unique (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_openat i dirfd pathp flags eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.Open.check_openat at h
  (repeat' first | vm_step h | openat_layer h) <;>
    first
      | exact hu
      | (rcases Checks.Sys.Fs.Open.check_open_result_cases h with rfl | ⟨fd, rfl⟩ <;>
          first
            | exact hu
            | exact fd_table_unique_fd_insert _ _ _ hu)

/-- `check_openat` leaves every pipe as it was. -/
theorem check_openat_pipes_within_capacity (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Open.check_openat i dirfd pathp flags eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.Open.check_openat at h
  (repeat' first | vm_step h | openat_layer h) <;>
    first
      | exact hu
      | (rcases Checks.Sys.Fs.Open.check_open_result_cases h with rfl | ⟨fd, rfl⟩ <;> exact hu)

/-- `check_close` keeps the descriptor table's keys distinct. -/
theorem check_close_fd_table_unique (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : Checks.Sys.Fs.Open.check_close fd eff m = CheckOk m' evs)
    (hu : fd_table_unique (m_fds m)) : fd_table_unique (m_fds m') := by
  unfold Checks.Sys.Fs.Open.check_close at h
  (repeat' vm_step h) <;>
    first
      | exact hu
      | exact fd_table_unique_fd_remove _ _ hu

/-- `check_close` leaves every pipe as it was. -/
theorem check_close_pipes_within_capacity (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : Checks.Sys.Fs.Open.check_close fd eff m = CheckOk m' evs)
    (hu : pipes_within_capacity (m_pipes m)) : pipes_within_capacity (m_pipes m') := by
  unfold Checks.Sys.Fs.Open.check_close at h
  (repeat' vm_step h) <;> exact hu

/-- `vm_wf` × `openat`: the ledger fact above. -/
theorem vm_wf_arm_openat : arm_preserves inv_vm_wf arm_openat :=
  Arms.arm_openat_preserves_vm

/-- `fd_table_unique` × `openat`: the minted descriptor is bound by
`fd_insert`, and every other accepted answer leaves the table as it was
(`check_openat_fd_table_unique`). -/
theorem fd_table_unique_arm_openat : arm_preserves inv_fd_table_unique arm_openat := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_openat_fd_table_unique i _ _ _ eff m m' evs h hold

/-- `pipes_within_capacity` × `openat`: no accepted answer reaches the
pipes (`check_openat_pipes_within_capacity`). -/
theorem pipes_within_capacity_arm_openat : arm_preserves inv_pipes_within_capacity arm_openat := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_openat_pipes_within_capacity i _ _ _ eff m m' evs h hold

/-- `vm_wf` × `close`: the ledger fact above. -/
theorem vm_wf_arm_close : arm_preserves inv_vm_wf arm_close :=
  Arms.arm_close_preserves_vm

/-- `fd_table_unique` × `close`: the closed descriptor's bindings are
dropped by `fd_remove`, and the -EBADF answer leaves the table as it was
(`check_close_fd_table_unique`). -/
theorem fd_table_unique_arm_close : arm_preserves inv_fd_table_unique arm_close := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_close_fd_table_unique _ eff m m' evs h hold

/-- `pipes_within_capacity` × `close`: no accepted answer reaches the
pipes (`check_close_pipes_within_capacity`). -/
theorem pipes_within_capacity_arm_close : arm_preserves inv_pipes_within_capacity arm_close := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  exact check_close_pipes_within_capacity _ eff m m' evs h hold

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
