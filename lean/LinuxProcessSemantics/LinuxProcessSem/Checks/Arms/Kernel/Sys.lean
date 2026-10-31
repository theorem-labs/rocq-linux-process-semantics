import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Sys — uname, prctl and prlimit64 on the checked surface

The registration of `Checks/Sys/Kernel/Sys.lean`'s uname (160), prctl
(167) and prlimit64 (261) checkers in `checked_table`, in the one file
that registration writes.  `tools/gen_lean_checked.py` renders
`checked_table`, `checked_table_preserves_vm` and `registry_preserves`
from the files under `Checks/Arms/`, one per checker twin, so that
registering an arm creates or edits no hub but this file; its docstring
is the shape it reads and what it refuses. The file holds three
sections, each in the namespace its declarations had when those three
hubs were written by hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_uname`, `arm_prctl`,
  `arm_prlimit64`) and their four `arm_unfold` lemmas each;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The checker twin answers eleven more numbers — the id, pid and session
arms — whose registration is ticket V-Kernel-Sys-ids's and is appended to
this file, not written beside it: one arm file per checker twin is the
generator's rule.

WHAT EACH ROW DECIDES is which registers reach the checker, and in which
width: riscv64's `__riscv_sys<name>` hands the registers over in order,
`orig_a0` then `a1`, `a2`, `a3` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46, commit
1f99e9ab748f, applied at :95), and `__se_sys<name>` narrows each to the
type the `SYSCALL_DEFINE` declares through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  Each row's
docstring says what that makes of its prototype; each row is the term
`Sys/Registry/Kernel/Sys.lean` builds, which `checked_table_arms` checks,
and each is Rocq's `arm_<name>` in `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`.
The `check_syscall` pins that read a row back — the lookup, the register
and the width — are in `Checks/Cases/Checks/Sys/Kernel/Sys.lean`.

THE DESCRIPTOR FRAMES are Lean-only: the Rocq tree registers no `m_fd`
invariant, so `check_uname_fd_state_frame` and its two companions have no
twin.  The tree's rule is that a checker's frame lemma lives beside the
checker, as `check_eventfd2_fd_state_frame` does in
`Checks/Sys/Fs/EventFd.lean`; these three are in this file, as
`check_exit_fd_state_frame` is in `Checks/Arms/Kernel/Exit.lean`, because
the ticket that wrote them kept its Lean edits to this file and the
Cases file.  Moving them beside the checker changes nothing but their
home.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit; the three rows are identical there
and on the day branch this file was written against. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### uname (160) -/

/-- uname (160).  THE DESTINATION IS REGISTER `a0`, READ WHOLE:
`SYSCALL_DEFINE1(newuname, struct new_utsname __user *, name)`
(kernel/sys.c:1351, Linux v6.18.46) declares a pointer, 64 bits on
riscv64, so the cast drops nothing.  The checker also takes the whole
input, since the writable view it walks is `i.in_wmem`. -/
def arm_uname : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 160 (fun i => Sys.Kernel.Sys.uname_spec (in_arg i 0) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Sys.check_uname i (in_arg i 0) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Sys.uname_witness (in_arg i 0) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_uname_sound_ok i (in_arg i 0) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_uname_sound_unmodeled i (in_arg i 0) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_uname_complete_ok i (in_arg i 0) m eff m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_uname_complete_unmodeled i (in_arg i 0) m h eff
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.uname_witness_ok (in_arg i 0) i m

@[arm_unfold] theorem ca_check_arm_uname (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_uname.ca_check i eff m = Checks.Sys.Kernel.Sys.check_uname i (in_arg i 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_uname (i : SyscallInput) (m : Model) :
    arm_uname.ca_witness i m = Checks.Sys.Kernel.Sys.uname_witness (in_arg i 0) i m := rfl
@[arm_unfold] theorem sa_spec_arm_uname (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_uname.ca_arm.sa_spec i m o = Sys.Kernel.Sys.uname_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_uname : ca_no arm_uname = 160 := rfl

/- ### prctl (167) -/

/-- prctl (167).  THE OPTION IS REGISTER `a0` CUT TO ITS LOW 32 BITS, AND
`arg2` IS `a1` READ WHOLE: `SYSCALL_DEFINE5(prctl, int, option, unsigned
long, arg2, …)` (kernel/sys.c:2518, Linux v6.18.46) declares the option
an `int`, so the cast keeps the low half, and `arg2` an `unsigned long`,
64 bits on riscv64.  `Sys.Syscall.int32` is that reading of the option,
applied here at the boundary as Rocq's `arm_prctl` applies it, so the
checker and the witness receive the narrowed word: `prctl(2^32 | 23, 0)`
is `PR_CAPBSET_READ` to the kernel — `security_task_prctl` is handed the
`int` (:2525) — and the probe's `hiopt` mode records the kernel answering
it 1.  A row handing over the whole register would decline that call
where Linux answers it; one narrowing `arg2` would answer
`prctl(23, 2^32)` as capability 0 where `cap_task_prctl`'s
`PR_CAPBSET_READ` case (security/commoncap.c:1298-1301, Linux v6.18.46)
tests `cap_valid` on the whole `unsigned long` and answers -EINVAL.  `a2` to `a4` are read by nothing on the one modeled
option's path, and the row reads none of them. -/
def arm_prctl : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 167
    (fun i => Sys.Kernel.Sys.prctl_spec (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_prctl (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Sys.prctl_witness (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_prctl_sound_ok (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) eff
      m m' evs h i
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_prctl_sound_unmodeled (Sys.Syscall.int32 (in_arg i 0))
      (in_arg i 1) eff m h i
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_prctl_complete_ok (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1)
      i m eff m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_prctl_complete_unmodeled (Sys.Syscall.int32 (in_arg i 0))
      (in_arg i 1) i m h eff
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.prctl_witness_ok (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_prctl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_prctl.ca_check i eff m
      = Checks.Sys.Kernel.Sys.check_prctl (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_prctl (i : SyscallInput) (m : Model) :
    arm_prctl.ca_witness i m
      = Checks.Sys.Kernel.Sys.prctl_witness (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) m := rfl
@[arm_unfold] theorem sa_spec_arm_prctl (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_prctl.ca_arm.sa_spec i m o
      = Sys.Kernel.Sys.prctl_spec (Sys.Syscall.int32 (in_arg i 0)) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_prctl : ca_no arm_prctl = 167 := rfl

/- ### prlimit64 (261) -/

/-- prlimit64 (261).  ALL FOUR REGISTERS, `a0` TO `a3`, READ WHOLE — and
for the first two that is a DECLINE, not the kernel's reading.
`SYSCALL_DEFINE4(prlimit64, pid_t, pid, unsigned int, resource, const
struct rlimit64 __user *, new_rlim, struct rlimit64 __user *, old_rlim)`
(kernel/sys.c:1729-1731, Linux v6.18.46) declares the two pointers 64
bits wide, so reading them whole is the cast; but `pid_t` is an `int`
(include/uapi/asm-generic/posix_types.h:28 and include/linux/types.h:27,
Linux v6.18.46) and `resource` an `unsigned int`, so Linux answers
`prlimit64(2^32, …)` as pid 0 and `prlimit64(0, 2^32 | RLIMIT_CORE, …)`
as `RLIMIT_CORE`.  Rocq's `arm_prlimit64` hands both registers over whole
and `prlimit64_spec` (`Sys/Kernel/Sys.lean`) declines a pid that is not
exactly 0 and a resource that is not exactly `RLIMIT_CORE`, so a high bit
in either is declined at the spec's first two gates, never answered; the
probe's `pid-high` and `res-high` modes are those two calls, and both are
`fail-closed` cases.
Narrowing here, as `arm_prctl` does, would be the row answering calls
the spec it is checked against (`checked_table_arms`) declines. -/
def arm_prlimit64 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 261
    (fun i => Sys.Kernel.Sys.prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Sys.prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_prlimit64_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_prlimit64_sound_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_prlimit64_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) m eff m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_prlimit64_complete_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) m h eff
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.prlimit64_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_prlimit64 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_prlimit64.ca_check i eff m
      = Checks.Sys.Kernel.Sys.check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2)
          (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_prlimit64 (i : SyscallInput) (m : Model) :
    arm_prlimit64.ca_witness i m
      = Checks.Sys.Kernel.Sys.prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2)
          (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_prlimit64 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_prlimit64.ca_arm.sa_spec i m o
      = Sys.Kernel.Sys.prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          i m o := rfl
@[arm_unfold] theorem ca_no_arm_prlimit64 : ca_no arm_prlimit64 = 261 := rfl


/- ### setgid (144) -/

/-- setgid (144).  The argument is `uid32` of register `a0`, and the
narrowing is this arm's, not the checker's: `SYSCALL_DEFINE1(setgid,
gid_t, gid)` (kernel/sys.c:515, Linux v6.18.46) declares a `gid_t`, which
is `__kernel_gid32_t`, an `unsigned int` (include/linux/types.h:38,
include/uapi/asm-generic/posix_types.h:50, Linux v6.18.46), and riscv's
wrapper hands `__do_sys_setgid` the register as `(__force gid_t) gid`
(`__SC_CAST`, include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), so a
register whose low 32 bits are all ones is the id -1 whatever its upper
half holds.  `check_setid` compares the id against `ID_MINUS_ONE` at full
width and is handed the narrowed word, as Rocq's `arm_setgid` hands it.
`ca_arm` is the term `Sys/Registry/Kernel/Sys.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_setgid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 144 (fun i => Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_setid Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false
      (uid32 (in_arg i 0)) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Sys.setid_witness (uid32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setid_sound_ok Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids
      false (uid32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_setid_sound_unmodeled Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setid_complete_ok Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_setid_complete_unmodeled Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) i m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.setid_witness_ok Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids
      false (uid32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_setgid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_setgid.ca_check i eff m =
      Checks.Sys.Kernel.Sys.check_setid Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false
        (uid32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setgid (i : SyscallInput) (m : Model) :
    arm_setgid.ca_witness i m = Checks.Sys.Kernel.Sys.setid_witness (uid32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_setgid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_setgid.ca_arm.sa_spec i m o =
      Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false
        (uid32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_setgid : ca_no arm_setgid = 144 := rfl

/- ### setuid (146) -/

/-- setuid (146).  `arm_setgid` over the uid triple, with `user` set so
that the checker weighs the two -EAGAINs `__sys_setuid`'s capable arm can
raise; the parameter is `uid_t`
(`SYSCALL_DEFINE1(setuid, uid_t, uid)`, kernel/sys.c:698, Linux
v6.18.46), aliased to `__kernel_uid32_t` (include/linux/types.h:37,
Linux v6.18.46), narrowed by the same `__SC_CAST`. -/
def arm_setuid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 146 (fun i => Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_setid Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true
      (uid32 (in_arg i 0)) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Sys.setid_witness (uid32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setid_sound_ok Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids
      true (uid32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_setid_sound_unmodeled Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setid_complete_ok Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_setid_complete_unmodeled Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) i m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.setid_witness_ok Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids
      true (uid32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_setuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_setuid.ca_check i eff m =
      Checks.Sys.Kernel.Sys.check_setid Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true
        (uid32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setuid (i : SyscallInput) (m : Model) :
    arm_setuid.ca_witness i m = Checks.Sys.Kernel.Sys.setid_witness (uid32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_setuid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_setuid.ca_arm.sa_spec i m o =
      Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true
        (uid32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_setuid : ca_no arm_setuid = 146 := rfl

/- ### setresuid (147) -/

/-- setresuid (147).  All three arguments are narrowed:
`SYSCALL_DEFINE3(setresuid, uid_t, ruid, uid_t, euid, uid_t, suid)`
(kernel/sys.c:783, Linux v6.18.46) casts each register by `__SC_CAST`
(include/linux/syscalls.h:132, arch/riscv/include/asm/syscall_wrapper.h:88,
Linux v6.18.46), so "leave this id alone" is any register whose low
half is all ones, which is what the checker's full-width `ID_MINUS_ONE`
test sees once this arm has narrowed the word. -/
def arm_setresuid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 147 (fun i => Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_setresid Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true
      (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Sys.setresid_witness Sys.Kernel.Sys.cred_uids
      (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setresid_sound_ok Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_setresid_sound_unmodeled Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setresid_complete_ok Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_setresid_complete_unmodeled Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) i m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.setresid_witness_ok Sys.Kernel.Sys.cred_uids
      Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) i m

@[arm_unfold] theorem ca_check_arm_setresuid (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_setresuid.ca_check i eff m =
      Checks.Sys.Kernel.Sys.check_setresid Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids
        true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setresuid (i : SyscallInput) (m : Model) :
    arm_setresuid.ca_witness i m =
      Checks.Sys.Kernel.Sys.setresid_witness Sys.Kernel.Sys.cred_uids
        (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := rfl
@[arm_unfold] theorem sa_spec_arm_setresuid (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_setresuid.ca_arm.sa_spec i m o =
      Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true
        (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_setresuid : ca_no arm_setresuid = 147 := rfl

/- ### setresgid (149) -/

/-- setresgid (149).  `arm_setresuid` over the gid triple, without the
`user` flag; `SYSCALL_DEFINE3(setresgid, gid_t, rgid, gid_t, egid,
gid_t, sgid)` (kernel/sys.c:872, Linux v6.18.46) narrows as setresuid
does. -/
def arm_setresgid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 149 (fun i => Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Sys.check_setresid Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false
      (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Sys.setresid_witness Sys.Kernel.Sys.cred_gids
      (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setresid_sound_ok Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_setresid_sound_unmodeled Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setresid_complete_ok Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_setresid_complete_unmodeled Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) i m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sys.setresid_witness_ok Sys.Kernel.Sys.cred_gids
      Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1))
      (uid32 (in_arg i 2)) i m

@[arm_unfold] theorem ca_check_arm_setresgid (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_setresgid.ca_check i eff m =
      Checks.Sys.Kernel.Sys.check_setresid Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids
        false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setresgid (i : SyscallInput) (m : Model) :
    arm_setresgid.ca_witness i m =
      Checks.Sys.Kernel.Sys.setresid_witness Sys.Kernel.Sys.cred_gids
        (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := rfl
@[arm_unfold] theorem sa_spec_arm_setresgid (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_setresgid.ca_arm.sa_spec i m o =
      Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false
        (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_setresgid : ca_no arm_setresgid = 149 := rfl

/- ### setsid (157) -/

/-- setsid (157).  No argument: `SYSCALL_DEFINE0(setsid)`
(kernel/sys.c:1303, Linux v6.18.46). -/
def arm_setsid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 157 (fun i => Sys.Kernel.Sys.setsid_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_setsid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.setsid_witness m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Sys.check_setsid_sound_ok i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Kernel.Sys.check_setsid_sound_unmodeled i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_setsid_complete_ok i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_setsid_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.setsid_witness_ok i m

@[arm_unfold] theorem ca_check_arm_setsid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_setsid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_setsid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setsid (i : SyscallInput) (m : Model) :
    arm_setsid.ca_witness i m = Checks.Sys.Kernel.Sys.setsid_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_setsid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_setsid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.setsid_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_setsid : ca_no arm_setsid = 157 := rfl

/- ### getpid (172) -/

/-- getpid (172).  `check_getpid` is `check_set_tid_address` under
another name; the checker twin's header says why the two share it. -/
def arm_getpid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 172 (fun i => Sys.Kernel.Sys.getpid_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_getpid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.getpid_witness m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Sys.check_getpid_sound_ok i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Kernel.Sys.check_getpid_sound_unmodeled i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getpid_complete_ok i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_getpid_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.getpid_witness_ok i m

@[arm_unfold] theorem ca_check_arm_getpid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getpid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_getpid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getpid (i : SyscallInput) (m : Model) :
    arm_getpid.ca_witness i m = Checks.Sys.Kernel.Sys.getpid_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_getpid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_getpid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.getpid_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_getpid : ca_no arm_getpid = 172 := rfl

/- ### getuid (174), geteuid (175), getgid (176), getegid (177) -/

/-- getuid (174).  One reader per credential field, the field being the
selector every lemma takes. -/
def arm_getuid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 174 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_uid i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_getid Creds.cr_uid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.getid_witness Creds.cr_uid m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_ok Creds.cr_uid eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_unmodeled Creds.cr_uid eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_ok Creds.cr_uid eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_unmodeled Creds.cr_uid i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.getid_witness_ok Creds.cr_uid i m

@[arm_unfold] theorem ca_check_arm_getuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getuid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_getid Creds.cr_uid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getuid (i : SyscallInput) (m : Model) :
    arm_getuid.ca_witness i m = Checks.Sys.Kernel.Sys.getid_witness Creds.cr_uid m := rfl
@[arm_unfold] theorem sa_spec_arm_getuid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_getuid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.getid_spec Creds.cr_uid i m o := rfl
@[arm_unfold] theorem ca_no_arm_getuid : ca_no arm_getuid = 174 := rfl

/-- geteuid (175). -/
def arm_geteuid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 175 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_euid i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_getid Creds.cr_euid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.getid_witness Creds.cr_euid m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_ok Creds.cr_euid eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_unmodeled Creds.cr_euid eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_ok Creds.cr_euid eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_unmodeled Creds.cr_euid i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.getid_witness_ok Creds.cr_euid i m

@[arm_unfold] theorem ca_check_arm_geteuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_geteuid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_getid Creds.cr_euid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_geteuid (i : SyscallInput) (m : Model) :
    arm_geteuid.ca_witness i m = Checks.Sys.Kernel.Sys.getid_witness Creds.cr_euid m := rfl
@[arm_unfold] theorem sa_spec_arm_geteuid (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_geteuid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.getid_spec Creds.cr_euid i m o := rfl
@[arm_unfold] theorem ca_no_arm_geteuid : ca_no arm_geteuid = 175 := rfl

/-- getgid (176). -/
def arm_getgid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 176 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_gid i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_getid Creds.cr_gid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.getid_witness Creds.cr_gid m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_ok Creds.cr_gid eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_unmodeled Creds.cr_gid eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_ok Creds.cr_gid eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_unmodeled Creds.cr_gid i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.getid_witness_ok Creds.cr_gid i m

@[arm_unfold] theorem ca_check_arm_getgid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getgid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_getid Creds.cr_gid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getgid (i : SyscallInput) (m : Model) :
    arm_getgid.ca_witness i m = Checks.Sys.Kernel.Sys.getid_witness Creds.cr_gid m := rfl
@[arm_unfold] theorem sa_spec_arm_getgid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_getgid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.getid_spec Creds.cr_gid i m o := rfl
@[arm_unfold] theorem ca_no_arm_getgid : ca_no arm_getgid = 176 := rfl

/-- getegid (177). -/
def arm_getegid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 177 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_egid i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_getid Creds.cr_egid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.getid_witness Creds.cr_egid m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_ok Creds.cr_egid eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sys.check_getid_sound_unmodeled Creds.cr_egid eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_ok Creds.cr_egid eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_getid_complete_unmodeled Creds.cr_egid i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.getid_witness_ok Creds.cr_egid i m

@[arm_unfold] theorem ca_check_arm_getegid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getegid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_getid Creds.cr_egid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getegid (i : SyscallInput) (m : Model) :
    arm_getegid.ca_witness i m = Checks.Sys.Kernel.Sys.getid_witness Creds.cr_egid m := rfl
@[arm_unfold] theorem sa_spec_arm_getegid (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_getegid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.getid_spec Creds.cr_egid i m o := rfl
@[arm_unfold] theorem ca_no_arm_getegid : ca_no arm_getegid = 177 := rfl

/- ### gettid (178) -/

/-- gettid (178).  `arm_getpid` under the next number: the one-thread
process this model carries has one id for both. -/
def arm_gettid : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 178 (fun i => Sys.Kernel.Sys.gettid_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sys.check_gettid eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sys.gettid_witness m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Sys.check_gettid_sound_ok i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Kernel.Sys.check_gettid_sound_unmodeled i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sys.check_gettid_complete_ok i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sys.check_gettid_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sys.gettid_witness_ok i m

@[arm_unfold] theorem ca_check_arm_gettid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_gettid.ca_check i eff m = Checks.Sys.Kernel.Sys.check_gettid eff m := rfl
@[arm_unfold] theorem ca_witness_arm_gettid (i : SyscallInput) (m : Model) :
    arm_gettid.ca_witness i m = Checks.Sys.Kernel.Sys.gettid_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_gettid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_gettid.ca_arm.sa_spec i m o = Sys.Kernel.Sys.gettid_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_gettid : ca_no arm_gettid = 178 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `uname` (160): an accepted call hands back `m` or `with_utsname bs m`,
and the latter rebuilds the process state alone, so the ledger is what
it was (`check_uname_frame`, stated beside the checker in
`Checks/Sys/Kernel/Sys.lean`). -/
theorem arm_uname_preserves_vm : arm_preserves_vm arm_uname :=
  arm_preserves_of_frame arm_uname (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_uname_frame _ _ eff m m' evs h)

/-- `prctl` (167): both accepting arms hand back `m`
(`check_prctl_frame`). -/
theorem arm_prctl_preserves_vm : arm_preserves_vm arm_prctl :=
  arm_preserves_of_frame arm_prctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_prctl_frame _ _ eff m m' evs h)

/-- `prlimit64` (261): an accepted call hands back `m` or
`with_rlimit_core bs m`, which rebuilds the limit state alone
(`check_prlimit64_frame`). -/
theorem arm_prlimit64_preserves_vm : arm_preserves_vm arm_prlimit64 :=
  arm_preserves_of_frame arm_prlimit64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_prlimit64_frame _ _ _ _ _ eff m m' evs h)


/-! Each ledger fact is the checker's frame lemma, stated beside the
checker in `Checks/Sys/Kernel/Sys.lean`, lifted through
`arm_preserves_of_frame`. -/

theorem arm_setgid_preserves_vm : arm_preserves_vm arm_setgid :=
  arm_preserves_of_frame arm_setgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_setid_frame _ _ _ _ eff m m' evs h)

theorem arm_setuid_preserves_vm : arm_preserves_vm arm_setuid :=
  arm_preserves_of_frame arm_setuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_setid_frame _ _ _ _ eff m m' evs h)

theorem arm_setresuid_preserves_vm : arm_preserves_vm arm_setresuid :=
  arm_preserves_of_frame arm_setresuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_setresid_frame _ _ _ _ _ _ eff m m' evs h)

theorem arm_setresgid_preserves_vm : arm_preserves_vm arm_setresgid :=
  arm_preserves_of_frame arm_setresgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_setresid_frame _ _ _ _ _ _ eff m m' evs h)

theorem arm_setsid_preserves_vm : arm_preserves_vm arm_setsid :=
  arm_preserves_of_frame arm_setsid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_setsid_frame eff m m' evs h)

theorem arm_getpid_preserves_vm : arm_preserves_vm arm_getpid :=
  arm_preserves_of_frame arm_getpid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_getpid_frame eff m m' evs h)

theorem arm_getuid_preserves_vm : arm_preserves_vm arm_getuid :=
  arm_preserves_of_frame arm_getuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_getid_frame _ eff m m' evs h)

theorem arm_geteuid_preserves_vm : arm_preserves_vm arm_geteuid :=
  arm_preserves_of_frame arm_geteuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_getid_frame _ eff m m' evs h)

theorem arm_getgid_preserves_vm : arm_preserves_vm arm_getgid :=
  arm_preserves_of_frame arm_getgid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_getid_frame _ eff m m' evs h)

theorem arm_getegid_preserves_vm : arm_preserves_vm arm_getegid :=
  arm_preserves_of_frame arm_getegid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_getid_frame _ eff m m' evs h)

theorem arm_gettid_preserves_vm : arm_preserves_vm arm_gettid :=
  arm_preserves_of_frame arm_gettid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sys.check_gettid_frame eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys

/-! ## The descriptor-state frame lemmas

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma per checker over the whole record answers both.  Each is its
checker's `check_<name>_frame` (`Checks/Sys/Kernel/Sys.lean`) with a
different projection at the end: the accepted models are the same, and
`with_utsname` and `with_rlimit_core` rebuild the model from `m.m_fd`
unchanged (`State/Model.lean`), so every leaf is `rfl`.  The header says
why they are here and not beside the checker. -/

/-! The id, pid and session checkers answer the same way: every model
they hand back is the one handed in or one rebuilt by `with_tid`,
`with_creds` or `with_setsid_succeeded` (`State/Model.lean`), each of
which also copies `m_fd` unchanged, so each of those proofs is its own
checker's vm frame lemma with a different projection at the end too.
They are stated here rather than beside the checkers because the
registration ticket's files do not include the checker twin, as
`Checks/Arms/Kernel/Exit.lean` says of `check_exit_fd_state_frame`;
moving one there changes nothing but its home. -/

/-- `check_prctl` answers with `m` on both accepting arms, so the
descriptor subsystem is the one it was handed. -/
theorem check_prctl_fd_state_frame (option_ arg2 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_prctl option_ arg2 eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_prctl at h
  split at h
  · cases h
  · split at h
    · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl

/-- `check_uname` answers with `m` (the fault) or with `m` or
`with_utsname bs m` (the copy: the record repeated, or drawn and
recorded); none touches a descriptor. -/
theorem check_uname_fd_state_frame (i : SyscallInput) (name : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_uname i name eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_uname at h
  split at h
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · split at h
    · cases h
    · obtain ⟨_, -, -, hcase⟩ := check_uname_copy_ok _ _ _ _ _ _ h
      rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

/-- `check_prlimit64` answers with `m` (the faults, the -EINVAL, the
pinned read) or with `with_rlimit_core bs m` (the first read, the set);
none touches a descriptor. -/
theorem check_prlimit64_fd_state_frame (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_prlimit64 at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · split at h
      · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        rfl
      · cases h
    · obtain ⟨_, -, -, hcase⟩ := check_rlim64_read_ok _ _ _ _ _ _ h
      rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  · split at h
    · cases h
    · split at h
      · split at h
        · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          rfl
        · cases h
      · split at h
        · obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
          rfl
        · split at h
          · cases h
          · obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            rfl

/-- `vm_wf` × `uname`: the ledger fact above. -/
theorem vm_wf_arm_uname : arm_preserves inv_vm_wf arm_uname :=
  Arms.arm_uname_preserves_vm

/-- `vm_wf` × `prctl`: likewise. -/
theorem vm_wf_arm_prctl : arm_preserves inv_vm_wf arm_prctl :=
  Arms.arm_prctl_preserves_vm

/-- `vm_wf` × `prlimit64`: likewise. -/
theorem vm_wf_arm_prlimit64 : arm_preserves inv_vm_wf arm_prlimit64 :=
  Arms.arm_prlimit64_preserves_vm

/-- `fd_table_unique` × `uname`. -/
theorem fd_table_unique_arm_uname : arm_preserves inv_fd_table_unique arm_uname :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_uname (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_uname_fd_state_frame _ _ eff m m' evs h))

/-- `fd_table_unique` × `prctl`. -/
theorem fd_table_unique_arm_prctl : arm_preserves inv_fd_table_unique arm_prctl :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_prctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_prctl_fd_state_frame _ _ eff m m' evs h))

/-- `fd_table_unique` × `prlimit64`. -/
theorem fd_table_unique_arm_prlimit64 : arm_preserves inv_fd_table_unique arm_prlimit64 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_prlimit64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (check_prlimit64_fd_state_frame _ _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `uname`. -/
theorem pipes_within_capacity_arm_uname : arm_preserves inv_pipes_within_capacity arm_uname :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_uname (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_uname_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `prctl`. -/
theorem pipes_within_capacity_arm_prctl : arm_preserves inv_pipes_within_capacity arm_prctl :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_prctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_prctl_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `prlimit64`. -/
theorem pipes_within_capacity_arm_prlimit64 :
    arm_preserves inv_pipes_within_capacity arm_prlimit64 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_prlimit64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (check_prlimit64_fd_state_frame _ _ _ _ _ eff m m' evs h))

/-- `check_getpid` (and `check_gettid`, the same function) is
`check_set_tid_address`, whose accepted model is `m` or `with_tid ret m`. -/
theorem check_getpid_fd_state_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sys.check_getpid eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sys.check_getpid Checks.Sys.Kernel.Fork.check_set_tid_address at h
  split at h
  · split at h
    · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
        rfl
      · cases h
    · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
        rfl
      · cases h
  · cases h

/-- `check_setsid`: `m` or `with_setsid_succeeded (with_tid ret m)`. -/
theorem check_setsid_fd_state_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sys.check_setsid eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sys.check_setsid at h
  split at h
  · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
      rfl
    · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
          rfl
        · cases h
  · cases h

/-- `check_getid`: a reader hands back the model it was given. -/
theorem check_getid_fd_state_frame (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : Checks.Sys.Kernel.Sys.check_getid sel eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sys.check_getid at h
  obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  rfl

/-- `check_setid`: `m` or `with_creds _ m` on every arm. -/
theorem check_setid_fd_state_frame (get : Creds → Sys.Kernel.Sys.IdTriple)
    (put : Sys.Kernel.Sys.IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sys.check_setid get put user v eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  simp only [Checks.Sys.Kernel.Sys.check_setid] at h
  split at h
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · split at h
    · rcases Checks.Sys.Kernel.Sys.check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl
    · split at h
      · rcases Checks.Sys.Kernel.Sys.check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;>
          rfl
      · rcases Checks.Sys.Kernel.Sys.check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;>
          rfl

/-- `check_setresid`: `m` or `with_creds _ m` on every arm. -/
theorem check_setresid_fd_state_frame (get : Creds → Sys.Kernel.Sys.IdTriple)
    (put : Sys.Kernel.Sys.IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sys.check_setresid get put user r e s eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  simp only [Checks.Sys.Kernel.Sys.check_setresid] at h
  rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · rcases Checks.Sys.Kernel.Sys.ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    · rcases Checks.Sys.Kernel.Sys.check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl

/-! ## `vm_wf`: the ledger facts above -/

theorem vm_wf_arm_setgid : arm_preserves inv_vm_wf arm_setgid :=
  Arms.arm_setgid_preserves_vm

theorem vm_wf_arm_setuid : arm_preserves inv_vm_wf arm_setuid :=
  Arms.arm_setuid_preserves_vm

theorem vm_wf_arm_setresuid : arm_preserves inv_vm_wf arm_setresuid :=
  Arms.arm_setresuid_preserves_vm

theorem vm_wf_arm_setresgid : arm_preserves inv_vm_wf arm_setresgid :=
  Arms.arm_setresgid_preserves_vm

theorem vm_wf_arm_setsid : arm_preserves inv_vm_wf arm_setsid :=
  Arms.arm_setsid_preserves_vm

theorem vm_wf_arm_getpid : arm_preserves inv_vm_wf arm_getpid :=
  Arms.arm_getpid_preserves_vm

theorem vm_wf_arm_getuid : arm_preserves inv_vm_wf arm_getuid :=
  Arms.arm_getuid_preserves_vm

theorem vm_wf_arm_geteuid : arm_preserves inv_vm_wf arm_geteuid :=
  Arms.arm_geteuid_preserves_vm

theorem vm_wf_arm_getgid : arm_preserves inv_vm_wf arm_getgid :=
  Arms.arm_getgid_preserves_vm

theorem vm_wf_arm_getegid : arm_preserves inv_vm_wf arm_getegid :=
  Arms.arm_getegid_preserves_vm

theorem vm_wf_arm_gettid : arm_preserves inv_vm_wf arm_gettid :=
  Arms.arm_gettid_preserves_vm

/-! ## `fd_table_unique` and `pipes_within_capacity`: the frames above -/

theorem fd_table_unique_arm_setgid : arm_preserves inv_fd_table_unique arm_setgid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setid_fd_state_frame _ _ _ _ eff m m' evs h))

theorem pipes_within_capacity_arm_setgid : arm_preserves inv_pipes_within_capacity arm_setgid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setid_fd_state_frame _ _ _ _ eff m m' evs h))

theorem fd_table_unique_arm_setuid : arm_preserves inv_fd_table_unique arm_setuid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setid_fd_state_frame _ _ _ _ eff m m' evs h))

theorem pipes_within_capacity_arm_setuid : arm_preserves inv_pipes_within_capacity arm_setuid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setid_fd_state_frame _ _ _ _ eff m m' evs h))

theorem fd_table_unique_arm_setresuid : arm_preserves inv_fd_table_unique arm_setresuid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setresuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setresid_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

theorem pipes_within_capacity_arm_setresuid :
    arm_preserves inv_pipes_within_capacity arm_setresuid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setresuid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setresid_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

theorem fd_table_unique_arm_setresgid : arm_preserves inv_fd_table_unique arm_setresgid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setresgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setresid_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

theorem pipes_within_capacity_arm_setresgid :
    arm_preserves inv_pipes_within_capacity arm_setresgid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setresgid (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setresid_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

theorem fd_table_unique_arm_setsid : arm_preserves inv_fd_table_unique arm_setsid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setsid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setsid_fd_state_frame eff m m' evs h))

theorem pipes_within_capacity_arm_setsid : arm_preserves inv_pipes_within_capacity arm_setsid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setsid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setsid_fd_state_frame eff m m' evs h))

theorem fd_table_unique_arm_getpid : arm_preserves inv_fd_table_unique arm_getpid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getpid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getpid_fd_state_frame eff m m' evs h))

theorem pipes_within_capacity_arm_getpid : arm_preserves inv_pipes_within_capacity arm_getpid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getpid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getpid_fd_state_frame eff m m' evs h))

theorem fd_table_unique_arm_getuid : arm_preserves inv_fd_table_unique arm_getuid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getid_fd_state_frame _ eff m m' evs h))

theorem pipes_within_capacity_arm_getuid : arm_preserves inv_pipes_within_capacity arm_getuid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getid_fd_state_frame _ eff m m' evs h))

theorem fd_table_unique_arm_geteuid : arm_preserves inv_fd_table_unique arm_geteuid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_geteuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getid_fd_state_frame _ eff m m' evs h))

theorem pipes_within_capacity_arm_geteuid : arm_preserves inv_pipes_within_capacity arm_geteuid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_geteuid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getid_fd_state_frame _ eff m m' evs h))

theorem fd_table_unique_arm_getgid : arm_preserves inv_fd_table_unique arm_getgid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getgid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getid_fd_state_frame _ eff m m' evs h))

theorem pipes_within_capacity_arm_getgid : arm_preserves inv_pipes_within_capacity arm_getgid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getgid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getid_fd_state_frame _ eff m m' evs h))

theorem fd_table_unique_arm_getegid : arm_preserves inv_fd_table_unique arm_getegid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getegid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getid_fd_state_frame _ eff m m' evs h))

theorem pipes_within_capacity_arm_getegid : arm_preserves inv_pipes_within_capacity arm_getegid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getegid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getid_fd_state_frame _ eff m m' evs h))

theorem fd_table_unique_arm_gettid : arm_preserves inv_fd_table_unique arm_gettid :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_gettid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getpid_fd_state_frame eff m m' evs h))

theorem pipes_within_capacity_arm_gettid : arm_preserves inv_pipes_within_capacity arm_gettid :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_gettid (fun _ eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getpid_fd_state_frame eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
