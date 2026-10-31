import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.TacticCore
import LinuxProcessSemantics.LinuxProcessSem.Specs

/-! # Checks.Cases.Tactic — `TacticCore` plus the registrations that need `Specs`

Not part of the trusted specification.  `Checks/Cases/TacticCore.lean`
holds the tactic, the readings and the register of the model's setters and
getters, and imports no spec; this file re-exports it and adds what names a
spec or the dispatcher: the `sys_simp` unfoldings of `syscall_spec`,
`dispatch`, `lookup_arm`, `spec_table`, `exit_spec` and `mmap_spec`, and the
worked checks that read them.  A pin file whose subject is one twin imports
`TacticCore`, so that its mutation cache key stops at that twin's own
`Sys/` file instead of reaching every arm through `spec_table`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Specs

-- Sys/Dispatch.lean, Sys/SyscallTable.lean, Specs.lean: the dispatcher.
attribute [sys_simp low] syscall_spec.eq_1 dispatch.eq_1 lookup_arm.eq_1 lookup_arm.eq_2 spec_table.eq_1

-- Sys/Kernel/Exit.lean.
attribute [sys_simp low] exit_spec.eq_1

-- Sys/Mm/Mmap.lean: the spec, its errno list, and its post-state builders.
attribute [sys_simp low]
  mmap_spec.eq_1 mmap_errnos.eq_1 with_mmap_backing.eq_1 with_mmap_replacement.eq_1
  with_mmap_destroyed.eq_1 mmap_fixed_rw_next.eq_1 mmap_fixed_destroyed_next.eq_1
  mmap_fixed_rw_span_next.eq_1 mmap_fixed_noaccess_span_next.eq_1

/-! ### `exit`, the real spec whose post-state is wholly symbolic

`SYSCALL_DEFINE1(exit, int, error_code)` calls
`do_exit((error_code&0xff)<<8)` and `exit_group` calls
`do_group_exit((error_code & 0xff) << 8)` (kernel/exit.c:1085-1087 and
:1129-1131, Linux v6.18.46, commit 1f99e9ab748f): the seven high bytes are
gone before any status exists.  `Sys.Kernel.Exit.exit_spec`'s docstring
carries the rest of the argument; the arm's pins are
`Checks/Cases/Kernel/Exit.lean`'s (ticket S-Kernel-Exit, where
`exit_256_halts_with_zero` and `exit_256_unmasked_rejected` are stated
again as that file's own), `Checks/Examples.lean` pins the same facts
through the dispatcher by hand, and the four below are the TACTIC's smoke
test on a real spec — they stay here so that a change to `sys_norm` fails
in this file first. -/

theorem exit_iff (code : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    exit_spec code i m o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [] := by
  sys_norm

/-- `exit(256)` halts with status 0: the low byte. -/
theorem exit_256_halts_with_zero (i : SyscallInput) (m : Model) :
    exit_spec 256 i m (Ok (mkEffect 0 [] []) (with_halted 0 m) []) := by
  sys_norm

/-- …and a kernel reporting the unmasked 256 is lying. -/
theorem exit_256_unmasked_rejected (i : SyscallInput) (m : Model) :
    ¬ exit_spec 256 i m (Ok (mkEffect 0 [] []) (with_halted 256 m) []) := by
  sys_refute

theorem exit_never_unmodeled (code : word) (i : SyscallInput) (m : Model) :
    ¬ exit_spec code i m Unmodeled := by
  sys_refute

/-! ### The dispatcher, read through the table -/

/-- Syscall 94 (`exit_group`) with a0 = 256 reaches `exit_spec` and halts
with 0. -/
theorem sysno_94_is_exit_group (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 94 [256, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect 0 [] []) (with_halted 0 m) [] := by
  sys_norm

/-- `io_setup` (0) has no arm: it declines, whatever the arguments and the
memory (`dispatch` reads the number and nothing else).  The demo sat on
`write` (64) until that arm was ported; `io_setup` is outside the Rocq
table too (`docs/syscalls/` has no page for it), so no port can move it
again. -/
theorem sysno_0_is_unmodeled (args : List word) (mem wmem : word → Option byte) (m : Model)
    (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 0 args mem wmem) m o ↔ o = Unmodeled := by
  sys_norm


end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
