import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.VmMapsDisjoint.Witness — the counterexample, one syscall at a time

The third part of the `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
twin: PART 1's step examples, each a `check_syscall` call taking one
witness state to the next, and the three refusals Rocq pins beside them.
`Checks/VmMapsDisjoint.lean` holds the states the steps name, the PART 1
examples that read a ledger alone, and the kernel fact the chain turns on;
the argument each step makes is on the Rocq example it twins and is not
repeated.  Not part of the trusted specification.
`Checks/Cases/Checks/VmMapsDisjoint/Witness.lean` holds what Rocq does not
state: the refusals of the lies a kernel could tell at those steps, and
the pins of the elaborator claim below.

WHY A PART.  `check_syscall` dispatches over `Checks/Sys/Table.lean`,
which imports `Checks/Sys/Mm/Mmap.lean`, the file of the brk, munmap and
mmap checkers the steps call; that file imports `Checks/VmMapsDisjoint.lean`
for the invariant and the ledger lemmas its preserves lemmas walk, so the
steps stated in the whole would close a cycle.  This file imports the
whole and `Checks/ExecutableSpecs.lean`, and no spec or checker file
imports it: the direction the generated `Checks/VmMapsDisjoint/Arms.lean`
takes, for the same reason.  The
argument stops holding once no module `Checks/ExecutableSpecs.lean`
reaches imports the whole.  Today that module is the mmap checkers' file
alone; `Checks/Sys/Fs/EventPoll.lean` and `Checks/Sys/Fs/Ioctl.lean`
import the whole too, and join it the day `Checks/Sys/Table.lean` imports
either.

THE HEADER'S BASELINE is the whole's, a71fd38a, and not the port's common
baseline f44244ad, which is no ancestor of the branch: PART 1 reads the
same at both commits and at the branch's own head.

HOW A STEP CLOSES.  Rocq's `check_eq` is `vm_compute` and then
`reflexivity`, descending by `f_equal` to the `bv` leaves.  Its twin is
not `decide`, whatever `Checks/VmMapsDisjoint.lean`'s header anticipates
for this file: a step equates two `check_result`s that carry a `Model`,
and `Model` has no `DecidableEq`, its input streams being functions.  The
comparison is definitional equality, and the kernel re-checks every proof
below whichever of three routes the elaborator is taken by:
- `rfl`, where the elaborator's `isDefEq` evaluates the checker's answer;
- `conv => lhs; whnf` first, on the munmap step: `check_munmap`'s
  `TASK_SIZE < addr + nZ` gate is an `Int` `<` against a literal, and at
  the default `maxRecDepth` (512) `rfl` exceeds it on that gate alone
  (`decide (TASK_SIZE < bv_unsigned (65536 : word) + 4096) = false`),
  where `Meta.whnf` evaluates it;
- on the two mmap grants the `whnf` reaches `CheckOk` but not the model:
  the accepted ledger carries the grant's page-rounded length
  `Z_to_bv 64 (page_round_up_Z (bv_unsigned 4096))`, which `rfl` at that
  depth cannot equate with `4096` even alone, so `decide` evaluates it
  and a `rw` hands `rfl` the literal.
A fourth route, not taken here, is the depth itself, the one
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`'s K6c section takes: under
`set_option maxRecDepth 32768` plain `rfl` closes the munmap step and
both grants.  Why `isDefEq` exceeds the default depth where `whnf` and
`decide` do not — `whnfCore` under the projection setting
`.yesWithDeltaI` — is
`Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`'s header's
measurement.  The pins file holds this file's claims to it both ways:
each plain `rfl` said to fail above fails at the default depth, and
closes once that setting is off or the depth is raised. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The heap, grown, cut and emptied -/

/-- STEP 1 — brk(0x11000): an ordinary page-crossing grow from the start
state.  Rocq: `VmMapsDisjoint.wit_step1`. -/
theorem wit_step1 :
    check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) wit_s0
      = CheckOk wit_s1 [] := by
  rfl

/-- STEP 2 — brk(0x11064): 100 bytes past the page boundary; the effect
zeroes the whole new page and the ledger records the 100 bytes.  Rocq:
`VmMapsDisjoint.wit_step2`. -/
theorem wit_step2 :
    check_syscall (brk_in 69732) (mkEffect 69732 [] [(69632, 4096)]) wit_s1
      = CheckOk wit_s2 [] := by
  rfl

/-- STEP 3 — munmap(0x10000, 4096): the first heap grant dropped, the break
where it was.  Rocq: `VmMapsDisjoint.wit_step3`. -/
theorem wit_step3 :
    check_syscall
        (SyscallInput.mkInput 215 [65536, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) wit_s2
      = CheckOk wit_s3 [] := by
  conv => lhs; whnf
  rfl

/-- STEP 4 — brk(0x107d0): a shrink into the hole step 3 opened, freeing
the second heap page; the ledger empties.  Rocq:
`VmMapsDisjoint.wit_step4`. -/
theorem wit_step4 :
    check_syscall (brk_in 67536) (SyscallEffect.mkEffectU 67536 [] [] [(69632, 4096)] [] [])
        wit_s3
      = CheckOk wit_s4 [] := by
  rfl

/-! ## A mapping where the heap was -/

/-- STEP 5 — an anonymous rw page at the hint 0x10000: the break now points
inside it.  Rocq: `VmMapsDisjoint.wit_step5`. -/
theorem wit_step5 :
    check_syscall
        (SyscallInput.mkInput 222 [65536, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 65536 [] [(65536, 4096)]) wit_s4
      = CheckOk wit_s5 [] := by
  conv => lhs; whnf
  rw [show Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg
      (SyscallInput.mkInput 222 [65536, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none)) 1))) = 4096 by decide]
  rfl

/-- …and the hint is not load-bearing: the same grant for a NULL hint is
admitted.  Rocq: `VmMapsDisjoint.wit_step5_null_hint_also_admitted`. -/
theorem wit_step5_null_hint_also_admitted :
    check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 65536 [] [(65536, 4096)]) wit_s4
      = CheckOk wit_s5 [] := by
  conv => lhs; whnf
  rw [show Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg
      (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none)) 1))) = 4096 by decide]
  rfl

/-- The NULL-hint grant at an unaligned address is refused.  Rocq:
`VmMapsDisjoint.wit_step5_null_hint_unaligned_refused`. -/
theorem wit_step5_null_hint_unaligned_refused :
    check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 65537 [] [(65537, 4096)]) wit_s4
      = CheckReject := by
  rfl

/-- …and so is the one overlapping the page step 5 placed.  Rocq:
`VmMapsDisjoint.wit_step5_null_hint_overlapping_refused`. -/
theorem wit_step5_null_hint_overlapping_refused :
    check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 65536 [] [(65536, 4096)]) wit_s5
      = CheckReject := by
  rfl

/-- mmap cannot place at the mid-page break itself: the step-5 request
with only the address changed is refused on alignment.  Rocq:
`VmMapsDisjoint.mmap_cannot_place_at_the_midpage_break`. -/
theorem mmap_cannot_place_at_the_midpage_break :
    check_syscall
        (SyscallInput.mkInput 222 [67536, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 67536 [] [(67536, 4096)]) wit_s4
      = CheckReject := by
  rfl

/-! ## The break inside a mapping it does not own -/

/-- THE OVERLAP — brk(0x10834): a 100-byte grow within one page, granted
with no address-space test, inside the step-5 mapping.  Rocq:
`VmMapsDisjoint.wit_overlap_step`. -/
theorem wit_overlap_step :
    check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s5 = CheckOk wit_overlap [] := by
  rfl

/-- STEP 6 — brk(0x107c6), from `wit_s5`: a ten-byte shrink inside one page
that splits the step-5 ledger entry at the old break.  Rocq:
`VmMapsDisjoint.wit_step6`. -/
theorem wit_step6 :
    check_syscall (brk_in 67526) (mkEffect 67526 [] []) wit_s5 = CheckOk wit_s6 [] := by
  rfl

/-- STEP 7 — brk(0x107d0): the ten bytes grown back, same page.  Rocq:
`VmMapsDisjoint.wit_step7`. -/
theorem wit_step7 :
    check_syscall (brk_in 67536) (mkEffect 67536 [] []) wit_s6 = CheckOk wit_s7 [] := by
  rfl

/-- STEP 8 — brk(0x10834): a same-page grow from the base of the step-6
remnant, leaving two entries based at 67536.  Rocq:
`VmMapsDisjoint.wit_step8`. -/
theorem wit_step8 :
    check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s7 = CheckOk wit_s8 [] := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness
