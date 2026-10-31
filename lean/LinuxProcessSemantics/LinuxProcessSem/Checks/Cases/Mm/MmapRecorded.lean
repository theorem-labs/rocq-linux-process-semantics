import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle

/-! # Checks.Cases.Mm.MmapRecorded — mmap's decisions, stated over recorded answers

`Checks.Cases.Mm.Mmap` states what `mmap_spec` answers with the kernel side
written out by hand: `errno_ret EINVAL`, an address, a boundary. This file
states the same decisions with the kernel side taken from a run -- a row of
`Checks.Cases.Oracle`, rendered from `testing/syscall-check/traces/` by
`tools/gen_lean_oracle.py`.

Not part of the trusted specification. Nothing here is imported by a `Sys/`
module or by a proof of the equivalence; these are worked cases, read the
way `Checks.Cases.Prelude` says.

WHY THIS IS A SEPARATE FILE, and it is not tidiness. A row's state is folded
with `Checks.ExecutableSpecs.check_syscall_for_run`, so any file citing a row
imports the executable CHECKER and its soundness proofs. Those proofs are
written against the spec's branch structure, so a mutant that reorders
`mmap_spec`'s gates fails in `Checks/Sys/Mm/Mmap.lean` -- BEFORE any pin is
elaborated. `tools/lean_mutate.py` calls that STILLBORN and counts it
"separately and never against the gate": had these pins gone into
`Checks/Cases/Mm/Mmap.lean`, which `--spec Mm/Mmap` resolves to as its twin
and which imports nothing that reaches the checker, the whole check-swap
family of mmap mutants would have stopped being SCORED instead of being
killed, and the G12 gate would have gone quiet without going red. The twin
therefore keeps its import graph and the row pins live here.

The cost is stated where it is paid: a row pin in this file kills no mutant,
because `lean_mutate` does not build this module. What closes that gap is a
generated module for prefix-free rows -- whose state is `init_model` alone
and needs no checker -- which the twin could import; it is not done here.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.MmapRecorded

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The same decisions, stated over the recorded answers

Every pin in `Checks.Cases.Mm.Mmap` writes its kernel side out:
`errno_ret EINVAL`, an address, a ledger.  That is where a value can be
wrong in a way nothing else there notices -- the spec, the pin and the probe are all the port's own work, and
a value copied wrong from the Rocq comment agrees with a spec that read the
same comment (docs/lean-port/TESTING.md, L7).  The pins below say the same
things with no value in them at all: the number, the six registers, the
state and the answer are projections of a `Checks.Cases.Oracle` row, and a
row is one `syscall` record of the recorded corpus, rendered by
`tools/gen_lean_oracle.py` from what the pinned kernel did under
`testing/syscall-check/run-tests.sh`.  Rewrite a value here and the row
stops matching the recording; rewrite the row and the generator's
`--verify` refuses the module.

WHY THE MODEL MATTERS, and why these are not the same pins twice.  A pin
in the twin holds for EVERY model, or for a fixture it builds; a row holds
in the state the recorded run was in when it made the call -- the trace's
header through `State.init_model`, folded over the records before it.  The
two are different claims, and neither implies the other: the quantified pin
is stronger about states and says nothing about any run, and the row says
what one real run really got.  Where the corpus has a row for a call, both
stand, and `tools/check_lean_oracle_pins.py` is what keeps the hand-written
half from standing alone.

HOW A ROW AT `seq` ABOVE 0 IS PROVED.  `sys_norm`'s ground pass does not
evaluate `oracle_fold`: the fold is a run of the checker itself over the
recorded prefix, and simp gives up on it at any recursion depth (measured
to 1000000).  Kernel reduction does it in milliseconds, so those pins
resolve the fold first -- `show row_..._state = some _ from rfl`, which
puts the folded model in the goal as the literal the kernel computed -- and
then normalize.  The `rfl` is the fail-closed half too: a row whose prefix
the checker refuses has no such equation, and the pin does not elaborate
rather than closing on `spec_at`'s `False` arm.  (The word for that which
this paragraph cannot use is one `tools/check_lean_policy.py` refuses
anywhere in project source, comments included.)

The row's name is its id with `/` and `#` spelled out, because a
guillemet-quoted name under `Checks/Cases/` is one no reader of
`tools/check_lean_pins.py` resolves (PIN-7) -- the generator's own
MODULE-SHAPE rule refuses a rendering that carries one.

WHAT A ROW PIN CANNOT SAY.  A row is ONE implementation's answer on one run,
so a pin over it proves the spec ADMITS that answer, never that every
supported implementation gives it; and where the admitted set is infinite
(the fresh grant) the row can only be admitted, not `iff`-pinned, because
the placement the run happened to get is not the only one Linux may choose.

WHAT `row_…_answer` IS, and the bound it puts on which rows can be pinned
positively.  `answer_at` is `Ok eff m []` with `m` the PRE-call model: the
record carries the effect and no post-model, so the row's answer is the
recorded effect in an unchanged state.  An `iff` or an admitted application
over a row therefore closes only where the spec leaves the model as it was
-- every errno below does -- and a row whose spec changes the model (a
grant that enters the ledger) can be pinned only NEGATIVELY, as an answer
the spec refuses.  That is not a limit on what the row records; it is why
the positive pins here are all errnos and the grants appear only as
refused stagings.

KERNEL READINGS the rows are stated against, pinned to Linux v6.18.46 the
way the twin pins them: `riscv_sys_mmap` (arch/riscv/kernel/sys_riscv.c)
refuses an offset that is not page-aligned before `ksys_mmap_pgoff`
(mm/mmap.c) resolves the fd, so the misaligned-offset rows are -EINVAL
with fd 999 closed and fd -1 alike; `do_mmap` (mm/mmap.c, Linux v6.18.46)
refuses a zero length before anything is charged, so the zero-length rows
are -EINVAL in a folded state that already holds a grant; and the anonymous
fresh grant's only errno in the model is the -ENOMEM `mmap_errnos` admits --
-EACCES is `do_mmap`'s (mm/mmap.c, Linux v6.18.46) on the FILE-BACKED path,
where the inode's mode is read, and no anonymous call reaches it.
-/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle

/-- The misaligned offset, decided before the fd, with nothing written by
hand: the recorded call and the recorded answer, and the `iff` says the
recorded answer is the ONLY one -- which is what refutes a spec that read
the fd first, since fd 999 is closed in the model the run had.  The order
is `riscv_sys_mmap`'s (arch/riscv/kernel/sys_riscv.c, Linux v6.18.46):
the alignment test is in the arch entry, the fd lookup in
`ksys_mmap_pgoff` (mm/mmap.c) it calls.
trace: mmap_file_backed/002 -/
theorem recorded_misaligned_offset_is_einval (o : outcome SyscallEffect) :
    row_mmap_file_backed_002_s0_holds o ↔ o = row_mmap_file_backed_002_s0_answer := by
  sys_norm

/-- The same call with -EBADF staged in its place: the fd is not what this
call fails on, so the answer a fd-first reading would give is refused.
trace: mmap_file_backed/003 -/
theorem recorded_misaligned_offset_ebadf_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_file_backed_003_s0_holds (Ok row_mmap_file_backed_003_s0_effect m' evs) := by
  sys_refute

/-- …and with -ENOMEM staged: the environment's errno is not this call's
either.
trace: mmap_file_backed/004 -/
theorem recorded_misaligned_offset_enomem_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_file_backed_004_s0_holds (Ok row_mmap_file_backed_004_s0_effect m' evs) := by
  sys_refute

/-- The anonymous misaligned offset: `fd` is -1 and the offset still
decides, so the answer is the same errno at a call that touches no file.
trace: mmap_file_backed/005 -/
theorem recorded_anonymous_misaligned_offset_is_einval (o : outcome SyscallEffect) :
    row_mmap_file_backed_005_s0_holds o ↔ o = row_mmap_file_backed_005_s0_answer := by
  sys_norm

/-- …and a SUCCESS staged in its place -- an address where the kernel
answered an errno -- is refused: a misaligned offset is not a grant
whatever the placement.
trace: mmap_file_backed/006 -/
theorem recorded_anonymous_misaligned_success_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_file_backed_006_s0_holds (Ok row_mmap_file_backed_006_s0_effect m' evs) := by
  sys_refute

/-- The zero length, at seq 1: the record before it is a real grant, so the
model this answer was given in is the folded one and the ledger it carries
is what the earlier call left.  `do_mmap` (mm/mmap.c, Linux v6.18.46)
answers `-EINVAL` to `len == 0` before it charges anything.
trace: mmap_shapes/001 -/
theorem recorded_zero_len_anonymous_is_einval (o : outcome SyscallEffect) :
    row_mmap_shapes_001_s1_holds o ↔ o = row_mmap_shapes_001_s1_answer := by
  simp only [row_mmap_shapes_001_s1_holds, row_mmap_shapes_001_s1_answer, spec_at, answer_at,
    show row_mmap_shapes_001_s1_state = some _ from rfl]
  sys_norm

/-- The same zero-length call with a success staged: address 0 is not an
answer to it.
trace: mmap_shapes/002 -/
theorem recorded_zero_len_anonymous_success_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_shapes_002_s1_holds (Ok row_mmap_shapes_002_s1_effect m' evs) := by
  intro h
  simp only [row_mmap_shapes_002_s1_holds, spec_at, show row_mmap_shapes_002_s1_state = some _ from rfl] at h
  sys_refute at h

/-- …and with -ENOMEM staged: the length is refused before anything is
charged, so the budget's errno is not this call's.
trace: mmap_shapes/003 -/
theorem recorded_zero_len_anonymous_enomem_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_shapes_003_s1_holds (Ok row_mmap_shapes_003_s1_effect m' evs) := by
  intro h
  simp only [row_mmap_shapes_003_s1_holds, spec_at, show row_mmap_shapes_003_s1_state = some _ from rfl] at h
  sys_refute at h

/-- -ENOMEM four records into a run: three 32 TiB NORESERVE grants are in
the folded ledger and the case staged the fourth request's answer.  What
the pin proves is that the spec ADMITS -ENOMEM in that state, and it does
so through the `errno_from mmap_errnos` escape the fresh-grant arm carries
in EVERY model -- the folded ledger does no work in closing it, and the
same statement over a row with an empty prefix (`recorded_rw_grant_enomem_admitted`
below) closes the same way.  Admitted and not `iff`-pinned, because a
request this size may still be placed by a kernel whose layout leaves a
gap.  The claim that DOES depend on the ledger is the next pin.
trace: mmap_budget/009 -/
theorem recorded_over_budget_enomem_admitted :
    row_mmap_budget_009_s3_holds row_mmap_budget_009_s3_answer := by
  simp only [row_mmap_budget_009_s3_holds, row_mmap_budget_009_s3_answer, spec_at, answer_at,
    show row_mmap_budget_009_s3_state = some _ from rfl]
  sys_norm

/-- The fourth 32 TiB request answered with a GRANT at 2^44 -- an address
the case staged, where no kernel found a gap: `[2^44, 3·2^44)` overlaps
the third recorded grant, whose range the folded ledger holds, and the
staged effect zeroes nothing where a grant zeroes its range.  Refused in
that state, which is the claim over this trace that the prefix carries:
the ledger three real grants left is what makes the placement impossible.
trace: mmap_budget/010 -/
theorem recorded_over_budget_fourth_gap_refused (m' : Model) (evs : List event) :
    ¬ row_mmap_budget_010_s3_holds (Ok row_mmap_budget_010_s3_effect m' evs) := by
  intro h
  simp only [row_mmap_budget_010_s3_holds, spec_at, show row_mmap_budget_010_s3_state = some _ from rfl] at h
  sys_refute at h

/-- The fresh grant's -ENOMEM, admitted with nothing changed: the errno the
environment may answer with, staged by the case because no probe can make
the guest kernel run out.
trace: errno_mmap/001 -/
theorem recorded_rw_grant_enomem_admitted :
    row_errno_mmap_001_s0_holds row_errno_mmap_001_s0_answer := by
  sys_norm

/-- -EBADF is not the fresh grant's: no fd is involved, and the answer is
refused in every model and with any events.
trace: errno_mmap/002 -/
theorem recorded_rw_grant_ebadf_refused (m' : Model) (evs : List event) :
    ¬ row_errno_mmap_002_s0_holds (Ok row_errno_mmap_002_s0_effect m' evs) := by
  sys_refute

/-- …and neither is -EACCES: `do_mmap` (mm/mmap.c, Linux v6.18.46) answers
it on the file-backed path, off the inode's mode and the file's flags, and
this anonymous call never reaches that path.
trace: errno_mmap/003 -/
theorem recorded_rw_grant_eacces_refused (m' : Model) (evs : List event) :
    ¬ row_errno_mmap_003_s0_holds (Ok row_errno_mmap_003_s0_effect m' evs) := by
  sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.MmapRecorded
