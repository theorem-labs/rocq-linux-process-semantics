import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

/-! # Checks.Cases.Checks.ExecutableSpecs — the acceptor's dispatch, accounting and boundary, made to fire

Pins over `Checks.ExecutableSpecs`, the twin of
`theories/LinuxProcessSem/Checks/ExecutableSpecs.v`.  The Rocq tree has no
check file for it — its theorems are stated in the file itself, and the
harness folds the acceptor over every syscall a real kernel makes — so
this file mirrors nothing: these are the Lean tree's tests for what the
twin ports, placed where every pin in this tree lives so that
`tools/check_lean_pins.py` and `tools/check_lean_pin_evidence.py` read
them.  Not part of the trusted specification: this file is QA on the
definitions, written to be READ.

THREE DECISIONS are under test.  The twin's header says why the first and
the third are exercised on fixture tables rather than on `checked_table`
alone — the real table holds only the arms registered so far — and why
both functions therefore take the table as a parameter; the positive over
the real table at 93 is in `Checks/Cases/Checks/Sys/Kernel/Exit.lean`,
beside the arm.

- THE DISPATCH.  `check_syscall_in` answers to the syscall NUMBER, through
  the checked arm it finds there, and declines where it finds none.  It is
  driven through the one-arm table `[fixture_arm_exit]` of
  `Checks/Cases/Checks/Sys/Dispatch.lean`: the arm's acceptor accepts the
  one effect `exit` produces and refuses one it cannot; and at 94 — a
  number the SPEC answers, through the same `exit_spec`, and the table does
  not carry — the checker declines, as it does at a number whose low 32
  bits spell 93 and whose high bits do not.  The decline at 94 is what the
  twin's premise exists for, and the section on the premise shows it
  holding at a checked number, holding at a number neither table carries,
  and FAILING at 93 over the empty table and at 94 over the one-arm table.
- THE ACCOUNTING.  `syscall_post_model` reads the terminal flag first and
  the budget second: a halted or killed post-model comes back untouched
  whatever the effect names — within budget or over it, which is where the
  two orders differ — a running one is charged for the pages it touched,
  read or written, and one that would overrun the budget is refused with
  `none`.
- THE BOUNDARY.  `check_syscall_for_run_in` routes the checker's three
  verdicts: an accepted effect through the accounting, a rejection and a
  decline straight through, and the accounting's refusal to the OUTER
  `none`, which is neither of the other two.  The exit fixture reaches the
  first three.  The fourth needs an accepted effect with a running
  post-model, which no ported arm produces: it is reached with the
  checker's answer as a hypothesis and everything else concrete, and again
  concretely through a fixture arm whose spec copies in.  The two INSTANCES
  over `checked_table` itself are named once, at a number no table will
  ever carry.

The kernel claims here are `exit`'s, read off `kernel/exit.c` by
`Checks/Cases/Kernel/Exit.lean`; the pins reuse those readings rather than
restate them.  The budget is the run's own — the `VmMaps.vm_limit` field,
the equivalence's allocation parameter — and the pins on it say `model:`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.ExecutableSpecs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

/-! ## The calls -/

/-- `exit(256)` at the ecall: a7 = 93, a0 = 256 and the rest zero, so the
observed code is `256 & 0xff` = 0. -/
def exit_256_input : SyscallInput :=
  SyscallInput.mkInput 93 [256, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `exit_group(0x12345)` at the ecall: the call `Checks/Cases/Kernel/Exit.lean`
reads the code 0x45 off, under the number the one-arm table does not
carry. -/
def exit_group_input : SyscallInput :=
  SyscallInput.mkInput 94 [0x12345, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `ecall` with a7 = 2^32 + 93: `exit`'s number in the low 32 bits of a7
and a 1 above them, with `exit_256_input`'s arguments. -/
def wrapped_exit_input : SyscallInput :=
  SyscallInput.mkInput 4294967389 [256, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `ecall` with a7 = 0: the number the fixture arms of
`Checks/Cases/Checks/Sys/Dispatch.lean` that stand in for no syscall sit
under, which no table in this file carries otherwise. -/
def zero_input : SyscallInput :=
  SyscallInput.mkInput 0 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `ecall` with a7 = 1000: off the kernel's table, as
`premise_holds_off_the_surface` says. -/
def off_surface_input : SyscallInput :=
  SyscallInput.mkInput 1000 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The table these pins dispatch over: `exit` (93) alone, the fixture arm
of `Checks/Cases/Checks/Sys/Dispatch.lean`. -/
def one_arm : List CheckedArm := [fixture_arm_exit]

attribute [local sys_simp low] exit_256_input.eq_1

section Dispatch

/-! ## The dispatch: by number, through the arm, fail closed without one -/

/-- Positive: at 93 the dispatch reaches the exit arm, and the arm accepts
the one effect `exit` produces — return 0 with every ledger empty — with
the halt carrying the low byte of a0.  The second conjunct is what makes
the acceptance sound at this call and not merely computed: the spec admits
that outcome (and only it, `Kernel.Exit.exit_halts_with_low_byte`), because
`do_exit((error_code & 0xff) << 8)` ends the process with that byte and
returns nothing.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem dispatch_accepts_what_exit_admits (m : Model) :
    check_syscall_in one_arm exit_256_input (mkEffect 0 [] []) m = CheckOk (with_halted 0 m) []
    ∧ syscall_spec exit_256_input m (Ok (mkEffect 0 [] []) (with_halted 0 m) []) := by
  refine ⟨rfl, ?_⟩
  sys_norm

/-- Negative: `do_exit` does not return to the caller, so no return value
of `exit` is ever observed.  The 0 the arm accepts is the harness's
placeholder for a call that never returns — `testing/syscall-check/main.ml`
feeds `eff_ret = 0` for 93 and 94, and `Checks/Sys/Kernel/Exit.v`'s
`check_exit` demands the same 0 — and 1 is what `--mutate exit:ret=1`
injects.  The arm refuses it with `CheckReject`, a conformance failure,
not a decline.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem dispatch_refuses_a_return_from_exit (m : Model) :
    check_syscall_in one_arm exit_256_input (mkEffect 1 [] []) m = CheckReject := rfl

/-- The dispatch reads the NUMBER.  At 94 the one-arm table has no arm, so
the checker declines — while the spec, which carries `exit_group` with the
same `exit_spec`, ANSWERS, since `do_group_exit` ends the process on every
input.  This is the number the twin's premise fails at over this table: a
harness checking `exit_group` against it would report `CheckUnmodeled`, the
fail-closed answer and not a verdict about Linux.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem dispatch_declines_exit_group_without_its_arm (m : Model) :
    check_syscall_in one_arm exit_group_input (mkEffect 0 [] []) m = CheckUnmodeled
    ∧ ¬ syscall_spec exit_group_input m Unmodeled := by
  refine ⟨rfl, fun h => ?_⟩
  have h' := (Kernel.Exit.sysno_94_is_exit_group m Unmodeled).1 h
  simp only [reduceCtorEq] at h'

/-- The dispatch reads the WHOLE number.  Linux takes a7 as a `long` and
dispatches only under `syscall >= 0 && syscall < NR_syscalls`, leaving the
`-ENOSYS` it preloaded into a0 otherwise (`do_trap_ecall_u`,
arch/riscv/kernel/traps.c:327-369, Linux v6.18.46), so a7 = 2^32 + 93 is
no call of `exit` to it.  The key here is `bv_unsigned` of the full word,
and a table holding 93 has no arm at 4294967389: the checker declines,
which is admissible under every supported implementation.  What this
refuses is a key read off the low 32 bits of a7, which would dispatch this
number to `exit` and answer where Linux answers `-ENOSYS`.
kernel: arch/riscv/kernel/traps.c:do_trap_ecall_u@v6.18.46 -/
theorem dispatch_declines_a_number_wrapping_to_exit (m : Model) :
    check_syscall_in one_arm wrapped_exit_input (mkEffect 0 [] []) m = CheckUnmodeled := rfl

end Dispatch

section Premise

/-! ## The premise: where the two lookups agree

`lookups_agree_in t n` says the dispatcher's arm at `n` is the checked arm's
own over the table `t`.  Rocq has it at every number from one equation; the
twin's header says why the Lean tree has it per number.  The three pins
here are its three kinds of number: a checked one, one outside both tables,
and one the spec carries and the table does not. -/

/-- Positive: at a checked number the two lookups agree — `Sys/SyscallTable.lean`
carries 93 with the fixture arm's own spec.
model: the two lookups over `Sys/SyscallTable.lean` and the one-arm table;
no kernel behaviour is claimed -/
theorem premise_holds_at_a_checked_number : lookups_agree_in one_arm 93 := rfl

/-- Positive: at a number neither table carries the two lookups agree on
`none`, over the real `checked_table` and whatever it will hold.  1000 is
above `__NR_syscalls` — 470 at include/uapi/asm-generic/unistd.h:862,
Linux v6.18.46, the generic header's count, and riscv64's own, which it
builds from scripts/syscall.tbl through scripts/syscallhdr.sh as one above
the highest entry, 469 — so no supported kernel has a syscall there and no
arm will ever answer to it in either table: the pin cannot go stale.
model: `lookups_agree_at_of_absent` at a number off the kernel's table; no
kernel behaviour is claimed -/
theorem premise_holds_off_the_surface : lookups_agree_at 1000 :=
  lookups_agree_at_of_absent 1000 rfl

/-- Negative: at a number the spec table carries and the checked table does
not, the premise FAILS — the empty table, which is what `checked_table`
was before K6a registered the exit arm, against `exit` at 93.  This is the case the
premise exists for: there the checker declines a call the spec answers, so
`check_syscall_sound_unmodeled` without the premise would be false.
model: the two lookups over `Sys/SyscallTable.lean` and the empty table; that
the spec answers at 93 is `dispatch_accepts_what_exit_admits`'s reading -/
theorem premise_fails_at_exit_over_the_empty_table : ¬ lookups_agree_in [] 93 := by
  intro h
  have h' : (some (SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i)) : Option SpecArm)
      = none := h
  simp only [reduceCtorEq] at h'

/-- …and over the one-arm table the premise fails at 94, the number
`dispatch_declines_exit_group_without_its_arm` declines at: a table WITH
an arm, at a number it lacks and the spec carries.  The proof reads the
spec table's answer at 94 as `some` without spelling the arm, so a
respelling of the registry entry does not reach it.
model: the two lookups over `Sys/SyscallTable.lean` and the one-arm table;
that the spec answers at 94 is `Kernel.Exit.sysno_94_is_exit_group`'s
reading -/
theorem premise_fails_at_exit_group_over_the_one_arm_table : ¬ lookups_agree_in one_arm 94 := by
  intro h
  have hs : (lookup_arm spec_table 94).isSome = true := rfl
  rw [show lookup_arm spec_table 94 = none from h] at hs
  exact absurd hs (by decide)

end Premise

section Accounting

/-! ## The accounting: the terminal flag first, the budget second

The fixtures are a lazily backed two-page grant under a ONE-page budget —
what a `MAP_NORESERVE` mapping leaves in the ledger
(`Checks/Cases/Mm/Madvise.lean`'s `lazy_grant` is the spec-side pin), with
the budget one page short of it — and four effects: one that read a byte
of the first page, one that read a byte of each, and the same two touches
as writes. -/

/-- The two-page grant at 65536, lazily backed, under a 4096-byte budget. -/
def tight_grant : Model :=
  vm_add_lazy 65536 8192
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))

/-- The grant with its first page charged. -/
def tight_grant_touched : Model :=
  with_vm_backing (m_vm_lazy tight_grant) [65536] tight_grant

/-- An effect whose arm read one byte of the first page: the copy-in ledger
`syscall_effect_accesses` charges. -/
def touch_one : SyscallEffect := with_copyins [(65536, 1)] (mkEffect 0 [] [])

/-- An effect whose arm read one byte of each page. -/
def touch_two : SyscallEffect := with_copyins [(65536, 1), (69632, 1)] (mkEffect 0 [] [])

/-- An effect whose arm WROTE one byte of the first page: the other ledger
`syscall_effect_accesses` charges, `write_accesses eff.eff_writes`. -/
def write_one : SyscallEffect := mkEffect 0 [(65536, [0])] []

/-- An effect whose arm wrote one byte of each page. -/
def write_two : SyscallEffect := mkEffect 0 [(65536, [0]), (69632, [0])] []

/-- The grant costs nothing until it is touched.
model: `State.vm_backing_used` on the fixture; no kernel behaviour is
claimed -/
theorem lazy_grant_costs_nothing_untouched : vm_backing_used tight_grant = 0 := by
  decide

/-- Positive: the first touch charges that page and no other — the running
arm of `syscall_post_model` IS the run's materializer, and the model it
hands back is the charged one.
model: the run's first-touch accounting (`Run.sstep_syscall`'s
materialization premise) under the fixture's budget, which is the
equivalence's parameter and not a kernel limit -/
theorem post_model_charges_the_first_touch :
    syscall_post_model tight_grant touch_one = some tight_grant_touched
    ∧ vm_backing_used tight_grant_touched = 4096 := by
  refine ⟨rfl, by decide⟩

/-- Negative: two pages under a one-page budget are refused, and the refusal
is `none` — no partially charged model comes back for the run to continue
on.
model: the run's first-touch accounting under the fixture's budget; the
budget is the equivalence's parameter and not a kernel limit -/
theorem post_model_refuses_over_budget :
    syscall_post_model tight_grant touch_two = none := rfl

/-- The accounting charges a WRITE as it charges a copy-in:
`State.syscall_effect_accesses` is the two ledgers appended, and an effect
that wrote one byte of the first page charges that page — the same charged
model `touch_one` produces.  What this refuses is an accounting that read
the copy-in ledger alone, which every `touch_*` pin in this file would
pass.
model: the run's first-touch accounting over the write ledger under the
fixture's budget, which is the equivalence's parameter and not a kernel
limit -/
theorem post_model_charges_a_first_write :
    syscall_post_model tight_grant write_one = some tight_grant_touched := rfl

/-- …and refuses two written pages under the one-page budget.
model: the run's first-touch accounting over the write ledger under the
fixture's budget; the budget is the equivalence's parameter and not a
kernel limit -/
theorem post_model_refuses_over_budget_writes :
    syscall_post_model tight_grant write_two = none := rfl

/-- Order: the terminal flag is read before the budget.  The same effect
that faults the running model is not charged to a halted one — an exit's
post-model comes back untouched, however many pages the effect names —
because a process that has called `do_exit` never returns to user space to
touch them (kernel/exit.c, Linux v6.18.46).
model: the halted arm reads the model's own terminal flag; the kernel line
says why the effect is moot, not what the model charges -/
theorem post_model_leaves_a_halted_model_alone :
    syscall_post_model (with_halted 0 tight_grant) touch_two
      = some (with_halted 0 tight_grant) := rfl

/-- …and a killed one, which is halted too (`State.killed_is_halted`): the
accounting does not tell the two ends apart, as `Run.sstep_killed` discards
the effect exactly as `Run.sstep_exit` does.
model: the halted arm reads the model's own terminal flag, which
`State.with_killed` writes; no kernel behaviour is claimed -/
theorem post_model_leaves_a_killed_model_alone :
    syscall_post_model (with_killed 9 tight_grant) touch_two
      = some (with_killed 9 tight_grant) := rfl

/-- Order, at the point where the two orders DIFFER.  `touch_two` is over
budget, and on an over-budget effect "flag first" and "budget first, the
untouched model on refusal" agree; `touch_one` the budget ADMITS, so a
post-model that read the budget first would hand back the charged model
here.  It hands back the halted one, uncharged: the terminal flag is read
before the accounting runs.
model: the halted arm reads the model's own terminal flag before the
budget; the budget is the equivalence's parameter and not a kernel limit -/
theorem post_model_leaves_a_halted_model_uncharged_within_budget :
    syscall_post_model (with_halted 0 tight_grant) touch_one
      = some (with_halted 0 tight_grant) := rfl

/-- …and the killed one likewise, within budget.
model: the halted arm reads the model's own terminal flag, which
`State.with_killed` writes, before the budget; no kernel behaviour is
claimed -/
theorem post_model_leaves_a_killed_model_uncharged_within_budget :
    syscall_post_model (with_killed 9 tight_grant) touch_one
      = some (with_killed 9 tight_grant) := rfl

end Accounting

section Boundary

/-! ## The boundary: three verdicts in, and the outer `none` -/

/-- Positive: an accepted exit through the boundary — the checker accepts,
the post-model is halted, the accounting hands it back untouched, and the
verdict is `some (CheckOk …)` with the arm's events.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem boundary_accounts_an_accepted_exit :
    check_syscall_for_run_in one_arm exit_256_input (mkEffect 0 [] []) tight_grant
      = some (CheckOk (with_halted 0 tight_grant) []) := rfl

/-- A rejection passes through as `some CheckReject`, with no accounting
done: a return value from `exit`, which no kernel produces — `do_exit`
never returns, and the arm's 0 is the harness's placeholder — refused at
the arm and handed out unchanged.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem boundary_passes_a_rejection_through (m : Model) :
    check_syscall_for_run_in one_arm exit_256_input (mkEffect 1 [] []) m = some CheckReject := rfl

/-- A decline passes through as `some CheckUnmodeled`: `exit_group` over the
one-arm table, which `dispatch_declines_exit_group_without_its_arm` reads.
model: the boundary's routing of the checker's decline over the one-arm
table; no kernel behaviour is claimed -/
theorem boundary_passes_a_decline_through (m : Model) :
    check_syscall_for_run_in one_arm exit_group_input (mkEffect 0 [] []) m
      = some CheckUnmodeled := rfl

/-- The accounting's refusal is the OUTER `none`.  Reached with the checker's
answer as a hypothesis, because no ported arm accepts an effect that
touches a lazily backed page: whatever table and input made the checker
accept `touch_two` with `tight_grant` as the post-model, the boundary
answers `none` — not `some CheckReject`, not `some CheckUnmodeled`.
model: the boundary's routing of `syscall_post_model`'s `none`, on
`post_model_refuses_over_budget`'s data -/
theorem boundary_fault_is_the_outer_none (t : List CheckedArm) (i : SyscallInput) (m : Model)
    (evs : List event) :
    check_syscall_in t i touch_two m = CheckOk tight_grant evs →
    check_syscall_for_run_in t i touch_two m = none := by
  intro h
  simp only [check_syscall_for_run_in, h, post_model_refuses_over_budget]

/-- …and an accepted effect the budget admits comes back CHARGED: the
post-model the boundary hands the run is the materialized one, not the
arm's.
model: the boundary's routing of `syscall_post_model`'s `some`, on
`post_model_charges_the_first_touch`'s data -/
theorem boundary_hands_back_the_charged_model (t : List CheckedArm) (i : SyscallInput)
    (m : Model) (evs : List event) :
    check_syscall_in t i touch_one m = CheckOk tight_grant evs →
    check_syscall_for_run_in t i touch_one m = some (CheckOk tight_grant_touched evs) := by
  intro h
  simp only [check_syscall_for_run_in, h, post_model_charges_the_first_touch.1]

/-- An arm whose spec READS.  `exit` copies nothing in, so nothing stated
over `exit` reaches the boundary's running arm with an effect the
accounting charges, except under a hypothesis as the two pins above do.
This fixture's spec admits one outcome — return 0, the ranges `reads`
copied in, the model unchanged, no event — and its checker is
`check_ret_only_copyins` demanding those ranges.  It sits under number 0
as `fixture_arm_emitting` does, a lambda standing in for no syscall; its
only job is to carry a copy-in to the boundary concretely. -/
def fixture_arm_reading (reads : List (word × Nat)) : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 0
    (fun _ m o => o = Ok (with_copyins reads (mkEffect 0 [] [])) m [])
  ca_check := fun _ eff m => check_ret_only_copyins reads eff 0 m []
  ca_witness := fun _ m => Ok (with_copyins reads (mkEffect 0 [] [])) m []
  ca_sound_ok := by
    intro i eff m m' evs h
    rw [check_ret_only_copyins_ok_iff] at h
    obtain ⟨heff, hm', hevs⟩ := h
    subst heff
    subst hm'
    subst hevs
    rfl
  ca_sound_unmodeled := by
    intro i eff m h
    exact absurd h (check_ret_only_copyins_no_unmodeled reads eff 0 m [])
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' : Ok eff m' evs = Ok (with_copyins reads (mkEffect 0 [] [])) m [] := h
    injection h' with heff hm' hevs
    subst heff
    subst hm'
    subst hevs
    exact check_ret_only_copyins_refl _ _ _ _
  ca_complete_unmodeled := by
    intro i m eff h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (with_copyins reads (mkEffect 0 [] [])) m [] := h
    simp only [reduceCtorEq] at h'
  ca_receptive := by
    intro i m
    rfl

/-- Positive, concrete: the charged path of the boundary at a witness.  The
reading arm accepts `touch_one` on the running two-page grant, the
accounting charges the first page, and the post-model the boundary hands
the run is the charged one — `boundary_hands_back_the_charged_model`'s
hypothesis, inhabited.
model: the boundary's routing of `syscall_post_model`'s `some` on the
reading fixture; the budget is the equivalence's parameter and not a
kernel limit -/
theorem boundary_charges_an_accepted_read :
    check_syscall_in [fixture_arm_reading [(65536, 1)]] zero_input touch_one tight_grant
        = CheckOk tight_grant []
    ∧ check_syscall_for_run_in [fixture_arm_reading [(65536, 1)]] zero_input touch_one
        tight_grant
        = some (CheckOk tight_grant_touched []) := ⟨rfl, rfl⟩

/-- Negative, concrete: the checker ACCEPTS `touch_two` and the boundary
still answers the outer `none` — `boundary_fault_is_the_outer_none`'s
hypothesis, inhabited, and the `CheckOk`-with-`none` branch of
`check_syscall_for_run_reject_iff` at a witness.
model: the boundary's routing of `syscall_post_model`'s `none` on the
reading fixture; the budget is the equivalence's parameter and not a
kernel limit -/
theorem boundary_fault_is_the_outer_none_at_a_witness :
    check_syscall_in [fixture_arm_reading [(65536, 1), (69632, 1)]] zero_input touch_two
        tight_grant
        = CheckOk tight_grant []
    ∧ check_syscall_for_run_in [fixture_arm_reading [(65536, 1), (69632, 1)]] zero_input
        touch_two tight_grant
        = none := ⟨rfl, rfl⟩

/-- The arm's EVENTS survive the running arm of the accounting.  `exit`
emits none and the reading fixture emits none, so this is the one concrete
pin on the events position of the boundary's `CheckOk`:
`fixture_arm_emitting` supplies the event, the model is running and
touches nothing, and the event comes back.
model: the boundary's routing of `syscall_post_model`'s `some` on a running
model with no lazy touch; no kernel behaviour is claimed -/
theorem boundary_keeps_the_arms_events (ev : event) :
    check_syscall_for_run_in [fixture_arm_emitting ev] zero_input (mkEffect 0 [] [])
        tight_grant
      = some (CheckOk tight_grant [ev]) := rfl

/-- The INSTANCES a harness calls, over `checked_table` itself.  Every other
pin here drives the `_in` handles over a fixture table, because over the
real table only the declining path is reachable while it is empty; this is
that path, at a number neither table will ever carry, so the pin holds now
and when the table is full.  It is inert against a mutant of the
instances' table choice — 1000 declines over any table — and is here to
name the two instances at all; the positive at 93 over the real table is
`check_syscall_accepts_exit_over_the_real_table` in
`Checks/Cases/Checks/Sys/Kernel/Exit.lean`, beside the arm.
model: `check_syscall` and `check_syscall_for_run` at `checked_table`, at a
number off the kernel's table; no kernel behaviour is claimed -/
theorem instances_decline_off_the_surface (eff : SyscallEffect) (m : Model) :
    check_syscall off_surface_input eff m = CheckUnmodeled
    ∧ check_syscall_for_run off_surface_input eff m = some CheckUnmodeled := ⟨rfl, rfl⟩

end Boundary

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.ExecutableSpecs
