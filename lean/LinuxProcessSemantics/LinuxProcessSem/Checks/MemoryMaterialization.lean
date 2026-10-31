-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/MemoryMaterialization.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.MemoryMaterialization — lazy backing checks

Mirrors `theories/LinuxProcessSem/Checks/MemoryMaterialization.v` in full:
the two reading helpers `page_numbers` and `materialized_numbers`, the six
`materialize_accesses` pins, the four `syscall_effect_accesses` pins, and
the accounted-checker pair that threads one model from a first write into
a second.  Not part of the trusted specification: like the Rocq file this
is QA on the definitions of `State/Backing.lean` and on the acceptor of
`Checks/ExecutableSpecs.lean`.

WHAT THE FILE PINS, in the Rocq header's words: the access-to-accounting
seam used by sparse anonymous mappings — page expansion deduplicates
repeated touches, recorded syscall ranges are included, and a cross-page
access either materializes every new page or none of them.  Instruction
reporting itself is checked separately by `Checks.RiscvAccessReporting`,
which has no Lean twin yet.

THE ROCQ DECLARATIONS THIS FILE PORTS, each under its own name, in the
Rocq file's order: the definitions `page_numbers`, `materialized_numbers`,
`accounted_write_model`, `byte_at`, `write_input_at`, `write_effect_at`,
`first_accounted_write` and `second_accounted_write`; and the `Example`s
`cross_page_expansion_is_complete`, `repeated_page_is_charged_once`,
`already_materialized_page_is_not_charged_twice`,
`cross_page_access_materializes_both_pages`,
`cross_page_access_fails_atomically_at_limit`,
`ordinary_mapping_does_not_consume_lazy_budget`,
`syscall_copyout_reports_exact_byte_range`,
`syscall_copyout_cross_page_is_atomic`,
`syscall_copyout_cross_page_fails_without_partial_charge`,
`demand_zero_grant_does_not_count_as_copyout`,
`syscall_copyins_precede_copyouts`,
`accounted_checker_threads_first_touch` and
`accounted_checker_preserves_charge_between_syscalls`.  Nothing of the
Rocq file is left out.

SPELLINGS.  Rocq's `Example` is a Lean `theorem`; `Z` is `Int` and
`nat` is `Nat`, so `8%nat` is `8` and `0x1000%Z` is `0x1000`; `list` is
`List` and `option` is `Option`, so Rocq's `Some`/`None` are `some`/`none`
and `List.map` is `.map`.  Rocq's record constructors `mkEffect`,
`mkEffectU`, `mkInput` and `mkProcInput` are `State.mkEffect`,
`SyscallEffect.mkEffectU`, `SyscallInput.mkInput` and
`ProcInput.mkProcInput`; `CheckOk` is `check_result.CheckOk`, exported
bare by `Checks/Sys/Prelude.lean`.  Rocq's `vm_compute; reflexivity` is
`decide` on the closed comparisons, which are small (eight bytes of page
expansion at most) and whose types have `DecidableEq`, and `rfl` on the
two that compare a `check_result`, which has none — there `rfl` is the
same closed computation, read by conversion instead of by a decision
procedure.  Neither tactic adds an axiom, so `Checks/Axioms.lean`'s walk
stays empty for this module; `native_decide`, which would, is not used.
The two accounted-checker pins raise `maxRecDepth` and `maxHeartbeats`
because conversion has to run the whole acceptor — the table lookup,
`check_write` and the backing accounting — inside one term. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.MemoryMaterialization

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## Reading a page list

The pins below compare page lists, and a page is a `word`.  These two
helpers read such a list as the numbers it holds, so that a failing pin
prints addresses rather than bitvector literals. -/

/-- Rocq: `MemoryMaterialization.page_numbers`. -/
def page_numbers (pages : List word) : List Int :=
  pages.map bv_unsigned

/-- Rocq: `MemoryMaterialization.materialized_numbers`. -/
def materialized_numbers (result : Option (List word)) : Option (List Int) :=
  match result with
  | some pages => some (page_numbers pages)
  | none => none

/-! ## Page expansion

`State.access_pages` is what an access of `n` bytes at `a` touches. -/

/-- An eight-byte access four bytes below a page boundary names BOTH
pages, newest first.  Rocq:
`MemoryMaterialization.cross_page_expansion_is_complete`. -/
theorem cross_page_expansion_is_complete :
    page_numbers (access_pages 0xffc 8) = [0x1000, 0] := by decide

/-! ## The charge `State.materialize_accesses` takes -/

/-- Two touches of one page are one charge.  Rocq:
`MemoryMaterialization.repeated_page_is_charged_once`. -/
theorem repeated_page_is_charged_once :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [] 0 0x2000
        [(0x10, 8), (0x20, 8)]) = some [0] := by decide

/-- A page already materialized is not charged again.  Rocq:
`MemoryMaterialization.already_materialized_page_is_not_charged_twice`. -/
theorem already_materialized_page_is_not_charged_twice :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [0] 0x1000 0x1000
        [(0x10, 8)]) = some [0] := by decide

/-- A cross-page access materializes both pages when the budget takes
both.  Rocq:
`MemoryMaterialization.cross_page_access_materializes_both_pages`. -/
theorem cross_page_access_materializes_both_pages :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [] 0 0x2000
        [(0xffc, 8)]) = some [0x1000, 0] := by decide

/-- …and when it takes only one, it materializes NEITHER: the atomicity
the file is named for.  Rocq:
`MemoryMaterialization.cross_page_access_fails_atomically_at_limit`. -/
theorem cross_page_access_fails_atomically_at_limit :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [] 0 0x1000
        [(0xffc, 8)]) = none := by decide

/-- An access outside every lazy range spends no budget, whatever the
limit is.  Rocq:
`MemoryMaterialization.ordinary_mapping_does_not_consume_lazy_budget`. -/
theorem ordinary_mapping_does_not_consume_lazy_budget :
    materialized_numbers
      (materialize_accesses [] [] 0 0 [(0xffc, 8)]) = some [] := by decide

/-! ## What a syscall effect reports

`State.syscall_effect_accesses` is the copy-in ledger followed by the
write ledger's ranges; the zero-fill ledger is not a user-memory read. -/

/-- A two-byte copy-out reports exactly two bytes at its own address.
Rocq: `MemoryMaterialization.syscall_copyout_reports_exact_byte_range`. -/
theorem syscall_copyout_reports_exact_byte_range :
    syscall_effect_accesses (mkEffect 0 [(0xfff, [0, 0])] [])
      = [(0xfff, 2)] := by decide

/-- That copy-out across a page boundary materializes both pages.  Rocq:
`MemoryMaterialization.syscall_copyout_cross_page_is_atomic`. -/
theorem syscall_copyout_cross_page_is_atomic :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [] 0 0x2000
        (syscall_effect_accesses (mkEffect 0 [(0xfff, [0, 0])] [])))
      = some [0x1000, 0] := by decide

/-- …and under a one-page budget it charges neither.  Rocq:
`MemoryMaterialization.syscall_copyout_cross_page_fails_without_partial_charge`. -/
theorem syscall_copyout_cross_page_fails_without_partial_charge :
    materialized_numbers
      (materialize_accesses [(0, 0x2000)] [] 0 0x1000
        (syscall_effect_accesses (mkEffect 0 [(0xfff, [0, 0])] [])))
      = none := by decide

/-- A demand-zero grant of a megabyte reports no read at all: the
zero-fill ledger is not a copy-out.  Rocq:
`MemoryMaterialization.demand_zero_grant_does_not_count_as_copyout`. -/
theorem demand_zero_grant_does_not_count_as_copyout :
    syscall_effect_accesses (mkEffect 0 [] [(0, 0x100000)]) = [] := rfl

/-- The order of the two ledgers: copy-ins precede copy-outs.  Rocq:
`MemoryMaterialization.syscall_copyins_precede_copyouts`. -/
theorem syscall_copyins_precede_copyouts :
    syscall_effect_accesses
      (SyscallEffect.mkEffectU 0 [(0x3000, [0, 0])] [] [] [] [(0x1000, 4)])
      = [(0x1000, 4), (0x3000, 2)] := by decide

/-! ## The accounted post-model the public checker threads

The extracted public checker must thread the accounted post-model, not
the raw syscall-body post-model.  These two writes touch distinct pages
of one lazy reservation under a one-page backing limit.  The first call
charges its page; the second sees that charge and takes the atomic
materialization-fault result. -/

/-- Rocq: `MemoryMaterialization.accounted_write_model`. -/
def accounted_write_model : Model :=
  with_vm_backing [(0, 0x2000)] []
    (init_model [] 0 0 (Z_to_bv 64 sp_window_lo) 0x1000
      (ProcInput.mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
        net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false .Sv48))

/-- A memory holding one readable zero byte, at `wanted` and nowhere
else.  Rocq: `MemoryMaterialization.byte_at`. -/
def byte_at (wanted : word) : word → Option byte :=
  fun a => if bv_eqb a wanted then some 0 else none

/-- `write(1, a, 1)`, reading the one byte `byte_at a` holds.  Rocq:
`MemoryMaterialization.write_input_at`. -/
def write_input_at (a : word) : SyscallInput :=
  SyscallInput.mkInput 64 [1, a, 1, 0, 0, 0] (byte_at a) (fun _ => none)

/-- Its effect: one byte returned, one byte copied in at `a`.  Rocq:
`MemoryMaterialization.write_effect_at`. -/
def write_effect_at (a : word) : SyscallEffect :=
  SyscallEffect.mkEffectU 1 [] [] [] [] [(a, 1)]

/-- Rocq: `MemoryMaterialization.first_accounted_write`. -/
def first_accounted_write : Option check_result :=
  check_syscall_for_run (write_input_at 0) (write_effect_at 0) accounted_write_model

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
/-- The first write's page is charged on the model the checker hands
back.  Rocq:
`MemoryMaterialization.accounted_checker_threads_first_touch`. -/
theorem accounted_checker_threads_first_touch :
    match first_accounted_write with
    | some (CheckOk m _) => page_numbers (m_vm_materialized m) = [0]
    | _ => False := rfl

/-- Rocq: `MemoryMaterialization.second_accounted_write`. -/
def second_accounted_write : Option check_result :=
  match first_accounted_write with
  | some (CheckOk m _) =>
      check_syscall_for_run (write_input_at 0x1000) (write_effect_at 0x1000) m
  | result => result

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
/-- The second write reads the first write's charge and faults: the
one-page budget is spent, so the accounting refuses the post-model and
the run adapter answers `none`.  A checker that threaded the raw
syscall-body post-model instead would accept it.  Rocq:
`MemoryMaterialization.accounted_checker_preserves_charge_between_syscalls`. -/
theorem accounted_checker_preserves_charge_between_syscalls :
    second_accounted_write = none := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.MemoryMaterialization
