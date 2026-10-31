import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantCoverage
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! # LinuxProcessSem.Checks.Invariants — the cross-arm invariants, over the dispatcher

What the cross-arm invariant registry gives the dispatcher.  The registry
itself — the `Invariant` structure, its entries and the tactics — is
`Checks/InvariantRegistry.lean`; `registry_preserves`, every registered
invariant preserved by every registered arm, is the generated module
`Checks.InvariantCoverage` that `tools/gen_lean_checked.py` renders from
the arm files under `Checks/Arms/`; and this file states, over that
theorem, the facts no arm's registration touches: the lookup, the
dispatcher and the two corollaries Rocq draws.  Nothing here names a
syscall or an invariant beyond `vm_wf`, and nothing grows when either
list does.

THIS FILE MIRRORS NOTHING, for the reason `Checks/InvariantRegistry.lean`
gives, and so carries no `rocq-baseline` header.
Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- …and therefore so does the arm the dispatcher finds, for every
registered invariant.  No syscall and no invariant is named here, and
nothing in this proof grows when either list does.  This is
`Checks.VmMapsDisjoint.Arms`'s `lookup_ca_preserves_vm_wf` over the registry. -/
theorem lookup_ca_preserves (inv : Invariant) (hinv : inv ∈ invariant_registry)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event) (c : CheckedArm)
    (hlk : lookup_ca checked_table (bv_unsigned i.in_sysno) = some c)
    (h : c.ca_check i eff m = CheckOk m' evs) (hold : inv.holds m) : inv.holds m' :=
  registry_preserves inv hinv c (lookup_ca_In checked_table _ c hlk) i eff m m' evs h hold

/-- …AND SO DOES `check_syscall` ITSELF, which is what ticket I3 names.
`Checks.VmMapsDisjoint.Arms` states its dispatcher-level theorem over the lookup because
the `Checks/ExecutableSpecs.v` twin had not landed when it was written;
that twin has landed (K3), its `check_syscall` is
`check_syscall_in checked_table`, a `match` on the very `lookup_ca` the
theorem above is stated over, and it imports only the checked table
and `Specs`, so this file can import it with no cycle.  The `none` arm
answers `CheckUnmodeled`, which is not `CheckOk`, so the accepted step
came through an arm the table holds.  This is Rocq's
`check_syscall_preserves_vm_wf` (`Checks/VmMapsDisjoint.v`) over the
registry; `Checks.VmMapsDisjoint.Arms`'s own `vm_wf` instance of it is the special case
at `inv_vm_wf` and is not restated there. -/
theorem check_syscall_preserves (inv : Invariant) (hinv : inv ∈ invariant_registry)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.ExecutableSpecs.check_syscall i eff m = CheckOk m' evs)
    (hold : inv.holds m) : inv.holds m' := by
  unfold Checks.ExecutableSpecs.check_syscall Checks.ExecutableSpecs.check_syscall_in at h
  split at h
  · exact lookup_ca_preserves inv hinv i eff m m' evs _ ‹_› h hold
  · cases h

/-! ## The two corollaries Rocq states over the dispatcher

Both rest on `check_syscall` -- the first is stated over the relational
`Specs.syscall_spec` and reaches the checker through `check_syscall_ok_iff`,
the second is stated over `check_syscall` itself -- so both had to wait
for `Checks/ExecutableSpecs.lean`, and both go through
`check_syscall_preserves` above.  The first is generic over the
registry, which is what puts it here; the second is `vm_wf`'s alone --
`base_entry_unique` under the `inv_vm_wf` instance -- and is here
because its one ingredient beyond that lemma is the instance, and
`Checks.VmMapsDisjoint.Arms` is a build product holding only what the
arms determine.  They are twins of Rocq lemmas and so stand beside the
definitions rather than in `Checks/Cases`; what
`Checks/Cases/Invariants.lean` holds is what their STATEMENTS do not
say: an application of each at a step the tree's real table accepts,
the refutation of the second with its alignment premise dropped, and the
number at which the first's added premise is false. -/

/-- The memory ledger's entry is registered.  Stated once, so that the
`vm_wf` instance of a generic theorem does not reprove it at each use. -/
theorem inv_vm_wf_registered : inv_vm_wf ∈ invariant_registry := by
  unfold invariant_registry
  exact List.mem_cons_self

/-- …AND SO DOES THE RELATIONAL SPEC, which is the form a downstream
proof steps through: the equivalence unfolds a source syscall step to
`Specs.syscall_spec`, never to the checker.  Rocq:
`VmMapsDisjoint.syscall_spec_preserves_vm_wf`, here at every registered
invariant rather than at `vm_wf` alone.

THE PREMISE ROCQ DOES NOT CARRY.  This statement is weaker than the
twin by exactly that premise, and the partial port forces it: the
direction used here is COMPLETENESS -- a RELATIONAL step has to be
exhibited as a CHECKED one before any fact about the checked arms
reaches it -- and at a number `spec_table` carries and `checked_table`
does not (the fourth kind in `Checks/ExecutableSpecs.lean`'s header) the
checker declines a call the spec answers, so no fact about the arms in
the table can speak for that step.  A premise-free statement would need
every arm of `spec_table` to preserve every registered invariant, which
the tree proves for the checked arms alone.  So this takes the premise
`check_syscall_complete_ok` takes; the `lookups_agree_at_of_*` lemmas
beside it say where it comes for free, and once the two tables
coincide it holds everywhere and this is Rocq's statement exactly.
`Checks/Cases/Invariants.lean` discharges it at the `mmap` number, and
pins that it really is false at a number only `spec_table` carries, so
neither half of that is prose. -/
theorem syscall_spec_preserves (inv : Invariant) (hinv : inv ∈ invariant_registry)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hagree : Checks.ExecutableSpecs.lookups_agree_at (bv_unsigned i.in_sysno))
    (h : Specs.syscall_spec i m (Monad.Ok eff m' evs)) (hold : inv.holds m) : inv.holds m' :=
  check_syscall_preserves inv hinv i eff m m' evs
    ((Checks.ExecutableSpecs.check_syscall_ok_iff i eff m m' evs hagree).mpr h) hold

/-- AT A PAGE-ALIGNED BASE, THE LEDGER A SYSCALL HANDS BACK NAMES EXACTLY
ONE ENTRY.  `map_has` tests the PAIR and `map_remove` removes on the BASE
alone, so `munmap`'s argument needs the two to name the same mapping, and
they do exactly while the ledger is well formed -- which is what the
registry's `vm_wf` entry carries across the step.  Rocq:
`VmMapsDisjoint.base_unique_after_syscall`, and this is its proof:
`base_entry_unique` under the preservation theorem, with `vm_wf` a
HYPOTHESIS here as it is there, not a fact about reachable states.
THE ALIGNMENT PREMISE IS LOAD-BEARING, and the tree's own witness says
so: `wit_s8`'s ledger is well formed and holds two entries based at
67536, which is not page aligned (`wit_duplicate_base`,
`wit_duplicate_base_is_unaligned`, and the pin in
`Checks/Cases/Invariants.lean` that the conclusion is false there).  So
is the well-formedness premise: the same file refutes the statement
with `vm_wf` dropped on a ledger holding an aligned base twice. -/
theorem base_unique_after_syscall (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (a n : word)
    (h : Checks.ExecutableSpecs.check_syscall i eff m = CheckOk m' evs)
    (hwf : vm_wf (m_vmmaps m)) (ha : bv_unsigned a % page_size = 0)
    (hhas : map_has (m_vmmaps m').vm_maps a n = true) :
    ((m_vmmaps m').vm_maps).filter (fun q => bv_eqb q.1 a) = [(a, n)] :=
  base_entry_unique _ a n
    (check_syscall_preserves inv_vm_wf inv_vm_wf_registered i eff m m' evs h hwf) ha hhas

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
