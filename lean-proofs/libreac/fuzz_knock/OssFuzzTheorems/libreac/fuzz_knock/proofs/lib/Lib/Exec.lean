-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/Exec.v
import LinuxProcessSemantics.Common.PropExec

/-! `lib/Lib/Exec.v`: the machine-step relation a function walk is stated over.

A step the model takes with no pending system call, its reflexive transitive
closure, the "eventually" `evt`, and the five lemmas about them the `lib/Prog/`
walks use. The Rocq file is 136 lines; what is left out is `SYSCALL_ECALL`,
`evt_eq`, and the eight arithmetic lemmas and six tactics of its `DA_Myrk`
module (`lib/Lib/Exec.v:13-79`). Every path in this docstring is in
theorem-labs/oss-verify-proofs-internal `ossv/recipes` `9b0ac6f0e6`, under
`projects/libreac/fuzz_knock/proofs/`. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec

/-- `lib/Lib/Exec.v:89-90`. -/
def mstep (segs : List Segment) (ms ms' : machine_state) : Prop :=
  ms.ms_svc_pending = none ∧
    LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step segs ms = .MachineOk ms'

/-- `lib/Lib/Exec.v:92-94`. -/
inductive msteps (segs : List Segment) : machine_state → machine_state → Prop where
  | refl (ms) : msteps segs ms ms
  | cons (ms ms1 ms2) : mstep segs ms ms1 → msteps segs ms1 ms2 → msteps segs ms ms2

/-- `lib/Lib/Exec.v:109-110`. -/
def evt (segs : List Segment) (Q : machine_state → Prop) (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ Q ms'


/-- `lib/Lib/Exec.v:98-99`. -/
theorem msteps_trans {segs : List Segment} {ms ms1 ms2 : machine_state}
    (h1 : msteps segs ms ms1) (h2 : msteps segs ms1 ms2) : msteps segs ms ms2 := by
  induction h1 with
  | refl _ => exact h2
  | cons ms msa msb hstep _ ih => exact .cons ms msa ms2 hstep (ih h2)

/-- `lib/Lib/Exec.v:119-124`: apply a callee's contract, then go on from its
post-state. The Rocq `call` tactic is `eapply evt_cut; [eapply SPEC |
post_call]` (`lib/Lib/Tac.v:250-253`). -/
theorem evt_cut {segs : List Segment} {P Q : machine_state → Prop} {ms}
    (h : evt segs P ms) (k : ∀ ms', P ms' → evt segs Q ms') : evt segs Q ms :=
  let ⟨ms1, h1, hp⟩ := h
  let ⟨ms2, h2, hq⟩ := k ms1 hp
  ⟨ms2, msteps_trans h1 h2, hq⟩

/-- `lib/Lib/Exec.v:112-113`. -/
theorem evt_done {segs : List Segment} {Q : machine_state → Prop} {ms} (h : Q ms) :
    evt segs Q ms := ⟨ms, .refl ms, h⟩

/-- `lib/Lib/Exec.v:115-116`. -/
theorem evt_step {segs : List Segment} {Q : machine_state → Prop} {ms ms1}
    (h : mstep segs ms ms1) (k : evt segs Q ms1) : evt segs Q ms :=
  let ⟨ms', hs, hq⟩ := k; ⟨ms', .cons ms ms1 ms' h hs, hq⟩

/-- `lib/Lib/Exec.v:126-128`. -/
theorem evt_mono {segs : List Segment} {Q R : machine_state → Prop} {ms}
    (h : evt segs Q ms) (hqr : ∀ ms', Q ms' → R ms') : evt segs R ms :=
  let ⟨ms', hs, hq⟩ := h; ⟨ms', hs, hqr ms' hq⟩

/-- A step of a `PropExec.mkst` state: `mkst` pins `ms_svc_pending` to `none`,
so the first conjunct of `mstep` holds by `rfl` (OSSV-265 gaps row T-6). -/
theorem mstep_mkst {segs : List Segment} {regs : bvmap 5 word} {pc : word}
    {mem rom : word → Option byte} {ms' : machine_state}
    (h : LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step segs (mkst regs pc mem rom)
      = .MachineOk ms') :
    mstep segs (mkst regs pc mem rom) ms' := ⟨rfl, h⟩

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
