-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/AbortWitness.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: abrt_image -- `Checks/Cases/EquivalenceDefinition/Equivalence.lean` line 2787 declares the same image under the same name, from the same six-instruction segment; this file imports that one and declares no second copy
unported: abrt_dies_by_signal -- the same theorem over the same image and input is at `Checks/Cases/EquivalenceDefinition/Equivalence.lean` line 2886; this file imports it
unported: abrt_dies_by_signal_scfg -- `Checks/Cases/EquivalenceDefinition/Equivalence.lean` line 2821 states it over EVERY `SpuriousCfg`, which carries the Rocq statement at `may_fail_cfg`; this file imports it
unported: abrt_refutes_error_free_abort -- at `Checks/Cases/EquivalenceDefinition/Equivalence.lean` line 2894, with the same two valid entries and the same input
unported: abrt_refutes_error_free_scfg_abort -- at `Checks/Cases/EquivalenceDefinition/Equivalence.lean` line 2902, over every configuration

# LinuxProcessSem.Checks.AbortWitness — an image that really aborts

Not part of the trusted specification: QA on the definitions, in the sense
`Checks/Examples.lean` describes.

## The gap

`Equivalence.error_free_unkilled` is `Equivalence.error_free` plus "and it is not
killed", and the abort-declared statement family is stated with it.  Two things
suggest the extra conjunct is doing work, and both stop short of a run:
`Equivalence.error_free_unkilled_bites` exhibits a HAND-WRITTEN `behavior` whose
trace set holds a `State.KillEv`, and
`Equivalence.strong_universal_error_free_T_abort_refuted_by_abort` takes
`Equivalence.dies_by_signal (Run.run …)` as a HYPOTHESIS.  A conditional
refutation whose condition is never met is indistinguishable, from inside the
development, from one whose condition cannot be met.

This file supplies the missing half: a concrete six-instruction image whose run
reaches `State.KillEv`.

## The program

Six instructions at 0x100, the shortest that can abort under this model, written
as the hex a loader would have produced:

```
  addi a7, x0, 96     06000893   set_tid_address
  addi a0, x0, 0      00000513   tidptr = NULL
  ecall               00000073   -> a0 = the tid the model chose
  addi a7, x0, 130    08200893   tkill
  addi a1, x0, 6      00600593   SIGABRT
  ecall               00000073   -> killed
```

THE FIRST SYSCALL IS NOT CEREMONY.  `Kernel.Signal.tkill_self` declines with
`Monad.unmodeled` while `State.m_tid` is `none`, and declines again unless the
`pid` it is handed EQUALS the recorded tid.  `Kernel.Fork.set_tid_address_spec`
pins that tid, and it pins it to a value drawn with `Monad.choose` from the whole
`Kernel.Fork.PID_MAX_ENVELOPE` window, so no image can carry the right `pid` as an
immediate.  What makes this program work is that `Run.apply_effect` writes the
syscall's return value into a0 and neither instruction between the two `ecall`s
touches a0, so the tid flows from the kernel's answer into `tkill`'s first
argument.

THE MASK IS THE OTHER PREMISE.  `abrt_input` launches with `State.in_sigmask`
clear, so SIGABRT is not blocked and `Kernel.Signal.send_sigabrt` takes the
`State.with_killed` branch rather than the `State.with_sigabrt_pending` one.

ADMISSION REASON (the third at the top of `Checks/Examples.lean`): what is pinned
here is that a `Run.run`'s TRACE SET holds a `State.KillEv`, which is a statement
about the model's own execution relation, not about anything a real run reveals.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.AbortWitness

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
  (with_mem with_mem_eta run_steps)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude (CheckOk CheckUnmodeled)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples (demo_proc_input demo_entry)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (demo_phdrs demo_draw)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal (abort_tid)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
  (abrt_image abort_input abort_input_valid)
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence

/-! ## The image, the launch, and the two syscall answers -/

/-- The one segment of the fixture: twenty-four read-and-execute bytes at 0x100,
the six instructions of the file's header comment.
model: Rocq `Checks.AbortWitness.abrt_segment`. -/
def abrt_segment : Segment :=
  ⟨0x100, 24, "r-x", ["930800061305000073000000930820089305600073000000"]⟩

/-- The image's segment list, which is that one segment.
model: Rocq `Checks.AbortWitness.abrt_segments`.  `abrt_image.img_segments`
reduces to this list, so the two name the same thing. -/
def abrt_segments : List Segment := [abrt_segment]

/-- The launch `Checks.Examples` runs its images on — one empty argument, no
environment, an empty file system, end of input — with the two fields this file
needs pinned: `State.in_sigmask` clear, so SIGABRT is deliverable, and
`State.in_abort_terminal` SET, which `Run.valid_input_abort` asks for and
`Kernel.Signal.tkill_spec` tests first.
model: Rocq `Checks.AbortWitness.abrt_input`.  The Lean tree already holds that
record as `Checks.Cases.EquivalenceDefinition.Equivalence.abort_input`, the demo
input with the declaration on, which is the same record field for field; this
name is the Rocq one for it rather than a second copy. -/
def abrt_input : ProcInput := abort_input

/-- The launch declares the abort stance.
model: the accessor `State.in_abort_terminal` on `abrt_input`. -/
theorem abrt_input_declares_abort : abrt_input.in_abort_terminal = true := rfl

/-- `Run.valid_input_abort` holds of it: the same shared clauses
`Checks.Omni.demo_input_valid` proves, with the abort declaration this file is
about rather than its negation.
model: Rocq `Checks.AbortWitness.abrt_input_valid`. -/
theorem abrt_input_valid : valid_input_abort abrt_input := abort_input_valid

/-- The entry is `Checks.Examples.demo_entry`, and it is valid for this image at
every abort-declared launch: the image's only segment sits in the first page, so
the same break base serves, and the fourth conjunct follows from
`Run.entry_stack_span_bound` on the argv and envp clauses alone.
model: `Run.valid_entry_sv48` at the demo entry, the way
`Equivalence.undecodable_entry_valid` is proved. -/
theorem demo_entry_valid_abrt (inp : ProcInput) (hvalid : valid_input_abort inp) :
    valid_entry abrt_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ hvalid)]
  obtain ⟨hargv, henvp, _⟩ := hvalid
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-! ## Walking the run -/

/-- The launch machine state of the fixture.
model: Rocq `Checks.AbortWitness.abrt_ms0`. -/
def abrt_ms0 : machine_state :=
  init_machine_state abrt_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    abrt_input.in_argv abrt_input.in_envp abrt_input.in_uid abrt_input.in_hwcap

/-- The state after `k` instructions of the first leg; a fault or an unmodeled
answer would leave the launch state, and the three steps below reach neither.
model: Rocq `Checks.AbortWitness.abrt_msk`. -/
def abrt_msk (k : Nat) : machine_state :=
  match run_steps k abrt_segments abrt_ms0 with
  | some ms => ms
  | none => abrt_ms0
/-- The same state with the memory abstracted the way `Checks.Omni`'s `wloop_msk`
family abstracts it: no instruction of this image writes memory, so every state
on the way carries the launch state's.
model: Rocq `Checks.AbortWitness.abrt_s`. -/
def abrt_s (k : Nat) : machine_state := with_mem (abrt_msk k) abrt_ms0.ms_mem

/-- The model the fixture launches with at allocation limit `lim`.
model: Rocq `Checks.AbortWitness.abrt_model`. -/
def abrt_model (lim : Int) : Model :=
  init_model (segments_reserved abrt_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim abrt_input

/-- The launch configuration.
model: Rocq `Checks.AbortWitness.abrt_c`. -/
def abrt_c (lim : Int) : config := config.mkCfg (abrt_s 0) (abrt_model lim)

/-- The configuration `Run.run` starts this image at is that one.  Rocq needs
`Checks.Omni.with_mem_eta` here; Lean's structure eta makes it `rfl`.
model: Rocq `Checks.AbortWitness.abrt_config`. -/
theorem abrt_config (lim : Int) :
    init_config abrt_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input
    = abrt_c lim := rfl

set_option maxRecDepth 32768 in
/-- Each of the first three instructions is a machine step, whatever memory the
state carries: none of them reads or writes memory.  Rocq closes this by
`vm_compute` with the memory abstract; Lean reaches the same three answers
through `Common.PropExec.step_of_fetch`, because the fallback fetch of
`RiscvSemantics.step` reads the memory and blocks the reduction while the
memory is a variable.
model: Rocq `Checks.AbortWitness.abrt_step`. -/
theorem abrt_step (k : Nat) (hk : k < 3) (mem : word → Option byte) :
    RiscvSemantics.step abrt_segments (with_mem (abrt_msk k) mem)
    = MachineOk (with_mem (abrt_msk (k + 1)) mem) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · have hpc : ms_pc (with_mem (abrt_msk 0) mem) = Z_to_bv 64 0x100 := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_msk 0) mem))
        = some 0x06000893 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x06000893 hf]
    rfl
  · have hpc : ms_pc (with_mem (abrt_msk 1) mem) = Z_to_bv 64 0x104 := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_msk 1) mem))
        = some 0x00000513 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x00000513 hf]
    rfl
  · have hpc : ms_pc (with_mem (abrt_msk 2) mem) = Z_to_bv 64 0x108 := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_msk 2) mem))
        = some 0x00000073 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x00000073 hf]
    rfl

set_option maxRecDepth 32768 in
/-- …so each of them is a silent transition of the model.
model: `Run.sstep_instr` with `Run.mi_account_step_no_lazy` for the accounting.
model: Rocq `Checks.AbortWitness.abrt_instr_sstep`. -/
theorem abrt_instr_sstep (lim : Int) (k : Nat) (hk : k < 3) :
    sstep abrt_segments (config.mkCfg (abrt_s k) (abrt_model lim)) []
      (SNext (config.mkCfg (abrt_s (k + 1)) (abrt_model lim))) := by
  unfold abrt_s
  apply sstep.sstep_instr _ _ _ _ rfl
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals first
      | rfl
      | decide +kernel
  · rw [mi_account_step_no_lazy _ _ _ rfl, abrt_step k hk]

set_option maxRecDepth 32768 in
/-- Three instructions in — the two `addi`s and the `ecall`, which is an ordinary
instruction step that leaves the number pending — the first syscall is at the
door and its number is 96.
model: Rocq `Checks.AbortWitness.abrt_svc3`. -/
theorem abrt_svc3 : (abrt_s 3).ms_svc_pending = some (Z_to_bv 64 96) := by
  decide +kernel

/-- THE TID THE MODEL CHOOSES.  `Monad.choose` admits any value in the window, so
this effect names one; `abrt_sc1` is the statement that the acceptor agrees it is
admissible, and nothing below depends on which one it is.
model: Rocq `Checks.AbortWitness.abrt_eff1`. -/
def abrt_eff1 : SyscallEffect := mkEffect abort_tid [] []

set_option maxRecDepth 32768 in
/-- The acceptor admits that answer to `set_tid_address` and records the tid.
model: `Checks.ExecutableSpecs.check_syscall` at the pending number 96.
model: Rocq `Checks.AbortWitness.abrt_sc1`. -/
theorem abrt_sc1 (lim : Int) :
    Checks.ExecutableSpecs.check_syscall
        (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96)) abrt_eff1 (abrt_model lim)
      = CheckOk (with_tid abort_tid (abrt_model lim)) [] := rfl

/-- The state the first syscall leaves: a0 holds the tid, and the pc has moved
past the `ecall`.  This is where the second leg starts.
model: Rocq `Checks.AbortWitness.abrt_t0`. -/
def abrt_t0 : machine_state :=
  advance_past_svc (apply_effect (abrt_s 3) abrt_eff1)
/-- The state after `k` instructions of the second leg.
model: Rocq `Checks.AbortWitness.abrt_tk`. -/
def abrt_tk (k : Nat) : machine_state :=
  match run_steps k abrt_segments abrt_t0 with
  | some ms => ms
  | none => abrt_t0
/-- The second leg abstracts ITS OWN memory rather than `abrt_ms0`'s.  The two are
equal — `abrt_eff1` carries no writes, copies, zeros or unmaps, and
`Run.apply_effect` touches memory only through those — but naming `abrt_t0`'s is
what lets `abrt_t 0` be `abrt_t0` by `Checks.Omni.with_mem_eta` alone.
model: Rocq `Checks.AbortWitness.abrt_t`. -/
def abrt_t (k : Nat) : machine_state := with_mem (abrt_tk k) abrt_t0.ms_mem

set_option maxRecDepth 32768 in
/-- The first syscall as a transition: the model records the chosen tid and the
machine moves past the `ecall`.
model: `Run.sstep_syscall` with `Checks.ExecutableSpecs.check_syscall_sound_ok` on
`abrt_sc1`.
model: Rocq `Checks.AbortWitness.abrt_syscall1_sstep`. -/
theorem abrt_syscall1_sstep (lim : Int) :
    sstep abrt_segments (config.mkCfg (abrt_s 3) (abrt_model lim)) []
      (SNext (config.mkCfg (abrt_t 0) (with_tid abort_tid (abrt_model lim)))) := by
  apply sstep.sstep_syscall _ _ (Z_to_bv 64 96) abrt_eff1
    (with_tid abort_tid (abrt_model lim)) (with_tid abort_tid (abrt_model lim)) []
    rfl abrt_svc3
  · exact Checks.ExecutableSpecs.check_syscall_sound_ok _ _ _ _ _ (abrt_sc1 lim)
  · rfl
  · exact materialize_model_accesses_no_lazy _ _ rfl

set_option maxRecDepth 32768 in
/-- Each of the next three instructions is a machine step too, on the same terms.
model: Rocq `Checks.AbortWitness.abrt_step2`. -/
theorem abrt_step2 (k : Nat) (hk : k < 3) (mem : word → Option byte) :
    RiscvSemantics.step abrt_segments (with_mem (abrt_tk k) mem)
    = MachineOk (with_mem (abrt_tk (k + 1)) mem) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · have hpc : ms_pc (with_mem (abrt_tk 0) mem) = Z_to_bv 64 0x10c := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_tk 0) mem))
        = some 0x08200893 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x08200893 hf]
    rfl
  · have hpc : ms_pc (with_mem (abrt_tk 1) mem) = Z_to_bv 64 0x110 := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_tk 1) mem))
        = some 0x00600593 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x00600593 hf]
    rfl
  · have hpc : ms_pc (with_mem (abrt_tk 2) mem) = Z_to_bv 64 0x114 := rfl
    have hf : fetch_word abrt_segments (ms_pc (with_mem (abrt_tk 2) mem))
        = some 0x00000073 := by rw [hpc]; decide +kernel
    rw [LinuxProcessSemantics.Common.PropExec.step_of_fetch abrt_segments _ 0x00000073 hf]
    rfl

set_option maxRecDepth 32768 in
/-- …so each is a silent transition, with the recorded tid carried along.
model: Rocq `Checks.AbortWitness.abrt_instr2_sstep`. -/
theorem abrt_instr2_sstep (lim : Int) (k : Nat) (hk : k < 3) :
    sstep abrt_segments
      (config.mkCfg (abrt_t k) (with_tid abort_tid (abrt_model lim))) []
      (SNext (config.mkCfg (abrt_t (k + 1)) (with_tid abort_tid (abrt_model lim)))) := by
  unfold abrt_t
  apply sstep.sstep_instr _ _ _ _ rfl
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals first
      | rfl
      | decide +kernel
  · rw [mi_account_step_no_lazy _ _ _ rfl, abrt_step2 k hk]

set_option maxRecDepth 32768 in
/-- Three more instructions, and the second `ecall` is pending at 130.
model: Rocq `Checks.AbortWitness.abrt_svc_tkill`. -/
theorem abrt_svc_tkill : (abrt_t 3).ms_svc_pending = some (Z_to_bv 64 130) := by
  decide +kernel

/-- The model the kill leaves: the recorded tid, and signal 6 in the killed field.
model: Rocq `Checks.AbortWitness.abrt_killed_model`. -/
def abrt_killed_model (lim : Int) : Model :=
  with_killed (Z_to_bv 64 6) (with_tid abort_tid (abrt_model lim))

set_option maxRecDepth 32768 in
/-- The kill itself: a0 carries the tid the first syscall returned, a1 carries 6,
and the post-model is `State.with_killed` — the answer
`Cases.Kernel.Signal.tkill_sigabrt_unblocked_kills` pins at a hand-built model,
reached here from a machine state whose registers the program put there.
model: `Checks.Sys.Table.check_tkill_a0_a1_eq` and the `tkill` checker on the
arguments read off `abrt_t 3`.
model: Rocq `Checks.AbortWitness.abrt_sc2`. -/
theorem abrt_sc2 (lim : Int) :
    Checks.ExecutableSpecs.check_syscall
        (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
        (mkEffect (Z_to_bv 64 0) [] []) (with_tid abort_tid (abrt_model lim))
      = CheckOk (abrt_killed_model lim) [] := by
  show Checks.ExecutableSpecs.check_syscall
      (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
      (mkEffect (Z_to_bv 64 0) [] []) (with_tid (Z_to_bv 64 4242) (abrt_model lim))
    = CheckOk (with_killed (Z_to_bv 64 6) (with_tid (Z_to_bv 64 4242) (abrt_model lim))) []
  change Checks.Sys.Table.check_tkill_a0_a1 _ _ _ = _
  rw [Checks.Sys.Table.check_tkill_a0_a1_eq]
  have hp : Sys.Syscall.pid32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0) =
      Z_to_bv 64 4242 := by decide +kernel
  have hs : Sys.Kernel.Signal.sig32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 1) =
      Z_to_bv 64 6 := by decide +kernel
  rw [hp, hs]
  have ha : m_abort_terminal (with_tid (4242#64) (abrt_model lim)) = true := rfl
  have ht : m_tid (with_tid (4242#64) (abrt_model lim)) = some (4242#64 : word) := rfl
  have hm : m_sigmask (with_tid (4242#64) (abrt_model lim)) = (0#64 : word) := rfl
  simp [Checks.Sys.Kernel.Signal.check_tkill, Checks.Sys.Kernel.Signal.check_tkill_self,
    Checks.Sys.Kernel.Signal.check_send_sigabrt, ha, ht, hm,
    Sys.Kernel.Signal.pid_positive, Sys.Kernel.Signal.tkill_sig_valid,
    Sys.Kernel.Signal.sigabrt_blocked, bv_eqb, bv_unsigned, Z_to_bv, bv_and,
    Sys.Uapi.SIGABRT, Sys.Uapi.sigabrt_mask, Sys.Syscall.w_is0]

/-- The trace the run ends on.
model: Rocq `Checks.AbortWitness.abrt_trace`. -/
def abrt_trace (lim : Int) : List event :=
  [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))]

set_option maxRecDepth 32768 in
/-- The second syscall as a transition: `Run.sstep_killed` rather than
`Run.sstep_exit` is the rule that fires, and it emits the kill event.
model: Rocq `Checks.AbortWitness.abrt_kill_sstep`. -/
theorem abrt_kill_sstep (lim : Int) :
    sstep abrt_segments
      (config.mkCfg (abrt_t 3) (with_tid abort_tid (abrt_model lim)))
      (abrt_trace lim)
      (SNext (config.mkCfg (abrt_t 3) (abrt_killed_model lim))) := by
  apply sstep.sstep_killed _ _ (Z_to_bv 64 130) (mkEffect (Z_to_bv 64 0) [] [])
    (abrt_killed_model lim) [] (Z_to_bv 64 6) rfl abrt_svc_tkill
  · exact Checks.ExecutableSpecs.check_syscall_sound_ok _ _ _ _ _ (abrt_sc2 lim)
  · rfl

set_option maxRecDepth 32768 in
/-- The whole execution: two instructions, `set_tid_address`, two more
instructions, `tkill`, and the process is dead.
model: `Run.star` over the eight transitions above.
model: Rocq `Checks.AbortWitness.abrt_star`. -/
theorem abrt_star (lim : Int) :
    star abrt_segments (abrt_c lim) (abrt_trace lim)
      (config.mkCfg (abrt_t 3) (abrt_killed_model lim)) :=
  star.star_step _ _ _ _ _ (abrt_instr_sstep lim 0 (by omega))
    (star.star_step _ _ _ _ _ (abrt_instr_sstep lim 1 (by omega))
    (star.star_step _ _ _ _ _ (abrt_instr_sstep lim 2 (by omega))
    (star.star_step _ _ _ _ _ (abrt_syscall1_sstep lim)
    (star.star_step _ _ _ _ _ (abrt_instr2_sstep lim 0 (by omega))
    (star.star_step _ _ _ _ _ (abrt_instr2_sstep lim 1 (by omega))
    (star.star_step _ _ _ _ _ (abrt_instr2_sstep lim 2 (by omega))
    (star.star_step _ _ _ _ _ (abrt_kill_sstep lim) (star.star_refl _))))))))

/-! ## What it buys -/

/-- THE CONTROL, and it is the half that says the refutation this fixture fires is
about the ABORT and not about the image.  The identical program is NOT refuted
that way with the declaration clear.
model: Rocq `Checks.AbortWitness.abrt_input_undeclared`, which is the demo input:
the same record with `State.in_abort_terminal` false. -/
def abrt_input_undeclared : ProcInput := demo_proc_input

set_option maxRecDepth 32768 in
/-- With the declaration clear `Kernel.Signal.tkill_spec` declines, the run leaves
the modeled surface, and there is no `State.KillEv` to refute anything by.
model: `Checks.ExecutableSpecs.check_syscall` at the same call and registers.
model: Rocq `Checks.AbortWitness.abrt_tkill_declined_undeclared`. -/
theorem abrt_tkill_declined_undeclared :
    Checks.ExecutableSpecs.check_syscall
        (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
        (mkEffect (Z_to_bv 64 0) [] [])
        (with_tid abort_tid
          (init_model (segments_reserved abrt_segments) (Z_to_bv 64 0x1000)
            (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000)
            source_alloc_limit abrt_input_undeclared))
      = CheckUnmodeled := by
  change Checks.Sys.Table.check_tkill_a0_a1 _ _ _ = _
  rw [Checks.Sys.Table.check_tkill_a0_a1_eq]
  have hp : Sys.Syscall.pid32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0) =
      Z_to_bv 64 4242 := by decide +kernel
  have hs : Sys.Kernel.Signal.sig32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 1) =
      Z_to_bv 64 6 := by decide +kernel
  rw [hp, hs]
  simp only [Checks.Sys.Kernel.Signal.check_tkill]
  rfl

set_option maxRecDepth 32768 in
/-- THE DATA FLOW, PINNED.  `tkill`'s first argument at the second `ecall` is the
value the FIRST syscall returned: the image contains no 4242, and a0 was last
written by `Run.apply_effect`.
model: Rocq `Checks.AbortWitness.abrt_tkill_pid_is_the_returned_tid`. -/
theorem abrt_tkill_pid_is_the_returned_tid :
    in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0 = abort_tid := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- The value was a CHOICE and not a constant: the acceptor admits a different tid
from the same state, so nothing in the model forced 4242.
model: Rocq `Checks.AbortWitness.abrt_sc1_admits_another_tid`. -/
theorem abrt_sc1_admits_another_tid (lim : Int) :
    Checks.ExecutableSpecs.check_syscall
        (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96))
        (mkEffect (Z_to_bv 64 1234) [] []) (abrt_model lim)
      = CheckOk (with_tid (Z_to_bv 64 1234) (abrt_model lim)) [] := rfl

set_option maxRecDepth 32768 in
/-- The match is what the kill DEPENDED on: the same call, the same registers, the
same declaration and a model whose recorded tid is one greater is declined rather
than fatal.  The death above is the arm firing because the program sent the signal
to ITSELF.
model: Rocq `Checks.AbortWitness.abrt_tkill_other_tid_declined`. -/
theorem abrt_tkill_other_tid_declined (lim : Int) :
    Checks.ExecutableSpecs.check_syscall
        (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
        (mkEffect (Z_to_bv 64 0) [] [])
        (with_tid (Z_to_bv 64 4243) (abrt_model lim))
      = CheckUnmodeled := by
  change Checks.Sys.Table.check_tkill_a0_a1 _ _ _ = _
  rw [Checks.Sys.Table.check_tkill_a0_a1_eq]
  have hp : Sys.Syscall.pid32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0) =
      Z_to_bv 64 4242 := by decide +kernel
  have hs : Sys.Kernel.Signal.sig32
      (in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 1) =
      Z_to_bv 64 6 := by decide +kernel
  rw [hp, hs]
  simp only [Checks.Sys.Kernel.Signal.check_tkill, Checks.Sys.Kernel.Signal.check_tkill_self]
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.AbortWitness
