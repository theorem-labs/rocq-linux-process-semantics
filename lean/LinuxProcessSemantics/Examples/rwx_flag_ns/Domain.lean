import LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
import LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage
import LinuxProcessSemantics.LinuxProcessSem.Run

/-! The universal theorem's domain is inhabited.

The entry witnesses work for every valid input, including the largest
permitted argument and environment blocks. The concrete input separately
checks that the input predicate itself has an inhabitant. Neither witness
replaces the universal quantifiers in the program theorem.
-/

namespace LinuxProcessSemantics.Examples.rwx_flag_ns.Domain

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage

def source_entry : ExecEntry :=
  ExecEntry.mkEntry (Z_to_bv 64 sp_window_lo) (Z_to_bv 64 0x11000)
    (Z_to_bv 64 mmap_base_max) (EntryDraw.mkDraw 0 (fun _ => 0))

def target_entry : ExecEntry :=
  ExecEntry.mkEntry (Z_to_bv 64 sp_window_lo) (Z_to_bv 64 0x1003000)
    (Z_to_bv 64 mmap_base_max) (EntryDraw.mkDraw 1 (fun _ => 1))

theorem source_entry_valid (inp : ProcInput) (hi : valid_input inp) :
    valid_entry Source.image source_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hi.1 hi.2.1).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

theorem target_entry_valid (inp : ProcInput) (hi : valid_input inp) :
    valid_entry Target.image target_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hi.1 hi.2.1).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- Each binary's entire entry draw remains independently quantified. -/
theorem source_entry_with_draw_valid (draw : EntryDraw) (inp : ProcInput)
    (hi : valid_input inp) :
    valid_entry Source.image { source_entry with en_draw := draw } inp :=
  source_entry_valid inp hi

theorem target_entry_with_draw_valid (draw : EntryDraw) (inp : ProcInput)
    (hi : valid_input inp) :
    valid_entry Target.image { target_entry with en_draw := draw } inp :=
  target_entry_valid inp hi

theorem entry_witnesses_have_distinct_random_draws :
    source_entry.en_draw.ed_random ≠ target_entry.en_draw.ed_random := by decide +kernel

theorem entry_witnesses_have_distinct_slack_bytes :
    source_entry.en_draw.ed_slack 0 ≠ target_entry.en_draw.ed_slack 0 := by decide +kernel

theorem entries_exist_for_every_valid_input (inp : ProcInput) (hi : valid_input inp) :
    ∃ es et, valid_entry Source.image es inp ∧ valid_entry Target.image et inp :=
  ⟨source_entry, target_entry, source_entry_valid inp hi, target_entry_valid inp hi⟩

def input_witness : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false .Sv48

theorem input_witness_valid : valid_input input_witness := by
  simp [valid_input, input_witness, ProcInput.mkProcInput, ProcInput.in_fs, fs_seed_tmp,
    valid_argv, valid_envp, valid_fs, fs_sorted, fs_image_real, fs_keys_canonical, fs_no_dir_key,
    total_arg_bytes, valid_creds, valid_id,
    valid_nofile, valid_sigmask, valid_hwcap, default_nofile, bv_unsigned, Z_to_bv, bv_and,
    valid_urandom, default_urandom, stream_const, stream_infinite]

def vector_input_witness : ProcInput :=
  { input_witness with in_hwcap := hwcap_rv64gcv }

theorem vector_input_witness_valid : valid_input vector_input_witness := by
  simp [valid_input, vector_input_witness, input_witness, ProcInput.mkProcInput,
    ProcInput.in_fs, fs_seed_tmp, valid_argv, valid_envp, valid_fs, fs_sorted, fs_image_real,
    fs_keys_canonical, fs_no_dir_key,
    total_arg_bytes, valid_creds, valid_id, valid_nofile, valid_sigmask, valid_hwcap,
    default_nofile, bv_unsigned, Z_to_bv, bv_and,
    valid_urandom, default_urandom, stream_const, stream_infinite]

theorem both_hardware_masks_are_valid :
    valid_hwcap hwcap_rv64gc ∧ valid_hwcap hwcap_rv64gcv :=
  ⟨Or.inl rfl, Or.inr rfl⟩

theorem missing_hardware_bits_rejected :
    ¬ valid_input { input_witness with in_hwcap := 0 } := by
  simp [valid_input, valid_hwcap, hwcap_rv64gc, hwcap_rv64gcv, Z_to_bv]

theorem undeclared_abort_input_is_in_baseline_domain : input_witness.in_abort_terminal = false := rfl

/-- The current reference baseline pins the task's abort declaration off;
the separate abort-declared statement is outside this pilot's API. -/
theorem abort_declaration_requires_its_own_contract :
    ¬ valid_input { input_witness with in_abort_terminal := true } := by
  simp [valid_input]

theorem theorem_domain_inhabited :
    ∃ es et inp, valid_entry Source.image es inp ∧ valid_entry Target.image et inp ∧
      valid_input inp :=
  ⟨source_entry, target_entry, input_witness, source_entry_valid _ input_witness_valid,
    target_entry_valid _ input_witness_valid, input_witness_valid⟩

/-- The entry guard rejects a concrete invalid placement; the witness above
does not pass because the guard became universally true. -/
theorem zero_stack_entry_rejected :
    ¬ valid_entry Source.image { source_entry with en_sp := Z_to_bv 64 0 } input_witness := by
  intro h
  rw [valid_entry_sv48 _ _ _ rfl] at h
  have hlo := h.1.1
  exact (by decide +kernel : ¬ sp_window_lo ≤ 0) hlo

theorem empty_argv_input_rejected : ¬ valid_input { input_witness with in_argv := [] } := by
  intro h
  exact (by decide : ¬ (1 : Int) ≤ 0) h.1.1.1

end LinuxProcessSemantics.Examples.rwx_flag_ns.Domain
