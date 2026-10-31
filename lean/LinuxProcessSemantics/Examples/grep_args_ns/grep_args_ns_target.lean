import LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/grep_args_ns/grep_args_ns_target.v` at the baseline above;
this proof-side file executes the Zig ReleaseSmall target from entry to exit,
concluding the two `to_wexit` derivations for argc ≥ 2 and argc < 2 used by
`Proof.v`. Rocq `Z` is `Int`, `nat` is `Nat`, `firstn`/`skipn` are
`List.take`/`List.drop`, and Section variables become explicit arguments or
`variable`s. Straight-line `sym_block` scripts use the merged StepTac family.
The stack-window restatements, argc unsigned value, stack-image bound, and
wrapped-stack read bridge reuse Common.ArgvEnv and Common.PropExec.
-/

namespace LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.grep_args_ns.TargetMemImage
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_code
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs

variable (av ev : List (List byte)) (uid hw : word)
variable (Hva : valid_argv av) (Hve : valid_envp ev)

/- The initial stack pointer is quantified (ASLR), independently of the
source binary's pointer. The target's AT_RANDOM draw is also independent. -/
variable (asp : word) (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp)
variable (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)

/- Rocq asp_lo_num / asp_hi_num are Common.ArgvEnv.sp_lo_num / sp_hi_num. -/

theorem target_init_pc_val : TargetMemImage_init_pc = 0x100115c := by decide

def aargcN : word := len_word av
def awmem : word → Option byte := wrap_mem target_phdrs asp av ev uid hw arnd
def arom : word → Option byte := seg_rom target_segs

/- Rocq u_aargcN is Common.ArgvEnv.u_argcN.
The no-overflow bound target_bsb_nw is Common.ArgvEnv.bsb_nw. -/

/- The two frames: _start's two slots, then run's eight slots, all below
initial sp, in execution order (innermost = first store). -/
def afmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (awmem av ev uid hw asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 ((0x100117c : word))))
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 (asp)))
    (Z_to_bv 64 (bv_unsigned asp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))

local notation "AF" => afmem av ev uid hw asp arnd
local notation "AW" => awmem av ev uid hw asp arnd

include Hsp_lo Hsp_hi

/-- Reads at or above initial sp see through the frame stores. -/
theorem rdn_afmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs AF a n = rdn target_segs AW a n := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  unfold afmem
  repeat (rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) Hn])

/- Rocq rdn_awmem_stack is Common.PropExec.rdn_wrap_stack_above. -/

include Hva Hve

theorem aread_argc : rdn target_segs AF asp 8 = some (word_le8 (aargcN av)) := by
  have hhi := sp_hi_num asp Hsp_hi
  rw [rdn_afmem_above av ev uid hw asp arnd Hsp_lo Hsp_hi asp 8 (by omega) (by omega)]
  unfold awmem
  rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
  exact read_argc _ _ _ _ _ _ _ _ (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi)


theorem aread_ptr (k : Nat) (Hk : k < av.length) :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (k : Int))) 8 =
      some (word_le8 (cat_argv_ptr asp av ev k)) := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  have hlen := valid_argv_len av Hva
  have he : Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (k : Int)) =
      asp + nat_to_word (8 + 8 * k) := by
    rw [word_add_nat]; congr 1; omega
  rw [he, rdn_afmem_above av ev uid hw asp arnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  unfold awmem
  rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ Hk (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi)

/- Rocq target_ptr_bounds is Common.ArgvEnv.argv_ptr_bounds_at. -/

theorem aread_str_byte (k j : Nat) (Hk : k < av.length)
    (Hj : j ≤ (av.getD k []).length) :
    rdn target_segs AF (cat_argv_ptr asp av ev k + nat_to_word j) 1 =
      some [byte_at (av.getD k []) j] := by
  have ⟨hge, hup⟩ := argv_ptr_bounds_at asp av ev Hva Hve Hsp_hi k Hk
  have hslen := valid_argv_str_len av k Hva Hk
  have hp := u64_range (cat_argv_ptr asp av ev k)
  rw [rdn_afmem_above av ev uid hw asp arnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  unfold awmem
  rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_byte_k _ _ _ _ _ _ _ _ _ _ Hk Hj (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi)

theorem aread_str (k : Nat) (Hk : k < av.length) :
    rdn target_segs AF (cat_argv_ptr asp av ev k) (av.getD k []).length =
      some (av.getD k []) := by
  have ⟨hge, hup⟩ := argv_ptr_bounds_at asp av ev Hva Hve Hsp_hi k Hk
  rw [rdn_afmem_above av ev uid hw asp arnd Hsp_lo Hsp_hi _ _ hge (by omega)]
  unfold awmem
  rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ hge (by omega)]
  exact read_argv_str_k _ _ _ _ _ _ _ _ _ Hk (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi)


omit Hva Hve Hsp_lo Hsp_hi in
/-- The newline byte in the target image at 0x1000158. -/
theorem aseg_rom_newline : seg_rom target_segs 0x1000158 = some (Z_to_bv 8 10) := by
  have bridge (segs : List Segment) (addr : word) (seg : Segment) (b : byte)
      (hf : find_segment segs (bv_unsigned addr) (↑(1 : Nat)) = some seg)
      (hr : seg_readable seg = true)
      (hb : segment_read_bytes seg.seg_bytes (bv_unsigned addr - seg.seg_base).toNat 1 = some [b]) :
      seg_rom segs addr = some b := by
    simp only [seg_rom, memory_read, hf, hr, ↓reduceIte, hb]
  apply bridge target_segs 0x1000158 TargetMemImage_segment_000 (Z_to_bv 8 10)
  · rfl
  · rfl
  · have hr : LinuxProcessSemantics.Common.ImageBytes.ascii_segment_read_bytes
        [TargetMemImage_seg_bytes_000_chars] 344 1 = some [Z_to_bv 8 10] := by decide +kernel
    exact (TargetMemImage_segment_000_read_ascii 344 1).trans hr

omit Hva Hve in
theorem aread_newline : rdn target_segs AF 0x1000158 1 = some [Z_to_bv 8 10] := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  unfold afmem
  repeat (rw [rdn_wbytes_below _ _ _ _ _ _
    (by imm_norm; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)])
  unfold awmem
  simp only [rdn, wrap_mem_below target_phdrs asp av ev 0x1000158 uid hw arnd
    (by rw [stack_max_size_val]; imm_norm; omega), aseg_rom_newline]

omit Hva Hve in
/-- Frame-slot read-back. -/
theorem aread_slot_ra :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8 =
      some (word_to_le_bytes 8 (0x100117c : word)) := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  unfold afmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]

omit Hva Hve in
theorem aread_slot_s0 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8 =
      some (word_to_le_bytes 8 asp) := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  unfold afmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]

omit Hva Hve in
theorem aread_slot_0 (a : word)
    (Ha : a ∈ [Z_to_bv 64 (bv_unsigned asp - 0x50), Z_to_bv 64 (bv_unsigned asp - 0x48),
      Z_to_bv 64 (bv_unsigned asp - 0x40), Z_to_bv 64 (bv_unsigned asp - 0x38),
      Z_to_bv 64 (bv_unsigned asp - 0x30), Z_to_bv 64 (bv_unsigned asp - 0x28)]) :
    rdn target_segs AF a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
  rcases Ha with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold afmem
  all_goals
    repeat first
      | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      | rw [rdn_wbytes_disjoint _ _ _ _ _ _
          (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
      | rw [rdn_wbytes_below _ _ _ _ _ _
          (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

omit Hva Hve in
theorem aread_slot_d8 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 40)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [or_true]

omit Hva Hve in
theorem aread_slot_d0 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 48)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [true_or, or_true]

omit Hva Hve in
theorem aread_slot_c8 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 56)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [true_or, or_true]

omit Hva Hve in
theorem aread_slot_c0 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 64)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [true_or, or_true]

omit Hva Hve in
theorem aread_slot_b8 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 72)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [true_or, or_true]

omit Hva Hve in
theorem aread_slot_b0 :
    rdn target_segs AF (Z_to_bv 64 (bv_unsigned asp - 80)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  apply aread_slot_0 av ev uid hw asp arnd Hsp_lo Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [true_or]


/- Target epilogue: a0 := s4, reload the eight callee-saved slots, pop
run's frame, and return through Zig's entry stub to the exit ecall.
The eight `stepld` read witnesses replace Rocq's `t_slot_rd` dispatcher.
Rocq's `wexit1` abbreviation is spelled out as `to_wallexit` at fd 1. -/
omit Hva Hve in
theorem target_epilogue (regs : bvmap 5 word) (code : word)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50))
    (H20 : reg_get regs 20 = code) (Hc : bv_unsigned code < 256) :
    to_wallexit target_segs (Z_to_bv 64 1) [] code (mkst regs 0x1001280 AF arom) := by
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  stepiv TF_1001280 TD_1001280 code (getr_resolve; rw [H20]; exact v_addi_0 _)
  stepld TF_1001284 TD_1001284 (Z_to_bv 64 (bv_unsigned asp - 24)) (0x100117c : word)
    (exact aread_slot_ra av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_1001288 TD_1001288 (Z_to_bv 64 (bv_unsigned asp - 32)) asp
    (exact aread_slot_s0 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_100128c TD_100128c (Z_to_bv 64 (bv_unsigned asp - 40)) (Z_to_bv 64 0)
    (exact aread_slot_d8 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_1001290 TD_1001290 (Z_to_bv 64 (bv_unsigned asp - 48)) (Z_to_bv 64 0)
    (exact aread_slot_d0 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_1001294 TD_1001294 (Z_to_bv 64 (bv_unsigned asp - 56)) (Z_to_bv 64 0)
    (exact aread_slot_c8 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_1001298 TD_1001298 (Z_to_bv 64 (bv_unsigned asp - 64)) (Z_to_bv 64 0)
    (exact aread_slot_c0 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_100129c TD_100129c (Z_to_bv 64 (bv_unsigned asp - 72)) (Z_to_bv 64 0)
    (exact aread_slot_b8 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepld TF_10012a0 TD_10012a0 (Z_to_bv 64 (bv_unsigned asp - 80)) (Z_to_bv 64 0)
    (exact aread_slot_b0 av ev uid hw asp arnd Hsp_lo Hsp_hi)
  stepi TF_10012a4 TD_10012a4
  stepjr TF_10012a8 TD_10012a8 (0x100117c : word) (getr_resolve; rfl)
  stepi TF_100117c TD_100117c
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ TF_1001180 rfl
  · apply tw_exit_coden
    · getr_resolve; rfl
    · regupd_resolve; rfl
    · exact Hc


/- slen: 0x10012e4..0x10012fc. -/
theorem aslen_loop (k : Nat) (Hk : k < av.length) (d j : Nat) (regs : bvmap 5 word)
    (Hjd : j + d = (av.getD k []).length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr asp av ev k)
    (Hr11 : reg_get regs 11 = nat_to_word j) :
    ∃ regs',
      (∀ r : reg, r ≠ 11 → r ≠ 12 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 11 = nat_to_word ((av.getD k []).length + 1) ∧
      msteps target_segs (mkst regs 0x10012e8 AF arom) (mkst regs' 0x10012f8 AF arom) := by
  have hslen := valid_argv_str_len av k Hva Hk
  have hsnz := valid_argv_str_nz av k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have hj : j = (av.getD k []).length := by omega
    let regs1 := regupd regs 12 (cat_argv_ptr asp av ev k + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 0)
    let regs3 := regupd regs2 11 (nat_to_word (j + 1))
    have E1 : step target_segs (mkst regs 0x10012e8 AF arom) =
        MachineOk (mkst regs1 0x10012ec AF arom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ TF_10012e8 rfl TD_10012e8 rfl
      getr_resolve
      rw [Hr10, Hr11, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm]
    have E2 : step target_segs (mkst regs1 0x10012ec AF arom) =
        MachineOk (mkst regs2 0x10012f0 AF arom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) TF_10012ec rfl TD_10012ec
      dsimp only [regs1]
      getr_resolve
      imm_norm
      rw [v_addi_0]
      have hr := aread_str_byte av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi k j Hk (by omega)
      rw [hj, byte_at_len] at hr
      simpa only [hj] using hr
    have E3 : step target_segs (mkst regs2 0x10012f0 AF arom) =
        MachineOk (mkst regs3 0x10012f4 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10012f0 rfl TD_10012f0 rfl
      dsimp only [regs2, regs1]
      getr_resolve
      rw [Hr11]
      exact v_addi_Sj j (by omega)
    have E4 : step target_segs (mkst regs3 0x10012f4 AF arom) =
        MachineOk (mkst regs3 0x10012f8 AF arom) := by
      apply step_bne_ft _ _ _ _ _ _ _ _ _ TF_10012f4 rfl TD_10012f4
      dsimp only [regs3, regs2]
      getr_resolve
      exact c_eq_0_true
    refine ⟨regs3, ?_, ?_, ?_⟩
    · intro r h11 h12
      dsimp only [regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ h11, regupd_other _ _ _ _ h12, regupd_other _ _ _ _ h12]
    · dsimp only [regs3]; rw [regupd_same, hj]
    · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
        (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4 (msteps.mst_refl _))))
  | succ d ih =>
    have hj : j < (av.getD k []).length := by omega
    let b := byte_at (av.getD k []) j
    have hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ hsnz hj
    let regs1 := regupd regs 12 (cat_argv_ptr asp av ev k + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 11 (nat_to_word (j + 1))
    have E1 : step target_segs (mkst regs 0x10012e8 AF arom) =
        MachineOk (mkst regs1 0x10012ec AF arom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ TF_10012e8 rfl TD_10012e8 rfl
      getr_resolve
      rw [Hr10, Hr11, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm]
    have E2 : step target_segs (mkst regs1 0x10012ec AF arom) =
        MachineOk (mkst regs2 0x10012f0 AF arom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ b TF_10012ec rfl TD_10012ec
      dsimp only [regs1]
      getr_resolve
      imm_norm
      rw [v_addi_0]
      exact aread_str_byte av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi k j Hk (by omega)
    have E3 : step target_segs (mkst regs2 0x10012f0 AF arom) =
        MachineOk (mkst regs3 0x10012f4 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10012f0 rfl TD_10012f0 rfl
      dsimp only [regs2, regs1]
      getr_resolve
      rw [Hr11]
      exact v_addi_Sj j (by omega)
    have E4 : step target_segs (mkst regs3 0x10012f4 AF arom) =
        MachineOk (mkst regs3 0x10012e8 AF arom) := by
      apply step_bne_tk _ _ _ _ _ _ _ _ _ TF_10012f4 rfl TD_10012f4
      dsimp only [regs3, regs2]
      getr_resolve
      apply c_eq_0_false
      rw [u_zext8]
      exact byte_nz_u b hbnz
    have h10' : reg_get regs3 10 = cat_argv_ptr asp av ev k := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr10
    obtain ⟨regs', hag, h11, hms⟩ := ih (j + 1) regs3 (by omega) h10' (regupd_same _ _ _)
    refine ⟨regs', ?_, h11, ?_⟩
    · intro r h11' h12'
      rw [hag r h11' h12']
      dsimp only [regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ h11', regupd_other _ _ _ _ h12', regupd_other _ _ _ _ h12']
    · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
        (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4 hms)))


theorem aslen (k : Nat) (RA : word) (regs : bvmap 5 word) (Hk : k < av.length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr asp av ev k)
    (Hr1 : reg_get regs 1 = RA) (Hvj : v_jalr RA 0 = RA) :
    ∃ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (av.getD k []).length ∧
      msteps target_segs (mkst regs 0x10012e4 AF arom) (mkst regs' RA AF arom) := by
  have hslen := valid_argv_str_len av k Hva Hk
  let regs1 := regupd regs 11 (nat_to_word 0)
  have E1 : step target_segs (mkst regs 0x10012e4 AF arom) =
      MachineOk (mkst regs1 0x10012e8 AF arom) := by
    apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10012e4 rfl TD_10012e4 rfl
    getr_resolve; rfl
  have h10 : reg_get regs1 10 = cat_argv_ptr asp av ev k := by
    dsimp only [regs1]; regupd_resolve; exact Hr10
  obtain ⟨regsL, hag, h11, hms⟩ := aslen_loop av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi
    k Hk (av.getD k []).length 0 regs1 (by omega) h10 (regupd_same _ _ _)
  let regsR := regupd regsL 10 (nat_to_word (av.getD k []).length)
  have E2 : step target_segs (mkst regsL 0x10012f8 AF arom) =
      MachineOk (mkst regsR 0x10012fc AF arom) := by
    apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10012f8 rfl TD_10012f8 rfl
    getr_resolve; rw [h11]
    imm_norm
    rw [← v_addi_Sj _ (by omega)]
    change v_addi (nat_to_word (av.getD k []).length + 1) (-1) = _
    exact v_addi_pred _
  have E3 : step target_segs (mkst regsR 0x10012fc AF arom) =
      MachineOk (mkst regsR RA AF arom) := by
    rw [step_jalr_x0 _ _ _ _ _ _ _ _ RA TF_10012fc rfl TD_10012fc (by
      dsimp only [regsR]; getr_resolve
      rw [hag 1 (by decide) (by decide)]
      dsimp only [regs1]; regupd_resolve; exact Hr1)]
    imm_norm; rw [Hvj]
  refine ⟨regsR, ?_, regupd_same _ _ _, ?_⟩
  · intro r h10 h11 h12
    dsimp only [regsR]
    rw [regupd_other _ _ _ _ h10, hag r h11 h12]
    exact regupd_other _ _ _ _ h11
  · exact msteps.mst_step _ _ _ rfl E1 (msteps_trans _ _ _ _ hms
      (msteps.mst_step _ _ _ rfl E2 (msteps.mst_step _ _ _ rfl E3 (msteps.mst_refl _))))


local macro "ga_step " h:term : tactic =>
  `(tactic| (chain_step; exact rfl; exact $h; norm_pc))

/- The put-style write-all retry loop is register-only. Memory and the
registers outside a0/a1/a2 carry through; blez a0's error arm is dead because
each delivery is nonempty. -/
omit Hva Hve Hsp_lo Hsp_hi in
theorem tput_wall (K : machine_state → Prop) (fuel : Nat)
    (rest : List byte) (p RA : word) (n : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) < 2 ^ 63)
    (H1 : reg_get regs 1 = RA) (Hvj : v_jalr RA 0 = RA)
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H11 : reg_get regs 11 = p) (H12 : reg_get regs 12 = len_word rest)
    (H17 : bv_unsigned (reg_get regs 17) = 64) (H17w : reg_get regs 17 = Z_to_bv 64 64)
    (Hread : rdn target_segs mem p rest.length = some rest)
    (Hcont : ∀ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      reg_get regs' 10 = Z_to_bv 64 0 → K (mkst regs' RA mem arom)) :
    to_wall_tail target_segs (Z_to_bv 64 1) (mkst regs 0x10012c4 mem arom) (rest.drop n) K := by
  induction fuel generalizing rest p RA n regs mem with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn n rest Hn2 (by omega)
    ga_step (step_bge_ft _ _ _ _ _ _ _ _ _ TF_10012c4 rfl TD_10012c4 (by
      getr_resolve; rw [H10]; apply c_lts_0_pos <;> rw [hu] <;> omega))
    stepiv TF_10012c8 TD_10012c8 (p + nat_to_word n)
      (getr_resolve; rw [H11, H10]; exact v_add_len_firstn p n rest Hn2)
    stepiv TF_10012cc TD_10012cc (len_word (rest.drop n))
      (getr_resolve; rw [H12, H10]; exact v_sub_len_firstn n rest Hn2 (by omega))
    by_cases heq : n = rest.length
    · subst n
      rw [List.drop_length]
      ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_10012d0 rfl TD_10012d0 (by
        getr_resolve; exact c_eq_0_of_u _ rfl))
      stepiv TF_10012d4 TD_10012d4 (Z_to_bv 64 0) (getr_resolve; bveq)
      stepjr TF_10012d8 TD_10012d8 RA (getr_resolve; exact H1)
      imm_norm; rw [Hvj]
      apply to_wall_tail.twt_done
      apply Hcont
      · intro r h10 h11 h12 h17
        repeat (rw [regupd_other _ _ _ _ (by assumption)])
      · regupd_resolve; rfl
    · have hdu := u_len_word (rest.drop n) (by rw [List.length_drop]; omega)
      have hsk := rdn_skipn target_segs mem rest.length p rest n Hread Hn2
      have hread' : rdn target_segs mem (p + nat_to_word n) (rest.drop n).length =
          some (rest.drop n) := by simpa only [List.length_drop] using hsk
      ga_step (step_bne_tk _ _ _ _ _ _ _ _ _ TF_10012d0 rfl TD_10012d0 (by
        getr_resolve; apply c_eq_0_false; rw [hdu, List.length_drop]; omega))
      stepiv TF_10012bc TD_10012bc (Z_to_bv 64 1) (getr_resolve; bveq)
      ga_step (step_ecall _ _ _ _ _ _ TF_10012c0 rfl)
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      apply twl_write_rec
      · getr_resolve; exact H17
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem (p + nat_to_word n) (word_to_nat (len_word (rest.drop n))) = _
        have hw : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          rw [← of_nat_word_to_nat] at hdu; omega
        rw [hw]; exact hread'
      · rw [List.length_drop]; omega
      · intro m hm1 hm2
        norm_pc
        apply ih (rest.drop n) (p + nat_to_word n) RA m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · regupd_resolve; exact H1
        · exact Hvj
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact H17
        · regupd_resolve; exact H17w
        · exact hread'
        · intro regs'' hag h0
          apply Hcont _ _ h0
          intro r h10 h11 h12 h17
          rw [hag r h10 h11 h12 h17]
          repeat (rw [regupd_other _ _ _ _ (by assumption)])


omit Hva Hve Hsp_lo Hsp_hi in
/-- put(buf, len), with len ≥ 1: write with retries and return zero to ra. -/
theorem tput_pos (regs : bvmap 5 word) (mem : word → Option byte) (buf : List byte)
    (B L RA : word) (bufs : List (List byte)) (code : word)
    (H10 : reg_get regs 10 = B) (H11 : reg_get regs 11 = L)
    (HL1 : 1 ≤ bv_unsigned L) (HL63 : bv_unsigned L < 2 ^ 63)
    (H1 : reg_get regs 1 = RA) (Hvj : v_jalr RA 0 = RA)
    (Hread : rdn target_segs mem B (word_to_nat L) = some buf)
    (Hcont : ∀ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      reg_get regs' 10 = Z_to_bv 64 0 →
      to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' RA mem arom)) :
    to_wallexit target_segs (Z_to_bv 64 1) (buf :: bufs) code (mkst regs 0x10012ac mem arom) := by
  have hbl := rdn_length _ _ _ _ _ Hread
  have hbufL : (buf.length : Int) = bv_unsigned L := by rw [hbl, of_nat_word_to_nat]
  have hlw : len_word buf = L := by
    apply bv_eq_of_unsigned
    rw [u_len_word buf (by omega), hbufL]
  constructor
  · omega
  stepiv TF_10012ac TD_10012ac L (getr_resolve; rw [H11]; exact v_addi_0 _)
  stepiv TF_10012b0 TD_10012b0 B (getr_resolve; rw [H10]; exact v_addi_0 _)
  stepiv TF_10012b4 TD_10012b4 (Z_to_bv 64 64) (getr_resolve; rfl)
  ga_step (step_beq_ft _ _ _ _ _ _ _ _ _ TF_10012b8 rfl TD_10012b8 (by
    getr_resolve; apply c_eq_0_false; omega))
  stepiv TF_10012bc TD_10012bc (Z_to_bv 64 1) (getr_resolve; rfl)
  ga_step (step_ecall _ _ _ _ _ _ TF_10012c0 rfl)
  apply to_wall_tail.twt_more
  · omega
  apply twl_write_rec
  · getr_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve
    rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    exact Hread
  · omega
  · intro n hn1 hn2
    norm_pc
    apply tput_wall _ buf.length buf B RA n
    · omega
    · exact hn1
    · exact hn2
    · omega
    · regupd_resolve; exact H1
    · exact Hvj
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; exact hlw.symm
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · rw [hbl]; exact Hread
    · intro regs' hag h0
      apply Hcont _ _ h0
      intro r h10 h11 h12 h17
      rw [hag r h10 h11 h12 h17]
      repeat (rw [regupd_other _ _ _ _ (by assumption)])


omit Hva Hve Hsp_lo Hsp_hi in
/-- put(buf, 0) makes no syscall and returns zero to ra. -/
theorem tput_zero (regs : bvmap 5 word) (mem : word → Option byte) (RA : word)
    (bufs : List (List byte)) (code : word)
    (H11 : reg_get regs 11 = Z_to_bv 64 0)
    (H1 : reg_get regs 1 = RA) (Hvj : v_jalr RA 0 = RA)
    (Hcont : ∀ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      reg_get regs' 10 = Z_to_bv 64 0 →
      to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' RA mem arom)) :
    to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs 0x10012ac mem arom) := by
  stepiv TF_10012ac TD_10012ac (Z_to_bv 64 0) (getr_resolve; rw [H11]; exact v_addi_0 _)
  stepi TF_10012b0 TD_10012b0
  stepi TF_10012b4 TD_10012b4
  ga_step (step_beq_tk _ _ _ _ _ _ _ _ _ TF_10012b8 rfl TD_10012b8 (by
    getr_resolve; exact c_eq_0_true))
  stepiv TF_10012d4 TD_10012d4 (Z_to_bv 64 0) (getr_resolve; exact v_addi_0 _)
  stepjr TF_10012d8 TD_10012d8 RA (getr_resolve; exact H1)
  imm_norm; rw [Hvj]
  apply Hcont
  · intro r h10 h11 h12 h17
    repeat (rw [regupd_other _ _ _ _ (by assumption)])
  · regupd_resolve; rfl

/- Rocq v_addi_ptr_S is Common.StepTac.word_add_nat_1: incrementing
pointer-plus-index advances one index, with both sides wrapping identically. -/


/- With a3 = remaining count, a4 = &hay[i+j], and a5 = &pat[j], the
comparison exits at 0x1001248 on a match or 0x100123c at the first mismatch.
It clobbers a3-a7. -/
theorem acmp (k : Nat) (Hk : k < av.length) (H2le : 2 ≤ av.length)
    (i d j : Nat) (regs : bvmap 5 word)
    (Hjd : j + d = (av.getD 1 []).length)
    (Hin : i + (av.getD 1 []).length ≤ (av.getD k []).length)
    (Hr13 : reg_get regs 13 = nat_to_word d)
    (Hr14 : reg_get regs 14 = cat_argv_ptr asp av ev k + nat_to_word (i + j))
    (Hr15 : reg_get regs 15 = cat_argv_ptr asp av ev 1 + nat_to_word j) :
    ∃ regs',
      (∀ r : reg, r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs' r = reg_get regs r) ∧
      msteps target_segs (mkst regs 0x1001220 AF arom)
        (mkst regs' (if prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i + j)
          then 0x1001248 else 0x100123c) AF arom) := by
  have hhlen := valid_argv_str_len av k Hva Hk
  have hplen := valid_argv_str_len av 1 Hva (by omega)
  induction d generalizing i j regs with
  | zero =>
    have E1 : step target_segs (mkst regs 0x1001220 AF arom) =
        MachineOk (mkst regs 0x1001248 AF arom) := by
      apply step_beq_tk _ _ _ _ _ _ _ _ _ TF_1001220 rfl TD_1001220
      getr_resolve; rw [Hr13]; exact c_eq_0_true
    refine ⟨regs, fun _ _ _ _ _ _ => rfl, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega : (av.getD 1 []).length ≤ j)]
    exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_refl _)
  | succ d ih =>
    have hjlt : j < (av.getD 1 []).length := by omega
    have hij : i + j < (av.getD k []).length := by omega
    let bh := byte_at (av.getD k []) (i + j)
    let bp := byte_at (av.getD 1 []) j
    have E1 : step target_segs (mkst regs 0x1001220 AF arom) =
        MachineOk (mkst regs 0x1001224 AF arom) := by
      apply step_beq_ft _ _ _ _ _ _ _ _ _ TF_1001220 rfl TD_1001220
      getr_resolve; rw [Hr13]; apply c_eq_0_false
      rw [u_ntw _ (by omega)]; omega
    let regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned bh))
    have E2 : step target_segs (mkst regs 0x1001224 AF arom) =
        MachineOk (mkst regs1 0x1001228 AF arom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ bh TF_1001224 rfl TD_1001224
      getr_resolve; rw [Hr14]; imm_norm; rw [v_addi_0]
      exact aread_str_byte av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi k (i+j) Hk (by omega)
    let regs2 := regupd regs1 17 (Z_to_bv 64 (bv_unsigned bp))
    have E3 : step target_segs (mkst regs1 0x1001228 AF arom) =
        MachineOk (mkst regs2 0x100122c AF arom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ bp TF_1001228 rfl TD_1001228
      dsimp only [regs1]; getr_resolve; rw [Hr15]; imm_norm; rw [v_addi_0]
      exact aread_str_byte av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi 1 j (by omega) (by omega)
    let regs3 := regupd regs2 15 (cat_argv_ptr asp av ev 1 + nat_to_word (j + 1))
    have E4 : step target_segs (mkst regs2 0x100122c AF arom) =
        MachineOk (mkst regs3 0x1001230 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_100122c rfl TD_100122c rfl
      dsimp only [regs2, regs1]; getr_resolve; rw [Hr15]; imm_norm
      exact word_add_nat_1 _ _
    let regs4 := regupd regs3 14 (cat_argv_ptr asp av ev k + nat_to_word (i + (j + 1)))
    have E5 : step target_segs (mkst regs3 0x1001230 AF arom) =
        MachineOk (mkst regs4 0x1001234 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_1001230 rfl TD_1001230 rfl
      dsimp only [regs3, regs2, regs1]; getr_resolve; rw [Hr14]; imm_norm
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using word_add_nat_1 (cat_argv_ptr asp av ev k) (i + j)
    let regs5 := regupd regs4 13 (nat_to_word d)
    have E6 : step target_segs (mkst regs4 0x1001234 AF arom) =
        MachineOk (mkst regs5 0x1001238 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_1001234 rfl TD_1001234 rfl
      dsimp only [regs4, regs3, regs2, regs1]; getr_resolve; rw [Hr13]; imm_norm
      rw [← v_addi_Sj d (by omega)]
      change v_addi (nat_to_word d + 1) (-1) = _
      exact v_addi_pred _
    have hspec : prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i+j) =
        (bv_eqb bh bp && prefix_eqb ((av.getD 1 []).drop (j+1)) (av.getD k []) (i+j+1)) := by
      rw [skipn_nth (av.getD 1 []) j (Z_to_bv 8 0) hjlt]
      simp only [prefix_eqb, ← nth_lt_byte_at _ _ hjlt]
      rfl
    have hag5 : ∀ r : reg, r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs5 r = reg_get regs r := by
      intro r h13 h14 h15 h16 h17
      dsimp only [regs5, regs4, regs3, regs2, regs1]
      repeat (rw [regupd_other _ _ _ _ (by assumption)])
    cases heqb : bv_eqb bh bp with
    | true =>
      have E7 : step target_segs (mkst regs5 0x1001238 AF arom) =
          MachineOk (mkst regs5 0x1001220 AF arom) := by
        apply step_beq_tk _ _ _ _ _ _ _ _ _ TF_1001238 rfl TD_1001238
        dsimp only [regs5, regs4, regs3, regs2, regs1]; getr_resolve
        rw [c_eq_small, bv_eqb_zext]; exact heqb
      obtain ⟨regs', hag, hms⟩ := ih i (j+1) regs5 (by omega) Hin
        (regupd_same _ _ _)
        (by dsimp only [regs5, regs4]; regupd_resolve; rfl)
        (by dsimp only [regs5, regs4, regs3]; regupd_resolve; rfl)
      refine ⟨regs', ?_, ?_⟩
      · intro r h13 h14 h15 h16 h17
        rw [hag r h13 h14 h15 h16 h17]; exact hag5 r h13 h14 h15 h16 h17
      · rw [hspec, heqb]; simp only [Bool.true_and]
        ga_step E1; ga_step E2; ga_step E3; ga_step E4; ga_step E5; ga_step E6; ga_step E7
        simpa only [Nat.add_assoc] using hms
    | false =>
      have E7 : step target_segs (mkst regs5 0x1001238 AF arom) =
          MachineOk (mkst regs5 0x100123c AF arom) := by
        apply step_beq_ft _ _ _ _ _ _ _ _ _ TF_1001238 rfl TD_1001238
        dsimp only [regs5, regs4, regs3, regs2, regs1]; getr_resolve
        rw [c_eq_small, bv_eqb_zext]; exact heqb
      refine ⟨regs5, hag5, ?_⟩
      rw [hspec, heqb]; simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      ga_step E1; ga_step E2; ga_step E3; ga_step E4; ga_step E5; ga_step E6; ga_step E7
      exact msteps.mst_refl _

/- Rocq word_add_0_r is Common.StepTac.word_add_nat_0: wrapping addition
of the zero natural offset is the identity, without hypotheses. -/


/- At 0x100120c, a1 = i, a2 = &hay[i], a0 = pattern length ≥ 1,
s5 = hay length, and s2 = &pat. The scan exits at 0x1001248 iff a match
occurs at some position ≥ i, otherwise at 0x1001274; it clobbers a1-a7. -/
theorem ascan (k : Nat) (Hk : k < av.length) (H2le : 2 ≤ av.length)
    (f i : Nat) (regs : bvmap 5 word)
    (Hnn1 : 1 ≤ (av.getD 1 []).length)
    (Hnnhn : (av.getD 1 []).length ≤ (av.getD k []).length)
    (Hif : i + f = (av.getD k []).length - (av.getD 1 []).length + 1)
    (Hr11 : reg_get regs 11 = nat_to_word i)
    (Hr12 : reg_get regs 12 = cat_argv_ptr asp av ev k + nat_to_word i)
    (Hr10 : reg_get regs 10 = nat_to_word (av.getD 1 []).length)
    (Hr21 : reg_get regs 21 = nat_to_word (av.getD k []).length)
    (Hr18 : reg_get regs 18 = cat_argv_ptr asp av ev 1) :
    ∃ regs',
      (∀ r : reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs' r = reg_get regs r) ∧
      msteps target_segs (mkst regs 0x100120c AF arom)
        (mkst regs' (if scan_from (av.getD k []) (av.getD 1 []) i f
          then 0x1001248 else 0x1001274) AF arom) := by
  have hhlen := valid_argv_str_len av k Hva Hk
  have hplen := valid_argv_str_len av 1 Hva (by omega)
  induction f generalizing i regs with
  | zero =>
    let regs1 := regupd regs 13 (nat_to_word (i + (av.getD 1 []).length))
    have E1 : step target_segs (mkst regs 0x100120c AF arom) =
        MachineOk (mkst regs1 0x1001210 AF arom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ TF_100120c rfl TD_100120c rfl
      getr_resolve; rw [Hr11, Hr10]; exact v_add_ntw _ _
    have E2 : step target_segs (mkst regs1 0x1001210 AF arom) =
        MachineOk (mkst regs1 0x1001274 AF arom) := by
      apply step_bltu_tk _ _ _ _ _ _ _ _ _ TF_1001210 rfl TD_1001210
      dsimp only [regs1]; getr_resolve; rw [Hr21, c_ltu_ltb]
      rw [u_ntw _ (by omega), u_ntw _ (by omega)]
      exact decide_eq_true (by omega)
    refine ⟨regs1, ?_, ?_⟩
    · intro r h11 h12 h13 h14 h15 h16 h17
      exact regupd_other _ _ _ _ h13
    · ga_step E1; ga_step E2; exact msteps.mst_refl _
  | succ f ih =>
    have hin : i + (av.getD 1 []).length ≤ (av.getD k []).length := by omega
    let regs1 := regupd regs 13 (nat_to_word (i + (av.getD 1 []).length))
    have E1 : step target_segs (mkst regs 0x100120c AF arom) =
        MachineOk (mkst regs1 0x1001210 AF arom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ TF_100120c rfl TD_100120c rfl
      getr_resolve; rw [Hr11, Hr10]; exact v_add_ntw _ _
    have E2 : step target_segs (mkst regs1 0x1001210 AF arom) =
        MachineOk (mkst regs1 0x1001214 AF arom) := by
      apply step_bltu_ft _ _ _ _ _ _ _ _ _ TF_1001210 rfl TD_1001210
      dsimp only [regs1]; getr_resolve; rw [Hr21, c_ltu_ltb]
      rw [u_ntw _ (by omega), u_ntw _ (by omega)]
      exact decide_eq_false (by omega)
    let regs2 := regupd regs1 13 (nat_to_word (av.getD 1 []).length)
    have E3 : step target_segs (mkst regs1 0x1001214 AF arom) =
        MachineOk (mkst regs2 0x1001218 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_1001214 rfl TD_1001214 rfl
      dsimp only [regs1]; getr_resolve; rw [Hr10]; exact v_addi_0 _
    let regs3 := regupd regs2 14 (cat_argv_ptr asp av ev k + nat_to_word (i + 0))
    have E4 : step target_segs (mkst regs2 0x1001218 AF arom) =
        MachineOk (mkst regs3 0x100121c AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_1001218 rfl TD_1001218 rfl
      dsimp only [regs2, regs1]; getr_resolve; rw [Hr12]; exact v_addi_0 _
    let regs4 := regupd regs3 15 (cat_argv_ptr asp av ev 1 + nat_to_word 0)
    have E5 : step target_segs (mkst regs3 0x100121c AF arom) =
        MachineOk (mkst regs4 0x1001220 AF arom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_100121c rfl TD_100121c rfl
      dsimp only [regs3, regs2, regs1]; getr_resolve; rw [Hr18, word_add_nat_0]
      exact v_addi_0 _
    obtain ⟨regsC, hagC, hmsC⟩ := acmp av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi
      k Hk H2le i (av.getD 1 []).length 0 regs4 (by omega) hin
      (by dsimp only [regs4, regs3, regs2]; regupd_resolve; rfl)
      (by dsimp only [regs4, regs3]; regupd_resolve; rfl)
      (regupd_same _ _ _)
    simp only [List.drop_zero, Nat.add_zero] at hmsC
    have hagC' : ∀ r : reg, r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regsC r = reg_get regs r := by
      intro r h13 h14 h15 h16 h17
      rw [hagC r h13 h14 h15 h16 h17]
      dsimp only [regs4, regs3, regs2, regs1]
      repeat (rw [regupd_other _ _ _ _ (by assumption)])
    simp only [scan_from]
    by_cases hpre : prefix_eqb (av.getD 1 []) (av.getD k []) i = true
    · simp only [hpre] at hmsC ⊢
      refine ⟨regsC, fun r _ _ h13 h14 h15 h16 h17 => hagC' r h13 h14 h15 h16 h17, ?_⟩
      simp only [Bool.true_or, ↓reduceIte] at hmsC ⊢
      ga_step E1; ga_step E2; ga_step E3; ga_step E4; ga_step E5; exact hmsC
    · have hpre : prefix_eqb (av.getD 1 []) (av.getD k []) i = false := by
        cases h : prefix_eqb (av.getD 1 []) (av.getD k []) i
        · rfl
        · exact False.elim (hpre h)
      simp only [hpre] at hmsC ⊢
      simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hmsC ⊢
      let regsD := regupd regsC 11 (nat_to_word (i + 1))
      have E6 : step target_segs (mkst regsC 0x100123c AF arom) =
          MachineOk (mkst regsD 0x1001240 AF arom) := by
        apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_100123c rfl TD_100123c rfl
        getr_resolve
        rw [hagC' 11 (by decide) (by decide) (by decide) (by decide) (by decide), Hr11]
        exact v_addi_Sj i (by omega)
      let regsE := regupd regsD 12 (cat_argv_ptr asp av ev k + nat_to_word (i + 1))
      have E7 : step target_segs (mkst regsD 0x1001240 AF arom) =
          MachineOk (mkst regsE 0x1001244 AF arom) := by
        apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_1001240 rfl TD_1001240 rfl
        dsimp only [regsD]; getr_resolve
        rw [hagC' 12 (by decide) (by decide) (by decide) (by decide) (by decide), Hr12]
        exact word_add_nat_1 _ _
      have E8 : step target_segs (mkst regsE 0x1001244 AF arom) =
          MachineOk (mkst regsE 0x100120c AF arom) :=
        step_jal_x0 _ _ _ _ _ _ _ TF_1001244 rfl TD_1001244
      have hagE : ∀ r : reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
          reg_get regsE r = reg_get regs r := by
        intro r h11 h12 h13 h14 h15 h16 h17
        dsimp only [regsE, regsD]
        rw [regupd_other _ _ _ _ h12, regupd_other _ _ _ _ h11]
        exact hagC' r h13 h14 h15 h16 h17
      obtain ⟨regs', hag', hms'⟩ := ih (i+1) regsE (by omega)
        (by dsimp only [regsE, regsD]; regupd_resolve; rfl) (regupd_same _ _ _)
        (by rw [hagE 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact Hr10)
        (by rw [hagE 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact Hr21)
        (by rw [hagE 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact Hr18)
      refine ⟨regs', ?_, ?_⟩
      · intro r h11 h12 h13 h14 h15 h16 h17
        rw [hag' r h11 h12 h13 h14 h15 h16 h17]; exact hagE r h11 h12 h13 h14 h15 h16 h17
      · ga_step E1; ga_step E2; ga_step E3; ga_step E4; ga_step E5
        apply msteps_trans _ _ _ _ hmsC
        ga_step E6; ga_step E7; ga_step E8; exact hms'


/- The match path writes argv[i] (skipping an empty argument's write),
then a newline, via put. Both return a0 = 0. It clobbers ra, a0-a2, a7,
and s4, which receives 3. -/
theorem aoutput (i : Nat) (regs : bvmap 5 word) (bufs : List (List byte)) (code : word)
    (Hi : i < av.length) (Hr20 : reg_get regs 20 = cat_argv_ptr asp av ev i)
    (Hr21 : reg_get regs 21 = nat_to_word (av.getD i []).length)
    (Hr19 : reg_get regs 19 = (0x1000158 : word))
    (Hcont : ∀ regs',
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 17 → r ≠ 20 →
        reg_get regs' r = reg_get regs r) →
      to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' 0x1001274 AF arom)) :
    to_wallexit target_segs (Z_to_bv 64 1)
      ((match av.getD i [] with | [] => [[Z_to_bv 8 10]] | _ => [av.getD i [], [Z_to_bv 8 10]]) ++ bufs)
      code (mkst regs 0x1001248 AF arom) := by
  have hslen := valid_argv_str_len av i Hva Hi
  cases Ea : av.getD i [] with
  | nil =>
    simp only [Ea, List.length_nil] at Hr21
    simp only [List.cons_append, List.nil_append]
    stepi TF_1001248 TD_1001248
    stepi TF_100124c TD_100124c
    stepi TF_1001250 TD_1001250
    stepjr TF_1001254 TD_1001254 (0x1001250 : word) (getr_resolve; bveq)
    apply tput_zero (RA := (0x1001258 : word))
    · regupd_resolve; getr_resolve; rw [Hr21]; bveq
    · regupd_resolve; bveq
    · bveq
    · intro regs1 hag1 h10_1
      stepi TF_1001258 TD_1001258
      ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_100125c rfl TD_100125c (by
        getr_resolve; rw [h10_1]; exact c_eq_0_true))
      stepi TF_1001260 TD_1001260
      stepi TF_1001264 TD_1001264
      stepi TF_1001268 TD_1001268
      stepjr TF_100126c TD_100126c (0x1001268 : word) (getr_resolve; bveq)
      apply tput_pos (B := (0x1000158 : word)) (L := Z_to_bv 64 1)
        (buf := [Z_to_bv 8 10]) (RA := (0x1001270 : word))
      · regupd_resolve; getr_resolve
        rw [hag1 19 (by decide) (by decide) (by decide) (by decide)]
        regupd_resolve; rw [Hr19]; exact v_addi_0 _
      · regupd_resolve; getr_resolve; bveq
      · decide
      · decide
      · regupd_resolve; bveq
      · bveq
      · exact aread_newline av ev uid hw asp arnd Hsp_lo Hsp_hi
      · intro regs2 hag2 h10_2
        ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001270 rfl TD_1001270 (by
          getr_resolve; rw [h10_2]; exact c_eq_0_true))
        apply Hcont
        intro r h1 h10 h11 h12 h17 h20
        rw [hag2 r h10 h11 h12 h17]
        repeat (rw [regupd_other _ _ _ _ (by assumption)])
        rw [hag1 r h10 h11 h12 h17]
        repeat (rw [regupd_other _ _ _ _ (by assumption)])
  | cons b0 srest =>
    have hnn : 1 ≤ (av.getD i []).length := by rw [Ea]; exact Nat.succ_le_succ (Nat.zero_le _)
    simp only [List.cons_append, List.nil_append]
    rw [← Ea]
    stepi TF_1001248 TD_1001248
    stepi TF_100124c TD_100124c
    stepi TF_1001250 TD_1001250
    stepjr TF_1001254 TD_1001254 (0x1001250 : word) (getr_resolve; bveq)
    apply tput_pos (B := cat_argv_ptr asp av ev i) (L := nat_to_word (av.getD i []).length)
      (buf := av.getD i []) (RA := (0x1001258 : word))
    · regupd_resolve; getr_resolve; rw [Hr20]; exact v_addi_0 _
    · regupd_resolve; getr_resolve; rw [Hr21]; exact v_addi_0 _
    · rw [u_ntw _ (by omega)]; omega
    · rw [u_ntw _ (by omega)]; omega
    · regupd_resolve; bveq
    · bveq
    · rw [word_to_nat_ntw _ (by omega)]
      exact aread_str av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i Hi
    · intro regs1 hag1 h10_1
      stepi TF_1001258 TD_1001258
      ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_100125c rfl TD_100125c (by
        getr_resolve; rw [h10_1]; exact c_eq_0_true))
      stepi TF_1001260 TD_1001260
      stepi TF_1001264 TD_1001264
      stepi TF_1001268 TD_1001268
      stepjr TF_100126c TD_100126c (0x1001268 : word) (getr_resolve; bveq)
      apply tput_pos (B := (0x1000158 : word)) (L := Z_to_bv 64 1)
        (buf := [Z_to_bv 8 10]) (RA := (0x1001270 : word))
      · regupd_resolve; getr_resolve
        rw [hag1 19 (by decide) (by decide) (by decide) (by decide)]
        regupd_resolve; rw [Hr19]; exact v_addi_0 _
      · regupd_resolve; getr_resolve; bveq
      · decide
      · decide
      · regupd_resolve; bveq
      · bveq
      · exact aread_newline av ev uid hw asp arnd Hsp_lo Hsp_hi
      · intro regs2 hag2 h10_2
        ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001270 rfl TD_1001270 (by
          getr_resolve; rw [h10_2]; exact c_eq_0_true))
        apply Hcont
        intro r h1 h10 h11 h12 h17 h20
        rw [hag2 r h10 h11 h12 h17]
        repeat (rw [regupd_other _ _ _ _ (by assumption)])
        rw [hag1 r h10 h11 h12 h17]
        repeat (rw [regupd_other _ _ _ _ (by assumption)])


/-- One argument: 0x10011d4 to 0x1001274. -/
theorem target_arg (i : Nat) (regs : bvmap 5 word) (bufs : List (List byte)) (code : word)
    (H2le : 2 ≤ av.length) (H2i : 2 ≤ i) (Hi : i < av.length)
    (Hr8 : reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8))
    (Hr9 : reg_get regs 9 = aargcN av)
    (Hr18 : reg_get regs 18 = cat_argv_ptr asp av ev 1)
    (Hr19 : reg_get regs 19 = (0x1000158 : word))
    (Hr22 : reg_get regs 22 = nat_to_word i)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50))
    (Hcont : ∀ regs',
      reg_get regs' 8 = Z_to_bv 64 (bv_unsigned asp + 8) → reg_get regs' 9 = aargcN av →
      reg_get regs' 18 = cat_argv_ptr asp av ev 1 → reg_get regs' 19 = (0x1000158 : word) →
      reg_get regs' 22 = nat_to_word i → reg_get regs' 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) →
      to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' 0x1001274 AF arom)) :
    to_wallexit target_segs (Z_to_bv 64 1) (arg_bufs (av.getD 1 []) (av.getD i []) ++ bufs)
      code (mkst regs 0x10011d4 AF arom) := by
  have hargc := valid_argv_len av Hva
  have hhlen := valid_argv_str_len av i Hva Hi
  have hplen := valid_argv_str_len av 1 Hva (by omega)
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  -- Index argv and load the argument pointer.
  let regs1 := regupd regs 10 (Z_to_bv 64 (8 * (i : Int)))
  have E1 : step target_segs (mkst regs 0x10011d4 AF arom) =
      MachineOk (mkst regs1 0x10011d8 AF arom) := by
    apply step_slli_at _ _ _ _ _ _ _ _ _ _ TF_10011d4 rfl TD_10011d4 rfl
    getr_resolve; rw [Hr22]; exact v_slli3_nat i (by omega)
  let regs2 := regupd regs1 10 (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (i : Int)))
  have E2 : step target_segs (mkst regs1 0x10011d8 AF arom) =
      MachineOk (mkst regs2 0x10011dc AF arom) := by
    apply step_add_at _ _ _ _ _ _ _ _ _ _ TF_10011d8 rfl TD_10011d8 rfl
    dsimp only [regs1]; getr_resolve; rw [Hr8]
    apply bv_eq_of_unsigned
    rw [v_add_small _ _ (by u_norm; omega)]; u_norm; rfl
  let regs3 := regupd regs2 20 (cat_argv_ptr asp av ev i)
  have E3 : step target_segs (mkst regs2 0x10011dc AF arom) =
      MachineOk (mkst regs3 0x10011e0 AF arom) := by
    apply step_ld _ _ _ _ _ _ _ _ _ (word_le8 (cat_argv_ptr asp av ev i))
      (cat_argv_ptr asp av ev i) TF_10011dc rfl TD_10011dc
    · dsimp only [regs2]; getr_resolve; imm_norm; rw [v_addi_0]
      exact aread_ptr av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i Hi
    · exact bytes_le_n_to_le_8 _
  let regs4 := regupd regs3 10 (cat_argv_ptr asp av ev i)
  have E4 : step target_segs (mkst regs3 0x10011e0 AF arom) =
      MachineOk (mkst regs4 0x10011e4 AF arom) := by
    apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10011e0 rfl TD_10011e0 rfl
    dsimp only [regs3]; getr_resolve; exact v_addi_0 _
  let regs5 := regupd regs4 1 (0x10011e4 : word)
  have E5 : step target_segs (mkst regs4 0x10011e4 AF arom) =
      MachineOk (mkst regs5 0x10011e8 AF arom) :=
    step_auipc _ _ _ _ _ _ _ _ TF_10011e4 rfl TD_10011e4
  let regs6 := regupd regs5 1 (0x10011ec : word)
  have E6 : step target_segs (mkst regs5 0x10011e8 AF arom) =
      MachineOk (mkst regs6 0x10012e4 AF arom) := by
    apply step_jalr_link _ _ _ _ _ _ _ _ _ (0x10011e4 : word) TF_10011e8 rfl TD_10011e8 rfl
    dsimp only [regs5]; getr_resolve; rfl
  -- slen(argv[i]).
  obtain ⟨regsH, hagH, h10H, hmsH⟩ := aslen av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi
    i 0x10011ec regs6 Hi
    (by dsimp only [regs6, regs5, regs4]; regupd_resolve; rfl) (regupd_same _ _ _) (by bveq)
  let regs7 := regupd regsH 21 (nat_to_word (av.getD i []).length)
  have E7 : step target_segs (mkst regsH 0x10011ec AF arom) =
      MachineOk (mkst regs7 0x10011f0 AF arom) := by
    apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10011ec rfl TD_10011ec rfl
    getr_resolve; rw [h10H]; exact v_addi_0 _
  let regs8 := regupd regs7 10 (cat_argv_ptr asp av ev 1)
  have E8 : step target_segs (mkst regs7 0x10011f0 AF arom) =
      MachineOk (mkst regs8 0x10011f4 AF arom) := by
    apply step_addi_at _ _ _ _ _ _ _ _ _ _ TF_10011f0 rfl TD_10011f0 rfl
    dsimp only [regs7]; getr_resolve
    rw [hagH 18 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve; rw [Hr18]; exact v_addi_0 _
  let regs9 := regupd regs8 1 (0x10011f4 : word)
  have E9 : step target_segs (mkst regs8 0x10011f4 AF arom) =
      MachineOk (mkst regs9 0x10011f8 AF arom) :=
    step_auipc _ _ _ _ _ _ _ _ TF_10011f4 rfl TD_10011f4
  let regs10 := regupd regs9 1 (0x10011fc : word)
  have E10 : step target_segs (mkst regs9 0x10011f8 AF arom) =
      MachineOk (mkst regs10 0x10012e4 AF arom) := by
    apply step_jalr_link _ _ _ _ _ _ _ _ _ (0x10011f4 : word) TF_10011f8 rfl TD_10011f8 rfl
    dsimp only [regs9]; getr_resolve; rfl
  -- slen(argv[1]).
  obtain ⟨regsP, hagP, h10P, hmsP⟩ := aslen av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi
    1 0x10011fc regs10 (by omega)
    (by dsimp only [regs10, regs9, regs8]; regupd_resolve; rfl) (regupd_same _ _ _) (by bveq)
  have hmsPre : msteps target_segs (mkst regs 0x10011d4 AF arom) (mkst regsP 0x10011fc AF arom) := by
    ga_step E1; ga_step E2; ga_step E3; ga_step E4; ga_step E5; ga_step E6
    apply msteps_trans _ _ _ _ hmsH
    ga_step E7; ga_step E8; ga_step E9; ga_step E10
    exact hmsP
  -- Transport the loop invariant across both calls.
  have H20P : reg_get regsP 20 = cat_argv_ptr asp av ev i := by
    rw [hagP 20 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 20 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    rfl
  have H21P : reg_get regsP 21 = nat_to_word (av.getD i []).length := by
    rw [hagP 21 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rfl
  have H18P : reg_get regsP 18 = cat_argv_ptr asp av ev 1 := by
    rw [hagP 18 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 18 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr18
  have H19P : reg_get regsP 19 = (0x1000158 : word) := by
    rw [hagP 19 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 19 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr19
  have H22P : reg_get regsP 22 = nat_to_word i := by
    rw [hagP 22 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 22 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr22
  have H2P : reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) := by
    rw [hagP 2 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 2 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr2
  have H8P : reg_get regsP 8 = Z_to_bv 64 (bv_unsigned asp + 8) := by
    rw [hagP 8 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 8 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr8
  have H9P : reg_get regsP 9 = aargcN av := by
    rw [hagP 9 (by decide) (by decide) (by decide)]
    dsimp only [regs10, regs9, regs8, regs7]
    regupd_resolve
    rw [hagH 9 (by decide) (by decide) (by decide)]
    dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
    regupd_resolve
    exact Hr9
  -- Empty pattern, a scan, or a pattern longer than the argument.
  by_cases hnn0 : (av.getD 1 []).length = 0
  · have hc : contains_b (av.getD i []) (av.getD 1 []) = true := by
      simp only [contains_b, hnn0, ↓reduceIte]
    simp only [arg_bufs, hc, ↓reduceIte]
    apply msteps_to_wallexit _ _ _ _ _ _ hmsPre
    ga_step (step_beq_tk _ _ _ _ _ _ _ _ _ TF_10011fc rfl TD_10011fc (by
      getr_resolve; rw [h10P, hnn0]; exact c_eq_0_true))
    apply aoutput av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i _ bufs code Hi H20P H21P H19P
    intro regsF hagF
    apply Hcont
    · rw [hagF 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H8P
    · rw [hagF 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H9P
    · rw [hagF 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H18P
    · rw [hagF 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H19P
    · rw [hagF 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H22P
    · rw [hagF 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H2P
  · have hnn1 : 1 ≤ (av.getD 1 []).length := by omega
    by_cases hle : (av.getD 1 []).length ≤ (av.getD i []).length
    · have hc : contains_b (av.getD i []) (av.getD 1 []) =
          scan_from (av.getD i []) (av.getD 1 []) 0 ((av.getD i []).length - (av.getD 1 []).length + 1) := by
        simp only [contains_b, hnn0, show ¬ (av.getD i []).length < (av.getD 1 []).length from by omega, ↓reduceIte]
      let regsQ1 := regupd regsP 11 (nat_to_word 0)
      let regsQ2 := regupd regsQ1 12 (cat_argv_ptr asp av ev i)
      have hmsQ : msteps target_segs (mkst regsP 0x10011fc AF arom) (mkst regsQ2 0x100120c AF arom) := by
        ga_step (step_beq_ft _ _ _ _ _ _ _ _ _ TF_10011fc rfl TD_10011fc (by
          getr_resolve; rw [h10P]; apply c_eq_0_false; rw [u_ntw _ (by omega)]; omega))
        ga_step (step_bltu_ft _ _ _ _ _ _ _ _ _ TF_1001200 rfl TD_1001200 (by
          getr_resolve; rw [H21P, h10P, c_ltu_ltb, u_ntw _ (by omega), u_ntw _ (by omega)]
          exact decide_eq_false (by omega)))
        stepiv TF_1001204 TD_1001204 (nat_to_word 0) (getr_resolve; bveq)
        stepiv TF_1001208 TD_1001208 (cat_argv_ptr asp av ev i) (getr_resolve; rw [H20P]; exact v_addi_0 _)
        exact msteps.mst_refl _
      obtain ⟨regsS, hagS, hmsS⟩ := ascan av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi
        i Hi H2le ((av.getD i []).length - (av.getD 1 []).length + 1) 0 regsQ2 hnn1 hle (by omega)
        (by dsimp only [regsQ2, regsQ1]; regupd_resolve; rfl)
        (by dsimp only [regsQ2]; rw [regupd_same, word_add_nat_0])
        (by dsimp only [regsQ2, regsQ1]; regupd_resolve; exact h10P)
        (by dsimp only [regsQ2, regsQ1]; regupd_resolve; exact H21P)
        (by dsimp only [regsQ2, regsQ1]; regupd_resolve; exact H18P)
      have hagS' : ∀ r : reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
          reg_get regsS r = reg_get regsP r := by
        intro r h11 h12 h13 h14 h15 h16 h17
        rw [hagS r h11 h12 h13 h14 h15 h16 h17]
        dsimp only [regsQ2, regsQ1]
        rw [regupd_other _ _ _ _ h12, regupd_other _ _ _ _ h11]
      unfold arg_bufs
      rw [hc]
      apply msteps_to_wallexit _ _ _ _ _ _ hmsPre
      apply msteps_to_wallexit _ _ _ _ _ _ hmsQ
      apply msteps_to_wallexit _ _ _ _ _ _ hmsS
      cases hsc : scan_from (av.getD i []) (av.getD 1 []) 0 ((av.getD i []).length - (av.getD 1 []).length + 1) with
      | true =>
        simp only [↓reduceIte]
        apply aoutput av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i _ bufs code Hi
        · rw [hagS' 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H20P
        · rw [hagS' 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H21P
        · rw [hagS' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H19P
        · intro regsF hagF
          apply Hcont
          · rw [hagF 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H8P
          · rw [hagF 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H9P
          · rw [hagF 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H18P
          · rw [hagF 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H19P
          · rw [hagF 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H22P
          · rw [hagF 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hagS' 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H2P
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
        apply Hcont
        · rw [hagS' 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H8P
        · rw [hagS' 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H9P
        · rw [hagS' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H18P
        · rw [hagS' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H19P
        · rw [hagS' 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H22P
        · rw [hagS' 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H2P
    · have hc : contains_b (av.getD i []) (av.getD 1 []) = false := by
        simp only [contains_b, hnn0, show (av.getD i []).length < (av.getD 1 []).length from by omega, ↓reduceIte]
      simp only [arg_bufs, hc, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      apply msteps_to_wallexit _ _ _ _ _ _ hmsPre
      ga_step (step_beq_ft _ _ _ _ _ _ _ _ _ TF_10011fc rfl TD_10011fc (by
        getr_resolve; rw [h10P]; apply c_eq_0_false; rw [u_ntw _ (by omega)]; omega))
      ga_step (step_bltu_tk _ _ _ _ _ _ _ _ _ TF_1001200 rfl TD_1001200 (by
        getr_resolve; rw [H21P, h10P, c_ltu_ltb, u_ntw _ (by omega), u_ntw _ (by omega)]
        exact decide_eq_true (by omega)))
      exact Hcont regsP H8P H9P H18P H19P H22P H2P


/-- The outer argument loop. -/
theorem target_loop (m i : Nat) (regs : bvmap 5 word)
    (H2le : 2 ≤ av.length) (H2i : 2 ≤ i) (Him : i + (m + 1) = av.length)
    (Hr8 : reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8))
    (Hr9 : reg_get regs 9 = aargcN av)
    (Hr18 : reg_get regs 18 = cat_argv_ptr asp av ev 1)
    (Hr19 : reg_get regs 19 = (0x1000158 : word))
    (Hr22 : reg_get regs 22 = nat_to_word i)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50)) :
    to_wallexit target_segs (Z_to_bv 64 1) (grep_bufs (av.getD 1 []) (av.drop i))
      (Z_to_bv 64 0) (mkst regs 0x10011d4 AF arom) := by
  have hargc := valid_argv_len av Hva
  have huA : bv_unsigned (aargcN av) = (av.length : Int) := u_argcN av Hva
  induction m generalizing i regs with
  | zero =>
    rw [skipn_nth av i [] (by omega)]
    simp only [grep_bufs, List.flatMap_cons]
    rw [List.drop_eq_nil_of_le (by omega : av.length ≤ i+1)]
    simp only [List.flatMap_nil]
    apply target_arg av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i regs [] (Z_to_bv 64 0)
      H2le H2i (by omega) Hr8 Hr9 Hr18 Hr19 Hr22 Hr2
    intro regs' h8 h9 h18 h19 h22 h2
    -- Bump the index; the final argument falls through to exit zero.
    stepiv TF_1001274 TD_1001274 (nat_to_word (i+1))
      (getr_resolve; rw [h22]; exact v_addi_Sj i (by omega))
    ga_step (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001278 rfl TD_1001278 (by
      getr_resolve; rw [h9, c_eq_small, bv_eqb_Z, u_ntw _ (by omega), huA]
      exact decide_eq_true (by omega)))
    stepiv TF_100127c TD_100127c (Z_to_bv 64 0) (getr_resolve; exact v_addi_0 _)
    apply target_epilogue av ev uid hw asp arnd Hsp_lo Hsp_hi
    · regupd_resolve; exact h2
    · regupd_resolve; rfl
    · decide
  | succ m ih =>
    rw [skipn_nth av i [] (by omega)]
    simp only [grep_bufs, List.flatMap_cons]
    apply target_arg av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi i regs _ (Z_to_bv 64 0)
      H2le H2i (by omega) Hr8 Hr9 Hr18 Hr19 Hr22 Hr2
    intro regs' h8 h9 h18 h19 h22 h2
    -- Bump the index and branch back while another argument remains.
    stepiv TF_1001274 TD_1001274 (nat_to_word (i+1))
      (getr_resolve; rw [h22]; exact v_addi_Sj i (by omega))
    ga_step (step_bne_tk _ _ _ _ _ _ _ _ _ TF_1001278 rfl TD_1001278 (by
      getr_resolve; rw [h9, c_eq_small, bv_eqb_Z, u_ntw _ (by omega), huA]
      exact decide_eq_false (by omega)))
    apply ih (i+1)
    · omega
    · omega
    · regupd_resolve; exact h8
    · regupd_resolve; exact h9
    · regupd_resolve; exact h18
    · regupd_resolve; exact h19
    · regupd_resolve; rfl
    · regupd_resolve; exact h2


/- Program entry. Rocq's t_read_argc/t_read_ptr1 scripts read the initial
stack under SymTac. The explicit loads below peel the frame stores already
executed and use the same initial-stack witnesses. -/
theorem target_wexit_ge2 (H2le : 2 ≤ av.length) :
    to_wallexit target_segs (Z_to_bv 64 1) (grep_bufs (av.getD 1 []) (av.drop 2)) (Z_to_bv 64 0)
      (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw) := by
  have hargc := valid_argv_len av Hva
  have huA : bv_unsigned (aargcN av) = (av.length : Int) := u_argcN av Hva
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  rw [init_mkst]
  norm_pc
  -- _start's two frame slots and its argc load.
  stepiv TF_100115c TD_100115c (Z_to_bv 64 (bv_unsigned asp - 16))
    (getr_resolve; exact v_addi_m16 asp (by omega))
  stepsd TF_1001160 TD_1001160 (Z_to_bv 64 (bv_unsigned asp - 8)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001164 TD_1001164 (Z_to_bv 64 (bv_unsigned asp - 16)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepiv TF_1001168 TD_1001168 asp
    (getr_resolve; sp_norm; apply bv_eq_of_unsigned; u_norm; omega)
  stepld TF_100116c TD_100116c asp (aargcN av)
    (repeat (rw [rdn_wbytes_disjoint _ _ _ _ _ _
       (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)])
     rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
     exact read_argc _ _ _ _ _ _ _ _ (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi))
  stepiv TF_1001170 TD_1001170 (Z_to_bv 64 (bv_unsigned asp + 8))
    (getr_resolve; sp_norm; rfl)
  stepi TF_1001174 TD_1001174
  stepjr TF_1001178 TD_1001178 (0x1001174 : word) (getr_resolve; bveq)
  -- run's eight slots, in afmem's execution order.
  stepiv TF_1001184 TD_1001184 (Z_to_bv 64 (bv_unsigned asp - 80))
    (getr_resolve; sp_norm; congr 1; omega)
  stepsd TF_1001188 TD_1001188 (Z_to_bv 64 (bv_unsigned asp - 24)) (0x100117c : word)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_100118c TD_100118c (Z_to_bv 64 (bv_unsigned asp - 32)) asp
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001190 TD_1001190 (Z_to_bv 64 (bv_unsigned asp - 40)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001194 TD_1001194 (Z_to_bv 64 (bv_unsigned asp - 48)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001198 TD_1001198 (Z_to_bv 64 (bv_unsigned asp - 56)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_100119c TD_100119c (Z_to_bv 64 (bv_unsigned asp - 64)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_10011a0 TD_10011a0 (Z_to_bv 64 (bv_unsigned asp - 72)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_10011a4 TD_10011a4 (Z_to_bv 64 (bv_unsigned asp - 80)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  change to_wallexit target_segs (Z_to_bv 64 1) _ (Z_to_bv 64 0) (mkst _ _ AF arom)
  stepiv TF_10011a8 TD_10011a8 (Z_to_bv 64 (bv_unsigned asp + 8)) (getr_resolve; exact v_addi_0 _)
  stepiv TF_10011ac TD_10011ac (Z_to_bv 64 1) (getr_resolve; rfl)
  ga_step (step_bltu_tk _ _ _ _ _ _ _ _ _ TF_10011b0 rfl TD_10011b0 (by
    getr_resolve; rw [c_ltu_ltb, huA]; imm_norm; u_norm; exact decide_eq_true (by omega)))
  stepiv TF_10011bc TD_10011bc (aargcN av) (getr_resolve; exact v_addi_0 _)
  stepld TF_10011c0 TD_10011c0 (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (1 : Int)))
    (cat_argv_ptr asp av ev 1)
    (exact aread_ptr av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi 1 (by omega))
  stepiv TF_10011c4 TD_10011c4 (nat_to_word 2) (getr_resolve; rfl)
  stepi TF_10011c8 TD_10011c8
  stepiv TF_10011cc TD_10011cc (0x1000158 : word) (getr_resolve; bveq)
  by_cases hav2 : av.length = 2
  · rw [List.drop_eq_nil_of_le (by omega : av.length ≤ 2)]
    change to_wallexit target_segs (Z_to_bv 64 1) [] _ _
    ga_step (step_beq_tk _ _ _ _ _ _ _ _ _ TF_10011d0 rfl TD_10011d0 (by
      getr_resolve; rw [c_eq_small, bv_eqb_Z, huA, u_ntw _ (by omega)]
      exact decide_eq_true (by omega)))
    stepiv TF_100127c TD_100127c (Z_to_bv 64 0) (getr_resolve; exact v_addi_0 _)
    apply target_epilogue av ev uid hw asp arnd Hsp_lo Hsp_hi
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · decide
  · ga_step (step_beq_ft _ _ _ _ _ _ _ _ _ TF_10011d0 rfl TD_10011d0 (by
      getr_resolve; rw [c_eq_small, bv_eqb_Z, huA, u_ntw _ (by omega)]
      exact decide_eq_false (by omega)))
    apply target_loop av ev uid hw Hva Hve asp arnd Hsp_lo Hsp_hi (av.length-3) 2
    · exact H2le
    · omega
    · omega
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl


/-- Program entry with argc < 2: exit two without output. -/
theorem target_wexit_lt2 (Hlt2 : av.length < 2) :
    to_wallexit target_segs (Z_to_bv 64 1) [] (Z_to_bv 64 2)
      (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw) := by
  have hargc := valid_argv_len av Hva
  have huA : bv_unsigned (aargcN av) = (av.length : Int) := u_argcN av Hva
  have hlo := sp_lo_num asp Hsp_lo
  have hhi := sp_hi_num asp Hsp_hi
  rw [init_mkst]
  norm_pc
  -- _start's two frame slots and its argc load.
  stepiv TF_100115c TD_100115c (Z_to_bv 64 (bv_unsigned asp - 16))
    (getr_resolve; exact v_addi_m16 asp (by omega))
  stepsd TF_1001160 TD_1001160 (Z_to_bv 64 (bv_unsigned asp - 8)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001164 TD_1001164 (Z_to_bv 64 (bv_unsigned asp - 16)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepiv TF_1001168 TD_1001168 asp
    (getr_resolve; sp_norm; apply bv_eq_of_unsigned; u_norm; omega)
  stepld TF_100116c TD_100116c asp (aargcN av)
    (repeat (rw [rdn_wbytes_disjoint _ _ _ _ _ _
       (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)])
     rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
     exact read_argc _ _ _ _ _ _ _ _ (bsb_nw _ _ _ _ _ _ _ Hva Hve Hsp_hi))
  stepiv TF_1001170 TD_1001170 (Z_to_bv 64 (bv_unsigned asp + 8))
    (getr_resolve; sp_norm; rfl)
  stepi TF_1001174 TD_1001174
  stepjr TF_1001178 TD_1001178 (0x1001174 : word) (getr_resolve; bveq)
  -- run's eight slots, in afmem's execution order.
  stepiv TF_1001184 TD_1001184 (Z_to_bv 64 (bv_unsigned asp - 80))
    (getr_resolve; sp_norm; congr 1; omega)
  stepsd TF_1001188 TD_1001188 (Z_to_bv 64 (bv_unsigned asp - 24)) (0x100117c : word)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_100118c TD_100118c (Z_to_bv 64 (bv_unsigned asp - 32)) asp
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001190 TD_1001190 (Z_to_bv 64 (bv_unsigned asp - 40)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001194 TD_1001194 (Z_to_bv 64 (bv_unsigned asp - 48)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_1001198 TD_1001198 (Z_to_bv 64 (bv_unsigned asp - 56)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_100119c TD_100119c (Z_to_bv 64 (bv_unsigned asp - 64)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_10011a0 TD_10011a0 (Z_to_bv 64 (bv_unsigned asp - 72)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  stepsd TF_10011a4 TD_10011a4 (Z_to_bv 64 (bv_unsigned asp - 80)) (Z_to_bv 64 0)
    (getr_resolve; rfl) (solve_store_ok)
  change to_wallexit target_segs (Z_to_bv 64 1) [] (Z_to_bv 64 2) (mkst _ _ AF arom)
  stepiv TF_10011a8 TD_10011a8 (Z_to_bv 64 (bv_unsigned asp + 8)) (getr_resolve; exact v_addi_0 _)
  stepiv TF_10011ac TD_10011ac (Z_to_bv 64 1) (getr_resolve; rfl)
  -- argc ≤ 1: the branch falls through, sets status two, and jumps to the epilogue.
  ga_step (step_bltu_ft _ _ _ _ _ _ _ _ _ TF_10011b0 rfl TD_10011b0 (by
    getr_resolve; rw [c_ltu_ltb, huA]; imm_norm; u_norm; exact decide_eq_false (by omega)))
  stepiv TF_10011b4 TD_10011b4 (Z_to_bv 64 2) (getr_resolve; rfl)
  stepj TF_10011b8 TD_10011b8
  apply target_epilogue av ev uid hw asp arnd Hsp_lo Hsp_hi
  · regupd_resolve; rfl
  · regupd_resolve; rfl
  · decide

end LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_target
