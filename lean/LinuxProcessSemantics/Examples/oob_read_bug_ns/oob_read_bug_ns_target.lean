import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/oob_read_bug_ns/oob_read_bug_ns_target.v` at
the baseline above; see that Rocq file for the argument.  Rocq section
parameters (`av ev uid hw asp arnd` and the hypotheses `Hva Hve Hsp_lo
Hsp_hi Hge2`) are explicit arguments, `Z` becomes `Int`, `nat` becomes
`Nat`, `nth j s d` becomes `s.getD j d`, `firstn`/`skipn` become
`List.take`/`List.drop`, `S n` becomes `n + 1`, and `Forall` becomes
`∀ b ∈ s`.  The Rocq `sym_block` reflective blocks, `sym_regs`,
`sym_close`, `norm_pc`, `tb_read_argc` and `solve_store_ok_inv` are
replaced by `cat_step` chains over the explicit instruction lemmas, with
`cat_regs` for register resolution.

The model facts `m_vmmaps_init_model` and `init_model_fd1chan` the outcomes
file needs live in the defs file.

unported: step_andi_at -- `Common/SeqExec.lean` carries it under the same name; the example reaches that one.
unported: word_add_nat_1 -- `Common/StepTac.lean` carries it under the same name; the example reaches that one.
unported: word_add_nat_m1 -- `Common/StepTac.lean` carries it under the same name; the example reaches that one.
unported: v_addi_natS_m1 -- lives in the defs file.
unported: sumb_nonneg -- lives in the defs file. -/

namespace LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem
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
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.NumPrint
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_code
open LinuxProcessSemantics.Examples.oob_read_bug_ns.TargetMemImage
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

local macro "cat_regs" : tactic =>
  `(tactic| simp (disch := decide) only [getr_nz, getr_zero, regupd_same, regupd_other])

local macro "cat_step " h:term : tactic =>
  `(tactic| first
    | refine to_wexit.tw_step _ _ _ _ rfl $h ?_
    | refine to_wall_tail.twt_step _ _ _ _ rfl $h ?_
    | refine msteps.mst_step _ _ _ rfl $h ?_)

/-- The target's instruction ROM, Rocq's `trom`. -/
def trom : word → Option byte := seg_rom target_segs

theorem v_andi_7_mod8 (x : word) : v_andi x 7 = Z_to_bv 64 (bv_unsigned x % 8) := by
  unfold v_andi
  apply congrArg (Z_to_bv 64)
  change Int.ofNat (x.toNat &&& 7) = (x.toNat : Int) % 8
  have h : x.toNat &&& 7 = x.toNat % 8 :=
    Nat.and_two_pow_sub_one_eq_mod x.toNat 3
  rw [h, Int.ofNat_eq_natCast]
  omega

theorem target_init_pc_val : TargetMemImage_init_pc = 0x100115c := rfl

theorem target_reserved_val :
    segments_reserved target_segs = [(0x1000000, 0x1000), (0x1001000, 0x1000)] := by
  decide +kernel

theorem target_avoids_stack (a : word) (n : Int) (ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true := by
  change ((false || !(decide (0x1000000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x1001000))) &&
    ((false || !(decide (0x1001000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x1002000))) &&
    true)) = true
  have h0 : ¬ bv_unsigned a < 0x1001000 := by omega
  have h1 : ¬ bv_unsigned a < 0x1002000 := by omega
  simp only [h0, h1, decide_false, Bool.and_false, Bool.not_false,
    Bool.false_or, Bool.and_true]

theorem target_free_avoids (b l : word)
    (hfree : region_free (segments_reserved target_segs) b l = true)
    (hl : 0 < bv_unsigned l) (a : word) (k : Int)
    (hlo : bv_unsigned b ≤ bv_unsigned a)
    (hhi : bv_unsigned a + k ≤ bv_unsigned b + bv_unsigned l) :
    range_avoids_ro_segs target_segs (bv_unsigned a) k = true := by
  rw [target_reserved_val] at hfree
  obtain ⟨h0, hrest⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨h1, _⟩ := region_free_cons _ _ _ _ _ hrest
  change bv_unsigned b + bv_unsigned l ≤ 0x1000000 ∨
    0x1001000 ≤ bv_unsigned b at h0
  change bv_unsigned b + bv_unsigned l ≤ 0x1001000 ∨
    0x1002000 ≤ bv_unsigned b at h1
  have hcase : bv_unsigned b + bv_unsigned l ≤ 0x1000000 ∨
      0x1002000 ≤ bv_unsigned b := by omega
  rcases hcase with hbelow | habove
  · change ((false || !(decide (0x1000000 < bv_unsigned a + k) &&
        decide (bv_unsigned a < 0x1001000))) &&
      ((false || !(decide (0x1001000 < bv_unsigned a + k) &&
        decide (bv_unsigned a < 0x1002000))) && true)) = true
    have h0 : ¬ 0x1000000 < bv_unsigned a + k := by omega
    have h1 : ¬ 0x1001000 < bv_unsigned a + k := by omega
    simp only [h0, h1, decide_false, Bool.false_and, Bool.not_false,
      Bool.false_or, Bool.and_true]
  · exact target_avoids_stack a k (by omega)

/-! ## The target run

Rocq's `Section TargetProof`: `av ev uid hw asp arnd` and the hypotheses
`Hva Hve Hsp_lo Hsp_hi` become explicit arguments. -/

theorem asp_lo_num (asp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned asp) :
    0x7fff80000000 ≤ bv_unsigned asp := hsp_lo

theorem asp_hi_num (asp : word) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp ≤ 0x800000000000 := hsp_hi

theorem asp_lt64 (asp : word) : bv_unsigned asp < 2 ^ 64 := (u64_range asp).2

/-- `argc` as the word the stack image carries. -/
def targcN (av : List (List byte)) : word := len_word av

/-- The initial memory of the target run, Rocq's `awmem`. -/
def awmem (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw) :
    word → Option byte :=
  wrap_mem target_phdrs asp av ev uid hw arnd

theorem u_targcN (av : List (List byte)) (hva : valid_argv av) :
    bv_unsigned (targcN av) = (av.length : Int) := by
  have := valid_argv_len av hva
  unfold targcN len_word
  exact u_Z2bv _ (by omega) (by omega)

theorem targcN_le (av : List (List byte)) (hva : valid_argv av) :
    (av.length : Int) ≤ 1024 := valid_argv_len av hva

theorem target_bsb_nw (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp
      + ((build_stack_bytes target_phdrs asp av ev uid hw arnd).length : Int) < 2 ^ 64 := by
  have := bsb_bound target_phdrs asp av ev uid hw arnd hva hve
  have := asp_hi_num asp hsp_hi
  omega

/-- Memory after crt's prologue (`sp = asp - 16`): zeros at `asp-8` and `asp-16`. -/
def amem1 (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw) :
    word → Option byte :=
  wbytes (wbytes (awmem av ev uid hw asp arnd) (Z_to_bv 64 (bv_unsigned asp - 8))
            (word_to_le_bytes 8 (Z_to_bv 64 0)))
         (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))

/-- Memory after main's prologue (`sp = asp - 64`):
`ra = 0x100117c` at `asp-24`, `s0 = asp` at `asp-32`. -/
def tfmem (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw) :
    word → Option byte :=
  wbytes (wbytes (amem1 av ev uid hw asp arnd) (Z_to_bv 64 (bv_unsigned asp - 24))
            (word_to_le_bytes 8 (0x100117c : word)))
         (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp)

theorem rdn_amem1_above (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (n : Nat) (ha : bv_unsigned asp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (amem1 av ev uid hw asp arnd) a n =
      rdn target_segs (awmem av ev uid hw asp arnd) a n := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  unfold amem1
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by
    rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]
    omega) hn]
  exact rdn_wbytes_disjoint _ _ _ _ _ _ (by
    rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]
    omega) hn

theorem rdn_tfmem_above (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (n : Nat) (ha : bv_unsigned asp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (tfmem av ev uid hw asp arnd) a n =
      rdn target_segs (awmem av ev uid hw asp arnd) a n := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  unfold tfmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by
    rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]
    omega) hn]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by
    rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]
    omega) hn]
  exact rdn_amem1_above av ev uid hw asp arnd hsp_lo hsp_hi a n ha hn

theorem rdn_awmem_stack (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (a : word) (n : Nat) (ha : bv_unsigned asp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (awmem av ev uid hw asp arnd) a n =
      rdn target_segs
        (stack_to_mem asp (entry_stack_image target_phdrs asp av ev uid hw arnd)) a n :=
  rdn_wrap_stack_above target_segs target_phdrs asp av ev a n uid hw arnd ha hn

theorem read_argc_a1 (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    rdn target_segs (amem1 av ev uid hw asp arnd) asp 8 = some (word_le8 (targcN av)) := by
  have hhi := asp_hi_num asp hsp_hi
  have hn : bv_unsigned asp + (8 : Int) ≤ 2 ^ 64 := by omega
  rw [rdn_amem1_above av ev uid hw asp arnd hsp_lo hsp_hi asp 8 (by omega) hn,
    rdn_awmem_stack av ev uid hw asp arnd asp 8 (by omega) hn]
  exact read_argc target_phdrs target_segs asp av ev uid hw arnd
    (target_bsb_nw av ev uid hw asp arnd hva hve hsp_hi)

/-- `argv[1]`, Rocq's `targ1`. -/
def targ1 (av : List (List byte)) : List byte := av.getD 1 []

/-- `strlen(argv[1])`, Rocq's `tnn`. -/
def tnn (av : List (List byte)) : Nat := (targ1 av).length

/-- `tnn` as a word, Rocq's `tnN`. -/
def tnN (av : List (List byte)) : word := nat_to_word (tnn av)

/-- The address of `argv[1]`'s bytes, Rocq's `ptrA`. -/
def ptrA (av ev : List (List byte)) (asp : word) : word := cat_argv_ptr asp av ev 1

theorem read_slot_ra_t (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    rdn target_segs (tfmem av ev uid hw asp arnd) (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x100117c : word)) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have h24 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 24)) =
      bv_unsigned asp - 24 := u_Z2bv _ (by omega) (by omega)
  have h32 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 32)) =
      bv_unsigned asp - 32 := u_Z2bv _ (by omega) (by omega)
  unfold tfmem
  rw [rdn_wbytes_disjoint]
  · apply rdn_wbytes_hit8
    rw [h24]
    omega
  · rw [length_N_to_le_bytes, h32, h24]
    omega
  · rw [h24]
    omega

theorem read_slot_s0_t (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    rdn target_segs (tfmem av ev uid hw asp arnd) (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  unfold tfmem
  apply rdn_wbytes_hit8
  rw [u_Z2bv _ (by omega) (by omega)]
  omega

/-- main's epilogue from `0x10011d0` with the exit code in `a3`: the two
frame reloads, the stack pop, `mv a0,a3`, `ret` into crt's `li a7,93` and
the `exit` ecall. -/
theorem target_exit (asp : word)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (h13 : reg_get regs 13 = code) (hc : bv_unsigned code < 256)
    (hra : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x100117c : word)))
    (hs0 : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp)) :
    to_wexit target_segs (mkst regs 0x10011d0 mem trom) [] code := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hu : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) =
      bv_unsigned asp - 64 := u_Z2bv _ (by omega) (by omega)
  cat_step (step_ld target_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (0x100117c : word)) (0x100117c : word)
    TF_10011d0 (by decide) TD_10011d0
    (by
      cat_regs
      rw [h2]
      change rdn target_segs mem
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 40)) 8 = _
      rw [hu, show bv_unsigned asp - 64 + 40 = bv_unsigned asp - 24 by omega]
      exact hra)
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld target_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 asp) asp TF_10011d4 (by decide) TD_10011d4
    (by
      cat_regs
      rw [h2]
      change rdn target_segs mem
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 32)) 8 = _
      rw [hu, show bv_unsigned asp - 64 + 32 = bv_unsigned asp - 32 by omega]
      exact hs0)
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 16)) TF_10011d8 (by decide) TD_10011d8
    (by decide) (by
      cat_regs
      rw [h2]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 48) = _
      rw [hu, show bv_unsigned asp - 64 + 48 = bv_unsigned asp - 16 by omega]))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ code
    TF_10011dc (by decide) TD_10011dc (by decide)
    (by cat_regs; rw [h13]; exact v_addi_0 code))
  cat_step (step_jalr_x0 target_segs _ _ _ _ _ _ _ (0x100117c : word)
    TF_10011e0 (by decide) TD_10011e0 (by cat_regs))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    TF_100117c (by decide) TD_100117c (by decide) (by cat_regs; rfl))
  cat_step (step_ecall target_segs _ _ _ _ _ TF_1001180 (by decide))
  apply tw_exit_coden
  · cat_regs; rfl
  · cat_regs
  · exact hc

/-- `argc < 2`: the entry prologue, the `argc` load, the call into main,
`bltu a2,a0` falling through, exit code 2. -/
theorem target_wexit_lt2 (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hlt2 : av.length < 2) :
    to_wexit target_segs
      (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw)
      [] (Z_to_bv 64 2) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hu16 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 16)) =
      bv_unsigned asp - 16 := u_Z2bv _ (by omega) (by omega)
  have hu8 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 8)) =
      bv_unsigned asp - 8 := u_Z2bv _ (by omega) (by omega)
  have hs8 : store_ok target_segs (awmem av ev uid hw asp arnd)
      (Z_to_bv 64 (bv_unsigned asp - 8)) 8 = true := by
    apply store_ok_wrap_window
    · rw [stack_max_size_val, hu8]; omega
    · rw [hu8]; omega
  have hs16 : store_ok target_segs (awmem av ev uid hw asp arnd)
      (Z_to_bv 64 (bv_unsigned asp - 16)) 8 = true := by
    apply store_ok_wrap_window
    · rw [stack_max_size_val, hu16]; omega
    · rw [hu16]; omega
  rw [init_mkst]
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 16))
    TF_100115c (by decide) TD_100115c (by decide) (by cat_regs; rfl))
  cat_step (step_sd_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 8)) (Z_to_bv 64 0)
    TF_1001160 (by decide) TD_1001160
    (by
      cat_regs
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 16)) + 8) = _
      rw [hu16, show bv_unsigned asp - 16 + 8 = bv_unsigned asp - 8 by omega])
    (by cat_regs; rfl) hs8)
  cat_step (step_sd_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 16)) (Z_to_bv 64 0)
    TF_1001164 (by decide) TD_1001164
    (by cat_regs; exact v_addi_0 _) (by cat_regs; rfl)
    (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _) hs16))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ asp
    TF_1001168 (by decide) TD_1001168 (by decide) (by
      cat_regs
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 16)) + 16) = asp
      rw [hu16, show bv_unsigned asp - 16 + 16 = bv_unsigned asp by omega]
      exact bv_eq_of_unsigned _ _ (u_Z2bv _ (u64_range asp).1 (u64_range asp).2)))
  cat_step (step_ld target_segs _ _ _ _ _ _ _ _
    (word_le8 (targcN av)) (targcN av)
    TF_100116c (by decide) TD_100116c
    (by
      cat_regs
      change rdn target_segs (amem1 av ev uid hw asp arnd) (v_addi asp 0) 8 = _
      rw [v_addi_0]
      exact read_argc_a1 av ev uid hw asp arnd hva hve hsp_lo hsp_hi)
    (bytes_le_n_to_le_8 _))
  simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (v_addi asp 8)
    TF_1001170 (by decide) TD_1001170 (by decide) (by cat_regs; rfl))
  cat_step (step_auipc_at target_segs _ _ _ _ _ _ _ (0x1001174 : word)
    TF_1001174 (by decide) TD_1001174 (by decide) (by rfl))
  cat_step (step_jalr_link target_segs _ _ _ _ _ _ _ _ (0x1001174 : word)
    TF_1001178 (by decide) TD_1001178 (by decide) (by cat_regs))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    TF_1001184 (by decide) TD_1001184 (by decide) (by cat_regs; rfl))
  cat_step (step_bltu_ft target_segs _ _ _ _ _ _ _ _
    TF_1001188 (by decide) TD_1001188 (by
      cat_regs
      rw [c_ltu_ltb, u_targcN av hva]
      change decide ((1 : Int) < (av.length : Int)) = false
      exact decide_eq_false (by omega)))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 2)
    TF_100118c (by decide) TD_100118c (by decide) (by cat_regs; rfl))
  cat_step (step_jal_x0 target_segs _ _ _ _ _ _ TF_1001190 (by decide) TD_1001190)
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 2)
    TF_10011dc (by decide) TD_10011dc (by decide) (by cat_regs; rfl))
  cat_step (step_jalr_x0 target_segs _ _ _ _ _ _ _ (0x100117c : word)
    TF_10011e0 (by decide) TD_10011e0 (by cat_regs; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    TF_100117c (by decide) TD_100117c (by decide) (by cat_regs; rfl))
  cat_step (step_ecall target_segs _ _ _ _ _ TF_1001180 (by decide))
  apply tw_exit_coden
  · cat_regs; rfl
  · cat_regs
  · decide

/-! ### `argc ≥ 2`

Rocq's `Section Ge2MainT`: `Hge2` becomes the explicit `hge2`. -/

theorem tnN_le (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    (tnn av : Int) ≤ 131071 := by
  unfold tnn targ1
  exact valid_argv_str_len av 1 hva (by omega)

theorem u_tnN (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    bv_unsigned (tnN av) = (tnn av : Int) := by
  have := tnN_le av hva hge2
  unfold tnN nat_to_word
  exact u_Z2bv _ (by omega) (by omega)

theorem targ1_nz (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    ¬ Z_to_bv 8 0 ∈ targ1 av := by
  unfold targ1
  exact valid_argv_str_nz av 1 hva (by omega)

theorem targ1_bytes (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    ∀ b ∈ targ1 av, bv_unsigned b < 256 := by
  unfold targ1
  exact valid_argv_str_bytes av 1 hva (by omega)

theorem ptrA_bounds (av ev : List (List byte)) (asp : word)
    (hva : valid_argv av) (hve : valid_envp ev) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned asp ≤ bv_unsigned (ptrA av ev asp) ∧
      bv_unsigned (ptrA av ev asp) + (tnn av : Int) + 1 < 2 ^ 64 := by
  unfold ptrA tnn targ1
  apply argv_ptr_bounds asp av ev 1 hva hve (by omega)
  have := asp_hi_num asp hsp_hi
  unfold argv_layout_slack
  omega

theorem ptrA_lo (av ev : List (List byte)) (asp : word)
    (hva : valid_argv av) (hve : valid_envp ev) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned asp ≤ bv_unsigned (ptrA av ev asp) :=
  (ptrA_bounds av ev asp hva hve hsp_hi hge2).1

theorem ptrA_hi (av ev : List (List byte)) (asp : word)
    (hva : valid_argv av) (hve : valid_envp ev) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned (ptrA av ev asp) + (tnn av : Int) + 1 < 2 ^ 64 :=
  (ptrA_bounds av ev asp hva hve hsp_hi hge2).2

theorem read_str_t (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    rdn target_segs (tfmem av ev uid hw asp arnd) (ptrA av ev asp) (tnn av + 1) =
      some (targ1 av ++ [Z_to_bv 8 0]) := by
  obtain ⟨hlo, hhi⟩ := ptrA_bounds av ev asp hva hve hsp_hi hge2
  have hn : bv_unsigned (ptrA av ev asp) + ((tnn av + 1 : Nat) : Int) ≤ 2 ^ 64 := by
    omega
  rw [rdn_tfmem_above av ev uid hw asp arnd hsp_lo hsp_hi _ _ hlo hn,
    rdn_awmem_stack av ev uid hw asp arnd _ _ hlo hn]
  have hnw := target_bsb_nw av ev uid hw asp arnd hva hve hsp_hi
  apply rdn_app target_segs _ (tnn av) 1
  · exact read_argv_str_k target_phdrs target_segs asp av ev 1 uid hw arnd
      (by omega) hnw
  · have hb := read_argv_byte_k target_phdrs target_segs asp av ev 1 (tnn av)
      uid hw arnd (by omega) (Nat.le_refl _) hnw
    change rdn target_segs _ (ptrA av ev asp + nat_to_word (tnn av)) 1 =
      some [byte_at (targ1 av) (targ1 av).length] at hb
    rw [byte_at_len] at hb
    exact hb

/-- From the entry to the `strlen` loop head at `0x1001334`: crt's prologue,
the `argc` load, the call into main, `bltu a2,a0` taken, main's prologue,
the `argv[1]` load and the call into `strlen`. -/
theorem target_to_loop (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    ∃ regs1 : bvmap 5 word,
      reg_get regs1 1 = (0x10011b0 : word) ∧
      reg_get regs1 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regs1 8 = ptrA av ev asp ∧
      reg_get regs1 10 = ptrA av ev asp ∧ reg_get regs1 11 = Z_to_bv 64 0 ∧
      msteps target_segs
        (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw)
        (mkst regs1 0x1001334 (tfmem av ev uid hw asp arnd) trom) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hu (k : Int) (hk : -16 ≤ k) (hk' : k ≤ 64) :
      bv_unsigned (Z_to_bv 64 (bv_unsigned asp - k)) = bv_unsigned asp - k :=
    u_Z2bv _ (by omega) (by omega)
  have hs (k : Int) (hk : 8 ≤ k) (hk' : k ≤ 64) :
      store_ok target_segs (awmem av ev uid hw asp arnd)
        (Z_to_bv 64 (bv_unsigned asp - k)) 8 = true := by
    apply store_ok_wrap_window
    · rw [hu k (by omega) hk', stack_max_size_val]; omega
    · rw [hu k (by omega) hk']; omega
  have hp : rdn target_segs (tfmem av ev uid hw asp arnd)
      (Z_to_bv 64 (bv_unsigned asp + 16)) 8 = some (word_le8 (ptrA av ev asp)) := by
    have hua : bv_unsigned (Z_to_bv 64 (bv_unsigned asp + 16)) =
        bv_unsigned asp + 16 := u_Z2bv _ (by omega) (by omega)
    rw [rdn_tfmem_above av ev uid hw asp arnd hsp_lo hsp_hi _ _
      (by rw [hua]; omega) (by rw [hua]; omega),
      rdn_awmem_stack av ev uid hw asp arnd _ _
        (by rw [hua]; omega) (by rw [hua]; omega)]
    have he : asp + nat_to_word 16 = Z_to_bv 64 (bv_unsigned asp + 16) :=
      word_add_nat asp 16
    rw [← he]
    exact read_argv_ptr_k target_phdrs target_segs asp av ev 1 uid hw arnd
      (by omega) (target_bsb_nw av ev uid hw asp arnd hva hve hsp_hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 6
  · rw [init_mkst]
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x100115c _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 16))
      TF_100115c (by decide) TD_100115c (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at target_segs _ 0x1001160 _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 8)) (Z_to_bv 64 0)
      TF_1001160 (by decide) TD_1001160
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) 8 = _
          unfold v_addi; rw [hu 16 (by omega) (by omega)]; congr 1; omega)
      (by cat_regs; rfl) (hs 8 (by omega) (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at target_segs _ 0x1001164 _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 16)) (Z_to_bv 64 0)
      TF_1001164 (by decide) TD_1001164
      (by cat_regs; exact v_addi_0 _) (by cat_regs; rfl)
      (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _) (hs 16 (by omega) (by omega)))) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x1001168 _ _ _ _ _ _ asp
      TF_1001168 (by decide) TD_1001168 (by decide) (by
        cat_regs
        change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) 16 = asp
        unfold v_addi
        rw [hu 16 (by omega) (by omega), Int.sub_add_cancel]
        exact v_addi_0 asp)) ?_
    refine msteps.mst_step _ _ _ rfl (step_ld target_segs _ 0x100116c _ _ _ _ _ _ (word_le8 (targcN av)) (targcN av)
      TF_100116c (by decide) TD_100116c
      (by cat_regs; change rdn target_segs (amem1 av ev uid hw asp arnd) (v_addi asp 0) 8 = _
          rw [v_addi_0]; exact read_argc_a1 av ev uid hw asp arnd hva hve hsp_lo hsp_hi)
      (bytes_le_n_to_le_8 _)) ?_
    simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x1001170 _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp + 8))
      TF_1001170 (by decide) TD_1001170 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_auipc_at target_segs _ 0x1001174 _ _ _ _ _ (0x1001174 : word)
      TF_1001174 (by decide) TD_1001174 (by decide) (by rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_jalr_link target_segs _ 0x1001178 _ _ _ _ _ _ (0x1001174 : word)
      TF_1001178 (by decide) TD_1001178 (by decide) (by cat_regs)) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x1001184 _ _ _ _ _ _ (Z_to_bv 64 1)
      TF_1001184 (by decide) TD_1001184 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_bltu_tk target_segs _ 0x1001188 _ _ _ _ _ _
      TF_1001188 (by decide) TD_1001188 (by
        cat_regs
        rw [c_ltu_ltb, u_targcN av hva]
        change decide (1 < (av.length : Int)) = true
        exact decide_eq_true (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x1001194 _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 64))
      TF_1001194 (by decide) TD_1001194 (by decide) (by
        cat_regs
        change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) (-48) = _
        unfold v_addi; rw [hu 16 (by omega) (by omega)]; congr 1; omega)) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at target_segs _ 0x1001198 _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 24)) (0x100117c : word)
      TF_1001198 (by decide) TD_1001198
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 40 = _
          unfold v_addi; rw [hu 64 (by omega) (by omega)]; congr 1; omega)
      (by cat_regs; rfl)
      (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _) (hs 24 (by omega) (by omega))))) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at target_segs _ 0x100119c _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned asp - 32)) asp
      TF_100119c (by decide) TD_100119c
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 32 = _
          unfold v_addi; rw [hu 64 (by omega) (by omega)]; congr 1; omega)
      (by cat_regs)
      (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
          (store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _) (hs 32 (by omega) (by omega)))))) ?_
    refine msteps.mst_step _ _ _ rfl (step_ld target_segs _ 0x10011a0 _ _ _ _ _ _ (word_le8 (ptrA av ev asp)) (ptrA av ev asp)
      TF_10011a0 (by decide) TD_10011a0 (by
        cat_regs
        change rdn target_segs (tfmem av ev uid hw asp arnd)
          (v_addi (Z_to_bv 64 (bv_unsigned asp + 8)) 8) 8 = _
        have he : v_addi (Z_to_bv 64 (bv_unsigned asp + 8)) 8 =
            Z_to_bv 64 (bv_unsigned asp + 16) := by
          unfold v_addi; rw [u_Z2bv _ (by omega) (by omega)]; congr 1
        rw [he]; exact hp) (bytes_le_n_to_le_8 _)) ?_
    simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x10011a4 _ _ _ _ _ _ (ptrA av ev asp)
      TF_10011a4 (by decide) TD_10011a4 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine msteps.mst_step _ _ _ rfl (step_auipc_at target_segs _ 0x10011a8 _ _ _ _ _ (0x10011a8 : word)
      TF_10011a8 (by decide) TD_10011a8 (by decide) (by rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_jalr_link target_segs _ 0x10011ac _ _ _ _ _ _ (0x10011a8 : word)
      TF_10011ac (by decide) TD_10011ac (by decide) (by cat_regs)) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at target_segs _ 0x1001330 _ _ _ _ _ _ (Z_to_bv 64 0)
      TF_1001330 (by decide) TD_1001330 (by decide) (by cat_regs; rfl)) ?_
    exact msteps.mst_refl _
  all_goals (cat_regs <;> rfl)

/-- The `strlen` loop at `0x1001334`..`0x1001340`, `d` iterations to go. -/
theorem target_strlen (av ev : List (List byte)) (asp : word)
    (hva : valid_argv av) (_hve : valid_envp ev) (_hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length)
    (mem : word → Option byte)
    (hread : rdn target_segs mem (ptrA av ev asp) (tnn av + 1) =
      some (targ1 av ++ [Z_to_bv 8 0]))
    (d j : Nat) (regs : bvmap 5 word) (hjd : j + d = tnn av)
    (h10 : reg_get regs 10 = ptrA av ev asp) (h11 : reg_get regs 11 = nat_to_word j) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 11 → x ≠ 12 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 11 = nat_to_word (tnn av + 1) ∧
      msteps target_segs (mkst regs 0x1001334 mem trom) (mkst regs' 0x1001344 mem trom) := by
  have hn := tnN_le av hva hge2
  have hnz := targ1_nz av hva hge2
  induction d generalizing j regs
  all_goals
    have hj : j ≤ tnn av := by omega
    let regs1 := regupd regs 12 (ptrA av ev asp + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned (byte_at (targ1 av) j)))
    let regs3 := regupd regs2 11 (nat_to_word (j + 1))
    have e1 : RiscvSemantics.step target_segs (mkst regs 0x1001334 mem trom) =
        MachineOk (mkst regs1 0x1001338 mem trom) := by
      apply step_add_at target_segs _ _ _ _ _ _ _ _ _
        TF_1001334 (by decide) TD_1001334 (by decide)
      cat_regs
      rw [h10, h11, v_add, u_ntw j (by omega), word_add_nat]
    have e2 : RiscvSemantics.step target_segs (mkst regs1 0x1001338 mem trom) =
        MachineOk (mkst regs2 0x100133c mem trom) := by
      have hr := rdn_nth target_segs mem (tnn av + 1) (ptrA av ev asp)
        (targ1 av ++ [Z_to_bv 8 0]) j hread (by omega)
      have hs := step_lbu target_segs regs1 0x1001338 mem trom _ 12 12 _
        (byte_at (targ1 av) j) TF_1001338 (by decide) TD_1001338 (by
          dsimp only [regs1]
          cat_regs
          change rdn target_segs mem (v_addi (ptrA av ev asp + nat_to_word j) 0) 1 = _
          rw [v_addi_0]
          exact hr)
      exact hs
    have e3 : RiscvSemantics.step target_segs (mkst regs2 0x100133c mem trom) =
        MachineOk (mkst regs3 0x1001340 mem trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ _
        TF_100133c (by decide) TD_100133c (by decide)
      dsimp only [regs2, regs1]
      cat_regs
      rw [h11]
      exact v_addi_Sj j (by omega)
    have hag : ∀ x : reg, x ≠ 11 → x ≠ 12 → reg_get regs3 x = reg_get regs x := by
      intro x hx11 hx12
      dsimp only [regs3, regs2, regs1]
      simp only [regupd_other _ _ _ _ hx11, regupd_other _ _ _ _ hx12]
    have hr11 : reg_get regs3 11 = nat_to_word (j + 1) := regupd_same _ _ _
    have hr12 : getr regs3 12 = Z_to_bv 64 (bv_unsigned (byte_at (targ1 av) j)) := by
      dsimp only [regs3, regs2]
      cat_regs
  case zero =>
    have hjend : j = tnn av := by omega
    have hb : byte_at (targ1 av) j = Z_to_bv 8 0 := by
      rw [hjend]
      exact byte_at_len (targ1 av)
    refine ⟨regs3, hag, ?_, ?_⟩
    · rw [hr11, hjend]
    · cat_step e1
      cat_step e2
      cat_step e3
      cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _
        TF_1001340 (by decide) TD_1001340 (by
          rw [hr12, hb, getr_zero]
          exact c_eq_0_true))
      exact msteps.mst_refl _
  case succ d ih =>
    have hblt : j < (targ1 av).length := by change j < tnn av; omega
    have hb := byte_at_nz (targ1 av) j hnz hblt
    obtain ⟨regs', hag', hr11', hms⟩ := ih (j + 1) regs3 (by omega)
      (by rw [hag 10 (by decide) (by decide)]; exact h10) hr11
    refine ⟨regs', ?_, hr11', ?_⟩
    · intro x hx11 hx12
      rw [hag' x hx11 hx12, hag x hx11 hx12]
    · cat_step e1
      cat_step e2
      cat_step e3
      cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _
        TF_1001340 (by decide) TD_1001340 (by
          rw [hr12, getr_zero]
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u _ hb))
      exact hms

/-- From the entry to main's cap test at `0x10011b0`, `a0 = strlen(argv[1])`. -/
theorem target_to_captest (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    ∃ regs2 : bvmap 5 word,
      reg_get regs2 1 = (0x10011b0 : word) ∧
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regs2 8 = ptrA av ev asp ∧
      reg_get regs2 10 = tnN av ∧
      msteps target_segs
        (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw)
        (mkst regs2 0x10011b0 (tfmem av ev uid hw asp arnd) trom) := by
  obtain ⟨regs1, h1, h2, h8, h10, h11, hms1⟩ :=
    target_to_loop av ev uid hw asp arnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨regs2, hag, h11', hms2⟩ :=
    target_strlen av ev asp hva hve hsp_hi hge2
      (tfmem av ev uid hw asp arnd)
      (read_str_t av ev uid hw asp arnd hva hve hsp_lo hsp_hi hge2)
      (tnn av) 0 regs1 (by omega) h10 h11
  refine ⟨regupd regs2 10 (tnN av), ?_, ?_, ?_, ?_, ?_⟩
  · cat_regs
    rw [hag 1 (by decide) (by decide)]
    exact h1
  · cat_regs
    rw [hag 2 (by decide) (by decide)]
    exact h2
  · cat_regs
    rw [hag 8 (by decide) (by decide)]
    exact h8
  · cat_regs
  · apply msteps_trans target_segs _ _ _ hms1
    apply msteps_trans target_segs _ _ _ hms2
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (tnN av)
      TF_1001344 (by decide) TD_1001344 (by decide) (by
        cat_regs
        rw [h11']
        exact v_addi_natS_m1 (tnn av)))
    cat_step (step_jalr_x0 target_segs _ _ _ _ _ _ _ (0x10011b0 : word)
      TF_1001348 (by decide) TD_1001348 (by
        cat_regs
        rw [hag 1 (by decide) (by decide)]
        exact h1))
    exact msteps.mst_refl _

/-- `strlen(argv[1]) > 65536`: `bgeu a2,a0` falls through, exit code 3. -/
theorem target_wexit_cap (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) (hcap : 65536 < (tnn av : Int)) :
    to_wexit target_segs
      (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw)
      [] (Z_to_bv 64 3) := by
  obtain ⟨regs2, h1, h2, h8, h10, hms⟩ :=
    target_to_captest av ev uid hw asp arnd hva hve hsp_lo hsp_hi hge2
  apply msteps_to_wexit target_segs _ _ _ _ hms
  cat_step (step_lui_at target_segs _ _ _ _ _ _ _ (Z_to_bv 64 65536)
    TF_10011b0 (by decide) TD_10011b0 (by decide) (by rfl))
  cat_step (step_bgeu_ft target_segs _ _ _ _ _ _ _ _
    TF_10011b4 (by decide) TD_10011b4 (by
      cat_regs
      rw [h10, c_ltu_ltb, u_tnN av hva hge2]
      exact decide_eq_true hcap))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 3)
    TF_10011b8 (by decide) TD_10011b8 (by decide) (by cat_regs; rfl))
  cat_step (step_jal_x0 target_segs _ _ _ _ _ _
    TF_10011bc (by decide) TD_10011bc)
  apply target_exit asp hsp_lo hsp_hi
  · cat_regs; exact h2
  · cat_regs
  · decide
  · exact read_slot_ra_t av ev uid hw asp arnd hsp_lo hsp_hi
  · exact read_slot_s0_t av ev uid hw asp arnd hsp_lo hsp_hi

/-- Retained from Rocq, where it is also uncalled: with the length under
the cap and not a multiple of 8, main reaches `0x10011c8`. -/
theorem target_continues_mod (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) (hcap : (tnn av : Int) ≤ 65536) (_hmod : tnn av % 8 ≠ 0) :
    ∃ regs3 : bvmap 5 word,
      msteps target_segs
        (init_machine_state target_segs 0x100115c target_phdrs asp arnd av ev uid hw)
        (mkst regs3 0x10011c8 (tfmem av ev uid hw asp arnd) trom) := by
  obtain ⟨regs2, _, _, _, h10, hms⟩ :=
    target_to_captest av ev uid hw asp arnd hva hve hsp_lo hsp_hi hge2
  refine ⟨regupd (regupd (regupd regs2 12 (Z_to_bv 64 65536)) 11 (tnN av))
    10 (Z_to_bv 64 0), ?_⟩
  apply msteps_trans target_segs _ _ _ hms
  cat_step (step_lui_at target_segs _ _ _ _ _ _ _ (Z_to_bv 64 65536)
    TF_10011b0 (by decide) TD_10011b0 (by decide) (by rfl))
  cat_step (step_bgeu_tk target_segs _ _ _ _ _ _ _ _
    TF_10011b4 (by decide) TD_10011b4 (by
      cat_regs
      rw [h10, c_ltu_ltb, u_tnN av hva hge2]
      change decide ((65536 : Int) < (tnn av : Int)) = false
      exact decide_eq_false (by omega)))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (tnN av)
    TF_10011c0 (by decide) TD_10011c0 (by decide)
    (by cat_regs; rw [h10]; exact v_addi_0 _))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    TF_10011c4 (by decide) TD_10011c4 (by decide) (by cat_regs; rfl))
  exact msteps.mst_refl _

/-- The byte-copy loop at `0x1001218`..`0x100122c`, `d` bytes to go, into
the granted region at `r`. -/
theorem target_copy (av ev : List (List byte)) (asp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length)
    (r : word) (mem0 : word → Option byte)
    (hgrant : store_grant_ok target_segs mem0 r (tnN av))
    (hread : rdn target_segs mem0 (ptrA av ev asp) (tnn av + 1) =
      some (targ1 av ++ [Z_to_bv 8 0]))
    (_hfree : region_free (segments_reserved target_segs) r (tnN av) = true)
    (hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (tnn av : Int) ≤ bv_unsigned asp - stack_max_size)
    (hrw : bv_unsigned r + (tnn av : Int) < 2 ^ 64)
    (d : Nat) (regs : bvmap 5 word) (hd1 : 1 ≤ d) (hd2 : d ≤ tnn av)
    (h8 : reg_get regs 8 = ptrA av ev asp + nat_to_word (tnn av - d))
    (h10 : reg_get regs 10 = r + nat_to_word (tnn av - d))
    (h13 : reg_get regs 13 = nat_to_word d) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 8 → x ≠ 10 → x ≠ 13 → x ≠ 14 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 8 = ptrA av ev asp + tnN av ∧ reg_get regs' 10 = r + tnN av ∧
      reg_get regs' 13 = Z_to_bv 64 0 ∧
      msteps target_segs
        (mkst regs 0x1001218 (wbytes mem0 r ((targ1 av).take (tnn av - d))) trom)
        (mkst regs' 0x1001230 (wbytes mem0 r (targ1 av)) trom) := by
  have hplo := ptrA_lo av ev asp hva hve hsp_hi hge2
  have hphi := ptrA_hi av ev asp hva hve hsp_hi hge2
  have hnn := tnN_le av hva hge2
  have hnu := u_tnN av hva hge2
  have hrp : bv_unsigned r + (tnn av : Int) ≤ bv_unsigned (ptrA av ev asp) := by
    rw [stack_max_size_val] at hrs
    omega
  induction d generalizing regs with
  | zero => omega
  | succ d ih =>
    let i := tnn av - (d + 1)
    have hi : i < tnn av := by dsimp only [i]; omega
    have hsi : i + 1 = tnn av - d := by dsimp only [i]; omega
    have hlen : ((targ1 av).take i).length = i :=
      List.length_take_of_le (by change i ≤ tnn av; omega)
    have hui : bv_unsigned (r + nat_to_word i) = bv_unsigned r + (i : Int) := by
      rw [word_add_nat]
      exact u_Z2bv _ (by omega) (by omega)
    have hupi : bv_unsigned (ptrA av ev asp + nat_to_word i) =
        bv_unsigned (ptrA av ev asp) + (i : Int) := by
      rw [word_add_nat]
      exact u_Z2bv _ (by have := (u64_range (ptrA av ev asp)).1; omega) (by omega)
    let b := (targ1 av).getD i (Z_to_bv 8 0)
    let memI := wbytes mem0 r ((targ1 av).take i)
    let memI' := wbytes mem0 r ((targ1 av).take (i + 1))
    let regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))
    let regs2 := regupd regs1 13 (nat_to_word d)
    let regs3 := regupd regs2 10 (r + nat_to_word (i + 1))
    let regs4 := regupd regs3 8 (ptrA av ev asp + nat_to_word (i + 1))
    have hb : rdn target_segs memI (ptrA av ev asp + nat_to_word i) 1 = some [b] := by
      dsimp only [memI]
      rw [rdn_wbytes_disjoint target_segs _ _ _ _ _
        (by rw [hlen, hupi]; omega) (by rw [hupi]; omega)]
      have hb := rdn_nth target_segs mem0 (tnn av + 1) (ptrA av ev asp)
        (targ1 av ++ [Z_to_bv 8 0]) i hread (by omega)
      simpa only [b, List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using hb
    have e1 : RiscvSemantics.step target_segs (mkst regs 0x1001218 memI trom) =
        MachineOk (mkst regs1 0x100121c memI trom) := by
      exact step_lbu target_segs _ _ _ _ _ _ _ _ b
        TF_1001218 (by decide) TD_1001218
        (by cat_regs; rw [h8]; exact (v_addi_0 _ ▸ hb))
    have e2 : RiscvSemantics.step target_segs (mkst regs1 0x100121c memI trom) =
        MachineOk (mkst regs2 0x1001220 memI trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ (nat_to_word d)
        TF_100121c (by decide) TD_100121c (by decide)
      dsimp only [regs1]
      cat_regs
      rw [h13]
      exact v_addi_natS_m1 d
    have hmem : wbytes memI (r + nat_to_word i) [b] = memI' := by
      dsimp only [memI', memI, b]
      rw [firstn_snoc _ _ hi, wbytes_app, hlen]
    have e3 : RiscvSemantics.step target_segs (mkst regs2 0x1001220 memI trom) =
        MachineOk (mkst regs2 0x1001224 memI' trom) := by
      rw [← hmem]
      apply step_sb_at target_segs _ _ _ _ _ _ _ _ (r + nat_to_word i)
        (Z_to_bv 64 (bv_unsigned b)) b TF_1001220 (by decide) TD_1001220
      · dsimp only [regs2, regs1]; cat_regs; rw [h10]; exact v_addi_0 _
      · dsimp only [regs2, regs1]; cat_regs
      · exact zext8_byte b
      · apply store_ok_mono target_segs 1 mem0 memI _
          (wbytes_grows _ _ _)
        apply hgrant
        · rw [hui]; omega
        · rw [hui, hnu]; omega
    have e4 : RiscvSemantics.step target_segs (mkst regs2 0x1001224 memI' trom) =
        MachineOk (mkst regs3 0x1001228 memI' trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ (r + nat_to_word (i + 1))
        TF_1001224 (by decide) TD_1001224 (by decide)
      dsimp only [regs2, regs1]; cat_regs; rw [h10]
      exact word_add_nat_1 r i
    have e5 : RiscvSemantics.step target_segs (mkst regs3 0x1001228 memI' trom) =
        MachineOk (mkst regs4 0x100122c memI' trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _
        (ptrA av ev asp + nat_to_word (i + 1))
        TF_1001228 (by decide) TD_1001228 (by decide)
      dsimp only [regs3, regs2, regs1]; cat_regs; rw [h8]
      exact word_add_nat_1 (ptrA av ev asp) i
    have hsteps : msteps target_segs (mkst regs 0x1001218 memI trom)
        (mkst regs4 0x100122c memI' trom) := by
      cat_step e1
      cat_step e2
      cat_step e3
      cat_step e4
      cat_step e5
      exact msteps.mst_refl _
    have hag : ∀ x : reg, x ≠ 8 → x ≠ 10 → x ≠ 13 → x ≠ 14 →
        reg_get regs4 x = reg_get regs x := by
      intro x hx8 hx10 hx13 hx14
      dsimp only [regs4, regs3, regs2, regs1]
      simp only [regupd_other _ _ _ _ hx8, regupd_other _ _ _ _ hx10,
        regupd_other _ _ _ _ hx13, regupd_other _ _ _ _ hx14]
    have hr8 : reg_get regs4 8 = ptrA av ev asp + nat_to_word (tnn av - d) := by
      dsimp only [regs4]; rw [regupd_same, hsi]
    have hr10 : reg_get regs4 10 = r + nat_to_word (tnn av - d) := by
      dsimp only [regs4, regs3]; cat_regs; rw [hsi]
    have hr13 : reg_get regs4 13 = nat_to_word d := by
      dsimp only [regs4, regs3, regs2]; cat_regs
    by_cases hd : d = 0
    · subst d
      have hfull : memI' = wbytes mem0 r (targ1 av) := by
        dsimp only [memI']
        rw [hsi, Nat.sub_zero]
        exact congrArg (wbytes mem0 r) (List.take_length (l := targ1 av))
      refine ⟨regs4, hag, ?_, ?_, ?_, ?_⟩
      · exact hr8
      · exact hr10
      · exact hr13
      · apply msteps_trans target_segs _ _ _ hsteps
        rw [← hfull]
        cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _
          TF_100122c (by decide) TD_100122c
          (by cat_regs; rw [hr13]; exact c_eq_0_true))
        exact msteps.mst_refl _
    · obtain ⟨regs', hag', h8', h10', h13', hms⟩ :=
        ih regs4 (by omega) (by omega) hr8 hr10 hr13
      refine ⟨regs', ?_, h8', h10', h13', ?_⟩
      · intro x hx8 hx10 hx13 hx14
        rw [hag' x hx8 hx10 hx13 hx14, hag x hx8 hx10 hx13 hx14]
      · apply msteps_trans target_segs _ _ _ hsteps
        cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _
          TF_100122c (by decide) TD_100122c
          (by cat_regs; rw [hr13]; apply c_eq_0_false
              rw [u_ntw d (by omega)]; omega))
        rw [show btgt (0x100122c : word) (bv_signed (0x1fec : BitVec 13)) =
          (0x1001218 : word) from by decide]
        simpa only [memI', hsi] using hms

/-- The write-all loop of `put` from the `ecall` return at `0x1001310`. -/
theorem tgt_put_wall (K : machine_state → Prop) (fuel : Nat) (rest : List byte)
    (p RA : word) (n : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (hfuel : rest.length ≤ fuel) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length)
    (hlen : (rest.length : Int) < 2 ^ 31)
    (h1 : reg_get regs 1 = RA) (hRA : v_jalr RA 0 = RA)
    (h10 : reg_get regs 10 = len_word (rest.take n))
    (h11 : reg_get regs 11 = p) (h12 : reg_get regs 12 = len_word rest)
    (h17u : bv_unsigned (reg_get regs 17) = 64) (h17 : reg_get regs 17 = Z_to_bv 64 64)
    (hread : rdn target_segs mem p rest.length = some rest)
    (hK : ∀ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 17 → reg_get regs' x = reg_get regs x) →
      reg_get regs' 10 = Z_to_bv 64 0 → K (mkst regs' RA mem trom)) :
    to_wall_tail target_segs (Z_to_bv 64 1) (mkst regs (0x1001310 : word) mem trom)
      (rest.drop n) K := by
  induction fuel generalizing rest p n regs with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn n rest hn2 (by omega)
    have hdlen : ((rest.drop n).length : Int) < 2 ^ 64 := by
      rw [List.length_drop]; omega
    have hdu := u_len_word (rest.drop n) hdlen
    cat_step (step_bge_ft target_segs _ _ _ _ _ _ _ _ TF_1001310 (by decide) TD_1001310
      (by cat_regs; rw [h10]; exact c_lts_0_pos _ (by omega) (by omega)))
    cat_step (step_add_at target_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned p + (n : Int))) TF_1001314 (by decide) TD_1001314
      (by decide) (by cat_regs; rw [h11, h10]; exact v_add_len_firstn_Z p n rest hn2 (by omega)))
    cat_step (step_sub_at target_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
      TF_1001318 (by decide) TD_1001318 (by decide)
      (by cat_regs; rw [h12, h10]; exact v_sub_len_firstn n rest hn2 (by omega)))
    by_cases heq : n = rest.length
    · have hempty : rest.drop n = [] := by rw [heq, List.drop_length]
      rw [hempty]
      cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _ TF_100131c (by decide) TD_100131c
        (by cat_regs; exact c_eq_0_true))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        TF_1001320 (by decide) TD_1001320 (by decide) (by cat_regs; rfl))
      cat_step (step_jalr_x0 target_segs _ _ _ _ _ _ _ RA
        TF_1001324 (by decide) TD_1001324 (by cat_regs; exact h1))
      change to_wall_tail target_segs (Z_to_bv 64 1) (mkst _ (v_jalr RA 0) mem trom) [] K
      rw [hRA]
      apply to_wall_tail.twt_done
      apply hK
      · intro x hx10 hx11 hx12 hx17
        simp only [regupd_other _ _ _ _ hx10, regupd_other _ _ _ _ hx12,
          regupd_other _ _ _ _ hx11]
      · cat_regs
    · have hnonempty : 1 ≤ (rest.drop n).length := by rw [List.length_drop]; omega
      have hsk := rdn_skipn target_segs mem rest.length p rest n hread hn2
      rw [word_add_nat_Z p n (by omega), ← List.length_drop] at hsk
      cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _ TF_100131c (by decide) TD_100131c
        (by cat_regs; exact c_eq_0_false _ (by rw [hdu]; omega)))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        TF_1001308 (by decide) TD_1001308 (by decide) (by cat_regs; rfl))
      cat_step (step_ecall target_segs _ _ _ _ _ TF_100130c (by decide))
      apply to_wall_tail.twt_more _ _ _ hnonempty
      apply twl_write_rec
      · cat_regs; exact h17u
      · cat_regs
      · cat_regs
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (word_to_nat (len_word (rest.drop n))) = _
        have hw : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          change (word_to_nat (len_word (rest.drop n)) : Int) =
            ((rest.drop n).length : Int) at hdu
          omega
        rw [hw]; exact hsk
      · exact hnonempty
      · intro m hm1 hm2
        apply ih (rest.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · cat_regs; exact h1
        · cat_regs
        · cat_regs
        · cat_regs
        · cat_regs; exact h17u
        · cat_regs; exact h17
        · exact hsk
        · intro regs' hag h0
          apply hK regs' _ h0
          intro x hx10 hx11 hx12 hx17
          rw [hag x hx10 hx11 hx12 hx17]
          simp only [regupd_other _ _ _ _ hx10, regupd_other _ _ _ _ hx12,
            regupd_other _ _ _ _ hx11]

/-- `put(ptr, len)` from its entry at `0x10012f8`: the whole buffer is
written, then control returns to `RA` with `a0 = 0`. -/
theorem target_put (regs : bvmap 5 word) (mem : word → Option byte) (buf : List byte)
    (ptr len RA : word) (bufs : List (List byte)) (code : word)
    (h1 : reg_get regs 1 = RA) (h10 : reg_get regs 10 = ptr) (h11 : reg_get regs 11 = len)
    (hlen0 : 0 < bv_unsigned len) (hlen : bv_unsigned len < 2 ^ 31)
    (hRA : v_jalr RA 0 = RA)
    (hread : rdn target_segs mem ptr (word_to_nat len) = some buf)
    (hK : ∀ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 17 → reg_get regs' x = reg_get regs x) →
      reg_get regs' 10 = Z_to_bv 64 0 →
      to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' RA mem trom)) :
    to_wallexit target_segs (Z_to_bv 64 1) (buf :: bufs) code
      (mkst regs 0x10012f8 mem trom) := by
  have hbl := rdn_length target_segs mem (word_to_nat len) ptr buf hread
  have hbuf : (buf.length : Int) = bv_unsigned len := by
    rw [hbl]
    rfl
  have hlw : len_word buf = len := by
    apply bv_eq_of_unsigned
    rw [u_len_word buf (by omega), hbuf]
  have hnonempty : 1 ≤ buf.length := by omega
  refine ⟨hnonempty, ?_⟩
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ len
    TF_10012f8 (by decide) TD_10012f8 (by decide)
    (by cat_regs; rw [h11]; exact v_addi_0 len))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ ptr
    TF_10012fc (by decide) TD_10012fc (by decide)
    (by cat_regs; rw [h10]; exact v_addi_0 ptr))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
    TF_1001300 (by decide) TD_1001300 (by decide) (by cat_regs; rfl))
  cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
    TF_1001304 (by decide) TD_1001304
    (by cat_regs; exact c_eq_0_false len (by omega)))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    TF_1001308 (by decide) TD_1001308 (by decide) (by cat_regs; rfl))
  cat_step (step_ecall target_segs _ _ _ _ _ TF_100130c (by decide))
  apply to_wall_tail.twt_more _ _ _ hnonempty
  apply twl_write_rec
  · cat_regs; rfl
  · cat_regs
  · cat_regs
    rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    exact hread
  · exact hnonempty
  · intro n hn1 hn2
    apply tgt_put_wall _ buf.length buf ptr RA n
    · exact Nat.le_refl _
    · exact hn1
    · exact hn2
    · omega
    · cat_regs; exact h1
    · exact hRA
    · cat_regs
    · cat_regs
    · cat_regs; exact hlw.symm
    · cat_regs; rfl
    · cat_regs
    · rw [hbl]; exact hread
    · intro regs' hag h0
      apply hK regs' _ h0
      intro x hx10 hx11 hx12 hx17
      rw [hag x hx10 hx11 hx12 hx17]
      simp only [regupd_other _ _ _ _ hx10, regupd_other _ _ _ _ hx17,
        regupd_other _ _ _ _ hx11, regupd_other _ _ _ _ hx12]

theorem sumb_firstn_bound (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (k : Nat) : sumb ((targ1 av).take k) ≤ 255 * (tnn av : Int) := by
  have hsplit := sumb_app ((targ1 av).take k) ((targ1 av).drop k)
  rw [List.take_append_drop] at hsplit
  have hnonneg := sumb_nonneg ((targ1 av).drop k)
  have hbound := sumb_le (targ1 av) (targ1_bytes av hva hge2)
  unfold tnn
  omega

/-- The inner summing loop at `0x1001244`..`0x1001254`: `c` bytes to go from
offset `s`. -/
theorem target_sum_inner (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (memC : word → Option byte) (r : word) (total : Nat)
    (hbyte : ∀ i, i < total →
      rdn target_segs memC (r + nat_to_word i) 1 = some [(targ1 av).getD i (Z_to_bv 8 0)])
    (hrw : bv_unsigned r + (total : Int) < 2 ^ 64)
    (c s : Nat) (regs : bvmap 5 word) (hc : 1 ≤ c) (hsc : s + c ≤ total)
    (h10 : reg_get regs 10 = Z_to_bv 64 (sumb ((targ1 av).take s)))
    (h14 : reg_get regs 14 = nat_to_word c)
    (h15 : reg_get regs 15 = r + nat_to_word s) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 10 → x ≠ 14 → x ≠ 15 → x ≠ 16 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 10 = Z_to_bv 64 (sumb ((targ1 av).take (s + c))) ∧
      reg_get regs' 15 = r + nat_to_word (s + c) ∧
      msteps target_segs (mkst regs 0x1001244 memC trom) (mkst regs' 0x1001258 memC trom) := by
  have hlen := tnN_le av hva hge2
  have hr := u64_range r
  induction c generalizing s regs with
  | zero => omega
  | succ c ih =>
    let b := (targ1 av).getD s (Z_to_bv 8 0)
    let regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned b))
    let regs2 := regupd regs1 14 (nat_to_word c)
    let regs3 := regupd regs2 10 (Z_to_bv 64 (sumb ((targ1 av).take (s + 1))))
    let regs4 := regupd regs3 15 (r + nat_to_word (s + 1))
    have hsum0 := sumb_nonneg ((targ1 av).take s)
    have hsumb := sumb_le ((targ1 av).take s) (fun b _ => (u8_range b).2)
    have htlen : (((targ1 av).take s).length : Int) ≤ (tnn av : Int) := by
      unfold tnn
      simp only [List.length_take]
      omega
    have hsum : sumb ((targ1 av).take s) < 2 ^ 64 := by omega
    have e1 : RiscvSemantics.step target_segs (mkst regs 0x1001244 memC trom) =
        MachineOk (mkst regs1 0x1001248 memC trom) := by
      have h := step_lbu target_segs regs 0x1001244 memC trom _ 16 15 _ b
        TF_1001244 (by decide) TD_1001244 (by
          cat_regs
          rw [h15]
          change rdn target_segs memC (v_addi (r + nat_to_word s) 0) 1 = some [b]
          rw [v_addi_0]
          exact hbyte s (by omega))
      exact h
    have e2 : RiscvSemantics.step target_segs (mkst regs1 0x1001248 memC trom) =
        MachineOk (mkst regs2 0x100124c memC trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ _
        TF_1001248 (by decide) TD_1001248 (by decide)
      dsimp only [regs1]
      cat_regs
      rw [h14]
      exact v_addi_natS_m1 c
    have e3 : RiscvSemantics.step target_segs (mkst regs2 0x100124c memC trom) =
        MachineOk (mkst regs3 0x1001250 memC trom) := by
      apply step_add_at target_segs _ _ _ _ _ _ _ _ _
        TF_100124c (by decide) TD_100124c (by decide)
      dsimp only [regs2, regs1]
      cat_regs
      rw [h10]
      unfold v_add
      rw [u_Z2bv _ hsum0 hsum, u_zext8, sumb_firstn_S_default]
    have e4 : RiscvSemantics.step target_segs (mkst regs3 0x1001250 memC trom) =
        MachineOk (mkst regs4 0x1001254 memC trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ _
        TF_1001250 (by decide) TD_1001250 (by decide)
      dsimp only [regs3, regs2, regs1]
      cat_regs
      rw [h15]
      exact word_add_nat_1 r s
    have hag : ∀ x : reg, x ≠ 10 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get regs4 x = reg_get regs x := by
      intro x hx10 hx14 hx15 hx16
      simp (disch := assumption) only [regs4, regs3, regs2, regs1, regupd_other]
    have ha10 : reg_get regs4 10 = Z_to_bv 64 (sumb ((targ1 av).take (s + 1))) := by
      dsimp only [regs4, regs3]; cat_regs
    have ha14 : reg_get regs4 14 = nat_to_word c := by
      dsimp only [regs4, regs3, regs2]; cat_regs
    have ha15 : reg_get regs4 15 = r + nat_to_word (s + 1) := by
      exact regupd_same _ _ _
    have hprefix : ∀ ms, msteps target_segs (mkst regs4 0x1001254 memC trom) ms →
        msteps target_segs (mkst regs 0x1001244 memC trom) ms := by
      intro ms hms
      cat_step e1
      cat_step e2
      cat_step e3
      cat_step e4
      exact hms
    by_cases hz : c = 0
    · subst c
      refine ⟨regs4, hag, ha10, ha15, hprefix _ ?_⟩
      cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _
        TF_1001254 (by decide) TD_1001254 (by
          cat_regs
          rw [ha14]
          exact c_eq_0_true))
      exact msteps.mst_refl _
    · obtain ⟨regs', hag', h10', h15', hms⟩ :=
        ih (s + 1) regs4 (by omega) (by omega) ha10 ha14 ha15
      have heq : s + 1 + c = s + Nat.succ c := by omega
      refine ⟨regs', ?_, ?_, ?_, hprefix _ ?_⟩
      · intro x hx10 hx14 hx15 hx16
        exact (hag' x hx10 hx14 hx15 hx16).trans (hag x hx10 hx14 hx15 hx16)
      · simpa only [heq] using h10'
      · simpa only [heq] using h15'
      · cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _
          TF_1001254 (by decide) TD_1001254 (by
            cat_regs
            rw [ha14]
            apply c_eq_0_false
            rw [u_ntw c (by omega)]
            omega))
        exact hms

/-- The outer summing loop at `0x1001238`..`0x1001260`: `m` groups of eight
bytes from offset `s`, the last group running past `tnn` into the zeroed
tail of the grant. -/
theorem target_sum (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (memC : word → Option byte) (r : word) (total : Nat)
    (hbyte : ∀ i, i < total →
      rdn target_segs memC (r + nat_to_word i) 1 = some [(targ1 av).getD i (Z_to_bv 8 0)])
    (hrw : bv_unsigned r + (total : Int) < 2 ^ 64)
    (m s : Nat) (regs : bvmap 5 word) (hm : 1 ≤ m)
    (hlo : s + 8 * (m - 1) < tnn av) (hhi : tnn av ≤ s + 8 * m) (htot : s + 8 * m = total)
    (h10 : reg_get regs 10 = Z_to_bv 64 (sumb ((targ1 av).take s)))
    (h11 : reg_get regs 11 = tnN av)
    (h12 : reg_get regs 12 = r + nat_to_word s)
    (h13 : reg_get regs 13 = nat_to_word s) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 10 → x ≠ 12 → x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 10 = Z_to_bv 64 (sumb (targ1 av)) ∧
      msteps target_segs (mkst regs 0x1001238 memC trom) (mkst regs' 0x1001264 memC trom) := by
  have hr := u64_range r
  induction m generalizing s regs with
  | zero => omega
  | succ m ih =>
    have hs8 : s + 8 ≤ total := by omega
    have hus : bv_unsigned (r + nat_to_word s) = bv_unsigned r + (s : Int) := by
      rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]
    let regs1 := regupd regs 14 (nat_to_word 8)
    let regs2 := regupd regs1 15 (r + nat_to_word s)
    have hi10 : reg_get regs2 10 = Z_to_bv 64 (sumb ((targ1 av).take s)) := by
      dsimp only [regs2, regs1]; cat_regs; exact h10
    have hi14 : reg_get regs2 14 = nat_to_word 8 := by
      dsimp only [regs2, regs1]; cat_regs
    have hi15 : reg_get regs2 15 = r + nat_to_word s := regupd_same _ _ _
    obtain ⟨regsI, hagI, h10I, _, hmsI⟩ :=
      target_sum_inner av hva hge2 memC r total hbyte hrw 8 s regs2
        (by decide) hs8 hi10 hi14 hi15
    let regs4 := regupd regsI 13 (nat_to_word (s + 8))
    let regs5 := regupd regs4 12 (r + nat_to_word (s + 8))
    have hi12 : reg_get regsI 12 = r + nat_to_word s := by
      rw [hagI 12 (by decide) (by decide) (by decide) (by decide)]
      dsimp only [regs2, regs1]; cat_regs; exact h12
    have hi13 : reg_get regsI 13 = nat_to_word s := by
      rw [hagI 13 (by decide) (by decide) (by decide) (by decide)]
      dsimp only [regs2, regs1]; cat_regs; exact h13
    have ha10 : reg_get regs5 10 = Z_to_bv 64 (sumb ((targ1 av).take (s + 8))) := by
      dsimp only [regs5, regs4]; cat_regs; exact h10I
    have ha11 : reg_get regs5 11 = tnN av := by
      dsimp only [regs5, regs4]; cat_regs
      rw [hagI 11 (by decide) (by decide) (by decide) (by decide)]
      dsimp only [regs2, regs1]; cat_regs; exact h11
    have ha12 : reg_get regs5 12 = r + nat_to_word (s + 8) := regupd_same _ _ _
    have ha13 : reg_get regs5 13 = nat_to_word (s + 8) := by
      dsimp only [regs5, regs4]; cat_regs
    have hag : ∀ x : reg, x ≠ 10 → x ≠ 12 → x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get regs5 x = reg_get regs x := by
      intro x hx10 hx12 hx13 hx14 hx15 hx16
      simp (disch := assumption) only [regs5, regs4, regupd_other]
      rw [hagI x hx10 hx14 hx15 hx16]
      simp (disch := assumption) only [regs2, regs1, regupd_other]
    have hprefix : ∀ ms, msteps target_segs (mkst regs5 0x1001260 memC trom) ms →
        msteps target_segs (mkst regs 0x1001238 memC trom) ms := by
      intro ms hms
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (nat_to_word 8)
        TF_1001238 (by decide) TD_1001238 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (r + nat_to_word s)
        TF_100123c (by decide) TD_100123c (by decide)
        (by cat_regs; rw [h12]; exact v_addi_0 _))
      cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
        TF_1001240 (by decide) TD_1001240 (by cat_regs; decide))
      apply msteps_trans target_segs _ _ _ hmsI
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (nat_to_word (s + 8))
        TF_1001258 (by decide) TD_1001258 (by decide) (by
          cat_regs; rw [hi13]
          change v_addi (nat_to_word s) 8 = nat_to_word (s + 8)
          unfold v_addi
          rw [u_ntw s (by omega)]
          unfold nat_to_word
          congr 1))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (r + nat_to_word (s + 8))
        TF_100125c (by decide) TD_100125c (by decide) (by
          cat_regs; rw [hi12]
          change v_addi (r + nat_to_word s) 8 = r + nat_to_word (s + 8)
          unfold v_addi
          rw [hus, word_add_nat]
          congr 1))
      exact hms
    by_cases hz : m = 0
    · subst m
      refine ⟨regs5, hag, ?_, hprefix _ ?_⟩
      · rw [ha10, List.take_of_length_le]
        change tnn av ≤ s + 8
        omega
      · cat_step (step_bltu_ft target_segs _ _ _ _ _ _ _ _
          TF_1001260 (by decide) TD_1001260 (by
            cat_regs; rw [ha13, ha11, c_ltu_ltb, u_tnN av hva hge2,
              u_ntw (s + 8) (by omega)]
            exact decide_eq_false (by omega)))
        exact msteps.mst_refl _
    · obtain ⟨regs', hag', h10', hms⟩ :=
        ih (s + 8) regs5 (by omega) (by omega) (by omega) (by omega)
          ha10 ha11 ha12 ha13
      refine ⟨regs', ?_, h10', hprefix _ ?_⟩
      · intro x hx10 hx12 hx13 hx14 hx15 hx16
        exact (hag' x hx10 hx12 hx13 hx14 hx15 hx16).trans
          (hag x hx10 hx12 hx13 hx14 hx15 hx16)
      · cat_step (step_bltu_tk target_segs _ _ _ _ _ _ _ _
          TF_1001260 (by decide) TD_1001260 (by
            cat_regs; rw [ha13, ha11, c_ltu_ltb, u_tnN av hva hge2,
              u_ntw (s + 8) (by omega)]
            exact decide_eq_true (by omega)))
        exact hms

end LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target
