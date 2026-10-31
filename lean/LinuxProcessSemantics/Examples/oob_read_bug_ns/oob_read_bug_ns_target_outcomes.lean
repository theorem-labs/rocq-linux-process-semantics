import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/oob_read_bug_ns/oob_read_bug_ns_target_outcomes.v`
at the baseline above; see that Rocq file for the argument.  The Rocq
section parameters become explicit arguments: `inp` with `av := inp.in_argv`,
`ev := inp.in_envp`, `uid := inp.in_uid` and `hw := inp.in_hwcap`, then
`asp arnd abrk amb` and the hypotheses `hva hve hsp_lo hsp_hi hbrk_lo
hbrk_hi hge2 hbrk_mod`.  The rest of the conventions are those of the target
file.  Rocq's `model` rewrite database and `wlits` are replaced by the
explicit `adv_brk`/`apply_zeros_*`/`brk_*` lemmas of `Common/AllocSim.lean`
and the two `init_model` facts in the defs file. -/

namespace LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target_outcomes

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
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

local macro "cat_regs" : tactic =>
  `(tactic| simp (disch := decide) only [getr_nz, getr_zero, regupd_same, regupd_other])

local macro "cat_step " h:term : tactic =>
  `(tactic| first
    | refine to_wexit.tw_step _ _ _ _ rfl $h ?_
    | refine to_wall_tail.twt_step _ _ _ _ rfl $h ?_
    | refine msteps.mst_step _ _ _ rfl $h ?_)

/-- The `'\n'` constant lives in rodata at `0x1000158`. -/
theorem read_newline_t (mem : word → Option byte) (h : mem (0x1000158 : word) = none) :
    rdn target_segs mem (0x1000158 : word) 1 = some [Z_to_bv 8 10] := by
  have read_one (segs : List Segment) (m : word → Option byte) (a : word)
      (seg : Segment) (b : byte)
      (hm : m a = none)
      (hs : find_segment segs (bv_unsigned a) (↑(1 : Nat)) = some seg)
      (hr : seg_readable seg = true)
      (hb : segment_read_bytes seg.seg_bytes (bv_unsigned a - seg.seg_base).toNat 1 =
        some [b]) : rdn segs m a 1 = some [b] := by
    simp only [rdn, hm, seg_rom, memory_read, hs, hr, ↓reduceIte, hb]
  apply read_one target_segs mem (0x1000158 : word) TargetMemImage_segment_000
    (Z_to_bv 8 10) h rfl (by decide +kernel)
  have ha : LinuxProcessSemantics.Common.ImageBytes.ascii_segment_read_bytes
      [TargetMemImage_seg_bytes_000_chars] 344 1 = some [Z_to_bv 8 10] := by
    decide +kernel
  exact (TargetMemImage_segment_000_read_ascii 344 1).trans ha

theorem target_free_cases (b l : word)
    (hfree : region_free (segments_reserved target_segs) b l = true)
    (hl : 0 < bv_unsigned l) :
    bv_unsigned b + bv_unsigned l ≤ 0x1000000 ∨ 0x1002000 ≤ bv_unsigned b := by
  rw [target_reserved_val] at hfree
  obtain ⟨h0, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨h1, _⟩ := region_free_cons _ _ _ _ _ hfree
  change bv_unsigned b + bv_unsigned l ≤ 0x1000000 ∨
    0x1001000 ≤ bv_unsigned b at h0
  change bv_unsigned b + bv_unsigned l ≤ 0x1001000 ∨
    0x1002000 ≤ bv_unsigned b at h1
  omega

/-! ## The target run's outcomes

Rocq's `Section TargetProof`: `inp asp arnd abrk amb` and the hypotheses
become explicit arguments. -/

theorem rtop_tgt_val : reserved_top (segments_reserved target_segs) = 0x1002000 := by
  rw [target_reserved_val]
  rfl

theorem abrk_lo_num (abrk : word)
    (hbrk_lo : reserved_top (segments_reserved target_segs) ≤ bv_unsigned abrk) :
    0x1002000 ≤ bv_unsigned abrk := by
  rw [← rtop_tgt_val]
  exact hbrk_lo

theorem abrk_hi_num (abrk : word)
    (hbrk_hi : bv_unsigned abrk ≤ reserved_top (segments_reserved target_segs) + brk_aslr_max) :
    bv_unsigned abrk ≤ 0x1002000 + 1073741824 := by
  rw [← rtop_tgt_val, ← brk_aslr_max_val]
  exact hbrk_hi

theorem abrk_lt64 (abrk : word) : bv_unsigned abrk < 2 ^ 64 := (u64_range abrk).2

/-- Below the stack window the frame memory is unmapped. -/
theorem tfmem_low_none (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (ha : bv_unsigned a < bv_unsigned asp - stack_max_size) :
    tfmem av ev uid hw asp arnd a = none := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hsms := stack_max_size_val
  have hbelow (k : Int) (hk : 8 ≤ k ∧ k ≤ 32)
      (m : word → Option byte) (v : word) :
      wbytes m (Z_to_bv 64 (bv_unsigned asp - k)) (word_to_le_bytes 8 v) a = m a := by
    have hu := u_Z2bv (bv_unsigned asp - k) (by omega) (by omega)
    apply wbytes_below
    · rw [length_N_to_le_bytes, hu]
      omega
    · rw [hu]
      omega
  unfold tfmem amem1
  rw [hbelow 32 (by omega), hbelow 24 (by omega),
    hbelow 16 (by omega), hbelow 8 (by omega)]
  have hsp : ¬ bv_unsigned asp ≤ bv_unsigned a := by omega
  have hlow : ¬ bv_unsigned asp - stack_max_size ≤ bv_unsigned a := by omega
  simp only [awmem, wrap_mem, stack_to_mem, hsp, hlow, ite_false,
    decide_false, Bool.false_and, Bool.false_eq_true]

/-! ### `argc ≥ 2` -/

/-- From the entry to the first `brk` ecall at `0x10011e8`, with `a0 = 0`
(the query) and `a3 = 4` (the failure code) in place. -/
theorem target_to_brk1 (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (hcap : (tnn inp.in_argv : Int) ≤ 65536) :
    ∃ regsB : bvmap 5 word,
      reg_get regsB 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regsB 8 = ptrA inp.in_argv inp.in_envp asp ∧
      reg_get regsB 10 = Z_to_bv 64 0 ∧
      reg_get regsB 11 = tnN inp.in_argv ∧
      reg_get regsB 13 = Z_to_bv 64 4 ∧
      msteps target_segs
        (init_machine_state target_segs 0x100115c target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regsB, ms_fregs := bvmap_empty, ms_pc_val := (0x10011e8 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0,
          ms_mem := tfmem inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap asp arnd,
          ms_rom := trom } := by
  obtain ⟨regs2, _, h2, h8, h10, hms⟩ :=
    target_to_captest inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap asp arnd
      hva hve hsp_lo hsp_hi hge2
  refine ⟨regupd (regupd (regupd (regupd (regupd regs2 12 (Z_to_bv 64 65536))
    11 (tnN inp.in_argv)) 10 (Z_to_bv 64 0)) 13 (Z_to_bv 64 4))
    17 (Z_to_bv 64 214), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cat_regs; exact h2
  · cat_regs; exact h8
  · cat_regs
  · cat_regs
  · cat_regs
  · refine msteps_trans target_segs _ _ _ hms ?_
    cat_step (step_lui_at target_segs _ _ _ _ _ _ _ (Z_to_bv 64 65536)
      TF_10011b0 (by decide) TD_10011b0 (by decide) (by rfl))
    cat_step (step_bgeu_tk target_segs _ _ _ _ _ _ _ _
      TF_10011b4 (by decide) TD_10011b4
      (by
        cat_regs
        rw [h10, c_ltu_ltb, u_tnN inp.in_argv hva hge2]
        change decide (65536 < (tnn inp.in_argv : Int)) = false
        exact decide_eq_false (by omega)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (tnN inp.in_argv)
      TF_10011c0 (by decide) TD_10011c0 (by decide)
      (by cat_regs; rw [h10]; exact v_addi_0 _))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      TF_10011c4 (by decide) TD_10011c4 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 4)
      TF_10011c8 (by decide) TD_10011c8 (by decide) (by cat_regs; rfl))
    cat_step (step_beq_tk target_segs _ _ _ _ _ _ _ _
      TF_10011cc (by decide) TD_10011cc (by cat_regs; exact c_eq_0_true))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      TF_10011e4 (by decide) TD_10011e4 (by decide) (by cat_regs; rfl))
    cat_step (step_ecall target_segs _ _ _ _ _ TF_10011e8 (by decide))
    cat_regs
    exact msteps.mst_refl _

/-- From the first `brk`'s return (`a0 = r`, nonzero) to the second `brk`
ecall at `0x1001204`, asking for `r + n`. -/
theorem target_to_brk2 (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (_hve : valid_envp inp.in_envp)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned asp) (_hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length)
    (regsB : bvmap 5 word) (r : word)
    (hB2 : reg_get regsB 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (hB8 : reg_get regsB 8 = ptrA inp.in_argv inp.in_envp asp)
    (hB11 : reg_get regsB 11 = tnN inp.in_argv)
    (hB13 : reg_get regsB 13 = Z_to_bv 64 4)
    (hr0 : r ≠ Z_to_bv 64 0)
    (hrw : bv_unsigned r + (tnn inp.in_argv : Int) < 2 ^ 64) :
    ∃ regs5 : bvmap 5 word,
      reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regs5 8 = ptrA inp.in_argv inp.in_envp asp ∧
      reg_get regs5 10 = r + tnN inp.in_argv ∧
      reg_get regs5 11 = tnN inp.in_argv ∧
      reg_get regs5 12 = r ∧
      reg_get regs5 13 = Z_to_bv 64 4 ∧
      reg_get regs5 14 = r + tnN inp.in_argv ∧
      msteps target_segs
        (mkst (regupd regsB 10 r) 0x10011ec
          (tfmem inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap asp arnd) trom)
        { ms_regs := regs5, ms_fregs := bvmap_empty, ms_pc_val := (0x1001204 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0,
          ms_mem := tfmem inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap asp arnd,
          ms_rom := trom } := by
  have hn := u_tnN inp.in_argv hva hge2
  have hsum : bv_unsigned r + bv_unsigned (tnN inp.in_argv) < 2 ^ 64 := by
    rw [hn]
    exact hrw
  have hu : bv_unsigned (r + tnN inp.in_argv) =
      bv_unsigned r + (tnn inp.in_argv : Int) := by
    rw [u_add_small _ _ hsum, hn]
  have hadd : v_add r (tnN inp.in_argv) = r + tnN inp.in_argv := by
    apply bv_eq_of_unsigned
    rw [v_add_small _ _ hsum, u_add_small _ _ hsum]
  refine ⟨regupd (regupd (regupd (regupd (regupd regsB 10 r) 12 r)
    14 (r + tnN inp.in_argv)) 17 (Z_to_bv 64 214)) 10 (r + tnN inp.in_argv),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cat_regs; exact hB2
  · cat_regs; exact hB8
  · cat_regs
  · cat_regs; exact hB11
  · cat_regs
  · cat_regs; exact hB13
  · cat_regs
  · cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
      TF_10011ec (by decide) TD_10011ec
      (by cat_regs; exact c_eq_0_false r (word_neq0_unsigned r hr0)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ r
      TF_10011f0 (by decide) TD_10011f0 (by decide)
      (by cat_regs; exact v_addi_0 r))
    cat_step (step_add_at target_segs _ _ _ _ _ _ _ _ (r + tnN inp.in_argv)
      TF_10011f4 (by decide) TD_10011f4 (by decide)
      (by cat_regs; rw [hB11]; exact hadd))
    cat_step (step_bltu_ft target_segs _ _ _ _ _ _ _ _
      TF_10011f8 (by decide) TD_10011f8
      (by cat_regs; rw [c_ltu_ltb, hu]; exact decide_eq_false (by omega)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      TF_10011fc (by decide) TD_10011fc (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (r + tnN inp.in_argv)
      TF_1001200 (by decide) TD_1001200 (by decide)
      (by cat_regs; exact v_addi_0 _))
    cat_step (step_ecall target_segs _ _ _ _ _ TF_1001204 (by decide))
    cat_regs
    exact msteps.mst_refl _

/-- The decimal-digit loop at `0x1001278`..`0x1001298`, writing the digits
of `v` into the stack buffer at `asp - 56`, right-aligned at offset `k`. -/
theorem target_udec_loop (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (f : Nat) (m : word → Option byte) (v k : Int) (regs : bvmap 5 word)
    (hv1 : 1 ≤ v) (hv64 : v < 2 ^ 64) (hvf : v < 10 ^ f)
    (hk1 : ((udec v).length : Int) ≤ k) (hk2 : k ≤ 23)
    (h10 : reg_get regs 10 = Z_to_bv 64 v)
    (h11 : reg_get regs 11 = Z_to_bv 64 k)
    (h12 : reg_get regs 12 = Z_to_bv 64 (bv_unsigned asp - 56))
    (h13 : reg_get regs 13 = Z_to_bv 64 10)
    (hgrow : mem_grows (awmem av ev uid hw asp arnd) m) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 10 → x ≠ 11 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 11 = Z_to_bv 64 (k - ((udec v).length : Int)) ∧
      msteps target_segs (mkst regs 0x1001278 m trom)
        (mkst regs' 0x100129c
          (wbytes m
            (Z_to_bv 64 (bv_unsigned asp - 56 + (k + 1 - ((udec v).length : Int))))
            (udec v)) trom) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  induction f generalizing m v k regs with
  | zero =>
    change v < 1 at hvf
    omega
  | succ f ih =>
    have hlen := udec_len_pos v
    have hd0 : 0 ≤ v % 10 := Int.emod_nonneg v (by decide)
    have hd9 : v % 10 < 10 := Int.emod_lt_of_pos v (by decide)
    have hq0 : 0 ≤ v / 10 := by omega
    have hq64 : v / 10 < 2 ^ 64 := by omega
    have hm0 : 0 ≤ v / 10 * 10 := by omega
    have hm64 : v / 10 * 10 < 2 ^ 64 := by omega
    have uv := u_Z2bv v (by omega) hv64
    have uk := u_Z2bv k (by omega) (by omega)
    have uq := u_Z2bv (v / 10) hq0 hq64
    have um := u_Z2bv (v / 10 * 10) hm0 hm64
    have ud := u_Z2bv (v % 10) hd0 (by omega)
    have uc := u_Z2bv (48 + v % 10) (by omega) (by omega)
    have ub := u_Z2bv (bv_unsigned asp - 56) (by omega) (by omega)
    have ua := u_Z2bv (bv_unsigned asp - 56 + k) (by omega) (by omega)
    have u10 : bv_unsigned (Z_to_bv 64 10) = 10 := by decide
    let r1 := regupd regs 14 (Z_to_bv 64 (v / 10))
    let r2 := regupd r1 15 (Z_to_bv 64 (bv_unsigned asp - 56 + k))
    let r3 := regupd r2 16 (Z_to_bv 64 (v / 10 * 10))
    let r4 := regupd r3 10 (Z_to_bv 64 (v % 10))
    let r5 := regupd r4 10 (Z_to_bv 64 (48 + v % 10))
    let m1 := wbytes m (Z_to_bv 64 (bv_unsigned asp - 56 + k))
      [Z_to_bv 8 (48 + v % 10)]
    let r7 := regupd r5 11 (Z_to_bv 64 (k - 1))
    let r8 := regupd r7 10 (Z_to_bv 64 (v / 10))
    have e1 : RiscvSemantics.step target_segs (mkst regs 0x1001278 m trom) =
        MachineOk (mkst r1 0x100127c m trom) := by
      rw [step_divu target_segs _ _ _ _ _ _ _ _ TF_1001278 (by decide)
        TD_1001278 (by cat_regs; rw [h13, u10]; decide)]
      simp only [show bv_eqb (14 : reg) 0 = false from rfl, Bool.false_eq_true,
        ↓reduceIte]
      have he : v_divu (getr regs 10) (getr regs 13) = Z_to_bv 64 (v / 10) := by
        cat_regs
        rw [h10, h13, v_divu, uv, u10]
      rw [he]
      rfl
    have e2 : RiscvSemantics.step target_segs (mkst r1 0x100127c m trom) =
        MachineOk (mkst r2 0x1001280 m trom) := by
      apply step_add_at target_segs _ _ _ _ _ _ _ _ _ TF_100127c (by decide)
        TD_100127c (by decide)
      dsimp only [r1]
      cat_regs
      rw [h12, h11, v_add, ub, uk]
    have e3 : RiscvSemantics.step target_segs (mkst r2 0x1001280 m trom) =
        MachineOk (mkst r3 0x1001284 m trom) := by
      apply step_mul_at target_segs _ _ _ _ _ _ _ _ _ TF_1001280 (by decide)
        TD_1001280 (by decide)
      dsimp only [r2, r1]
      cat_regs
      rw [h13, v_mul, uq, u10]
    have e4 : RiscvSemantics.step target_segs (mkst r3 0x1001284 m trom) =
        MachineOk (mkst r4 0x1001288 m trom) := by
      rw [step_subw target_segs _ _ _ _ _ _ _ _ TF_1001284 (by decide) TD_1001284]
      simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true,
        ↓reduceIte]
      have he : v_subw (getr r3 10) (getr r3 16) = Z_to_bv 64 (v % 10) := by
        dsimp only [r3, r2, r1]
        cat_regs
        rw [h10]
        apply bv_eq_of_unsigned
        rw [v_subw_small _ _ (by rw [uv, um]; omega)
          (by rw [uv, um]; omega), uv, um, ud]
        omega
      rw [he]
      rfl
    have e5 : RiscvSemantics.step target_segs (mkst r4 0x1001288 m trom) =
        MachineOk (mkst r5 0x100128c m trom) := by
      apply step_ori_at target_segs _ _ _ _ _ _ _ _ _ TF_1001288 (by decide)
        TD_1001288 (by decide)
      dsimp only [r4]
      cat_regs
      change v_ori (Z_to_bv 64 (v % 10)) 48 = _
      rw [v_ori_lor _ (by rw [ud]; omega), ud]
      congr 1
      omega
    have e6 : RiscvSemantics.step target_segs (mkst r5 0x100128c m trom) =
        MachineOk (mkst r5 0x1001290 m1 trom) := by
      apply step_sb_at target_segs _ _ _ _ _ _ _ _ _
        (Z_to_bv 64 (48 + v % 10)) _ TF_100128c (by decide) TD_100128c
      · dsimp only [r5, r4, r3, r2]
        cat_regs
        exact v_addi_0 _
      · dsimp only [r5]
        cat_regs
      · rw [uc]
      · apply store_ok_mono _ _ _ _ _ hgrow
        apply store_ok_wrap_window
        · rw [ua, stack_max_size_val]
          omega
        · rw [ua]
          omega
    have e7 : RiscvSemantics.step target_segs (mkst r5 0x1001290 m1 trom) =
        MachineOk (mkst r7 0x1001294 m1 trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ _ TF_1001290 (by decide)
        TD_1001290 (by decide)
      dsimp only [r5, r4, r3, r2, r1]
      cat_regs
      rw [h11]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) + (-1)) = _
      rw [uk]
      rfl
    have e8 : RiscvSemantics.step target_segs (mkst r7 0x1001294 m1 trom) =
        MachineOk (mkst r8 0x1001298 m1 trom) := by
      apply step_addi_at target_segs _ _ _ _ _ _ _ _ _ TF_1001294 (by decide)
        TD_1001294 (by decide)
      dsimp only [r7, r5, r4, r3, r2, r1]
      cat_regs
      exact v_addi_0 _
    have hprefix : msteps target_segs (mkst regs 0x1001278 m trom)
        (mkst r8 0x1001298 m1 trom) := by
      cat_step e1
      cat_step e2
      cat_step e3
      cat_step e4
      cat_step e5
      cat_step e6
      cat_step e7
      cat_step e8
      exact msteps.mst_refl _
    have hag : ∀ x : reg, x ≠ 10 → x ≠ 11 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get r8 x = reg_get regs x := by
      intro x hx10 hx11 hx14 hx15 hx16
      dsimp only [r8, r7, r5, r4, r3, r2, r1]
      simp (disch := assumption) only [regupd_other]
    have hr11 : reg_get r8 11 = Z_to_bv 64 (k - 1) := by
      dsimp only [r8, r7]
      cat_regs
    have hr14 : getr r8 14 = Z_to_bv 64 (v / 10) := by
      dsimp only [r8, r7, r5, r4, r3, r2, r1]
      cat_regs
    by_cases hsmall : v ≤ 9
    · have hq : v / 10 = 0 := by omega
      have hd : v % 10 = v := by omega
      have hu : udec v = [Z_to_bv 8 (48 + v % 10)] := by
        rw [hd]
        exact udec_single v ⟨hv1, hsmall⟩
      refine ⟨r8, hag, ?_, ?_⟩
      · rw [hr11, hu]
        rfl
      · have he : k + 1 - ((udec v).length : Int) = k := by
          rw [hu]
          simp only [List.length_singleton, Int.natCast_one]
          omega
        rw [he, hu]
        apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _ TF_1001298 (by decide)
          TD_1001298 (by rw [hr14, getr_zero, hq]; exact c_eq_0_true))
        exact msteps.mst_refl _
    · have hu := udec_step v (by omega) hv64
      have hl : ((udec v).length : Int) = ((udec (v / 10)).length : Int) + 1 := by
        rw [hu]
        simp only [List.length_append, List.length_singleton, Int.natCast_add,
          Int.natCast_one]
      have hqf : v / 10 < 10 ^ f := by
        rw [Int.pow_succ] at hvf
        generalize (10 : Int) ^ f = P at hvf ⊢
        omega
      obtain ⟨regs', hag', hr', hm'⟩ := ih m1 (v / 10) (k - 1) r8
        (by omega) hq64 hqf (by omega) (by omega)
        (by dsimp only [r8]; cat_regs) hr11
        (by rw [hag 12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12)
        (by rw [hag 13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h13)
        (mem_grows_trans _ _ _ hgrow (wbytes_grows _ _ _))
      refine ⟨regs', ?_, ?_, ?_⟩
      · intro x hx10 hx11 hx14 hx15 hx16
        rw [hag' x hx10 hx11 hx14 hx15 hx16, hag x hx10 hx11 hx14 hx15 hx16]
      · rw [hr', hl]
        congr 1
        omega
      · have hstart : k + 1 - ((udec v).length : Int) =
            k - ((udec (v / 10)).length : Int) := by omega
        have hstart' : k - 1 + 1 - ((udec (v / 10)).length : Int) =
            k - ((udec (v / 10)).length : Int) := by omega
        have us := u_Z2bv (bv_unsigned asp - 56 +
          (k - ((udec (v / 10)).length : Int))) (by omega) (by omega)
        have hend : Z_to_bv 64 (bv_unsigned asp - 56 +
              (k - ((udec (v / 10)).length : Int))) + nat_to_word (udec (v / 10)).length =
            Z_to_bv 64 (bv_unsigned asp - 56 + k) := by
          rw [word_add_nat, us]
          congr 1
          omega
        rw [hstart, hu, wbytes_app, hend,
          wbytes_disjoint_comm _ _ _ _ _ (by rw [us, ua]; omega)
            (by rw [ua]; simp only [List.length_singleton, Int.natCast_one]; omega)]
        rw [hstart'] at hm'
        apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _ TF_1001298 (by decide)
          TD_1001298 (by rw [hr14, getr_zero]; exact c_eq_0_false _ (by rw [uq]; omega)))
        exact hm'

/-- From `0x10012b0`, with the digits in place: write them, write the
newline, exit 0. -/
theorem target_print_tail (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (regs : bvmap 5 word) (M : word → Option byte) (sum : Int)
    (hs0 : 0 ≤ sum) (hs64 : sum < 2 ^ 64)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (h11 : reg_get regs 11 = Z_to_bv 64 (24 - ((udec sum).length : Int)))
    (hnl : M (0x1000158 : word) = none)
    (hra : rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x100117c : word)))
    (hs0r : rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp))
    (hgrow : mem_grows (awmem av ev uid hw asp arnd) M) :
    to_wallexit target_segs (Z_to_bv 64 1) [udec sum, [Z_to_bv 8 10]] (Z_to_bv 64 0)
      (mkst regs 0x10012b0
        (wbytes M
          (Z_to_bv 64 (bv_unsigned asp - 56 + (24 - ((udec sum).length : Int))))
          (udec sum)) trom) := by
  have _ := hgrow
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hpos := udec_len_pos sum
  have hlen := udec_len_le sum hs0 hs64
  let L : Int := (udec sum).length
  let base := Z_to_bv 64 (bv_unsigned asp - 56 + (24 - L))
  let Md := wbytes M base (udec sum)
  have hL0 : 1 ≤ L := by dsimp only [L]; omega
  have hL20 : L ≤ 20 := by dsimp only [L]; omega
  have huL : bv_unsigned (Z_to_bv 64 L) = L :=
    u_Z2bv _ (by omega) (by omega)
  have hu24L : bv_unsigned (Z_to_bv 64 (24 - L)) = 24 - L :=
    u_Z2bv _ (by omega) (by omega)
  have hu64 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) =
      bv_unsigned asp - 64 := u_Z2bv _ (by omega) (by omega)
  have hu56 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 56)) =
      bv_unsigned asp - 56 := u_Z2bv _ (by omega) (by omega)
  have hubase : bv_unsigned base = bv_unsigned asp - 56 + (24 - L) :=
    u_Z2bv _ (by omega) (by omega)
  have hnw : bv_unsigned base + ((udec sum).length : Int) ≤ 2 ^ 64 := by
    rw [hubase]
    change bv_unsigned asp - 56 + (24 - L) + L ≤ 2 ^ 64
    omega
  have hread : rdn target_segs Md base (word_to_nat (Z_to_bv 64 L)) =
      some (udec sum) := by
    have hn : word_to_nat (Z_to_bv 64 L) = (udec sum).length := by
      change (Z_to_bv 64 L).toNat = (udec sum).length
      change ((Z_to_bv 64 L).toNat : Int) = L at huL
      omega
    rw [hn]
    exact rdn_wbytes_hit _ _ _ _ hnw
  have hnewline : rdn target_segs Md (0x1000158 : word) 1 =
      some [Z_to_bv 8 10] := by
    rw [rdn_wbytes_below target_segs (udec sum) M base _ 1
      (by change 0x1000158 + 1 ≤ bv_unsigned base; rw [hubase]; omega) hnw]
    have hrom : seg_rom target_segs (0x1000158 : word) = some (Z_to_bv 8 10) := by
      have read_rom (segs : List Segment) (seg : Segment) (a : word) (b : byte)
          (hf : find_segment segs (bv_unsigned a) 1 = some seg)
          (hr : seg_readable seg = true)
          (hb : segment_read_bytes seg.seg_bytes
            (bv_unsigned a - (seg.seg_base : Int)).toNat 1 = some [b]) :
          seg_rom segs a = some b := by
        simp only [seg_rom, memory_read, Int.natCast_one, hf, hr, ↓reduceIte, hb]
      apply read_rom target_segs TargetMemImage_segment_000
      · rfl
      · decide
      · exact (TargetMemImage_segment_000_read_ascii 0x158 1).trans (by decide +kernel)
    simp only [rdn, hnl, hrom]
  have hsaved (k : Int) (hk : k = 24 ∨ k = 32) :
      rdn target_segs Md (Z_to_bv 64 (bv_unsigned asp - k)) 8 =
      rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - k)) 8 := by
    have hu := u_Z2bv (bv_unsigned asp - k) (by rcases hk with h | h <;> omega)
      (by rcases hk with h | h <;> omega)
    apply rdn_wbytes_disjoint
    · rw [hubase, hu]
      change bv_unsigned asp - 56 + (24 - L) + L ≤ bv_unsigned asp - k
      rcases hk with h | h <;> omega
    · rw [hu]
      rcases hk with h | h <;> omega
  change to_wallexit _ _ _ _ (mkst regs 0x10012b0 Md trom)
  refine ⟨hpos, ?_⟩
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 56)) TF_10012b0 (by decide) TD_10012b0
    (by decide) (by
      cat_regs
      rw [h2]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 8) = _
      rw [hu64]
      congr 1 <;> omega))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 24)
    TF_10012b4 (by decide) TD_10012b4 (by decide) (by cat_regs; rfl))
  cat_step (step_add_at target_segs _ _ _ _ _ _ _ _ base
    TF_10012b8 (by decide) TD_10012b8 (by decide) (by
      cat_regs
      rw [h11]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 56)) +
        bv_unsigned (Z_to_bv 64 (24 - L))) = base
      rw [hu56, hu24L]))
  cat_step (step_sub_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 L)
    TF_10012bc (by decide) TD_10012bc (by decide) (by
      cat_regs
      rw [h11]
      change Z_to_bv 64 (24 - bv_unsigned (Z_to_bv 64 (24 - L))) = _
      rw [hu24L]
      congr 1 <;> omega))
  cat_step (step_auipc_at target_segs _ _ _ _ _ _ _ (0x10012c0 : word)
    TF_10012c0 (by decide) TD_10012c0 (by decide) (by rfl))
  cat_step (step_jalr_link target_segs _ _ _ _ _ _ _ _ (0x10012c0 : word)
    TF_10012c4 (by decide) TD_10012c4 (by decide) (by cat_regs))
  refine (target_put _ Md (udec sum) base (Z_to_bv 64 L) (0x10012c8 : word)
    [[Z_to_bv 8 10]] (Z_to_bv 64 0)
    (by cat_regs; rfl) (by cat_regs) (by cat_regs)
    (by rw [huL]; omega) (by rw [huL]; omega) (by rfl) hread ?_).2
  intro regs1 hag1 h10_1
  refine ⟨by decide, ?_⟩
  cat_step (step_beq_tk target_segs _ _ _ _ _ _ _ _
    TF_10012c8 (by decide) TD_10012c8
    (by cat_regs; rw [h10_1]; exact c_eq_0_true))
  cat_step (step_lui_at target_segs _ _ _ _ _ _ _ (0x1000000 : word)
    TF_10012d4 (by decide) TD_10012d4 (by decide) (by rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (0x1000158 : word)
    TF_10012d8 (by decide) TD_10012d8 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    TF_10012dc (by decide) TD_10012dc (by decide) (by cat_regs; rfl))
  cat_step (step_auipc_at target_segs _ _ _ _ _ _ _ (0x10012e0 : word)
    TF_10012e0 (by decide) TD_10012e0 (by decide) (by rfl))
  cat_step (step_jalr_link target_segs _ _ _ _ _ _ _ _ (0x10012e0 : word)
    TF_10012e4 (by decide) TD_10012e4 (by decide) (by cat_regs))
  refine (target_put _ Md [Z_to_bv 8 10] (0x1000158 : word) (Z_to_bv 64 1)
    (0x10012e8 : word) [] (Z_to_bv 64 0)
    (by cat_regs; rfl) (by cat_regs) (by cat_regs)
    (by decide) (by decide) (by rfl) hnewline ?_).2
  intro regs2 hag2 h10_2
  cat_step (step_sltiu_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    TF_10012e8 (by decide) TD_10012e8 (by decide)
    (by cat_regs; rw [h10_2]; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    TF_10012ec (by decide) TD_10012ec (by decide) (by cat_regs; rfl))
  cat_step (step_andi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    TF_10012f0 (by decide) TD_10012f0 (by decide) (by cat_regs; rfl))
  cat_step (step_jal_x0 target_segs _ _ _ _ _ _ TF_10012f4 (by decide) TD_10012f4)
  apply target_exit asp hsp_lo hsp_hi
  · cat_regs
    rw [hag2 2 (by decide) (by decide) (by decide) (by decide)]
    cat_regs
    rw [hag1 2 (by decide) (by decide) (by decide) (by decide)]
    cat_regs
    exact h2
  · cat_regs
  · decide
  · rw [hsaved 24 (Or.inl rfl)]
    exact hra
  · rw [hsaved 32 (Or.inr rfl)]
    exact hs0r

/-- From `0x1001264` with the byte sum in `a0`: the decimal conversion and
the two writes, exit 0. -/
theorem target_success (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (regs : bvmap 5 word) (M : word → Option byte)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (h10 : reg_get regs 10 = Z_to_bv 64 (sumb (targ1 av)))
    (hnl : M (0x1000158 : word) = none)
    (hra : rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x100117c : word)))
    (hs0r : rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp))
    (hgrow : mem_grows (awmem av ev uid hw asp arnd) M) :
    to_wallexit target_segs (Z_to_bv 64 1) (outbufs (targ1 av)) (Z_to_bv 64 0)
      (mkst regs 0x1001264 M trom) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hsum0 := sumb_nonneg (targ1 av)
  have hsum64 : sumb (targ1 av) < 2 ^ 64 := by
    have hle := sumb_le (targ1 av) (targ1_bytes av hva hge2)
    have hlen := tnN_le av hva hge2
    change ((targ1 av).length : Int) ≤ 131071 at hlen
    omega
  have hlen := udec_len_le (sumb (targ1 av)) hsum0 hsum64
  have hpos := udec_len_pos (sumb (targ1 av))
  have usp := u_Z2bv (bv_unsigned asp - 64) (by omega) (by omega)
  unfold outbufs
  by_cases hz : sumb (targ1 av) = 0
  · have hudec : udec (sumb (targ1 av)) = [Z_to_bv 8 48] := by
      rw [hz]
      rfl
    apply msteps_to_wallexit (ms' :=
      mkst (regupd (regupd regs 10 (Z_to_bv 64 48)) 11 (Z_to_bv 64 23))
        0x10012b0 (wbytes M (Z_to_bv 64 (bv_unsigned asp - 33)) [Z_to_bv 8 48]) trom)
    · cat_step (step_beq_tk target_segs _ _ _ _ _ _ _ _
        TF_1001264 (by decide) TD_1001264
        (by cat_regs; rw [h10, hz]; exact c_eq_0_true))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 48)
        TF_10012a4 (by decide) TD_10012a4 (by decide) (by cat_regs; rfl))
      cat_step (step_sb_at target_segs _ _ _ _ _ _ _ _
        (Z_to_bv 64 (bv_unsigned asp - 33)) (Z_to_bv 64 48) (Z_to_bv 8 48)
        TF_10012a8 (by decide) TD_10012a8
        (by
          cat_regs
          rw [h2]
          change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 31) = _
          rw [usp]
          congr 1 <;> omega)
        (by cat_regs) (by rfl) (by
          apply store_ok_mono _ _ _ _ _ hgrow
          apply store_ok_wrap_window
          · rw [u_Z2bv _ (by omega) (by omega), stack_max_size_val]
            omega
          · rw [u_Z2bv _ (by omega) (by omega)]
            omega))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 23)
        TF_10012ac (by decide) TD_10012ac (by decide) (by cat_regs; rfl))
      exact msteps.mst_refl _
    · have hm : wbytes M (Z_to_bv 64 (bv_unsigned asp - 33)) [Z_to_bv 8 48] =
          wbytes M
            (Z_to_bv 64 (bv_unsigned asp - 56 +
              (24 - ((udec (sumb (targ1 av))).length : Int))))
            (udec (sumb (targ1 av))) := by
        rw [hudec]
        have ha : bv_unsigned asp - 33 = bv_unsigned asp - 56 + (24 - (1 : Int)) := by
          omega
        simp only [List.length_singleton, Int.natCast_one, ha]
      rw [hm]
      apply target_print_tail av ev uid hw asp arnd hsp_lo hsp_hi _ M _ hsum0 hsum64
      · cat_regs; exact h2
      · cat_regs; rw [hudec]; rfl
      · exact hnl
      · exact hra
      · exact hs0r
      · exact hgrow
  · let regsI := regupd
      (regupd (regupd regs 11 (Z_to_bv 64 23))
        12 (Z_to_bv 64 (bv_unsigned asp - 56))) 13 (Z_to_bv 64 10)
    obtain ⟨regsU, hagU, h11U, hmsU⟩ :=
      target_udec_loop av ev uid hw asp arnd hsp_lo hsp_hi
        25 M (sumb (targ1 av)) 23 regsI (by omega) hsum64
        (by omega) (by omega) (by omega)
        (by dsimp only [regsI]; cat_regs; exact h10)
        (by dsimp only [regsI]; cat_regs)
        (by dsimp only [regsI]; cat_regs)
        (by dsimp only [regsI]; cat_regs) hgrow
    apply msteps_to_wallexit (ms' := mkst regsU 0x100129c
      (wbytes M
        (Z_to_bv 64 (bv_unsigned asp - 56 + (24 - ((udec (sumb (targ1 av))).length : Int))))
        (udec (sumb (targ1 av)))) trom)
    · cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
        TF_1001264 (by decide) TD_1001264
        (by cat_regs; rw [h10]; exact c_eq_0_false _ (by
          rw [u_Z2bv _ hsum0 hsum64]; exact hz)))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 23)
        TF_1001268 (by decide) TD_1001268 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _
        (Z_to_bv 64 (bv_unsigned asp - 56))
        TF_100126c (by decide) TD_100126c (by decide) (by
          cat_regs
          rw [h2]
          change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 64)) + 8) = _
          rw [usp]
          congr 1 <;> omega))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 10)
        TF_1001270 (by decide) TD_1001270 (by decide) (by cat_regs; rfl))
      cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
        TF_1001274 (by decide) TD_1001274
        (by cat_regs; rw [h10]; exact c_eq_0_false _ (by
          rw [u_Z2bv _ hsum0 hsum64]; exact hz)))
      exact hmsU
    · apply msteps_to_wallexit (ms' :=
        mkst (regupd regsU 11 (Z_to_bv 64 (24 - ((udec (sumb (targ1 av))).length : Int))))
          0x10012b0
          (wbytes M
            (Z_to_bv 64 (bv_unsigned asp - 56 + (24 - ((udec (sumb (targ1 av))).length : Int))))
            (udec (sumb (targ1 av)))) trom)
      · cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _
          (Z_to_bv 64 (24 - ((udec (sumb (targ1 av))).length : Int)))
          TF_100129c (by decide) TD_100129c (by decide) (by
            cat_regs
            rw [h11U]
            change Z_to_bv 64 (bv_unsigned
              (Z_to_bv 64 (23 - ((udec (sumb (targ1 av))).length : Int))) + 1) = _
            rw [u_Z2bv _ (by omega) (by omega)]
            congr 1 <;> omega))
        cat_step (step_jal_x0 target_segs _ _ _ _ _ _
          TF_10012a0 (by decide) TD_10012a0)
        exact msteps.mst_refl _
      · apply target_print_tail av ev uid hw asp arnd hsp_lo hsp_hi _ M _ hsum0 hsum64
        · cat_regs
          rw [hagU 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
          dsimp only [regsI]
          cat_regs
          exact h2
        · cat_regs
        · exact hnl
        · exact hra
        · exact hs0r
        · exact hgrow

/-- `n = 0`: the second `brk` keeps the break, the copy and sum loops are
skipped, the output is `"0\n"`. -/
theorem target_run_empty (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (_hve : valid_envp ev) (hge2 : 2 ≤ av.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hnn0 : tnn av = 0) (regs5 : bvmap 5 word) (r : word)
    (_hrw : bv_unsigned r + (tnn av : Int) < 2 ^ 64)
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (h11 : reg_get regs5 11 = tnN av)
    (h12 : reg_get regs5 12 = r)
    (h14 : reg_get regs5 14 = r + tnN av) :
    to_wallexit target_segs (Z_to_bv 64 1) (outbufs (targ1 av)) (Z_to_bv 64 0)
      (mkst (regupd regs5 10 (r + tnN av)) 0x1001208 (tfmem av ev uid hw asp arnd) trom) := by
  have hn : tnN av = Z_to_bv 64 0 := by
    unfold tnN
    rw [hnn0]
    rfl
  have hempty : targ1 av = [] := List.length_eq_zero_iff.mp hnn0
  apply msteps_to_wallexit (ms' :=
    mkst (regupd (regupd (regupd (regupd regs5 10 (r + tnN av)) 10 r)
      13 (Z_to_bv 64 0)) 10 (Z_to_bv 64 0))
      0x1001264 (tfmem av ev uid hw asp arnd) trom)
  · cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _
      TF_1001208 (by decide) TD_1001208
      (by cat_regs; rw [h14]; exact c_eq_refl _))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ r
      TF_100120c (by decide) TD_100120c (by decide)
      (by cat_regs; rw [h12]; exact v_addi_0 _))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      TF_1001210 (by decide) TD_1001210 (by decide)
      (by cat_regs; rw [h11, hn]; rfl))
    cat_step (step_beq_tk target_segs _ _ _ _ _ _ _ _
      TF_1001214 (by decide) TD_1001214
      (by cat_regs; rw [h11, hn]; exact c_eq_0_true))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      TF_1001230 (by decide) TD_1001230 (by decide) (by cat_regs; rfl))
    cat_step (step_bgeu_tk target_segs _ _ _ _ _ _ _ _
      TF_1001234 (by decide) TD_1001234
      (by cat_regs; rw [h11, hn]; exact c_ltu_x0 _))
    exact msteps.mst_refl _
  · apply target_success av ev uid hw asp arnd hva hge2 hsp_lo hsp_hi
    · cat_regs
      exact h2
    · cat_regs
      rw [hempty]
      rfl
    · apply tfmem_low_none av ev uid hw asp arnd hsp_lo hsp_hi
      have hlo := asp_lo_num asp hsp_lo
      rw [stack_max_size_val]
      change (0x1000158 : Int) < bv_unsigned asp - 8388608
      omega
    · exact read_slot_ra_t av ev uid hw asp arnd hsp_lo hsp_hi
    · exact read_slot_s0_t av ev uid hw asp arnd hsp_lo hsp_hi
    · unfold tfmem amem1
      apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
      apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
      apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
      exact wbytes_grows _ _ _

/-- `n > 0` and the second `brk` granted: copy, sum over the zero-padded
grant, print. -/
theorem target_run_success (av ev : List (List byte)) (uid hw asp : word) (arnd : EntryDraw)
    (hva : valid_argv av) (hve : valid_envp ev) (hge2 : 2 ≤ av.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (regs5 : bvmap 5 word) (r grant : word)
    (hgrant : bv_unsigned (tnN av) ≤ bv_unsigned grant)
    (htotalgrant : ((8 * ((tnn av + 7) / 8) : Nat) : Int) ≤ bv_unsigned grant)
    (hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned asp - stack_max_size)
    (hr0 : 0 < bv_unsigned r)
    (hceil : bv_unsigned r + (tnn av : Int) ≤ bv_unsigned asp - stack_max_size)
    (hfree : region_free (segments_reserved target_segs) r (tnN av) = true)
    (hphysfree : region_free (segments_reserved target_segs) r grant = true)
    (hnnz : tnn av ≠ 0)
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (h8 : reg_get regs5 8 = ptrA av ev asp)
    (h11 : reg_get regs5 11 = tnN av)
    (h12 : reg_get regs5 12 = r)
    (h14 : reg_get regs5 14 = r + tnN av) :
    to_wallexit target_segs (Z_to_bv 64 1) (outbufs (targ1 av)) (Z_to_bv 64 0)
      (mkst (regupd regs5 10 (r + tnN av)) 0x1001208
        (zmem (tfmem av ev uid hw asp arnd) r grant) trom) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hsms := stack_max_size_val
  have hnu := u_tnN av hva hge2
  have hp := ptrA_bounds av ev asp hva hve hsp_hi hge2
  have hrw : bv_unsigned r + (tnn av : Int) < 2 ^ 64 := by omega
  have hgnw : bv_unsigned r + bv_unsigned grant ≤ 2 ^ 64 := by omega
  let chunks := (tnn av + 7) / 8
  let total := 8 * chunks
  have hchunks : 1 ≤ chunks := by dsimp only [chunks]; omega
  have hstop : 8 * (chunks - 1) < tnn av ∧ tnn av ≤ 8 * chunks := by
    dsimp only [chunks]; omega
  have htg : (total : Int) ≤ bv_unsigned grant := htotalgrant
  have htrw : bv_unsigned r + (total : Int) < 2 ^ 64 := by omega
  let mem0 := zmem (tfmem av ev uid hw asp arnd) r grant
  let M := wbytes mem0 r (targ1 av)
  let regsI := regupd (regupd (regupd regs5 10 (r + tnN av)) 10 r) 13 (tnN av)
  have hread : rdn target_segs mem0 (ptrA av ev asp) (tnn av + 1) =
      some (targ1 av ++ [Z_to_bv 8 0]) := by
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (Or.inr (by omega))]
    exact read_str_t av ev uid hw asp arnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨regsC, hagC, _, _, h13C, hmsC⟩ :=
    target_copy av ev asp hva hve hsp_lo hsp_hi hge2 r mem0
      (store_grant_zmem_prefix _ _ _ _ _ hgrant hgnw) hread hfree hr0 hceil hrw
      (tnn av) regsI (by omega) (Nat.le_refl _)
      (by dsimp only [regsI]; cat_regs; rw [h8, Nat.sub_self, word_add_0])
      (by dsimp only [regsI]; cat_regs; rw [Nat.sub_self, word_add_0])
      (by dsimp only [regsI]; cat_regs; rfl)
  simp only [Nat.sub_self, List.take_zero, wbytes] at hmsC
  have h11C : reg_get regsC 11 = tnN av := by
    rw [hagC 11 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [regsI]; cat_regs; exact h11
  have h12C : reg_get regsC 12 = r := by
    rw [hagC 12 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [regsI]; cat_regs; exact h12
  have hbyte : ∀ i, i < total →
      rdn target_segs M (r + nat_to_word i) 1 =
        some [(targ1 av).getD i (Z_to_bv 8 0)] := by
    intro i hi
    have hui : bv_unsigned (r + nat_to_word i) = bv_unsigned r + (i : Int) := by
      rw [word_add_nat]
      exact u_Z2bv _ (by omega) (by omega)
    by_cases hin : i < tnn av
    · exact rdn_nth _ _ _ _ _ i
        (rdn_wbytes_hit target_segs (targ1 av) mem0 r (by
          change bv_unsigned r + (tnn av : Int) ≤ 2 ^ 64
          omega)) hin
    · have hout : (targ1 av).getD i (Z_to_bv 8 0) = Z_to_bv 8 0 := by
        have hi : (targ1 av).length ≤ i := by change tnn av ≤ i; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
      rw [hout]
      change rdn target_segs (wbytes mem0 r (targ1 av)) _ 1 = _
      rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [hui]; change bv_unsigned r + (tnn av : Int) ≤ _; omega)
        (by rw [hui]; omega)]
      apply rdn_zmem_in1
      rw [hui]
      constructor <;> omega
  obtain ⟨regsS, hagS, h10S, hmsS⟩ :=
    target_sum av hva hge2 M r total hbyte htrw chunks 0
      (regupd regsC 10 (Z_to_bv 64 0)) hchunks
      (by omega) (by omega) (by exact Nat.zero_add _)
      (by cat_regs; rfl) (by cat_regs; exact h11C)
      (by cat_regs; rw [h12C, word_add_0]) (by cat_regs; exact h13C)
  apply msteps_to_wallexit (ms' := mkst regsS 0x1001264 M trom)
  · cat_step (step_bne_ft target_segs _ _ _ _ _ _ _ _
      TF_1001208 (by decide) TD_1001208
      (by cat_regs; rw [h14]; exact c_eq_refl _))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ r
      TF_100120c (by decide) TD_100120c (by decide)
      (by cat_regs; rw [h12]; exact v_addi_0 _))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (tnN av)
      TF_1001210 (by decide) TD_1001210 (by decide)
      (by cat_regs; rw [h11]; exact v_addi_0 _))
    cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _
      TF_1001214 (by decide) TD_1001214
      (by cat_regs; rw [h11]; exact c_eq_0_false _ (by rw [hnu]; omega)))
    apply msteps_trans _ _ _ _ hmsC
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      TF_1001230 (by decide) TD_1001230 (by decide) (by cat_regs; rfl))
    cat_step (step_bgeu_ft target_segs _ _ _ _ _ _ _ _
      TF_1001234 (by decide) TD_1001234 (by
        cat_regs
        rw [h13C, h11C, c_ltu_ltb, hnu]
        change decide (0 < (tnn av : Int)) = true
        exact decide_eq_true (by omega)))
    exact hmsS
  · apply target_success av ev uid hw asp arnd hva hge2 hsp_lo hsp_hi
    · rw [hagS 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      cat_regs
      rw [hagC 2 (by decide) (by decide) (by decide) (by decide)]
      dsimp only [regsI]; cat_regs; exact h2
    · exact h10S
    · have hcases := target_free_cases r grant hphysfree (by rw [hnu] at hgrant; omega)
      have hcasesn := target_free_cases r (tnN av) hfree (by rw [hnu]; omega)
      change wbytes mem0 r (targ1 av) (0x1000158 : word) = none
      have hm : wbytes mem0 r (targ1 av) (0x1000158 : word) =
          mem0 (0x1000158 : word) := by
        rcases hcasesn with hb | ha
        · apply wbytes_above
          change bv_unsigned r + (tnn av : Int) ≤ 0x1000158
          rw [hnu] at hb; omega
        · apply wbytes_below
          · change bv_unsigned r + (tnn av : Int) ≤ 2 ^ 64; omega
          · change 0x1000158 < bv_unsigned r; omega
      rw [hm]
      dsimp only [mem0]
      rw [zmem_out _ _ _ _ (by
        change 0x1000158 < bv_unsigned r ∨ bv_unsigned r + bv_unsigned grant ≤ 0x1000158
        rcases hcases with hb | ha
        · exact Or.inr (by omega)
        · exact Or.inl (by omega))]
      exact tfmem_low_none av ev uid hw asp arnd hsp_lo hsp_hi _ (by
        change 0x1000158 < bv_unsigned asp - stack_max_size; omega)
    · have hu := u_Z2bv (bv_unsigned asp - 24) (by omega) (by omega)
      change rdn target_segs (wbytes mem0 r (targ1 av)) _ 8 = _
      rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [hu]; change bv_unsigned r + (tnn av : Int) ≤ _; omega)
        (by rw [hu]; omega)]
      rw [rdn_zmem_out _ _ _ _ _ _ (by rw [hu]; omega)
        (Or.inr (by rw [hu]; omega))]
      exact read_slot_ra_t av ev uid hw asp arnd hsp_lo hsp_hi
    · have hu := u_Z2bv (bv_unsigned asp - 32) (by omega) (by omega)
      change rdn target_segs (wbytes mem0 r (targ1 av)) _ 8 = _
      rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [hu]; change bv_unsigned r + (tnn av : Int) ≤ _; omega)
        (by rw [hu]; omega)]
      rw [rdn_zmem_out _ _ _ _ _ _ (by rw [hu]; omega)
        (Or.inr (by rw [hu]; omega))]
      exact read_slot_s0_t av ev uid hw asp arnd hsp_lo hsp_hi
    · apply mem_grows_trans _ mem0 _ _ (wbytes_grows _ _ _)
      apply mem_grows_trans _ (tfmem av ev uid hw asp arnd) _
      · unfold tfmem amem1
        repeat first
          | apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
          | exact mem_grows_refl _
      · intro x hx
        change (if _ then some (Z_to_bv 8 0) else _) ≠ none
        split
        · exact Option.some_ne_none _
        · exact hx

/-- The target's outcome set under the length cap: `{([], 4)} ∪ {(outbufs s, 0)}`. -/
theorem target_outcomes (inp : ProcInput) (asp : word) (arnd : EntryDraw) (abrk amb : word)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp) (hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (hbrk_lo : reserved_top (segments_reserved target_segs) ≤ bv_unsigned abrk)
    (hbrk_hi : bv_unsigned abrk ≤ reserved_top (segments_reserved target_segs) + brk_aslr_max)
    (hge2 : 2 ≤ inp.in_argv.length)
    (hbrk_mod : bv_unsigned abrk % page_size = 0)
    (hcap : (tnn inp.in_argv : Int) ≤ 65536) :
    to_outcomes target_segs
      (init_machine_state target_segs 0x100115c target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (oobU (tnN inp.in_argv) (outbufs (targ1 inp.in_argv))) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hblo := abrk_lo_num abrk hbrk_lo
  have hbhi := abrk_hi_num abrk hbrk_hi
  have hsms := stack_max_size_val
  have hn := u_tnN inp.in_argv hva hge2
  have hr0 : abrk ≠ Z_to_bv 64 0 := by
    intro he
    have hu := congrArg bv_unsigned he
    change bv_unsigned abrk = 0 at hu
    omega
  have hnw : bv_unsigned abrk + (tnn inp.in_argv : Int) < 2 ^ 64 := by omega
  have hurn : bv_unsigned (abrk + tnN inp.in_argv) =
      bv_unsigned abrk + (tnn inp.in_argv : Int) := by
    rw [u_add_small _ _ (by rw [hn]; exact hnw), hn]
  have hwant0 : abrk + tnN inp.in_argv ≠ Z_to_bv 64 0 := by
    intro he
    have hu := congrArg bv_unsigned he
    rw [hurn] at hu
    change bv_unsigned abrk + (tnn inp.in_argv : Int) = 0 at hu
    omega
  let model := init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp
  let ledger := VmMaps.mkVmMapsFull (segments_reserved target_segs) [] []
    abrk abrk target_alloc_limit amb asp
  have hquery : ∀ r, brk_resolution_ok model (Z_to_bv 64 0) r ↔ r = abrk := by
    intro r
    change brk_r_ok ledger (Z_to_bv 64 0) r ↔ r = abrk
    exact brk_r_ok_query_iff ledger r
  have hmodel : brk_model (Z_to_bv 64 0) abrk model = model := by
    rw [brk_model_query abrk model rfl]
    rfl
  have hfd : fd1chan model := init_model_fd1chan _ _ _ _ _ _
  obtain ⟨regsB, hB2, hB8, hB10, hB11, hB13, hms⟩ :=
    target_to_brk1 inp asp arnd hva hve hsp_lo hsp_hi hge2 hcap
  apply tou_msteps _ _ _ _ _ hms
  apply tou_brk_r (x8 := Z_to_bv 64 214)
    (T' := T1 (segments_reserved target_segs) target_alloc_limit
      (bv_unsigned asp - stack_max_size) (tnN inp.in_argv) (outbufs (targ1 inp.in_argv)))
    (Hsvc := rfl) (Hno := by decide)
  · intro r hok
    change brk_resolution_ok model (reg_get regsB 10) r at hok
    rw [hB10] at hok
    have he := (hquery r).mp hok
    subst r
    change to_outcomes target_segs
      (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU abrk []
        (Sys.Mm.Mmap.brk_zeros (reg_get regsB 10) abrk abrk) (Sys.Mm.Mmap.brk_unmaps abrk abrk) [] [])))
      (brk_model (reg_get regsB 10) abrk model) _
    rw [hB10, brk_zeros_query, brk_unmaps_keep, adv_brk, apply_zeros_nil, hmodel]
    obtain ⟨regs5, h2, h8, h10, h11, h12, h13, h14, hms2⟩ :=
      target_to_brk2 inp asp arnd hva hve hsp_lo hsp_hi hge2
        regsB abrk hB2 hB8 hB11 hB13 hr0 hnw
    apply tou_msteps _ _ _ _ _ hms2
    apply tou_brk_r (x8 := Z_to_bv 64 214)
      (T' := T2 (abrk + tnN inp.in_argv) (outbufs (targ1 inp.in_argv)))
      (Hsvc := rfl) (Hno := by decide)
    · intro r2 hok2
      change brk_r_ok ledger (reg_get regs5 10) r2 at hok2
      rw [h10] at hok2
      have hcases := (brk_r_ok_grow_iff _ _ _ _ _ _ _ _ _ _
        (by rw [hurn]; omega) (by rw [hurn]; omega) (by rw [hurn]; omega)).mp hok2
      change to_outcomes target_segs
        (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU r2 []
          (Sys.Mm.Mmap.brk_zeros (reg_get regs5 10) r2 abrk) (Sys.Mm.Mmap.brk_unmaps r2 abrk) [] [])))
        (brk_model (reg_get regs5 10) r2 model) _
      rw [h10]
      by_cases he : r2 = abrk + tnN inp.in_argv
      · subst r2
        rw [brk_unmaps_grow _ _ (by rw [hurn]; omega)]
        by_cases hz : tnn inp.in_argv = 0
        · have hn0 : tnN inp.in_argv = Z_to_bv 64 0 := by
            unfold tnN
            rw [hz]
            rfl
          have hzs : Sys.Mm.Mmap.brk_zeros (abrk + tnN inp.in_argv)
              (abrk + tnN inp.in_argv) abrk = [] := by
            rw [hn0, word_add_0_r, brk_zeros_keep]
          rw [hzs, adv_brk, apply_zeros_nil]
          apply tou_equiv (U := fun o => o = (outbufs (targ1 inp.in_argv), Z_to_bv 64 0))
          · apply tou_wexit_eq
            · exact fd1chan_brk_model _ _ _ hfd
            · exact target_run_empty inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
                asp arnd hva hve hge2 hsp_lo hsp_hi hz regs5 abrk hnw h2 h11 h12 h14
            · exact outbufs_modeled _
          · exact T2_succ_iff _ _
        · have hgrow := hcases.2
          rw [brk_grow_ok_aligned_grow ledger _ _ hwant0 (by change 0 < bv_unsigned abrk; omega)
            (by change bv_unsigned abrk < bv_unsigned (abrk + tnN inp.in_argv); rw [hurn]; omega)
            hbrk_mod] at hgrow
          simp only [ledger, List.append_nil, Bool.and_eq_true, decide_eq_true_eq] at hgrow
          obtain ⟨⟨hceil, hfree⟩, _⟩ := hgrow
          let grant := Z_to_bv 64
            (page_round_up_Z (bv_unsigned (abrk + tnN inp.in_argv)) - bv_unsigned abrk)
          obtain ⟨hgu, hgrant, hphysceil, hrawceil, hrawfree, hgrantfree⟩ :=
            brk_aligned_grant_ok (segments_reserved target_segs) abrk (tnN inp.in_argv)
              grant (bv_unsigned abrk + (tnn inp.in_argv : Int))
              (bv_unsigned asp - stack_max_size)
              (by rw [hurn, hn]) hurn rfl (by change _ + 4096 < _; omega) hceil hfree
          have htotal : ((8 * ((tnn inp.in_argv + 7) / 8) : Nat) : Int) ≤ bv_unsigned grant := by
            rw [hgu, hurn]
            have hround := round8_le_page_grant (bv_unsigned abrk)
              (tnn inp.in_argv : Int) (by omega) (by omega) hbrk_mod
            omega
          rw [brk_zeros_aligned_grow _ _ _ hwant0 (by omega) (by rw [hurn]; omega)
            hbrk_mod, adv_brk, apply_zeros_one]
          apply tou_equiv (U := fun o => o = (outbufs (targ1 inp.in_argv), Z_to_bv 64 0))
          · apply tou_wexit_eq
            · exact fd1chan_brk_model _ _ _ hfd
            · exact target_run_success inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
                asp arnd hva hve hge2 hsp_lo hsp_hi regs5 abrk grant hgrant htotal
                hphysceil (by omega) hrawceil hrawfree hgrantfree hz h2 h8 h11 h12 h14
            · exact outbufs_modeled _
          · exact T2_succ_iff _ _
      · have hr2 : r2 = abrk := hcases.1.resolve_left he
        subst r2
        rw [brk_zeros_keep, brk_unmaps_keep, adv_brk, apply_zeros_nil]
        apply tou_equiv (U := fun o => o = ([], Z_to_bv 64 4))
        · apply tou_wexit_eq
          · exact fd1chan_brk_model _ _ _ hfd
          · change to_wexit target_segs _ [] (Z_to_bv 64 4)
            cat_step (step_bne_tk target_segs _ _ _ _ _ _ _ _
              TF_1001208 (by decide) TD_1001208
              (by cat_regs; rw [h14]; apply c_eq_neq; intro hu
                  exact he (bv_eq_of_unsigned _ _ hu)))
            apply target_exit asp hsp_lo hsp_hi
            · cat_regs; exact h2
            · cat_regs; exact h13
            · decide
            · exact read_slot_ra_t _ _ _ _ _ _ hsp_lo hsp_hi
            · exact read_slot_s0_t _ _ _ _ _ _ hsp_lo hsp_hi
          · intro b hb; cases hb
        · exact T2_fail_iff _ _ _ he
    · intro o
      change _ ↔ ∃ r2, brk_r_ok ledger (reg_get regs5 10) r2 ∧ _
      rw [h10]
      exact T1_iff_T2 _ _ abrk amb asp _ _ abrk hr0 (by omega) (by rw [hn]; exact hnw) o
  · intro o
    change _ ↔ ∃ r, brk_resolution_ok model (reg_get regsB 10) r ∧ _
    rw [hB10]
    apply oobU_iff_T1 _ _ _ _ _ abrk _ hquery
    refine ⟨hr0, ?_, ?_⟩
    · rw [hn]; exact hnw
    · by_cases hz : tnn inp.in_argv = 0
      · left
        unfold tnN
        rw [hz]
        rfl
      · right
        apply growable_aligned_grow _ _ _ _ _ hbrk_mod hbrk_lo
        · rw [hn]; omega
        · rw [hn]
          change _ + 4096 - 1 ≤ _
          omega
        · rw [hn]
          change _ ≤ (0x8000000000 : Int)
          omega

end LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target_outcomes
