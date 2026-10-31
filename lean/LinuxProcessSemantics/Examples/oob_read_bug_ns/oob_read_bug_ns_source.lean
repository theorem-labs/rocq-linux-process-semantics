import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs


/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/oob_read_bug_ns/oob_read_bug_ns_source.v` at
the baseline above; see that Rocq file for the argument.  Rocq's
`Section SourceProof` parameters (`inp rsp rrnd rbrk rmb` and the
hypotheses `Hva Hve Hsp_lo Hsp_hi Hbrk_lo Hbrk_hi Hge2 Hbrk_mod`) are
explicit arguments, and `av`/`ev` are spelled `inp.in_argv`/`inp.in_envp`.
`Z` becomes `Int`, `nat` becomes `Nat`, `nth j s d` becomes `s.getD j d`,
`firstn`/`skipn` become `List.take`/`List.drop`, `S n` becomes `n + 1`,
`Forall` becomes `∀ b ∈ s`, and `In a [..]` becomes `a ∈ [..]`.  The Rocq
`sym_block` reflective blocks are replaced by `cat_step` chains over the
explicit instruction lemmas, with `cat_regs` for register resolution.

`source_data_wseg` and `source_store_ok` follow the modprint_ns port: the
two binaries share the 0x13000 data page layout.

unported: nN_le' -- section-closed restatement of `nN_le` under `Hge2`; without sections the primed form has nothing to add.
unported: u_nN' -- section-closed restatement of `u_nN`; same reason.
unported: ptr_lo' -- section-closed restatement of `ptr_lo`; same reason.
unported: ptr_hi' -- section-closed restatement of `ptr_hi`; same reason.
unported: ptr_hi8' -- section-closed restatement of `ptr_hi8`; same reason.
unported: sumb_nonneg -- lives in the defs file, where the target file reaches it too.
unported: argcN -- `Common/ArgvEnv.lean` carries the same definition under the same name; the example reaches that one.
unported: u_argcN -- `Common/ArgvEnv.lean` carries the same statement under the same name; the example reaches that one.
unported: wmem -- ported as `oob_wmem`: `Common/ArgvEnv.lean` owns the name `wmem` for the general form over the phdrs, argv and envp; this one is specialised to the example's `ProcInput`.
unported: rdn_wmem_stack -- ported as `oob_rdn_wmem_stack`, over `oob_wmem`; `Common/ArgvEnv.lean` owns the name for the general form.
unported: read_argc_w -- ported as `oob_read_argc_w`, over `oob_wmem`; same reason. -/

namespace LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_source

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
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_code
open LinuxProcessSemantics.Examples.oob_read_bug_ns.SourceMemImage
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs
open LinuxProcessSemantics.Common.ArgvEnv (argcN u_argcN)

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

local macro "cat_regs" : tactic =>
  `(tactic| simp (disch := decide) only [getr_nz, getr_zero, regupd_same, regupd_other])

local macro "cat_step " h:term : tactic =>
  `(tactic| first
    | refine to_wexit.tw_step _ _ _ _ rfl $h ?_
    | refine to_wall_tail.twt_step _ _ _ _ rfl $h ?_
    | refine msteps.mst_step _ _ _ rfl $h ?_)

/-- The source's instruction ROM, Rocq's `rrom`. -/
def rrom : word → Option byte := seg_rom source_segs

theorem source_init_pc_val : SourceMemImage_init_pc = 0x111c8 := rfl

theorem word_add_nat_split (r : word) (m j : Nat)
    (h : bv_unsigned r + (m : Int) + (j : Int) < 2 ^ 64) :
    v_add (r + nat_to_word m) (nat_to_word j) = r + nat_to_word (m + j) := by
  have hr := (u64_range r).1
  unfold v_add
  rw [word_add_nat, u_Z2bv _ (by omega) (by omega), u_ntw j (by omega),
    word_add_nat, Int.natCast_add, Int.add_assoc]

theorem v_addi_nat_add (k n : Nat) (h : (k : Int) + (n : Int) < 2 ^ 64) :
    v_addi (nat_to_word k) (n : Int) = nat_to_word (k + n) := by
  rw [v_addi, u_ntw k (by omega), nat_to_word, Int.natCast_add]

theorem v_addi_off_nat_add (r : word) (k n : Nat)
    (h : bv_unsigned r + (k : Int) + (n : Int) < 2 ^ 64) :
    v_addi (r + nat_to_word k) (n : Int) = r + nat_to_word (k + n) := by
  have hr := u64_range r
  rw [word_add_nat, v_addi, u_Z2bv _ (by omega) (by omega),
    word_add_nat, Int.natCast_add, Int.add_assoc]

theorem source_reserved_val :
    segments_reserved source_segs =
      [(0x10000, 0x1000), (0x11000, 0x1000), (0x12000, 0x1000), (0x13000, 0x1000)] := by
  decide +kernel

theorem source_avoids_stack (a : word) (n : Int) (ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true := by
  simp only [range_avoids_ro_segs, source_segs, Source.loaded_segments,
    SourceMemImage_loaded_segments, List.all_cons, List.all_nil,
    SourceMemImage_segment_000, SourceMemImage_segment_001,
    SourceMemImage_segment_002, SourceMemImage_segment_003]
  change
    ((! (decide (0x10000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x11000))) &&
      ((! (decide (0x11000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x12000))) &&
        ((! (decide (0x12000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x13000))) &&
          true))) = true
  have h0 : ¬ bv_unsigned a < 0x11000 := by omega
  have h1 : ¬ bv_unsigned a < 0x12000 := by omega
  have h2 : ¬ bv_unsigned a < 0x13000 := by omega
  simp only [h0, h1, h2, decide_false, Bool.and_false, Bool.not_false,
    Bool.and_true]

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  have hchars := SourceMemImage_seg_bytes_003_hex
  have hlen : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  have window (n : Nat) (a : word) (hlo : 0x13000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
      wseg_ok source_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment source_segs (bv_unsigned a) 1 = some SourceMemImage_segment_003 := by
        simp only [source_segs, Source.loaded_segments, SourceMemImage_loaded_segments,
          find_segment, SourceMemImage_segment_000, SourceMemImage_segment_001, SourceMemImage_segment_002, SourceMemImage_segment_003]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        repeat
          first | split | omega | rfl
      have hoff : (bv_unsigned a - 0x13000).toNat < 4096 := by omega
      have hb : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - 0x13000).toNat).isSome = true := by
        rw [SourceMemImage_segment_003_byte_ascii]
        simp only [ascii_segment_byte_at, hlen]
        rw [ite_eq_left (by omega)]
        exact hex_chars_byte_at_isSome _ _ hchars (by omega)
      have hu : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      have hw : seg_writable SourceMemImage_segment_003 = true := by decide +kernel
      rw [wseg_ok]
      simp only [hf, hw, ht, Bool.true_and, Bool.and_true]
      have hb' : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat).isSome = true := hb
      cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb'
      | some b => rfl
  exact window 4096 0x13000 (by decide +kernel) (by decide +kernel)

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true := by
  exact store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) source_data_wseg hlo hhi

theorem source_free_cases (b l : word)
    (hfree : region_free (segments_reserved source_segs) b l = true)
    (hl : 0 < bv_unsigned l) :
    bv_unsigned b + bv_unsigned l ≤ 0x10000 ∨ 0x14000 ≤ bv_unsigned b := by
  rw [source_reserved_val] at hfree
  obtain ⟨h0, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨h1, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨h2, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨h3, _⟩ := region_free_cons _ _ _ _ _ hfree
  change bv_unsigned b + bv_unsigned l ≤ 0x10000 ∨ 0x11000 ≤ bv_unsigned b at h0
  change bv_unsigned b + bv_unsigned l ≤ 0x11000 ∨ 0x12000 ≤ bv_unsigned b at h1
  change bv_unsigned b + bv_unsigned l ≤ 0x12000 ∨ 0x13000 ≤ bv_unsigned b at h2
  change bv_unsigned b + bv_unsigned l ≤ 0x13000 ∨ 0x14000 ≤ bv_unsigned b at h3
  omega

theorem source_free_avoids (b l : word)
    (hfree : region_free (segments_reserved source_segs) b l = true)
    (_hl : 0 < bv_unsigned l) (a k : Int) (ha : bv_unsigned b ≤ a)
    (hk : a + k ≤ bv_unsigned b + bv_unsigned l) :
    range_avoids_ro_segs source_segs a k = true := by
  rw [source_reserved_val] at hfree
  change
    (!(decide (bv_unsigned b < 0x11000) &&
        decide (0x10000 < bv_unsigned b + bv_unsigned l)) &&
      (!(decide (bv_unsigned b < 0x12000) &&
          decide (0x11000 < bv_unsigned b + bv_unsigned l)) &&
        (!(decide (bv_unsigned b < 0x13000) &&
            decide (0x12000 < bv_unsigned b + bv_unsigned l)) &&
          (!(decide (bv_unsigned b < 0x14000) &&
              decide (0x13000 < bv_unsigned b + bv_unsigned l)) && true)))) = true at hfree
  change
    (!(decide (0x10000 < a + k) && decide (a < 0x11000)) &&
      (!(decide (0x11000 < a + k) && decide (a < 0x12000)) &&
        (!(decide (0x12000 < a + k) && decide (a < 0x13000)) && true))) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, and_true] at hfree ⊢
  omega

theorem srom_none_hi (a : word) (ha : 0x14000 ≤ bv_unsigned a) :
    seg_rom source_segs a = none := by
  have hf : find_segment source_segs (bv_unsigned a) 1 = none := by
    simp only [source_segs, Source.loaded_segments, SourceMemImage_loaded_segments,
      find_segment, SourceMemImage_segment_000, SourceMemImage_segment_001,
      SourceMemImage_segment_002, SourceMemImage_segment_003]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    repeat
      first | split | omega | rfl
  simp only [seg_rom, memory_read, Int.natCast_one, hf]

theorem rdn_window (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat)
    (bs : List byte) (j k : Nat) (h : rdn segs mem a n = some bs) (hjk : j + k ≤ n) :
    rdn segs mem (a + nat_to_word j) k = some ((bs.drop j).take k) := by
  have hs := rdn_skipn segs mem n a bs j h (by omega)
  exact rdn_firstn segs mem (n - j) (a + nat_to_word j) (bs.drop j) k hs (by omega)

theorem zmem0 (mem : word → Option byte) (b : word) : zmem mem b (Z_to_bv 64 0) = mem := by
  funext a
  apply zmem_out
  change bv_unsigned a < bv_unsigned b ∨ bv_unsigned b + 0 ≤ bv_unsigned a
  omega

theorem bsb_tail16 (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) :
    ∃ tail : List byte,
      build_stack_bytes ph sp av ev uid hw rnd =
        cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail ∧
      16 ≤ tail.length := by
  unfold build_stack_bytes cat_struct_prefix cat_env_base cat_string_base
  dsimp only
  rw [string_addrs_pair av]
  dsimp only
  rw [string_addrs_pair ev]
  dsimp only
  rw [length_auxv_bytes]
  refine ⟨_, (by simp only [List.append_assoc]; rfl), ?_⟩
  simp only [List.length_append, List.length_replicate, length_at_random_bytes]
  omega

theorem read_argv_str_tail (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    ∃ tl : List byte, tl.length = 7 ∧
      bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 8 ≤
        bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) ∧
      rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k)
        ((av.getD k []).length + 8) =
        some (av.getD k [] ++ [Z_to_bv 8 0] ++ tl) := by
  obtain ⟨tail, htail, htailLen⟩ := bsb_tail16 ph sp av ev uid hw rnd
  let pre := cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (av.take k)
  let post := flatten_strings (av.drop (k + 1)) ++ tail
  have hsplit : build_stack_bytes ph sp av ev uid hw rnd =
      pre ++ ((av.getD k [] ++ [Z_to_bv 8 0]) ++ post) := by
    rw [htail, flatten_strings_decomp av k hk]
    simp only [pre, post, List.append_assoc]
  have hpost : 7 ≤ post.length := by
    dsimp only [post]
    rw [List.length_append]
    omega
  have htake : (post.take 7).length = 7 := by
    rw [List.length_take, Nat.min_eq_left hpost]
  have hpre : pre.length = cat_struct_size av ev + total_arg_bytes_nat (av.take k) := by
    simp only [pre, List.length_append, length_cat_struct_prefix, length_flatten_strings]
  have hptr : cat_argv_ptr sp av ev k = sp + nat_to_word pre.length := by
    rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base,
      nat_to_word_add_merge, hpre]
  have hlen : (build_stack_bytes ph sp av ev uid hw rnd).length =
      pre.length + ((av.getD k []).length + 1 + post.length) := by
    rw [hsplit]
    simp only [List.length_append, List.length_singleton]
  have hsp := (u64_range sp).1
  have hu : bv_unsigned (sp + nat_to_word pre.length) =
      bv_unsigned sp + (pre.length : Int) := by
    rw [word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  refine ⟨post.take 7, htake, ?_, ?_⟩
  · rw [hptr, hu]
    omega
  · rw [hptr]
    apply read_at_offset_image segs ph sp av ev uid hw rnd pre
      (av.getD k [] ++ [Z_to_bv 8 0] ++ post.take 7) (post.drop 7)
      ((av.getD k []).length + 8) _ _ hnw
    · rw [hsplit]
      simp only [List.append_assoc, List.take_append_drop]
    · simp only [List.length_append, List.length_singleton, htake]

/-! ## The source run

Rocq's `Section SourceProof`: `inp rsp rrnd` and the hypotheses become
explicit arguments. -/

theorem rsp_lo_num (rsp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) :
    0x7fff80000000 ≤ bv_unsigned rsp := hsp_lo

theorem rsp_hi_num (rsp : word) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp ≤ 0x800000000000 := hsp_hi

theorem rtop_src_val : reserved_top (segments_reserved source_segs) = 0x14000 := by
  rw [source_reserved_val]
  rfl

theorem rbrk_lo_num (rbrk : word)
    (hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk) :
    0x14000 ≤ bv_unsigned rbrk := by
  rw [← rtop_src_val]
  exact hbrk_lo

theorem rbrk_hi_num (rbrk : word)
    (hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max) :
    bv_unsigned rbrk ≤ 0x14000 + 1073741824 := by
  rw [← rtop_src_val, ← brk_aslr_max_val]
  exact hbrk_hi

theorem rbrk_lt64 (rbrk : word) : bv_unsigned rbrk < 2 ^ 64 := (u64_range rbrk).2

/-- Rocq's `wmem`: the source's wrapped entry memory, specialised to this
example's `ProcInput`; `Common/ArgvEnv.lean`'s `wmem` is the general form. -/
def oob_wmem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wrap_mem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd

theorem argcN_le (av : List (List byte)) (hva : valid_argv av) :
    bv_unsigned (argcN av) ≤ 1024 := by
  rw [u_argcN av hva]
  exact valid_argv_len av hva

theorem source_bsb_nw (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp +
      ((build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
        rrnd).length : Int) < 2 ^ 64 := by
  have hlen := bsb_bound source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd hva hve
  have hhi := rsp_hi_num rsp hsp_hi
  omega

/-- Rocq's `envp_val`. -/
def envp_val (av : List (List byte)) (rsp : word) : word :=
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * (av.length : Int))

theorem envp_val_eq (av : List (List byte)) (rsp : word) (hva : valid_argv av)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3)) 8 = envp_val av rsp := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hlen := valid_argv_len av hva
  have hargc : bv_unsigned (argcN av) = (av.length : Int) :=
    u_len_word av (by omega)
  have hshift : bv_unsigned (v_slli (argcN av) 3) = 8 * (av.length : Int) := by
    rw [v_slli_3 _ (by omega), hargc]
  have hptr : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + 8)) =
      bv_unsigned rsp + 8 := u_Z2bv _ (by omega) (by omega)
  unfold v_addi envp_val
  rw [v_add_small _ _ (by rw [hptr, hshift]; omega), hptr, hshift]
  congr 1
  omega

/-- Rocq's `emem`: `wmem` after the `envp` store to `0x13000`. -/
def emem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wbytes (oob_wmem inp rsp rrnd) 0x13000 (word_to_le_bytes 8 (envp_val inp.in_argv rsp))

/-- Rocq's `fmem`: main()'s 80-byte frame (stores in execution order; sp = rsp - 80).
gcc 15 with `-fno-builtin` saves s0/ra/s1/s2 in that order. -/
def fmem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x111f4 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))

theorem rdn_emem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (_hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (ha : bv_unsigned rsp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (emem inp rsp rrnd) a n = rdn source_segs (oob_wmem inp rsp rrnd) a n := by
  unfold emem
  apply rdn_wbytes_disjoint _ _ _ _ _ _ ?_ hn
  rw [length_N_to_le_bytes]
  have hlo := rsp_lo_num rsp hsp_lo
  change (0x13000 : Int) + 8 ≤ bv_unsigned a
  omega

theorem rdn_fmem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (ha : bv_unsigned rsp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (fmem inp rsp rrnd) a n = rdn source_segs (oob_wmem inp rsp rrnd) a n := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]; omega) hn]
  exact rdn_emem_above inp rsp rrnd hsp_lo hsp_hi a n ha hn

theorem oob_rdn_wmem_stack (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (a : word) (n : Nat) (ha : bv_unsigned rsp ≤ bv_unsigned a)
    (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (oob_wmem inp rsp rrnd) a n =
      rdn source_segs
        (stack_to_mem rsp (entry_stack_image source_phdrs rsp inp.in_argv inp.in_envp
          inp.in_uid inp.in_hwcap rrnd)) a n :=
  rdn_wrap_stack_above source_segs source_phdrs rsp inp.in_argv inp.in_envp a n
    inp.in_uid inp.in_hwcap rrnd ha hn

theorem oob_read_argc_w (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    rdn source_segs (oob_wmem inp rsp rrnd) rsp 8 = some (word_le8 (argcN inp.in_argv)) := by
  have hhi := rsp_hi_num rsp hsp_hi
  have hlen := bsb_bound source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd hva hve
  rw [oob_rdn_wmem_stack inp rsp rrnd rsp 8 (by omega) (by omega)]
  exact read_argc source_phdrs source_segs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd (by omega)

/-- Rocq's `arg1`: `argv[1]`. -/
def arg1 (av : List (List byte)) : List byte := av.getD 1 []

/-- Rocq's `nn`: `strlen (argv[1])`. -/
def nn (av : List (List byte)) : Nat := (arg1 av).length

/-- Rocq's `nN`: `nn` as a word. -/
def nN (av : List (List byte)) : word := nat_to_word (nn av)

/-- Rocq's `ptr`: the address of `argv[1]` on the entry stack. -/
def ptr (av ev : List (List byte)) (rsp : word) : word := cat_argv_ptr rsp av ev 1

/-! ### `argc ≥ 2` (Rocq's `Section Ge2`) -/

theorem nN_le (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    (nn av : Int) ≤ 131071 := by
  unfold nn arg1
  exact valid_argv_str_len av 1 hva (by omega)

theorem u_nN (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    bv_unsigned (nN av) = (nn av : Int) := by
  have := nN_le av hva hge2
  unfold nN
  exact u_ntw _ (by omega)

theorem arg1_nz (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    Z_to_bv 8 0 ∉ arg1 av := by
  unfold arg1
  exact valid_argv_str_nz av 1 hva (by omega)

theorem arg1_bytes (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length) :
    ∀ b ∈ arg1 av, bv_unsigned b < 256 := by
  unfold arg1
  exact valid_argv_str_bytes av 1 hva (by omega)

theorem ptr_bounds (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned rsp ≤ bv_unsigned (ptr av ev rsp) ∧
      bv_unsigned (ptr av ev rsp) + (nn av : Int) + 1 < 2 ^ 64 := by
  unfold ptr nn arg1
  apply argv_ptr_bounds rsp av ev 1 hva hve (by omega)
  have hhi := rsp_hi_num rsp hsp_hi
  unfold argv_layout_slack
  omega

theorem ptr_lo (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned rsp ≤ bv_unsigned (ptr av ev rsp) :=
  (ptr_bounds av ev rsp hva hve hsp_lo hsp_hi hge2).1

theorem ptr_hi (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned (ptr av ev rsp) + (nn av : Int) + 1 < 2 ^ 64 :=
  (ptr_bounds av ev rsp hva hve hsp_lo hsp_hi hge2).2

theorem ptr_hi8 (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) :
    bv_unsigned (ptr av ev rsp) + (nn av : Int) + 8 < 2 ^ 64 := by
  have hsp := rsp_hi_num rsp hsp_hi
  have hr := (u64_range rsp).1
  have hn := nN_le av hva hge2
  have hav := valid_argv_len av hva
  have hev : (ev.length : Int) ≤ 256 := hve.1
  have htot := hva.2.1
  rw [total_arg_bytes_Z] at htot
  have htake := total_arg_bytes_firstn_le 1 av
  have hsize : (cat_struct_size av ev : Int) ≤ 10424 := by
    unfold cat_struct_size StackLayout.auxv_size
    omega
  have hoff :
      ((cat_struct_size av ev + total_arg_bytes_nat (av.take 1) : Nat) : Int) ≤
        2107576 := by omega
  unfold ptr
  rw [cat_argv_ptr_offset rsp av ev 1 (by omega)]
  unfold cat_string_base
  rw [nat_to_word_add_merge, word_add_nat, u_Z2bv _ (by omega) (by omega)]
  omega

theorem read_str_f (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) :
    rdn source_segs (fmem inp rsp rrnd) (ptr inp.in_argv inp.in_envp rsp) (nn inp.in_argv + 1) =
      some (arg1 inp.in_argv ++ [Z_to_bv 8 0]) := by
  obtain ⟨hlo, hhi⟩ := ptr_bounds inp.in_argv inp.in_envp rsp
    hva hve hsp_lo hsp_hi hge2
  have hrlo := rsp_lo_num rsp hsp_lo
  have hrhi := rsp_hi_num rsp hsp_hi
  have hnw := source_bsb_nw inp rsp rrnd hva hve hsp_lo hsp_hi
  unfold fmem
  simp (disch := (first | omega |
    (simp (disch := omega) only [length_N_to_le_bytes, u_Z2bv]; omega)))
    only [rdn_wbytes_disjoint]
  rw [rdn_emem_above inp rsp rrnd hsp_lo hsp_hi _ _ hlo (by omega),
    oob_rdn_wmem_stack inp rsp rrnd _ _ hlo (by omega)]
  apply rdn_app
  · exact read_argv_str_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1
      inp.in_uid inp.in_hwcap rrnd (by omega) hnw
  · have hb := read_argv_byte_k source_phdrs source_segs rsp inp.in_argv inp.in_envp
      1 (nn inp.in_argv) inp.in_uid inp.in_hwcap rrnd (by omega) (Nat.le_refl _) hnw
    have hz : (inp.in_argv.getD 1 [] ++ [Z_to_bv 8 0]).getD
        (nn inp.in_argv) (Z_to_bv 8 0) = Z_to_bv 8 0 :=
      byte_at_len (arg1 inp.in_argv)
    rw [hz] at hb
    exact hb

theorem read_str_f8 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) :
    ∃ tl : List byte, tl.length = 7 ∧
      rdn source_segs (fmem inp rsp rrnd) (ptr inp.in_argv inp.in_envp rsp) (nn inp.in_argv + 8) =
        some (arg1 inp.in_argv ++ [Z_to_bv 8 0] ++ tl) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hnw := source_bsb_nw inp rsp rrnd hva hve hsp_lo hsp_hi
  obtain ⟨tail, hbuild, htail⟩ := bsb_tail16 source_phdrs rsp
    inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd
  let pre := cat_struct_prefix source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap ++ flatten_strings (inp.in_argv.take 1)
  let post := flatten_strings (inp.in_argv.drop (1 + 1)) ++ tail
  have hsplit : build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap rrnd =
      pre ++ ((arg1 inp.in_argv ++ [Z_to_bv 8 0]) ++ post) := by
    rw [hbuild, flatten_strings_decomp inp.in_argv 1 (by omega)]
    simp only [pre, post, arg1, List.append_assoc]
  have hpost : 7 ≤ post.length := by
    dsimp only [post]
    rw [List.length_append]
    omega
  have htl : (post.take 7).length = 7 := by
    rw [List.length_take, Nat.min_eq_left hpost]
  have hpre : ptr inp.in_argv inp.in_envp rsp = rsp + nat_to_word pre.length := by
    simp only [pre, List.length_append, length_cat_struct_prefix,
      length_flatten_strings, ptr, cat_argv_ptr_offset rsp inp.in_argv inp.in_envp 1
        (by omega), cat_string_base, nat_to_word_add_merge]
  have hlen : pre.length + (nn inp.in_argv + 8) ≤
      (build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap rrnd).length := by
    rw [hsplit]
    simp only [List.length_append, List.length_cons, List.length_nil]
    change pre.length + (nn inp.in_argv + 8) ≤
      pre.length + ((nn inp.in_argv + (0 + 1)) + post.length)
    omega
  have hu : bv_unsigned (ptr inp.in_argv inp.in_envp rsp) =
      bv_unsigned rsp + (pre.length : Int) := by
    rw [hpre, word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  have hp : bv_unsigned rsp ≤ bv_unsigned (ptr inp.in_argv inp.in_envp rsp) := by
    rw [hu]
    omega
  have hend : bv_unsigned (ptr inp.in_argv inp.in_envp rsp) +
      ((nn inp.in_argv + 8 : Nat) : Int) ≤ 2 ^ 64 := by
    rw [hu]
    omega
  refine ⟨post.take 7, htl, ?_⟩
  unfold fmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]; omega) hend]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]; omega) hend]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]; omega) hend]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]; omega) hend]
  rw [rdn_emem_above inp rsp rrnd hsp_lo hsp_hi _ _ hp hend,
    oob_rdn_wmem_stack inp rsp rrnd _ _ hp hend, hpre]
  apply read_at_offset_image source_segs source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd pre _ (post.drop 7) _ ?_ ?_ hnw
  · rw [hsplit]
    simp only [List.append_assoc, List.take_append_drop]
  · simp only [List.length_append, List.length_cons, List.length_nil, htl, nn]

/-! ### Frame-slot read-back -/

theorem read_slot_ra (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h8 := u_Z2bv (bv_unsigned rsp - 8) (by omega) (by omega)
  have h24 := u_Z2bv (bv_unsigned rsp - 24) (by omega) (by omega)
  have h32 := u_Z2bv (bv_unsigned rsp - 32) (by omega) (by omega)
  unfold fmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, h32, h8]; omega) (by rw [h8]; omega)]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes, h24, h8]; omega) (by rw [h8]; omega)]
  exact rdn_wbytes_hit8 _ _ _ _ (by rw [h8]; omega)

theorem read_slot_0 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word)
    (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
      Z_to_bv 64 (bv_unsigned rsp - 32)]) :
    rdn source_segs (fmem inp rsp rrnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> unfold fmem <;>
    simp (disch := (simp (disch := omega) only [length_N_to_le_bytes, u_Z2bv]; omega))
      only [rdn_wbytes_hit8, rdn_wbytes_disjoint, rdn_wbytes_below]

/-- The common epilogue from `0x11068`: restore the frame and exit with `a0`. -/
theorem source_epilogue (rsp : word)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h10 : reg_get regs 10 = code) (hc : bv_unsigned code < 256)
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)))
    (hslots : ∀ a : word,
      a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
        Z_to_bv 64 (bv_unsigned rsp - 32)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    to_wexit source_segs (mkst regs 0x11068 mem rrom) [] code := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have haddr (k : Int) :
      v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) k =
        Z_to_bv 64 (bv_unsigned rsp - (80 - k)) := by
    unfold v_addi
    rw [h80]
    congr 1
    omega
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (0x111f4 : word)) (0x111f4 : word)
    SF_11068 (by decide) SD_11068
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 72) 8 = _
        rw [haddr]; exact hra)
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_1106c (by decide) SD_1106c
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 64) 8 = _
        rw [haddr]; apply hslots; exact List.Mem.head _)
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11070 (by decide) SD_11070
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 56) 8 = _
        rw [haddr]; apply hslots; exact List.Mem.tail _ (List.Mem.head _))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (9 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11074 (by decide) SD_11074
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 48) 8 = _
        rw [haddr]; apply hslots
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (18 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi source_segs _ _ _ _ _ _ _ _
    SF_11078 (by decide) SD_11078)
  simp only [show bv_eqb (2 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x111f4 : word)
    SF_1107c (by decide) SD_1107c (by cat_regs))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    SF_111f4 (by decide) SD_111f4 (by decide) (by cat_regs; rfl))
  cat_step (step_ecall source_segs _ _ _ _ _ SF_111f8 (by decide))
  apply tw_exit_coden
  · cat_regs; rfl
  · cat_regs; exact h10
  · exact hc

theorem source_wexit_lt2 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hlt2 : inp.in_argv.length < 2) :
    to_wexit source_segs
      (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      [] (Z_to_bv 64 2) := by
  have hcmp : c_lts (Z_to_bv 64 1) (argcN inp.in_argv) = false := by
    have hlen : inp.in_argv.length = 0 ∨ inp.in_argv.length = 1 := by omega
    unfold argcN len_word
    rcases hlen with hlen | hlen <;> rw [hlen] <;> decide
  rw [init_mkst]
  cat_step (step_auipc_at source_segs _ _ _ _ _ _ _ (0x131c8 : word)
    SF_111c8 (by decide) SD_111c8 (by decide) (by rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x13800 : word)
    SF_111cc (by decide) SD_111cc (by decide) (by cat_regs; rfl))
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_le8 (argcN inp.in_argv)) (argcN inp.in_argv)
    SF_111d0 (by decide) SD_111d0
    (by
      cat_regs
      change rdn source_segs (oob_wmem inp rsp rrnd) (v_addi rsp 0) 8 = _
      rw [v_addi_0]
      exact oob_read_argc_w inp rsp rrnd hva hve hsp_lo hsp_hi)
    (bytes_le_n_to_le_8 _))
  simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned rsp + 8))
    SF_111d4 (by decide) SD_111d4 (by decide) (by cat_regs; rfl))
  cat_step (step_slli_at source_segs _ _ _ _ _ _ _ _ (v_slli (argcN inp.in_argv) 3)
    SF_111d8 (by decide) SD_111d8 (by decide) (by cat_regs; rfl))
  cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
    (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp.in_argv) 3))
    SF_111dc (by decide) SD_111dc (by decide) (by cat_regs))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (envp_val inp.in_argv rsp)
    SF_111e0 (by decide) SD_111e0 (by decide)
    (by cat_regs; exact envp_val_eq inp.in_argv rsp hva hsp_lo hsp_hi))
  cat_step (step_auipc_at source_segs _ _ _ _ _ _ _ (0x131e4 : word)
    SF_111e4 (by decide) SD_111e4 (by decide) (by rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x13000 : word)
    SF_111e8 (by decide) SD_111e8 (by decide) (by cat_regs; rfl))
  cat_step (step_sd_at source_segs _ _ _ _ _ _ _ _ (0x13000 : word)
    (envp_val inp.in_argv rsp) SF_111ec (by decide) SD_111ec
    (by cat_regs; rfl) (by cat_regs)
    (source_store_ok _ _ _ (by decide) (by decide)))
  cat_step (step_jal_link source_segs _ _ _ _ _ _ _
    SF_111f0 (by decide) SD_111f0)
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    SF_11000 (by decide) SD_11000 (by decide) (by cat_regs; rfl))
  cat_step (step_branch_tk_gen source_segs _ _ _ _ _ _ _ _ _
    SF_11004 (by decide) SD_11004
    (by cat_regs; change (!c_lts (Z_to_bv 64 1) (argcN inp.in_argv)) = true
        rw [hcmp]; rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 2)
    SF_111c0 (by decide) SD_111c0 (by decide) (by cat_regs; rfl))
  cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x111f4 : word)
    SF_111c4 (by decide) SD_111c4 (by cat_regs; rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    SF_111f4 (by decide) SD_111f4 (by decide) (by cat_regs; rfl))
  cat_step (step_ecall source_segs _ _ _ _ _ SF_111f8 (by decide))
  apply tw_exit_coden
  · cat_regs; rfl
  · cat_regs
  · decide

/-! ### `argc ≥ 2`: the main path (Rocq's `Section Ge2Main`)

Rocq's primed restatements `nN_le'`, `u_nN'`, `ptr_lo'`, `ptr_hi'` and
`ptr_hi8'` exist only to discharge the inner section's hypothesis; with
explicit arguments the unprimed lemmas serve directly. -/

theorem u_ptr_off (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length) (j : Nat) (hj : j ≤ nn av + 8) :
    bv_unsigned (ptr av ev rsp + nat_to_word j) = bv_unsigned (ptr av ev rsp) + (j : Int) := by
  have hsp := u64_range rsp
  have hhi := rsp_hi_num rsp hsp_hi
  have hav := valid_argv_len av hva
  have hev : (ev.length : Int) ≤ 256 := hve.1
  have hlen := nN_le av hva hge2
  have htotal := hva.2.1
  rw [total_arg_bytes_Z] at htotal
  have htake := total_arg_bytes_firstn_le 1 av
  have hstruct : (cat_struct_size av ev : Int) ≤ 10424 := by
    unfold cat_struct_size auxv_size
    omega
  have hoff : ((cat_struct_size av ev + total_arg_bytes_nat (av.take 1) : Nat) : Int)
      ≤ 2107576 := by omega
  have hptr : bv_unsigned (ptr av ev rsp) = bv_unsigned rsp +
      ((cat_struct_size av ev + total_arg_bytes_nat (av.take 1) : Nat) : Int) := by
    unfold ptr
    rw [cat_argv_ptr_offset rsp av ev 1 (by omega)]
    unfold cat_string_base
    rw [nat_to_word_add_merge, word_add_nat, u_Z2bv _ (by omega) (by omega)]
  rw [word_add_nat, u_Z2bv _ (by have := (u64_range (ptr av ev rsp)).1; omega)
    (by omega)]

theorem nth_full_lt (av : List (List byte)) (tl : List byte) (j : Nat) (hj : j < nn av) :
    (arg1 av ++ [Z_to_bv 8 0] ++ tl).getD j (Z_to_bv 8 0) = (arg1 av).getD j (Z_to_bv 8 0) := by
  simp only [List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (show j < (arg1 av).length from hj)]

theorem nth_full_nn (av : List (List byte)) (tl : List byte) :
    (arg1 av ++ [Z_to_bv 8 0] ++ tl).getD (nn av) (Z_to_bv 8 0) = Z_to_bv 8 0 := by
  rw [nn, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem sl_byte (av ev : List (List byte)) (rsp : word)
    (_hva : valid_argv av) (_hve : valid_envp ev)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (_hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (_hge2 : 2 ≤ av.length)
    (mem : word → Option byte) (tl : List byte)
    (hread : rdn source_segs mem (ptr av ev rsp) (nn av + 8) = some (arg1 av ++ [Z_to_bv 8 0] ++ tl))
    (j : Nat) (hj : j ≤ nn av) :
    rdn source_segs mem (ptr av ev rsp + nat_to_word j) 1 =
      some [(arg1 av ++ [Z_to_bv 8 0] ++ tl).getD j (Z_to_bv 8 0)] := by
  exact rdn_nth source_segs mem (nn av + 8) (ptr av ev rsp) _ j hread (by omega)

theorem nth_arg1_nz (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (j : Nat) (hj : j < nn av) :
    (arg1 av).getD j (Z_to_bv 8 0) ≠ Z_to_bv 8 0 := by
  rw [← nth_lt_byte_at (arg1 av) j hj]
  exact byte_at_nz (arg1 av) j (arg1_nz av hva hge2) hj

/-- The inline byte-at-a-time `strlen` scan, `0x11024` to `0x11030`. -/
theorem source_slen_loop (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length)
    (mem : word → Option byte) (tl : List byte)
    (hread : rdn source_segs mem (ptr av ev rsp) (nn av + 8) = some (arg1 av ++ [Z_to_bv 8 0] ++ tl))
    (d j : Nat) (regs : bvmap 5 word) (hjd : j + d = nn av)
    (h18 : reg_get regs 18 = ptr av ev rsp)
    (h8 : reg_get regs 8 = nat_to_word j) :
    ∃ regs' : bvmap 5 word,
      (∀ r : reg, r ≠ 8 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 8 = nN av ∧
      msteps source_segs (mkst regs 0x11024 mem rrom) (mkst regs' 0x11030 mem rrom) := by
  have hn := nN_le av hva hge2
  induction d generalizing j regs with
  | zero =>
    have hj : j = nn av := by omega
    let regs1 := regupd regs 15 (ptr av ev rsp + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 0)
    refine ⟨regs2, ?_, ?_, ?_⟩
    · intro r hr8 hr15
      simp only [regs2, regs1, regupd_other _ _ _ _ hr15]
    · change reg_get (regupd (regupd regs 15 _) 15 _) 8 = _
      cat_regs
      rw [h8, hj]
      rfl
    · cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
        (ptr av ev rsp + nat_to_word j) SF_11024 (by decide) SD_11024
        (by decide) (by
          cat_regs
          rw [h18, h8, v_add, u_ntw j (by omega), word_add_nat]))
      have hl := step_lbu source_segs regs1 0x11028 mem rrom _ 15 15 _
        (Z_to_bv 8 0) SF_11028 (by decide) SD_11028 (by
          dsimp only [regs1]
          cat_regs
          change rdn source_segs mem (v_addi (ptr av ev rsp + nat_to_word j) 0) 1 = _
          rw [v_addi_0, sl_byte av ev rsp hva hve hsp_lo hsp_hi hge2 mem tl hread j
            (by omega), hj, nth_full_nn])
      simp only [show bv_eqb (15 : reg) 0 = false from rfl,
        Bool.false_eq_true, ↓reduceIte] at hl
      cat_step hl
      cat_step (step_bne_ft source_segs _ _ _ _ _ _ _ _ SF_1102c (by decide) SD_1102c
        (by cat_regs; exact c_eq_0_true))
      exact msteps.mst_refl _
  | succ d ih =>
    have hj : j < nn av := by omega
    let b := (arg1 av).getD j (Z_to_bv 8 0)
    have hbnz : b ≠ Z_to_bv 8 0 := nth_arg1_nz av hva hge2 j hj
    let regs1 := regupd regs 15 (ptr av ev rsp + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 8 (nat_to_word (j + 1))
    obtain ⟨regs', hag, h8', hms⟩ := ih (j + 1) regs3 (by omega)
      (by dsimp only [regs3, regs2, regs1]; cat_regs; exact h18)
      (by exact regupd_same _ _ _)
    refine ⟨regs', ?_, h8', ?_⟩
    · intro r hr8 hr15
      rw [hag r hr8 hr15]
      simp only [regs3, regs2, regs1, regupd_other _ _ _ _ hr8,
        regupd_other _ _ _ _ hr15]
    · cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
        (ptr av ev rsp + nat_to_word j) SF_11024 (by decide) SD_11024
        (by decide) (by
          cat_regs
          rw [h18, h8, v_add, u_ntw j (by omega), word_add_nat]))
      have hl := step_lbu source_segs regs1 0x11028 mem rrom _ 15 15 _ b
        SF_11028 (by decide) SD_11028 (by
          dsimp only [regs1]
          cat_regs
          change rdn source_segs mem (v_addi (ptr av ev rsp + nat_to_word j) 0) 1 = _
          rw [v_addi_0, sl_byte av ev rsp hva hve hsp_lo hsp_hi hge2 mem tl hread j
            (by omega), nth_full_lt av tl j hj])
      simp only [show bv_eqb (15 : reg) 0 = false from rfl,
        Bool.false_eq_true, ↓reduceIte] at hl
      cat_step hl
      cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _ SF_1102c (by decide) SD_1102c
        (by
          dsimp only [regs1]
          cat_regs
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u b hbnz))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (nat_to_word (j + 1))
        SF_11080 (by decide) SD_11080 (by decide) (by
          dsimp only [regs1]
          cat_regs
          rw [h8]
          exact v_addi_Sj j (by omega)))
      cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_11084 (by decide) SD_11084)
      exact hms

theorem source_to_loop (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) :
    ∃ regs1 : bvmap 5 word,
      reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ∧
      reg_get regs1 8 = nat_to_word 0 ∧
      reg_get regs1 18 = ptr inp.in_argv inp.in_envp rsp ∧
      msteps source_segs
        (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs1 0x11024 (fmem inp rsp rrnd) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hargc := valid_argv_len inp.in_argv hva
  have huargc : bv_unsigned (argcN inp.in_argv) = (inp.in_argv.length : Int) :=
    u_len_word _ (by omega)
  have hframe : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) =
      bv_unsigned rsp - 80 := u_Z2bv _ (by omega) (by omega)
  have hslot (k : Int) (hk : 8 ≤ k) (hk' : k ≤ 80) :
      store_ok source_segs (oob_wmem inp rsp rrnd)
        (Z_to_bv 64 (bv_unsigned rsp - k)) 8 = true := by
    apply store_ok_wrap_window
    · rw [u_Z2bv _ (by omega) (by omega), stack_max_size_val]
      omega
    · rw [u_Z2bv _ (by omega) (by omega)]
      omega
  have hptrread : rdn source_segs (fmem inp rsp rrnd)
      (Z_to_bv 64 (bv_unsigned rsp + 16)) 8 =
        some (word_le8 (ptr inp.in_argv inp.in_envp rsp)) := by
    have hu : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + 16)) =
        bv_unsigned rsp + 16 := u_Z2bv _ (by omega) (by omega)
    rw [rdn_fmem_above inp rsp rrnd hsp_lo hsp_hi _ _ (by omega) (by omega),
      oob_rdn_wmem_stack inp rsp rrnd _ _ (by omega) (by omega)]
    have ha : rsp + nat_to_word 16 = Z_to_bv 64 (bv_unsigned rsp + 16) :=
      word_add_nat rsp 16
    rw [← ha]
    apply read_argv_ptr_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1
      inp.in_uid inp.in_hwcap rrnd
    · omega
    · have := bsb_bound source_phdrs rsp inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap rrnd hva hve
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  · rw [init_mkst]
    refine msteps.mst_step _ _ _ rfl (step_auipc_at source_segs _ _ _ _ _ _ _ (0x131c8 : word)
      SF_111c8 (by decide) SD_111c8 (by decide) (by rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x13800 : word)
      SF_111cc (by decide) SD_111cc (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _
      (word_le8 (argcN inp.in_argv)) (argcN inp.in_argv)
      SF_111d0 (by decide) SD_111d0
      (by cat_regs; change rdn source_segs (oob_wmem inp rsp rrnd) (v_addi rsp 0) 8 = _
          rw [v_addi_0]; exact oob_read_argc_w inp rsp rrnd hva hve hsp_lo hsp_hi)
      (bytes_le_n_to_le_8 _)) ?_
    simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp + 8))
      SF_111d4 (by decide) SD_111d4 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_slli_at source_segs _ _ _ _ _ _ _ _ (v_slli (argcN inp.in_argv) 3)
      SF_111d8 (by decide) SD_111d8 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_add_at source_segs _ _ _ _ _ _ _ _
      (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp.in_argv) 3))
      SF_111dc (by decide) SD_111dc (by decide) (by cat_regs)) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (envp_val inp.in_argv rsp)
      SF_111e0 (by decide) SD_111e0 (by decide)
      (by cat_regs; exact envp_val_eq inp.in_argv rsp hva hsp_lo hsp_hi)) ?_
    refine msteps.mst_step _ _ _ rfl (step_auipc_at source_segs _ _ _ _ _ _ _ (0x131e4 : word)
      SF_111e4 (by decide) SD_111e4 (by decide) (by rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x13000 : word)
      SF_111e8 (by decide) SD_111e8 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (0x13000 : word)
      (envp_val inp.in_argv rsp) SF_111ec (by decide) SD_111ec
      (by cat_regs; rfl) (by cat_regs)
      (source_store_ok _ _ _ (by decide) (by decide))) ?_
    refine msteps.mst_step _ _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _
      SF_111f0 (by decide) SD_111f0) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
      SF_11000 (by decide) SD_11000 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_bge_ft source_segs _ _ _ _ _ _ _ _
      SF_11004 (by decide) SD_11004 (by
        cat_regs
        rw [c_lts_small _ _ (by decide) (by omega)]
        change c_ltu (Z_to_bv 64 1) (argcN inp.in_argv) = true
        rw [c_ltu_ltb]
        exact decide_eq_true (by change (1 : Int) < bv_unsigned (argcN inp.in_argv); omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 80))
      SF_11008 (by decide) SD_11008 (by decide) (by cat_regs; rfl)) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 16)) (Z_to_bv 64 0)
      SF_1100c (by decide) SD_1100c
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 64 = _
          rw [v_addi, hframe]; congr 1; omega)
      (by cat_regs; rfl)
      (by
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        exact hslot 16 (by omega) (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 8)) ((0x111f4 : word))
      SF_11010 (by decide) SD_11010
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 72 = _
          rw [v_addi, hframe]; congr 1; omega)
      (by cat_regs; rfl)
      (by
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        exact hslot 8 (by omega) (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 24)) (Z_to_bv 64 0)
      SF_11014 (by decide) SD_11014
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 56 = _
          rw [v_addi, hframe]; congr 1; omega)
      (by cat_regs; rfl)
      (by
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        exact hslot 24 (by omega) (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 32)) (Z_to_bv 64 0)
      SF_11018 (by decide) SD_11018
      (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 48 = _
          rw [v_addi, hframe]; congr 1; omega)
      (by cat_regs; rfl)
      (by
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
        exact hslot 32 (by omega) (by omega))) ?_
    refine msteps.mst_step _ _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _
      (word_le8 (ptr inp.in_argv inp.in_envp rsp)) (ptr inp.in_argv inp.in_envp rsp)
      SF_1101c (by decide) SD_1101c
      (by
        cat_regs
        change rdn source_segs (fmem inp rsp rrnd)
          (v_addi (Z_to_bv 64 (bv_unsigned rsp + 8)) 8) 8 = _
        have ha : v_addi (Z_to_bv 64 (bv_unsigned rsp + 8)) 8 =
            Z_to_bv 64 (bv_unsigned rsp + 16) := by
          rw [v_addi, u_Z2bv _ (by omega) (by omega)]
          congr 1
        rw [ha]
        exact hptrread)
      (bytes_le_n_to_le_8 _)) ?_
    simp only [show bv_eqb (18 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine msteps.mst_step _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11020 (by decide) SD_11020 (by decide) (by cat_regs; rfl)) ?_
    exact msteps.mst_refl _
  all_goals (cat_regs <;> rfl)

theorem source_after_strlen (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) :
    ∃ regs2 : bvmap 5 word,
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ∧
      reg_get regs2 8 = nN inp.in_argv ∧
      reg_get regs2 18 = ptr inp.in_argv inp.in_envp rsp ∧
      msteps source_segs
        (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs2 0x11030 (fmem inp rsp rrnd) rrom) := by
  obtain ⟨regs1, h2, h8, h18, hms1⟩ :=
    source_to_loop inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨tl, _, hread⟩ := read_str_f8 inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨regsS, hagS, hS8, hmsS⟩ :=
    source_slen_loop inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
      (fmem inp rsp rrnd) tl hread (nn inp.in_argv) 0 regs1 (by omega) h18 h8
  refine ⟨regsS, ?_, hS8, ?_, msteps_trans source_segs _ _ _ hms1 hmsS⟩
  · rw [hagS 2 (by decide) (by decide)]
    exact h2
  · rw [hagS 18 (by decide) (by decide)]
    exact h18

theorem source_wexit_cap (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (hcap : 65536 < (nn inp.in_argv : Int)) :
    to_wexit source_segs
      (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      [] (Z_to_bv 64 3) := by
  obtain ⟨regs1, h2, h8, h18, hinit⟩ :=
    source_to_loop inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨tl, _, hread⟩ := read_str_f8 inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨regs2, hpres, h8', hloop⟩ :=
    source_slen_loop inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
      (fmem inp rsp rrnd) tl hread (nn inp.in_argv) 0 regs1 (by omega) h18 h8
  refine msteps_to_wexit source_segs _ _ _ _ hinit ?_
  refine msteps_to_wexit source_segs _ _ _ _ hloop ?_
  cat_step (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 65536)
    SF_11030 (by decide) SD_11030 (by decide) (by rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 3)
    SF_11034 (by decide) SD_11034 (by decide) (by cat_regs; rfl))
  cat_step (step_bltu_tk source_segs _ _ _ _ _ _ _ _
    SF_11038 (by decide) SD_11038 (by
      cat_regs
      rw [h8', c_ltu_ltb, u_nN inp.in_argv hva hge2]
      exact decide_eq_true hcap))
  apply source_epilogue rsp hsp_lo hsp_hi
  · cat_regs
    rw [hpres 2 (by decide) (by decide)]
    exact h2
  · cat_regs
  · decide
  · exact read_slot_ra inp rsp rrnd hsp_lo hsp_hi
  · exact read_slot_0 inp rsp rrnd hsp_lo hsp_hi

theorem source_exit4 (rsp : word)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)))
    (hslots : ∀ a : word,
      a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
        Z_to_bv 64 (bv_unsigned rsp - 32)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    to_wexit source_segs (mkst regs 0x11064 mem rrom) [] (Z_to_bv 64 4) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h80 : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) =
      bv_unsigned rsp - 80 := u_Z2bv _ (by omega) (by omega)
  have hoff (k : Int) :
      v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) k =
        Z_to_bv 64 (bv_unsigned rsp - (80 - k)) := by
    unfold v_addi
    rw [h80]
    congr 1
    omega
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 4)
    SF_11064 (by decide) SD_11064 (by decide) (by cat_regs; rfl))
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (0x111f4 : word)) (0x111f4 : word)
    SF_11068 (by decide) SD_11068
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 72) 8 = _
        rw [hoff]; exact hra)
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_1106c (by decide) SD_1106c
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 64) 8 = _
        rw [hoff]; exact hslots _ (by simp only [List.mem_cons]; exact Or.inl rfl))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11070 (by decide) SD_11070
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 56) 8 = _
        rw [hoff]; exact hslots _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl)))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (9 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11074 (by decide) SD_11074
    (by cat_regs; rw [h2]; change rdn source_segs mem
          (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 48) 8 = _
        rw [hoff]; exact hslots _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl))))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (18 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned rsp))
    SF_11078 (by decide) SD_11078 (by decide)
    (by cat_regs; rw [h2]
        change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 80 = _
        simpa only [Int.sub_self, Int.sub_zero] using hoff 80))
  cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x111f4 : word)
    SF_1107c (by decide) SD_1107c (by cat_regs))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    SF_111f4 (by decide) SD_111f4 (by decide) (by cat_regs; rfl))
  cat_step (step_ecall source_segs _ _ _ _ _ SF_111f8 (by decide))
  apply tw_exit_coden
  · cat_regs; decide
  · cat_regs
  · decide

/-- From the entry to the first `brk` ecall at `0x11218`, with `a0 = 0` (the query). -/
theorem source_to_brk1 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (hcap : (nn inp.in_argv : Int) ≤ 65536) :
    ∃ regs3 : bvmap 5 word,
      reg_get regs3 1 = (0x1105c : word) ∧
      reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ∧
      reg_get regs3 8 = nN inp.in_argv ∧
      reg_get regs3 10 = Z_to_bv 64 0 ∧
      reg_get regs3 17 = Z_to_bv 64 214 ∧
      reg_get regs3 18 = ptr inp.in_argv inp.in_envp rsp ∧
      msteps source_segs
        (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regs3, ms_fregs := bvmap_empty, ms_pc_val := (0x11218 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  obtain ⟨regs1, h2, h8, h18, hentry⟩ :=
    source_to_loop inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨tl, _, hread⟩ := read_str_f8 inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  obtain ⟨regs2, hpres, h8', hscan⟩ :=
    source_slen_loop inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
      (fmem inp rsp rrnd) tl hread (nn inp.in_argv) 0 regs1 (by omega) h18 h8
  have h2' : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 80) := by
    rw [hpres 2 (by decide) (by decide)]; exact h2
  have h18' : reg_get regs2 18 = ptr inp.in_argv inp.in_envp rsp := by
    rw [hpres 18 (by decide) (by decide)]; exact h18
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · refine msteps_trans source_segs _ _ _ hentry ?_
    refine msteps_trans source_segs _ _ _ hscan ?_
    cat_step (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 65536)
      SF_11030 (by decide) SD_11030 (by decide) (by rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 3)
      SF_11034 (by decide) SD_11034 (by decide) (by cat_regs; rfl))
    cat_step (step_bltu_ft source_segs _ _ _ _ _ _ _ _
      SF_11038 (by decide) SD_11038 (by
        cat_regs
        rw [h8', c_ltu_ltb, u_nN inp.in_argv hva hge2]
        apply decide_eq_false
        change ¬ (65536 : Int) < (nn inp.in_argv : Int)
        omega))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1103c (by decide) SD_1103c (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11040 (by decide) SD_11040 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11044 (by decide) SD_11044 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11048 (by decide) SD_11048 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1104c (by decide) SD_1104c (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11050 (by decide) SD_11050 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      SF_11054 (by decide) SD_11054 (by decide) (by cat_regs; rfl))
    cat_step (step_jal_link source_segs _ _ _ _ _ _ _
      SF_11058 (by decide) SD_11058)
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      SF_111fc (by decide) SD_111fc (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11200 (by decide) SD_11200 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11204 (by decide) SD_11204 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11208 (by decide) SD_11208 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1120c (by decide) SD_1120c (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11210 (by decide) SD_11210 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11214 (by decide) SD_11214 (by decide) (by cat_regs; rfl))
    cat_step (step_ecall source_segs _ _ _ _ _ SF_11218 (by decide))
    cat_regs
    exact msteps.mst_refl _
  · cat_regs; rfl
  · cat_regs; exact h2'
  · cat_regs; exact h8'
  · cat_regs
  · cat_regs
  · cat_regs; exact h18'

/-- Rocq's `fmem2`: `fmem` after the spill of `r + nN` at `rsp - 72`. -/
def fmem2 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (r : word) : word → Option byte :=
  wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 72))
    (word_to_le_bytes 8 (r + nN inp.in_argv))

theorem fmem2_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r x : word) (hx : bv_unsigned rsp - 64 ≤ bv_unsigned x) :
    fmem2 inp rsp rrnd r x = fmem inp rsp rrnd x := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  unfold fmem2
  apply wbytes_above
  rw [length_N_to_le_bytes, u_Z2bv _ (by omega) (by omega)]
  omega

theorem fmem2_below (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r x : word) (hx : bv_unsigned x < bv_unsigned rsp - 72) :
    fmem2 inp rsp rrnd r x = fmem inp rsp rrnd x := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have ha : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 72)) =
      bv_unsigned rsp - 72 := u_Z2bv _ (by omega) (by omega)
  unfold fmem2
  apply wbytes_below
  · rw [length_N_to_le_bytes, ha]
    omega
  · rw [ha]
    exact hx

theorem read_slot_ra2 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) :
    rdn source_segs (fmem2 inp rsp rrnd r) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h8 := u_Z2bv (bv_unsigned rsp - 8) (by omega) (by omega)
  apply Eq.trans (b := rdn source_segs (fmem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 8)) 8)
  · apply rdn_ext
    · rw [h8]
      omega
    · intro x hx
      apply fmem2_above inp rsp rrnd hsp_lo hsp_hi r x
      rw [h8] at hx
      omega
  · exact read_slot_ra inp rsp rrnd hsp_lo hsp_hi

theorem read_slot_02 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r a : word)
    (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
      Z_to_bv 64 (bv_unsigned rsp - 32)]) :
    rdn source_segs (fmem2 inp rsp rrnd r) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hab : bv_unsigned rsp - 32 ≤ bv_unsigned a ∧
      bv_unsigned a ≤ bv_unsigned rsp - 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      rw [u_Z2bv _ (by omega) (by omega)] <;> omega
  rw [rdn_ext source_segs 8 (fmem2 inp rsp rrnd r) (fmem inp rsp rrnd) a
    (by omega) (by
      intro x hx
      exact fmem2_above inp rsp rrnd hsp_lo hsp_hi r x (by omega))]
  exact read_slot_0 inp rsp rrnd hsp_lo hsp_hi a ha

theorem read_str_f8_2 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (r : word) :
    ∃ tl : List byte, tl.length = 7 ∧
      rdn source_segs (fmem2 inp rsp rrnd r) (ptr inp.in_argv inp.in_envp rsp) (nn inp.in_argv + 8) =
        some (arg1 inp.in_argv ++ [Z_to_bv 8 0] ++ tl) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hnw := source_bsb_nw inp rsp rrnd hva hve hsp_lo hsp_hi
  have hp := ptr_lo inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  obtain ⟨tail, he, ht⟩ := bsb_tail16 source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd
  rw [flatten_strings_decomp inp.in_argv 1 (by omega)] at he
  let pre := cat_struct_prefix source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap ++ flatten_strings (inp.in_argv.take 1)
  let post := flatten_strings (inp.in_argv.drop 2) ++ tail
  have he' : build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap rrnd =
      pre ++ ((arg1 inp.in_argv ++ [Z_to_bv 8 0]) ++ post) := by
    simpa only [pre, post, arg1, List.append_assoc] using he
  have hpost : 7 ≤ post.length := by
    simp only [post, List.length_append]
    omega
  have htl : (post.take 7).length = 7 := List.length_take_of_le hpost
  have hpre : pre.length = cat_struct_size inp.in_argv inp.in_envp +
      total_arg_bytes_nat (inp.in_argv.take 1) := by
    simp only [pre, List.length_append, length_cat_struct_prefix, length_flatten_strings]
  have haddr : ptr inp.in_argv inp.in_envp rsp = rsp + nat_to_word pre.length := by
    rw [ptr, cat_argv_ptr_offset rsp inp.in_argv inp.in_envp 1 (by omega),
      cat_string_base, nat_to_word_add_merge, hpre]
  have hlen : pre.length + (nn inp.in_argv + 8) ≤
      (build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap rrnd).length := by
    rw [he']
    simp only [List.length_append, List.length_singleton, nn]
    omega
  have hu : bv_unsigned (ptr inp.in_argv inp.in_envp rsp) =
      bv_unsigned rsp + (pre.length : Int) := by
    rw [haddr, word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  have hreadnw : bv_unsigned (ptr inp.in_argv inp.in_envp rsp) +
      ((nn inp.in_argv + 8 : Nat) : Int) ≤ 2 ^ 64 := by omega
  refine ⟨post.take 7, htl, ?_⟩
  rw [rdn_ext source_segs _ (fmem2 inp rsp rrnd r) (oob_wmem inp rsp rrnd) _ hreadnw
    (by
      intro x hx
      rw [fmem2_above inp rsp rrnd hsp_lo hsp_hi r x (by omega)]
      unfold fmem
      simp (disch := (simp (disch := omega) only
        [length_N_to_le_bytes, u_Z2bv]; omega)) only [wbytes_above]
      unfold emem
      apply wbytes_above
      rw [length_N_to_le_bytes]
      change (0x13000 : Int) + 8 ≤ bv_unsigned x
      omega)]
  rw [oob_rdn_wmem_stack inp rsp rrnd _ _ hp hreadnw, haddr]
  apply read_at_offset_image source_segs source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd pre _ (post.drop 7) _ _ _ hnw
  · rw [he']
    simp only [List.append_assoc, List.take_append_drop]
  · simp only [List.length_append, List.length_singleton, htl, nn]

/-- From the return of the first `brk` to the second `brk` ecall, with the
grow request `r + nN` in `a0` and spilled at `rsp - 72`. -/
theorem source_to_brk2 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (_hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length)
    (regs3 : bvmap 5 word) (r : word)
    (h1 : reg_get regs3 1 = (0x1105c : word))
    (h2 : reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h8 : reg_get regs3 8 = nN inp.in_argv)
    (h18 : reg_get regs3 18 = ptr inp.in_argv inp.in_envp rsp)
    (hr : r ≠ Z_to_bv 64 0)
    (hrn : bv_unsigned r + (nn inp.in_argv : Int) < 2 ^ 64) :
    ∃ regs5 : bvmap 5 word,
      reg_get regs5 1 = (0x110b0 : word) ∧
      reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ∧
      reg_get regs5 8 = nN inp.in_argv ∧
      reg_get regs5 9 = r ∧
      reg_get regs5 10 = r + nN inp.in_argv ∧
      reg_get regs5 17 = Z_to_bv 64 214 ∧
      reg_get regs5 18 = ptr inp.in_argv inp.in_envp rsp ∧
      msteps source_segs (mkst (regupd regs3 10 r) 0x1121c (fmem inp rsp rrnd) rrom)
        { ms_regs := regs5, ms_fregs := bvmap_empty, ms_pc_val := (0x11218 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem2 inp rsp rrnd r, ms_rom := rrom } := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hn := u_nN inp.in_argv hva hge2
  have hurn : bv_unsigned (r + nN inp.in_argv) =
      bv_unsigned r + (nn inp.in_argv : Int) := by
    rw [u_add_small _ _ (by rw [hn]; exact hrn), hn]
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have h72 := u_Z2bv (bv_unsigned rsp - 72) (by omega) (by omega)
  have hok : store_ok source_segs (fmem inp rsp rrnd)
      (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 = true := by
    unfold fmem emem
    repeat apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
    apply store_ok_wrap_window
    · rw [h72, stack_max_size_val]; omega
    · rw [h72]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x1105c : word)
      SF_1121c (by decide) SD_1121c (by cat_regs; exact h1))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ r
      SF_1105c (by decide) SD_1105c (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _
      SF_11060 (by decide) SD_11060
      (by cat_regs; exact c_eq_0_false r (word_neq0_unsigned r hr)))
    cat_step (step_add_at source_segs _ _ _ _ _ _ _ _ (r + nN inp.in_argv)
      SF_11088 (by decide) SD_11088 (by decide)
      (by cat_regs; rw [h8, v_add, hn]; exact (word_add_nat r _).symm))
    cat_step (step_bltu_ft source_segs _ _ _ _ _ _ _ _
      SF_1108c (by decide) SD_1108c
      (by cat_regs; rw [c_ltu_ltb, hurn]; apply decide_eq_false; omega))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11090 (by decide) SD_11090 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11094 (by decide) SD_11094 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11098 (by decide) SD_11098 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1109c (by decide) SD_1109c (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_110a0 (by decide) SD_110a0 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      SF_110a4 (by decide) SD_110a4 (by decide) (by cat_regs; rfl))
    cat_step (step_sd_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 72)) (r + nN inp.in_argv)
      SF_110a8 (by decide) SD_110a8
      (by cat_regs; rw [h2]
          change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + 8) = _
          rw [h80]; congr 1; omega)
      (by cat_regs) hok)
    cat_step (step_jal_link source_segs _ _ _ _ _ _ _
      SF_110ac (by decide) SD_110ac)
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 214)
      SF_111fc (by decide) SD_111fc (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (r + nN inp.in_argv)
      SF_11200 (by decide) SD_11200 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11204 (by decide) SD_11204 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11208 (by decide) SD_11208 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1120c (by decide) SD_1120c (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11210 (by decide) SD_11210 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_11214 (by decide) SD_11214 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_ecall source_segs _ _ _ _ _ SF_11218 (by decide))
    cat_regs
    exact msteps.mst_refl _
  · cat_regs; rfl
  · cat_regs; exact h2
  · cat_regs; exact h8
  · cat_regs
  · cat_regs
  · cat_regs
  · cat_regs; exact h18

theorem wmem_nl_none (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (_hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    oob_wmem inp rsp rrnd (0x12000 : word) = none := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hu : bv_unsigned (0x12000 : word) = 0x12000 := rfl
  have hbase : ¬ bv_unsigned rsp ≤ 0x12000 := by omega
  have hwindow : ¬ bv_unsigned rsp - stack_max_size ≤ 0x12000 := by
    rw [stack_max_size_val]
    omega
  simp only [oob_wmem, wrap_mem, stack_to_mem, hu, ite_eq_right hbase,
    hwindow, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]

/-- The newline literal in the rodata page. -/
theorem read_newline (mem : word → Option byte) (hnone : mem (0x12000 : word) = none) :
    rdn source_segs mem (0x12000 : word) 1 = some [Z_to_bv 8 10] := by
  have read_one (segs : List Segment) (m : word → Option byte) (a : word)
      (seg : Segment) (b : byte)
      (hm : m a = none)
      (hs : find_segment segs (bv_unsigned a) (↑(1 : Nat)) = some seg)
      (hr : seg_readable seg = true)
      (hb : segment_read_bytes seg.seg_bytes (bv_unsigned a - seg.seg_base).toNat 1 =
        some [b]) : rdn segs m a 1 = some [b] := by
    simp only [rdn, hm, seg_rom, memory_read, hs, hr, ↓reduceIte, hb]
  apply read_one source_segs mem (0x12000 : word) SourceMemImage_segment_002
    (Z_to_bv 8 10) hnone rfl (by decide +kernel)
  have ha : ascii_segment_read_bytes [SourceMemImage_seg_bytes_002_chars] 0 1 =
      some [Z_to_bv 8 10] := by
    decide +kernel
  exact (SourceMemImage_segment_002_read_ascii 0 1).trans ha

theorem fmem_none (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (ha : bv_unsigned a < bv_unsigned rsp - stack_max_size)
    (hd : bv_unsigned a < 0x13000 ∨ 0x13008 ≤ bv_unsigned a) :
    fmem inp rsp rrnd a = none := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have ha' := ha
  rw [stack_max_size_val] at ha'
  unfold fmem
  simp (disch := (simp (disch := omega) only [length_N_to_le_bytes, u_Z2bv]; omega))
    only [wbytes_below]
  have he : emem inp rsp rrnd a = oob_wmem inp rsp rrnd a := by
    unfold emem
    rcases hd with hd | hd
    · apply wbytes_below
      · rw [length_N_to_le_bytes]
        decide
      · exact hd
    · apply wbytes_above
      rw [length_N_to_le_bytes]
      exact hd
  rw [he]
  have hbase : ¬ bv_unsigned rsp ≤ bv_unsigned a := by omega
  have hwindow : ¬ bv_unsigned rsp - stack_max_size ≤ bv_unsigned a := by omega
  simp only [oob_wmem, wrap_mem, stack_to_mem, ite_eq_right hbase,
    hwindow, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]

theorem fmem2_none (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r a : word) (ha : bv_unsigned a < bv_unsigned rsp - stack_max_size)
    (hd : bv_unsigned a < 0x13000 ∨ 0x13008 ≤ bv_unsigned a) :
    fmem2 inp rsp rrnd r a = none := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hwindow : ¬ bv_unsigned rsp - stack_max_size ≤ bv_unsigned a := by omega
  rw [stack_max_size_val] at ha
  rw [fmem2_below inp rsp rrnd hsp_lo hsp_hi r a (by omega)]
  unfold fmem
  simp (disch := (simp (disch := omega) only [length_N_to_le_bytes, u_Z2bv]; omega))
    only [wbytes_below]
  have hemem : emem inp rsp rrnd a = oob_wmem inp rsp rrnd a := by
    unfold emem
    rcases hd with hd | hd
    · apply wbytes_below
      · rw [length_N_to_le_bytes]
        decide
      · exact hd
    · apply wbytes_above
      rw [length_N_to_le_bytes]
      exact hd
  rw [hemem]
  have hbase : ¬ bv_unsigned rsp ≤ bv_unsigned a := by omega
  simp only [oob_wmem, wrap_mem, stack_to_mem, ite_eq_right hbase,
    hwindow, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]

/-! ### The copy, the byte sum, and the output -/

/-- The byte copy `0x110bc` to `0x110c0`: `d` bytes left to copy. -/
theorem source_copy (av ev : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ av.length)
    (r : word) (mem0 : word → Option byte)
    (hgrant : store_grant_ok source_segs mem0 r (nN av))
    (hread : rdn source_segs mem0 (ptr av ev rsp) (nn av + 1) = some (arg1 av ++ [Z_to_bv 8 0]))
    (_hfree : region_free (segments_reserved source_segs) r (nN av) = true)
    (hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (nn av : Int) ≤ bv_unsigned rsp - stack_max_size)
    (d : Nat) (regs : bvmap 5 word) (hd : d ≤ nn av)
    (h18 : reg_get regs 18 = ptr av ev rsp) (h9 : reg_get regs 9 = r)
    (h8 : reg_get regs 8 = nN av)
    (h15 : reg_get regs 15 = nat_to_word (nn av - d)) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 13 → x ≠ 14 → x ≠ 15 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 15 = nN av ∧ reg_get regs' 9 = r ∧ reg_get regs' 8 = nN av ∧
      reg_get regs' 18 = ptr av ev rsp ∧
      msteps source_segs
        (mkst regs 0x110bc (wbytes mem0 r ((arg1 av).take (nn av - d))) rrom)
        (mkst regs' 0x110c0 (wbytes mem0 r (arg1 av)) rrom) := by
  have hplo := ptr_lo av ev rsp hva hve hsp_lo hsp_hi hge2
  have hphi := ptr_hi av ev rsp hva hve hsp_lo hsp_hi hge2
  have hn := nN_le av hva hge2
  have hun := u_nN av hva hge2
  have hsp := rsp_hi_num rsp hsp_hi
  have hrp : bv_unsigned r + (nn av : Int) ≤ bv_unsigned (ptr av ev rsp) := by
    rw [stack_max_size_val] at hrs
    omega
  induction d generalizing regs with
  | zero =>
    refine ⟨regs, (by intros; rfl), ?_, h9, h8, h18, ?_⟩
    · simpa only [Nat.sub_zero, nN] using h15
    · simp only [Nat.sub_zero, nn, List.take_length]
      cat_step (step_bne_ft source_segs _ _ _ _ _ _ _ _
        SF_110bc (by decide) SD_110bc
        (by cat_regs; rw [h15, h8, Nat.sub_zero]; exact c_eq_refl _))
      exact msteps.mst_refl _
  | succ d ih =>
    let i := nn av - (d + 1)
    have hi : i < nn av := by dsimp only [i]; omega
    have his : i + 1 = nn av - d := by dsimp only [i]; omega
    have hlen : ((arg1 av).take i).length = i :=
      List.length_take_of_le (by change i ≤ nn av; omega)
    have hui : bv_unsigned (ptr av ev rsp + nat_to_word i) =
        bv_unsigned (ptr av ev rsp) + (i : Int) :=
      u_ptr_off av ev rsp hva hve hsp_lo hsp_hi hge2 i (by omega)
    have hri : bv_unsigned (r + nat_to_word i) = bv_unsigned r + (i : Int) := by
      rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]
    let b := (arg1 av).getD i (Z_to_bv 8 0)
    let memI := wbytes mem0 r ((arg1 av).take i)
    let regs1 := regupd regs 14 (ptr av ev rsp + nat_to_word i)
    let regs2 := regupd regs1 13 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 14 (r + nat_to_word i)
    let regs4 := regupd regs3 15 (nat_to_word (i + 1))
    have hbyte : rdn source_segs memI (ptr av ev rsp + nat_to_word i) 1 = some [b] := by
      dsimp only [memI]
      rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [hlen, hui]; omega)
        (by rw [hui]; omega)]
      have hb := rdn_nth source_segs mem0 (nn av + 1) (ptr av ev rsp)
        (arg1 av ++ [Z_to_bv 8 0]) i hread (by omega)
      simpa only [b, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show i < (arg1 av).length from hi)] using hb
    have hstore : store_ok source_segs memI (r + nat_to_word i) 1 = true := by
      apply store_ok_mono _ _ mem0 _ _ (wbytes_grows _ _ _)
      apply hgrant
      · rw [hri]; omega
      · rw [hri, hun]; omega
    have hmem : wbytes memI (r + nat_to_word i) [b] =
        wbytes mem0 r ((arg1 av).take (nn av - d)) := by
      rw [← his, firstn_snoc _ _ hi, wbytes_app, hlen]
    have h18' : reg_get regs4 18 = ptr av ev rsp := by
      dsimp only [regs4, regs3, regs2, regs1]; cat_regs; exact h18
    have h9' : reg_get regs4 9 = r := by
      dsimp only [regs4, regs3, regs2, regs1]; cat_regs; exact h9
    have h8' : reg_get regs4 8 = nN av := by
      dsimp only [regs4, regs3, regs2, regs1]; cat_regs; exact h8
    have h15' : reg_get regs4 15 = nat_to_word (nn av - d) := by
      dsimp only [regs4]; rw [regupd_same, his]
    obtain ⟨regs', hag, h15f, h9f, h8f, h18f, hms⟩ :=
      ih regs4 (by omega) h18' h9' h8' h15'
    refine ⟨regs', ?_, h15f, h9f, h8f, h18f, ?_⟩
    · intro x hx13 hx14 hx15
      rw [hag x hx13 hx14 hx15]
      dsimp only [regs4, regs3, regs2, regs1]
      simp only [regupd_other _ _ _ _ hx15, regupd_other _ _ _ _ hx14,
        regupd_other _ _ _ _ hx13]
    · change msteps source_segs (mkst regs 0x110bc memI rrom) _
      cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _
        SF_110bc (by decide) SD_110bc
        (by
          cat_regs; rw [h15, h8]
          apply c_eq_neq
          rw [u_ntw _ (by omega), hun]
          omega))
      cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
        (ptr av ev rsp + nat_to_word i) SF_11144 (by decide) SD_11144 (by decide)
        (by cat_regs; rw [h18, h15]; change v_add _ (nat_to_word i) = _
            rw [v_add, u_ntw _ (by omega), word_add_nat]))
      change msteps source_segs (mkst regs1 0x11148 memI rrom) _
      cat_step (step_lbu source_segs _ _ _ _ _ _ _ _ b
        SF_11148 (by decide) SD_11148
        (by dsimp only [regs1]; cat_regs; change rdn _ _ (v_addi _ 0) _ = _
            rw [v_addi_0]; exact hbyte))
      change msteps source_segs (mkst regs2 0x1114c memI rrom) _
      cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
        (r + nat_to_word i) SF_1114c (by decide) SD_1114c (by decide)
        (by dsimp only [regs2, regs1]; cat_regs; rw [h15, h9]
            change v_add (nat_to_word i) r = _
            rw [v_add, u_ntw _ (by omega), word_add_nat, Int.add_comm]))
      change msteps source_segs (mkst regs3 0x11150 memI rrom) _
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _
        (nat_to_word (i + 1)) SF_11150 (by decide) SD_11150 (by decide)
        (by dsimp only [regs3, regs2, regs1]; cat_regs; rw [h15]
            exact v_addi_Sj i (by omega)))
      change msteps source_segs (mkst regs4 0x11154 memI rrom) _
      cat_step (step_sb_at source_segs _ _ _ _ _ _ _ _
        (r + nat_to_word i) (Z_to_bv 64 (bv_unsigned b)) b
        SF_11154 (by decide) SD_11154
        (by dsimp only [regs4, regs3]; cat_regs; exact v_addi_0 _)
        (by dsimp only [regs4, regs3, regs2]; cat_regs)
        (zext8_byte b) hstore)
      rw [hmem]
      cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_11158 (by decide) SD_11158)
      exact hms

theorem sum_firstn_bound (av : List (List byte)) (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (k : Nat) : sumb ((arg1 av).take k) ≤ 255 * (nn av : Int) := by
  have hsplit := sumb_app ((arg1 av).take k) ((arg1 av).drop k)
  rw [List.take_append_drop] at hsplit
  have hnonneg := sumb_nonneg ((arg1 av).drop k)
  have hbound := sumb_le (arg1 av) (arg1_bytes av hva hge2)
  unfold nn
  omega

/-- The inner eight-byte loop `0x11164` to `0x11178`: `c` bytes left in the chunk. -/
theorem source_sum_inner (av : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) (M : word → Option byte) (total m : Nat)
    (hbyte : ∀ i, i < total →
      rdn source_segs M (r + nat_to_word i) 1 = some [(arg1 av).getD i (Z_to_bv 8 0)])
    (hm : 8 * m + 8 ≤ total) (_hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (total : Int) ≤ bv_unsigned rsp - stack_max_size)
    (c : Nat) (regs : bvmap 5 word) (hc : 1 ≤ c ∧ c ≤ 8)
    (h10 : reg_get regs 10 = r + nat_to_word (8 * m))
    (h12 : reg_get regs 12 = Z_to_bv 64 8)
    (h13 : reg_get regs 13 = nat_to_word (8 - c))
    (h15 : reg_get regs 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * m + (8 - c))))) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 13 → x ≠ 11 → x ≠ 15 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * m + 8))) ∧
      msteps source_segs (mkst regs 0x11164 M rrom) (mkst regs' 0x11178 M rrom) := by
  have hnn := nN_le av hva hge2
  have hhi := rsp_hi_num rsp hsp_hi
  have hsms := stack_max_size_val
  induction c generalizing regs with
  | zero => omega
  | succ c ih =>
    let j := 8 - (c + 1)
    have hj : j < 8 := by dsimp only [j]; omega
    have hidx : 8 * m + j < total := by omega
    let b := (arg1 av).getD (8 * m + j) (Z_to_bv 8 0)
    have hb := u8_range b
    have hs0 := sumb_nonneg ((arg1 av).take (8 * m + j))
    have hs1 := sum_firstn_bound av hva hge2 (8 * m + j)
    let regsA := regupd regs 11 (r + nat_to_word (8 * m + j))
    let regsB := regupd regsA 11 (Z_to_bv 64 (bv_unsigned b))
    let regsC := regupd regsB 13 (nat_to_word (j + 1))
    let regsD := regupd regsC 15 (Z_to_bv 64 (sumb ((arg1 av).take (8 * m + j + 1))))
    have EA : RiscvSemantics.step source_segs (mkst regs 0x11164 M rrom) =
        MachineOk (mkst regsA 0x11168 M rrom) := by
      apply step_add_at source_segs _ _ _ _ _ _ _ _ _
        SF_11164 (by decide) SD_11164 (by decide)
      cat_regs
      rw [h10, h13]
      exact word_add_nat_split r (8 * m) j (by omega)
    have EB : RiscvSemantics.step source_segs (mkst regsA 0x11168 M rrom) =
        MachineOk (mkst regsB 0x1116c M rrom) := by
      exact step_lbu source_segs _ _ _ _ _ _ _ _ b
        SF_11168 (by decide) SD_11168 (by
          dsimp only [regsA]
          cat_regs
          change rdn source_segs M (v_addi (r + nat_to_word (8 * m + j)) 0) 1 = _
          rw [v_addi_0]
          exact hbyte _ hidx)
    have EC : RiscvSemantics.step source_segs (mkst regsB 0x1116c M rrom) =
        MachineOk (mkst regsC 0x11170 M rrom) := by
      apply step_addi_at source_segs _ _ _ _ _ _ _ _ _
        SF_1116c (by decide) SD_1116c (by decide)
      dsimp only [regsB, regsA]
      cat_regs
      rw [h13]
      exact v_addi_Sj j (by omega)
    have ED : RiscvSemantics.step source_segs (mkst regsC 0x11170 M rrom) =
        MachineOk (mkst regsD 0x11174 M rrom) := by
      apply step_add_at source_segs _ _ _ _ _ _ _ _ _
        SF_11170 (by decide) SD_11170 (by decide)
      dsimp only [regsC, regsB, regsA]
      cat_regs
      rw [h15]
      change v_add (Z_to_bv 64 (sumb ((arg1 av).take (8 * m + j))))
        (Z_to_bv 64 (bv_unsigned b)) = _
      rw [v_add, u_Z2bv _ hs0 (by omega), u_zext8,
        sumb_firstn_S_default]
    have HDother : ∀ x : reg, x ≠ 13 → x ≠ 11 → x ≠ 15 →
        reg_get regsD x = reg_get regs x := by
      intro x hx13 hx11 hx15
      dsimp only [regsD, regsC, regsB, regsA]
      rw [regupd_other _ _ _ _ hx15, regupd_other _ _ _ _ hx13,
        regupd_other _ _ _ _ hx11, regupd_other _ _ _ _ hx11]
    have HD13 : reg_get regsD 13 = nat_to_word (j + 1) := by
      dsimp only [regsD, regsC]
      cat_regs
    have HD12 : reg_get regsD 12 = Z_to_bv 64 8 := by
      rw [HDother 12 (by decide) (by decide) (by decide)]
      exact h12
    have HD10 : reg_get regsD 10 = r + nat_to_word (8 * m) := by
      rw [HDother 10 (by decide) (by decide) (by decide)]
      exact h10
    have HD15 : reg_get regsD 15 =
        Z_to_bv 64 (sumb ((arg1 av).take (8 * m + j + 1))) := by
      exact regupd_same _ _ _
    have hprefix : msteps source_segs (mkst regs 0x11164 M rrom)
        (mkst regsD 0x11174 M rrom) := by
      cat_step EA
      cat_step EB
      cat_step EC
      cat_step ED
      exact msteps.mst_refl _
    by_cases hz : c = 0
    · have hj7 : j = 7 := by dsimp only [j]; omega
      refine ⟨regsD, HDother, ?_, ?_⟩
      · rw [HD15, hj7]
      · apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bne_ft source_segs _ _ _ _ _ _ _ _
          SF_11174 (by decide) SD_11174 (by
            cat_regs
            rw [HD13, HD12, hj7]
            exact c_eq_refl _))
        exact msteps.mst_refl _
    · have hjnext : j + 1 = 8 - c := by dsimp only [j]; omega
      obtain ⟨regs', hag, hsum, hsteps⟩ := ih regsD (by omega) HD10 HD12
        (by rw [HD13, hjnext])
        (by rw [HD15]; congr 3; omega)
      refine ⟨regs', ?_, hsum, ?_⟩
      · intro x hx13 hx11 hx15
        rw [hag x hx13 hx11 hx15]
        exact HDother x hx13 hx11 hx15
      · apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _
          SF_11174 (by decide) SD_11174 (by
            cat_regs
            rw [HD13, HD12]
            apply c_eq_neq
            rw [u_ntw _ (by omega), u_Z2bv 8 (by omega) (by omega)]
            omega))
        exact hsteps

/-- One eight-byte chunk of the outer loop at `0x110cc`. -/
theorem source_sum_chunk (av : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) (M : word → Option byte) (total m : Nat)
    (hbyte : ∀ i, i < total →
      rdn source_segs M (r + nat_to_word i) 1 = some [(arg1 av).getD i (Z_to_bv 8 0)])
    (hlt : 8 * m < nn av) (hm : 8 * m + 8 ≤ total) (hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (total : Int) ≤ bv_unsigned rsp - stack_max_size)
    (regs : bvmap 5 word)
    (h14 : reg_get regs 14 = nat_to_word (8 * m))
    (h9 : reg_get regs 9 = r)
    (h15 : reg_get regs 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * m))))
    (h12 : reg_get regs 12 = Z_to_bv 64 8) (h8 : reg_get regs 8 = nN av) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 14 → x ≠ 10 → x ≠ 15 → x ≠ 13 → x ≠ 11 →
        reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 14 = nat_to_word (8 * (m + 1)) ∧
      reg_get regs' 9 = r ∧
      reg_get regs' 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * (m + 1)))) ∧
      reg_get regs' 12 = Z_to_bv 64 8 ∧ reg_get regs' 8 = nN av ∧
      msteps source_segs (mkst regs 0x110cc M rrom) (mkst regs' 0x110cc M rrom) := by
  have hnn := nN_le av hva hge2
  let regs0 := regupd regs 13 (Z_to_bv 64 0)
  let regsA := regupd regs0 10 (r + nat_to_word (8 * m))
  have hA12 : reg_get regsA 12 = Z_to_bv 64 8 := by
    dsimp only [regsA, regs0]
    cat_regs
    exact h12
  obtain ⟨regs1, hag, hsum, hinner⟩ :=
    source_sum_inner av rsp hva hge2 hsp_lo hsp_hi r M total m
      hbyte hm hr0 hrs 8 regsA (by omega)
      (regupd_same _ _ _) hA12
      (by dsimp only [regsA, regs0]; cat_regs; rfl)
      (by dsimp only [regsA, regs0]; cat_regs; simpa only [Nat.sub_self, Nat.add_zero] using h15)
  have hkeep (x : reg) (hx10 : x ≠ 10) (hx13 : x ≠ 13)
      (hx11 : x ≠ 11) (hx15 : x ≠ 15) :
      reg_get regs1 x = reg_get regs x := by
    rw [hag x hx13 hx11 hx15]
    dsimp only [regsA, regs0]
    rw [regupd_other _ _ _ _ hx10, regupd_other _ _ _ _ hx13]
  have h114 : reg_get regs1 14 = nat_to_word (8 * m) := by
    rw [hkeep 14 (by decide) (by decide) (by decide) (by decide)]
    exact h14
  let regs2 := regupd regs1 14 (nat_to_word (8 * (m + 1)))
  refine ⟨regs2, ?_, regupd_same _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx14 hx10 hx15 hx13 hx11
    dsimp only [regs2]
    rw [regupd_other _ _ _ _ hx14]
    exact hkeep x hx10 hx13 hx11 hx15
  · dsimp only [regs2]
    cat_regs
    rw [hkeep 9 (by decide) (by decide) (by decide) (by decide)]
    exact h9
  · dsimp only [regs2]
    cat_regs
    rw [hsum, Nat.mul_add, Nat.mul_one]
  · dsimp only [regs2]
    cat_regs
    rw [hkeep 12 (by decide) (by decide) (by decide) (by decide)]
    exact h12
  · dsimp only [regs2]
    cat_regs
    rw [hkeep 8 (by decide) (by decide) (by decide) (by decide)]
    exact h8
  · cat_step (step_bltu_tk source_segs _ _ _ _ _ _ _ _
      SF_110cc (by decide) SD_110cc (by
        cat_regs
        rw [h14, h8, c_ltu_ltb, u_ntw _ (by omega), u_nN av hva hge2]
        exact decide_eq_true (by omega)))
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
      SF_1115c (by decide) SD_1115c (by decide) (by cat_regs; rfl))
    change msteps source_segs (mkst regs0 0x11160 M rrom) _
    cat_step (step_add_at source_segs _ _ _ _ _ _ _ _ (r + nat_to_word (8 * m))
      SF_11160 (by decide) SD_11160 (by decide) (by
        dsimp only [regs0]
        cat_regs
        rw [h14, h9, v_add, u_ntw _ (by omega), word_add_nat, Int.add_comm]))
    apply msteps_trans _ _ _ _ hinner
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (nat_to_word (8 * (m + 1)))
      SF_11178 (by decide) SD_11178 (by decide) (by
        cat_regs
        rw [h114]
        change v_addi (nat_to_word (8 * m)) (8 : Int) = _
        rw [Nat.mul_add, Nat.mul_one]
        exact v_addi_nat_add (8 * m) 8 (by omega)))
    cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_1117c (by decide) SD_1117c)
    exact msteps.mst_refl _

/-- `c` chunks of the outer loop at `0x110cc`, starting at chunk `m0`. -/
theorem source_sum (av : List (List byte)) (rsp : word)
    (hva : valid_argv av) (hge2 : 2 ≤ av.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) (M : word → Option byte) (total : Nat)
    (hbyte : ∀ i, i < total →
      rdn source_segs M (r + nat_to_word i) 1 = some [(arg1 av).getD i (Z_to_bv 8 0)])
    (hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (total : Int) ≤ bv_unsigned rsp - stack_max_size)
    (c m0 : Nat) (regs : bvmap 5 word)
    (hlt : 8 * (m0 + c - 1) < nn av) (htot : 8 * (m0 + c) = total)
    (h14 : reg_get regs 14 = nat_to_word (8 * m0))
    (h9 : reg_get regs 9 = r)
    (h15 : reg_get regs 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * m0))))
    (h12 : reg_get regs 12 = Z_to_bv 64 8) (h8 : reg_get regs 8 = nN av) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 14 → x ≠ 10 → x ≠ 15 → x ≠ 13 → x ≠ 11 →
        reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 14 = nat_to_word (8 * (m0 + c)) ∧
      reg_get regs' 9 = r ∧
      reg_get regs' 15 = Z_to_bv 64 (sumb ((arg1 av).take (8 * (m0 + c)))) ∧
      reg_get regs' 12 = Z_to_bv 64 8 ∧ reg_get regs' 8 = nN av ∧
      msteps source_segs (mkst regs 0x110cc M rrom) (mkst regs' 0x110cc M rrom) := by
  induction c generalizing m0 regs with
  | zero =>
    exact ⟨regs, (by intros; rfl), h14, h9, h15, h12, h8, msteps.mst_refl _⟩
  | succ c ih =>
    obtain ⟨regs1, hag1, h1_14, h1_9, h1_15, h1_12, h1_8, hms1⟩ :=
      source_sum_chunk av rsp hva hge2 hsp_lo hsp_hi r M total m0 hbyte
        (by omega) (by omega) hr0 hrs regs h14 h9 h15 h12 h8
    obtain ⟨regs', hag', h'_14, h'_9, h'_15, h'_12, h'_8, hms'⟩ :=
      ih (m0 + 1) regs1 (by omega) (by omega) h1_14 h1_9 h1_15 h1_12 h1_8
    have heq : m0 + (c + 1) = (m0 + 1) + c := by omega
    refine ⟨regs', ?_, ?_, h'_9, ?_, h'_12, h'_8,
      msteps_trans _ _ _ _ hms1 hms'⟩
    · intro x hx14 hx10 hx15 hx13 hx11
      rw [hag' x hx14 hx10 hx15 hx13 hx11]
      exact hag1 x hx14 hx10 hx15 hx13 hx11
    · simpa only [Nat.succ_eq_add_one, heq] using h'_14
    · simpa only [Nat.succ_eq_add_one, heq] using h'_15

/-- The inner loop stays inside the valid bytes: `d` more steps from byte `j`. -/
theorem source_inner_valid (av : List (List byte)) (rsp : word)
    (_hva : valid_argv av) (_hge2 : 2 ≤ av.length)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) (M : word → Option byte) (m : Nat)
    (hread : rdn source_segs M r (nn av) = some (arg1 av))
    (_hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (nn av : Int) ≤ bv_unsigned rsp - stack_max_size)
    (d j : Nat) (regs : bvmap 5 word) (hjd : 8 * m + j + d ≤ nn av) (hj7 : j + d ≤ 7)
    (h10 : reg_get regs 10 = r + nat_to_word (8 * m)) (h12 : reg_get regs 12 = Z_to_bv 64 8)
    (h13 : reg_get regs 13 = nat_to_word j) :
    ∃ regs' : bvmap 5 word,
      reg_get regs' 10 = r + nat_to_word (8 * m) ∧ reg_get regs' 12 = Z_to_bv 64 8 ∧
      reg_get regs' 13 = nat_to_word (j + d) ∧
      msteps source_segs (mkst regs 0x11164 M rrom) (mkst regs' 0x11164 M rrom) := by
  have hsp := rsp_hi_num rsp hsp_hi
  have hsms := stack_max_size_val
  induction d generalizing j regs with
  | zero =>
    exact ⟨regs, h10, h12, h13, msteps.mst_refl _⟩
  | succ d ih =>
    let b := (arg1 av).getD (8 * m + j) (Z_to_bv 8 0)
    let regsA := regupd regs 11 (r + nat_to_word (8 * m + j))
    let regsB := regupd regsA 11 (Z_to_bv 64 (bv_unsigned b))
    let regsC := regupd regsB 13 (nat_to_word (j + 1))
    let regsD := regupd regsC 15 (v_add (getr regsC 15) (getr regsC 11))
    have hA : RiscvSemantics.step source_segs (mkst regs 0x11164 M rrom) =
        MachineOk (mkst regsA 0x11168 M rrom) := by
      exact step_add_at source_segs _ _ _ _ _ _ _ _ _
        SF_11164 (by decide) SD_11164 (by decide)
        (by cat_regs; rw [h10, h13]; apply word_add_nat_split; omega)
    have hB : RiscvSemantics.step source_segs (mkst regsA 0x11168 M rrom) =
        MachineOk (mkst regsB 0x1116c M rrom) := by
      exact step_lbu source_segs _ _ _ _ _ _ _ _ b
        SF_11168 (by decide) SD_11168 (by
          dsimp only [regsA]
          cat_regs
          rw [show bv_signed (0 : BitVec 12) = 0 from rfl, v_addi_0]
          exact rdn_nth source_segs M (nn av) r (arg1 av) (8 * m + j)
            hread (by omega))
    have hC : RiscvSemantics.step source_segs (mkst regsB 0x1116c M rrom) =
        MachineOk (mkst regsC 0x11170 M rrom) := by
      exact step_addi_at source_segs _ _ _ _ _ _ _ _ _
        SF_1116c (by decide) SD_1116c (by decide) (by
          dsimp only [regsB, regsA]
          cat_regs
          rw [h13]
          exact v_addi_Sj j (by omega))
    have hD : RiscvSemantics.step source_segs (mkst regsC 0x11170 M rrom) =
        MachineOk (mkst regsD 0x11174 M rrom) := by
      exact step_add source_segs _ _ _ _ _ _ _ _ SF_11170 (by decide) SD_11170
    have hD10 : reg_get regsD 10 = r + nat_to_word (8 * m) := by
      dsimp only [regsD, regsC, regsB, regsA]
      cat_regs
      exact h10
    have hD12 : reg_get regsD 12 = Z_to_bv 64 8 := by
      dsimp only [regsD, regsC, regsB, regsA]
      cat_regs
      exact h12
    have hD13 : reg_get regsD 13 = nat_to_word (j + 1) := by
      dsimp only [regsD, regsC]
      cat_regs
    have hE : RiscvSemantics.step source_segs (mkst regsD 0x11174 M rrom) =
        MachineOk (mkst regsD 0x11164 M rrom) := by
      exact step_bne_tk source_segs _ _ _ _ _ _ _ _
        SF_11174 (by decide) SD_11174 (by
          cat_regs
          rw [hD13, hD12]
          apply c_eq_neq
          rw [u_ntw (j + 1) (by omega), u_Z2bv 8 (by omega) (by omega)]
          omega)
    obtain ⟨regs', h10', h12', h13', hsteps⟩ :=
      ih (j + 1) regsD (by omega) (by omega) hD10 hD12 hD13
    refine ⟨regs', h10', h12', ?_, ?_⟩
    · rw [h13']
      congr 1
      omega
    · cat_step hA
      cat_step hB
      cat_step hC
      cat_step hD
      cat_step hE
      exact hsteps

/-- The `put` wrapper at `0x11220`: it saves `ra` below the frame (a machine
store, so `mem` has to be writable there) and the continuation gets the
`mem_grows` fact back for its own stores. -/
theorem source_put (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (K : machine_state → Prop) (regs : bvmap 5 word) (mem : word → Option byte)
    (buf : List byte) (pbuf len RA : word)
    (h1 : reg_get regs 1 = RA)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h10 : reg_get regs 10 = Z_to_bv 64 1)
    (h11 : reg_get regs 11 = pbuf) (h12 : reg_get regs 12 = len)
    (hlen0 : 0 < bv_unsigned len) (hlen : bv_unsigned len < 2 ^ 31)
    (hRA : v_jalr RA 0 = RA)
    (hread : rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88)) (word_to_le_bytes 8 RA))
      pbuf (word_to_nat len) = some buf)
    (hgrow : mem_grows (oob_wmem inp rsp rrnd) mem)
    (hK : ∀ (regs' : bvmap 5 word) (mem' : word → Option byte) (n : Nat), 1 ≤ n → n ≤ buf.length →
      reg_get regs' 1 = RA → reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 80) →
      reg_get regs' 8 = reg_get regs 8 →
      reg_get regs' 10 = len_word (buf.take n) →
      reg_get regs' 9 = reg_get regs 9 → reg_get regs' 18 = reg_get regs 18 →
      mem_grows (oob_wmem inp rsp rrnd) mem' →
      (∀ x : word, bv_unsigned x < bv_unsigned rsp - 88 ∨ bv_unsigned rsp - 80 ≤ bv_unsigned x →
        mem' x = mem x) →
      to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs' RA mem' rrom) (buf.drop n) K) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x11220 mem rrom) buf K := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have h88 := u_Z2bv (bv_unsigned rsp - 88) (by omega) (by omega)
  have h96 := u_Z2bv (bv_unsigned rsp - 96) (by omega) (by omega)
  have hbl := rdn_length _ _ _ _ _ hread
  have hbuf : (buf.length : Int) = bv_unsigned len := by
    rw [hbl]
    rfl
  have hnb : 1 ≤ buf.length := by omega
  have haddr : v_addi (Z_to_bv 64 (bv_unsigned rsp - 96)) 8 =
      Z_to_bv 64 (bv_unsigned rsp - 88) := by
    rw [v_addi, h96]
    congr 1 <;> omega
  have hok : store_ok source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 88)) 8 = true := by
    apply store_ok_mono _ _ _ _ _ hgrow
    apply store_ok_wrap_window
    · rw [h88, stack_max_size_val]
      omega
    · rw [h88]
      omega
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned rsp - 96)) SF_11220 (by decide) SD_11220
    (by decide) (by
      cat_regs
      rw [h2]
      change v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) (-16) = _
      rw [v_addi, h80]
      congr 1 <;> omega))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ len
    SF_11224 (by decide) SD_11224 (by decide)
    (by cat_regs; rw [h12]; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_11228 (by decide) SD_11228 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ pbuf
    SF_1122c (by decide) SD_1122c (by decide)
    (by cat_regs; rw [h11]; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_11230 (by decide) SD_11230 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    SF_11234 (by decide) SD_11234 (by decide)
    (by cat_regs; rw [h10]; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_11238 (by decide) SD_11238 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
    SF_1123c (by decide) SD_1123c (by decide) (by cat_regs; rfl))
  cat_step (step_sd_at source_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned rsp - 88)) RA SF_11240 (by decide) SD_11240
    (by cat_regs; exact haddr) (by cat_regs; exact h1) hok)
  cat_step (step_jal_link source_segs _ _ _ _ _ _ _ SF_11244 (by decide) SD_11244)
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_112b0 (by decide) SD_112b0)
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
    SF_1128c (by decide) SD_1128c (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    SF_11290 (by decide) SD_11290 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ pbuf
    SF_11294 (by decide) SD_11294 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ len
    SF_11298 (by decide) SD_11298 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_1129c (by decide) SD_1129c (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_112a0 (by decide) SD_112a0 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_112a4 (by decide) SD_112a4 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_ecall source_segs _ _ _ _ _ SF_112a8 (by decide))
  apply to_wall_tail.twt_more _ _ _ hnb
  apply twl_write_rec
  · cat_regs; rfl
  · cat_regs
  · cat_regs
    rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
    exact hread
  · exact hnb
  · intro n hn1 hn2
    cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11248 : word)
      SF_112ac (by decide) SD_112ac (by cat_regs; rfl))
    cat_step (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 RA) RA
      SF_11248 (by decide) SD_11248
      (by
        cat_regs
        change rdn source_segs _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 96)) 8) 8 = _
        rw [haddr]
        exact rdn_wbytes_hit8 _ _ _ _ (by rw [h88]; omega))
      (bytes_le_to_Z_8 RA))
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 80)) SF_1124c (by decide) SD_1124c
      (by decide) (by
        cat_regs
        change v_addi (Z_to_bv 64 (bv_unsigned rsp - 96)) 16 = _
        rw [v_addi, h96]
        congr 1 <;> omega))
    cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_11250 (by decide) SD_11250)
    cat_step (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 18446744073709547520)
      SF_11254 (by decide) SD_11254 (by decide) (by decide))
    cat_step (step_bltu_ft source_segs _ _ _ _ _ _ _ _ SF_11258 (by decide) SD_11258
      (by
        cat_regs
        rw [c_ltu_ltb, u_len_word_firstn n buf hn2 (by omega)]
        change decide ((18446744073709547520 : Int) < (n : Int)) = false
        simp only [decide_eq_false_iff_not]
        omega))
    cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ RA
      SF_1125c (by decide) SD_1125c (by cat_regs))
    change to_wall_tail source_segs _ (mkst _ (v_jalr RA 0) _ _) _ _
    rw [hRA]
    apply hK _ _ n hn1 hn2
    · cat_regs
    · cat_regs
    · cat_regs
    · cat_regs
    · cat_regs
    · cat_regs
    · exact mem_grows_trans _ _ _ hgrow (wbytes_grows _ _ _)
    · intro x hx
      rcases hx with hx | hx
      · apply wbytes_below
        · rw [length_N_to_le_bytes, h88]
          omega
        · rw [h88]
          exact hx
      · apply wbytes_above
        rw [length_N_to_le_bytes, h88]
        omega

/-- Rocq's `dbuf`: the digit buffer, a stack slot. -/
def dbuf (rsp : word) : word := Z_to_bv 64 (bv_unsigned rsp - 56)

/-- The decimal loop `0x1118c` to `0x111b0`; the digit buffer is a stack slot,
so the `sb` is a machine store. -/
theorem source_udec_loop (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (f : Nat) (m : word → Option byte) (v k : word) (regs : bvmap 5 word)
    (hv1 : 1 ≤ bv_unsigned v) (hvf : bv_unsigned v < 10 ^ f)
    (hk1 : ((udec (bv_unsigned v)).length : Int) + 1 ≤ bv_unsigned k)
    (hk2 : bv_unsigned k ≤ 23)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h10 : reg_get regs 10 = Z_to_bv 64 9) (h12 : reg_get regs 12 = Z_to_bv 64 10)
    (h11 : reg_get regs 11 = dbuf rsp)
    (h13 : reg_get regs 13 = k) (h15 : reg_get regs 15 = v)
    (hgrow : mem_grows (oob_wmem inp rsp rrnd) m) :
    ∃ regs' : bvmap 5 word,
      (∀ x : reg, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 14 =
        Z_to_bv 64 (bv_unsigned k + 1 - ((udec (bv_unsigned v)).length : Int)) ∧
      msteps source_segs (mkst regs 0x1118c m rrom)
        (mkst regs' 0x111b0
          (wbytes m
            (Z_to_bv 64 (bv_unsigned rsp - 56 +
              (bv_unsigned k + 1 - ((udec (bv_unsigned v)).length : Int))))
            (udec (bv_unsigned v))) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  induction f generalizing m v k regs with
  | zero => change bv_unsigned v < 1 at hvf; omega
  | succ f ih =>
    have huv := u64_range v
    have huk := u64_range k
    have hlp := udec_len_pos (bv_unsigned v)
    let d := bv_unsigned v % 10
    have hd : 0 ≤ d ∧ d < 10 := by dsimp only [d]; omega
    have ud := u_Z2bv d (by omega) (by omega)
    have uc := u_Z2bv (48 + d) (by omega) (by omega)
    let a := Z_to_bv 64 (bv_unsigned rsp - 56 + bv_unsigned k)
    have ua : bv_unsigned a = bv_unsigned rsp - 56 + bv_unsigned k :=
      u_Z2bv _ (by omega) (by omega)
    let r1 := regupd regs 14 (Z_to_bv 64 d)
    let r2 := regupd r1 16 a
    let r3 := regupd r2 14 (Z_to_bv 64 (48 + d))
    let m1 := wbytes m a [Z_to_bv 8 (48 + d)]
    let r4 := regupd r3 16 v
    let r5 := regupd r4 14 k
    let r6 := regupd r5 15 (Z_to_bv 64 (bv_unsigned v / 10))
    let r7 := regupd r6 13 (Z_to_bv 64 (bv_unsigned k - 1))
    have e1 : step source_segs (mkst regs 0x1118c m rrom) =
        MachineOk (mkst r1 0x11190 m rrom) := by
      rw [step_remu source_segs _ _ _ _ _ _ _ _ SF_1118c (by decide) SD_1118c
        (by cat_regs; rw [h12]; decide)]
      simp only [show bv_eqb (14 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      cat_regs
      rw [h15, h12]
      rfl
    have e2 : step source_segs (mkst r1 0x11190 m rrom) =
        MachineOk (mkst r2 0x11194 m rrom) := by
      apply step_add_at source_segs _ _ _ _ _ _ _ _ a SF_11190 (by decide) SD_11190 (by decide)
      dsimp only [r1]; cat_regs
      rw [h11, h13]
      unfold v_add dbuf
      rw [u_Z2bv _ (by omega) (by omega)]
    have e3 : step source_segs (mkst r2 0x11194 m rrom) =
        MachineOk (mkst r3 0x11198 m rrom) := by
      apply step_addiw_at source_segs _ _ _ _ _ _ _ _ _ SF_11194 (by decide) SD_11194 (by decide)
      dsimp only [r2, r1]; cat_regs
      change v_addiw (Z_to_bv 64 d) 48 = _
      apply bv_eq_of_unsigned
      rw [v_addiw_d48 _ (by rw [ud]; omega), ud, uc]
    have e4 : step source_segs (mkst r3 0x11198 m rrom) =
        MachineOk (mkst r3 0x1119c m1 rrom) := by
      apply step_sb_at source_segs _ _ _ _ _ _ _ _ a (Z_to_bv 64 (48 + d))
        (Z_to_bv 8 (48 + d)) SF_11198 (by decide) SD_11198
      · dsimp only [r3, r2]; cat_regs; exact v_addi_0 a
      · dsimp only [r3]; cat_regs
      · rw [uc]
      · apply store_ok_mono _ _ _ _ _ hgrow
        apply store_ok_wrap_window
        · rw [ua, stack_max_size_val]; omega
        · rw [ua]; omega
    have e5 : step source_segs (mkst r3 0x1119c m1 rrom) =
        MachineOk (mkst r4 0x111a0 m1 rrom) := by
      apply step_addi_at source_segs _ _ _ _ _ _ _ _ v SF_1119c (by decide) SD_1119c (by decide)
      dsimp only [r3, r2, r1]; cat_regs; rw [h15]; exact v_addi_0 v
    have e6 : step source_segs (mkst r4 0x111a0 m1 rrom) =
        MachineOk (mkst r5 0x111a4 m1 rrom) := by
      apply step_addi_at source_segs _ _ _ _ _ _ _ _ k SF_111a0 (by decide) SD_111a0 (by decide)
      dsimp only [r4, r3, r2, r1]; cat_regs; rw [h13]; exact v_addi_0 k
    have e7 : step source_segs (mkst r5 0x111a4 m1 rrom) =
        MachineOk (mkst r6 0x111a8 m1 rrom) := by
      rw [step_divu source_segs _ _ _ _ _ _ _ _ SF_111a4 (by decide) SD_111a4
        (by dsimp only [r5, r4, r3, r2, r1]; cat_regs; rw [h12]; decide)]
      simp only [show bv_eqb (15 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      dsimp only [r5, r4, r3, r2, r1, r6]
      cat_regs
      rw [h15, h12]
      rfl
    have e8 : step source_segs (mkst r6 0x111a8 m1 rrom) =
        MachineOk (mkst r7 0x111ac m1 rrom) := by
      apply step_addi_at source_segs _ _ _ _ _ _ _ _ _ SF_111a8 (by decide) SD_111a8 (by decide)
      dsimp only [r6, r5, r4, r3, r2, r1]; cat_regs; rw [h13]; rfl
    have hag : ∀ x : reg, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 →
        reg_get r7 x = reg_get regs x := by
      intro x hx13 hx14 hx15 hx16
      simp only [r7, r6, r5, r4, r3, r2, r1,
        regupd_other _ _ _ _ hx13, regupd_other _ _ _ _ hx14,
        regupd_other _ _ _ _ hx15, regupd_other _ _ _ _ hx16]
    have h14 : reg_get r7 14 = k := by
      dsimp only [r7, r6, r5]; cat_regs
    have h16 : getr r7 16 = v := by
      dsimp only [r7, r6, r5, r4]; cat_regs
    have h10' : getr r7 10 = Z_to_bv 64 9 := by
      rw [getr_nz _ _ (by decide), hag _ (by decide) (by decide) (by decide) (by decide), h10]
    have hprefix : msteps source_segs (mkst regs 0x1118c m rrom)
        (mkst r7 0x111ac m1 rrom) := by
      cat_step e1
      cat_step e2
      cat_step e3
      cat_step e4
      cat_step e5
      cat_step e6
      cat_step e7
      cat_step e8
      exact msteps.mst_refl _
    by_cases hv9 : bv_unsigned v ≤ 9
    · have hs := udec_single (bv_unsigned v) ⟨hv1, hv9⟩
      have hdv : d = bv_unsigned v := by dsimp only [d]; omega
      refine ⟨r7, hag, ?_, ?_⟩
      · rw [h14, hs]
        simp only [List.length_cons, List.length_nil]
        apply bv_eq_of_unsigned
        rw [u_Z2bv _ (by omega) (by omega)]
        omega
      · have hm : wbytes m
            (Z_to_bv 64 (bv_unsigned rsp - 56 +
              (bv_unsigned k + 1 - ((udec (bv_unsigned v)).length : Int))))
            (udec (bv_unsigned v)) = m1 := by
          rw [hs]
          simp only [List.length_cons, List.length_nil]
          dsimp only [m1, a]
          rw [hdv]
          congr 2 <;> omega
        rw [hm]
        apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bltu_ft source_segs _ _ _ _ _ _ _ _ SF_111ac (by decide) SD_111ac
          (by rw [h10', h16, c_ltu_ltb]; change decide (9 < bv_unsigned v) = false; exact decide_eq_false (by omega)))
        exact msteps.mst_refl _
    · have hs := udec_step (bv_unsigned v) (by omega) huv.2
      have hlen : ((udec (bv_unsigned v)).length : Int) =
          ((udec (bv_unsigned v / 10)).length : Int) + 1 := by
        rw [hs]
        simp only [List.length_append, List.length_cons, List.length_nil, Int.natCast_add, Int.natCast_one]
        omega
      have uq : bv_unsigned (Z_to_bv 64 (bv_unsigned v / 10)) = bv_unsigned v / 10 :=
        u_Z2bv _ (by omega) (by omega)
      have uk : bv_unsigned (Z_to_bv 64 (bv_unsigned k - 1)) = bv_unsigned k - 1 :=
        u_Z2bv _ (by omega) (by omega)
      have hqf : bv_unsigned v / 10 < 10 ^ f := by
        rw [Int.pow_succ] at hvf
        omega
      obtain ⟨regs', hag', h14', hms⟩ := ih m1
        (Z_to_bv 64 (bv_unsigned v / 10)) (Z_to_bv 64 (bv_unsigned k - 1)) r7
        (by rw [uq]; omega) (by rw [uq]; exact hqf)
        (by rw [uq, uk]; omega) (by rw [uk]; omega)
        (by rw [hag _ (by decide) (by decide) (by decide) (by decide)]; exact h2)
        (by rw [hag _ (by decide) (by decide) (by decide) (by decide)]; exact h10)
        (by rw [hag _ (by decide) (by decide) (by decide) (by decide)]; exact h12)
        (by rw [hag _ (by decide) (by decide) (by decide) (by decide)]; exact h11)
        (by dsimp only [r7]; cat_regs)
        (by dsimp only [r7, r6]; cat_regs)
        (mem_grows_trans _ _ _ hgrow (wbytes_grows _ _ _))
      rw [uq, uk] at h14' hms
      refine ⟨regs', ?_, ?_, ?_⟩
      · intro x hx13 hx14 hx15 hx16
        rw [hag' x hx13 hx14 hx15 hx16, hag x hx13 hx14 hx15 hx16]
      · rw [h14', hlen]
        congr 1
        omega
      · let p := Z_to_bv 64 (bv_unsigned rsp - 56 +
          (bv_unsigned k - 1 + 1 - ((udec (bv_unsigned v / 10)).length : Int)))
        have up : bv_unsigned p = bv_unsigned rsp - 56 +
            (bv_unsigned k - 1 + 1 - ((udec (bv_unsigned v / 10)).length : Int)) :=
          u_Z2bv _ (by omega) (by omega)
        have ha : p + nat_to_word (udec (bv_unsigned v / 10)).length = a := by
          rw [word_add_nat, up]
          dsimp only [a]
          congr 1
          omega
        have hm : wbytes m
            (Z_to_bv 64 (bv_unsigned rsp - 56 +
              (bv_unsigned k + 1 - ((udec (bv_unsigned v)).length : Int))))
            (udec (bv_unsigned v)) = wbytes m1 p (udec (bv_unsigned v / 10)) := by
          have hp : Z_to_bv 64 (bv_unsigned rsp - 56 +
              (bv_unsigned k + 1 - ((udec (bv_unsigned v)).length : Int))) = p := by
            dsimp only [p]
            congr 1
            omega
          rw [hp, hs, wbytes_app, ha]
          exact wbytes_disjoint_comm _ _ _ _ _ (by rw [up, ua]; omega)
            (by rw [ua]; change bv_unsigned rsp - 56 + bv_unsigned k + 1 < 2 ^ 64; omega)
        rw [hm]
        apply msteps_trans _ _ _ _ hprefix
        cat_step (step_bltu_tk source_segs _ _ _ _ _ _ _ _ SF_111ac (by decide) SD_111ac
          (by rw [h10', h16, c_ltu_ltb]; change decide (9 < bv_unsigned v) = true; exact decide_eq_true (by omega)))
        exact hms

theorem read_over_spill (rsp : word)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (mem : word → Option byte) (p RA : word) (k : Nat)
    (hp : bv_unsigned p + (k : Int) ≤ bv_unsigned rsp - 88 ∨ bv_unsigned rsp - 80 ≤ bv_unsigned p)
    (hk : bv_unsigned p + (k : Int) ≤ 2 ^ 64) :
    rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88)) (word_to_le_bytes 8 RA)) p k =
      rdn source_segs mem p k := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hu : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 88)) =
      bv_unsigned rsp - 88 := u_Z2bv _ (by omega) (by omega)
  rcases hp with hp | hp
  · apply rdn_wbytes_below
    · rw [hu]
      exact hp
    · rw [hu, length_N_to_le_bytes]
      omega
  · apply rdn_wbytes_disjoint
    · rw [hu, length_N_to_le_bytes]
      omega
    · exact hk

/-- The write loop at `0x11100` after a short write of `n` bytes. -/
theorem src_put_loop1 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (K : machine_state → Prop) (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (hfuel : rest.length ≤ fuel) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length)
    (hlen : (rest.length : Int) < 2 ^ 31)
    (hp : bv_unsigned p + (rest.length : Int) ≤ bv_unsigned rsp - 88 ∨
      (bv_unsigned rsp - 80 ≤ bv_unsigned p ∧ bv_unsigned p + (rest.length : Int) < 2 ^ 64))
    (h1 : reg_get regs 1 = (0x11100 : word))
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h8 : reg_get regs 8 = len_word rest) (h9 : reg_get regs 9 = p)
    (h10 : reg_get regs 10 = len_word (rest.take n))
    (hgrow : mem_grows (oob_wmem inp rsp rrnd) mem)
    (hread : rdn source_segs mem p rest.length = some rest)
    (hK : ∀ (regs' : bvmap 5 word) (mem' : word → Option byte),
      reg_get regs' 1 = (0x11100 : word) →
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 80) →
      reg_get regs' 18 = reg_get regs 18 →
      mem_grows (oob_wmem inp rsp rrnd) mem' →
      (∀ x : word, bv_unsigned x < bv_unsigned rsp - 88 ∨ bv_unsigned rsp - 80 ≤ bv_unsigned x →
        mem' x = mem x) →
      K (mkst regs' (0x11110 : word) mem' rrom)) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs (0x11100 : word) mem rrom) (rest.drop n) K := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have u80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have u88 := u_Z2bv (bv_unsigned rsp - 88) (by omega) (by omega)
  have u96 := u_Z2bv (bv_unsigned rsp - 96) (by omega) (by omega)
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn n rest hn2 (by omega)
    have hdlen : ((rest.drop n).length : Int) < 2 ^ 64 := by
      rw [List.length_drop]; omega
    have hdu := u_len_word (rest.drop n) hdlen
    have hup := u64_range p
    have hupn : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
      rw [word_add_nat_Z p n (by omega), u_Z2bv _ (by omega) (by rcases hp with hp | hp <;> omega)]
    cat_step (step_bge_ft source_segs _ _ _ _ _ _ _ _ SF_11100 (by decide) SD_11100
      (by cat_regs; rw [h10]; exact c_lts_0_pos _ (by omega) (by omega)))
    cat_step (step_sub_at source_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
      SF_11104 (by decide) SD_11104 (by decide)
      (by cat_regs; rw [h8, h10]; exact v_sub_len_firstn n rest hn2 (by omega)))
    cat_step (step_add_at source_segs _ _ _ _ _ _ _ _ (p + nat_to_word n)
      SF_11108 (by decide) SD_11108 (by decide)
      (by cat_regs; rw [h9, h10, word_add_nat_Z p n (by omega)];
          exact v_add_len_firstn_Z p n rest hn2 (by omega)))
    by_cases heq : n = rest.length
    · have hempty : rest.drop n = [] := by rw [heq, List.drop_length]
      rw [hempty]
      cat_step (step_bne_ft source_segs _ _ _ _ _ _ _ _ SF_1110c (by decide) SD_1110c
        (by cat_regs; exact c_eq_0_true))
      apply to_wall_tail.twt_done
      apply hK
      · cat_regs; exact h1
      · cat_regs; exact h2
      · cat_regs
      · exact hgrow
      · intro x hx; rfl
    · have hnonempty : 1 ≤ (rest.drop n).length := by rw [List.length_drop]; omega
      have hsk := rdn_skipn source_segs mem rest.length p rest n hread hn2
      rw [← List.length_drop] at hsk
      have hpd : bv_unsigned (p + nat_to_word n) + ((rest.drop n).length : Int)
          ≤ bv_unsigned rsp - 88 ∨ bv_unsigned rsp - 80 ≤ bv_unsigned (p + nat_to_word n) := by
        rw [hupn, List.length_drop]
        rcases hp with hp | hp
        · left; omega
        · right; omega
      have hpnw : bv_unsigned (p + nat_to_word n) + ((rest.drop n).length : Int) < 2 ^ 64 := by
        rw [hupn, List.length_drop]
        rcases hp with hp | hp <;> omega
      have hw : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
        change (word_to_nat (len_word (rest.drop n)) : Int) = ((rest.drop n).length : Int) at hdu
        omega
      cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _ SF_1110c (by decide) SD_1110c
        (by cat_regs; exact c_eq_0_false _ (by rw [hdu]; omega)))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
        SF_110f0 (by decide) SD_110f0 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (p + nat_to_word n)
        SF_110f4 (by decide) SD_110f4 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_110f8 (by decide) SD_110f8 (by decide) (by cat_regs; rfl))
      cat_step (step_jal_link source_segs _ _ _ _ _ _ _ SF_110fc (by decide) SD_110fc)
      simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 96))
        SF_11220 (by decide) SD_11220 (by decide)
        (by cat_regs; rw [h2]; change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + (-16)) = _;
            rw [u80]; congr 1; omega))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
        SF_11224 (by decide) SD_11224 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_11228 (by decide) SD_11228 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (p + nat_to_word n)
        SF_1122c (by decide) SD_1122c (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_11230 (by decide) SD_11230 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_11234 (by decide) SD_11234 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_11238 (by decide) SD_11238 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
        SF_1123c (by decide) SD_1123c (by decide) (by cat_regs; rfl))
      have hok : store_ok source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 88)) 8 = true := by
        apply store_ok_mono _ _ _ _ _ hgrow
        apply store_ok_wrap_window
        · rw [u88, stack_max_size_val]; omega
        · rw [u88]; omega
      cat_step (step_sd_at source_segs _ _ _ _ _ _ _ _
        (Z_to_bv 64 (bv_unsigned rsp - 88)) (0x11100 : word)
        SF_11240 (by decide) SD_11240
        (by cat_regs; change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) + 8) = _;
            rw [u96]; congr 1; omega)
        (by cat_regs; rfl) hok)
      cat_step (step_jal_link source_segs _ _ _ _ _ _ _ SF_11244 (by decide) SD_11244)
      simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_112b0 (by decide) SD_112b0)
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
        SF_1128c (by decide) SD_1128c (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_11290 (by decide) SD_11290 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (p + nat_to_word n)
        SF_11294 (by decide) SD_11294 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
        SF_11298 (by decide) SD_11298 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_1129c (by decide) SD_1129c (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_112a0 (by decide) SD_112a0 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
        SF_112a4 (by decide) SD_112a4 (by decide) (by cat_regs; rfl))
      cat_step (step_ecall source_segs _ _ _ _ _ SF_112a8 (by decide))
      apply to_wall_tail.twt_more _ _ _ hnonempty
      apply twl_write_rec
      · cat_regs; rfl
      · cat_regs
      · cat_regs
        rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        change rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88))
          (word_to_le_bytes 8 (0x11100 : word))) (p + nat_to_word n)
          (word_to_nat (len_word (rest.drop n))) = some (rest.drop n)
        rw [hw, read_over_spill rsp hsp_lo hsp_hi _ _ _ _ hpd (by omega)]
        exact hsk
      · exact hnonempty
      · intro m hm1 hm2
        cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11248 : word)
          SF_112ac (by decide) SD_112ac (by cat_regs; rfl))
        cat_step (step_ld source_segs _ _ _ _ _ _ _ _
          (word_to_le_bytes 8 (0x11100 : word)) (0x11100 : word)
          SF_11248 (by decide) SD_11248
          (by cat_regs
              have ha : v_addi (Z_to_bv 64 (bv_unsigned rsp - 96)) (bv_signed (8 : BitVec 12)) =
                  Z_to_bv 64 (bv_unsigned rsp - 88) := by
                change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) + 8) = _
                rw [u96]; congr 1; omega
              rw [ha]; exact rdn_wbytes_hit8 _ _ _ _ (by rw [u88]; omega))
          (bytes_le_to_Z_8 _))
        simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
        cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 80))
          SF_1124c (by decide) SD_1124c (by decide)
          (by cat_regs; change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) + 16) = _;
              rw [u96]; congr 1; omega))
        cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_11250 (by decide) SD_11250)
        cat_step (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 (2 ^ 64 - 4096))
          SF_11254 (by decide) SD_11254 (by decide) (by rfl))
        have hum := u_len_word_firstn m (rest.drop n) hm2 hdlen
        cat_step (step_bltu_ft source_segs _ _ _ _ _ _ _ _ SF_11258 (by decide) SD_11258
          (by cat_regs; rw [c_ltu_ltb]; apply decide_eq_false;
              change ¬ (18446744073709547520 : Int) < bv_unsigned (len_word ((rest.drop n).take m))
              rw [hum]; rw [List.length_drop] at hm2; omega))
        cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11100 : word)
          SF_1125c (by decide) SD_1125c (by cat_regs))
        apply ih (rest.drop n) (p + nat_to_word n) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · rcases hpd with hpd | hpd
          · exact Or.inl hpd
          · exact Or.inr ⟨hpd, hpnw⟩
        · cat_regs
        · cat_regs
        · cat_regs
        · cat_regs
        · cat_regs
        · exact mem_grows_trans _ _ _ hgrow (wbytes_grows _ _ _)
        · rw [read_over_spill rsp hsp_lo hsp_hi _ _ _ _ hpd (by omega)]
          exact hsk
        · intro regs' mem' h1' h2' h18' hgrow' hmem'
          apply hK regs' mem' h1' h2'
          · rw [h18']; cat_regs
          · exact hgrow'
          · intro x hx
            rw [hmem' x hx]
            rcases hx with hx | hx
            · apply wbytes_below
              · rw [length_N_to_le_bytes, u88]; omega
              · rw [u88]; exact hx
            · apply wbytes_above
              rw [length_N_to_le_bytes, u88]; omega

/-- From `0x110e4` with the decimal digits in the buffer: write them, write the
newline, exit 0.  The scratch stores are machine stores into the stack frame. -/
theorem source_print_tail (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (M : word → Option byte) (sum : Int)
    (hs0 : 0 ≤ sum) (hs64 : sum < 2 ^ 64)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h11 : reg_get regs 11 = dbuf rsp)
    (h15 : reg_get regs 15 = Z_to_bv 64 (24 - ((udec sum).length : Int)))
    (hnl : M (0x12000 : word) = none)
    (hra : rdn source_segs M (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)))
    (hslots : ∀ a : word,
      a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
        Z_to_bv 64 (bv_unsigned rsp - 32)] →
      rdn source_segs M a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (hgrow : mem_grows (oob_wmem inp rsp rrnd) M) :
    to_wallexit source_segs (Z_to_bv 64 1) [udec sum, [Z_to_bv 8 10]] (Z_to_bv 64 0)
      (mkst regs 0x110e4
        (wbytes M (Z_to_bv 64 (bv_unsigned rsp - 56 + (24 - ((udec sum).length : Int))))
          (udec sum)) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hl1 := udec_len_pos sum
  have hl20 := udec_len_le sum hs0 hs64
  let L : Int := (udec sum).length
  let base := Z_to_bv 64 (bv_unsigned rsp - 56 + (24 - L))
  let Md := wbytes M base (udec sum)
  have hL1 : 1 ≤ L := by dsimp only [L]; omega
  have hL20 : L ≤ 20 := by dsimp only [L]; omega
  have uL := u_Z2bv L (by omega) (by omega)
  have uoff := u_Z2bv (24 - L) (by omega) (by omega)
  have ub : bv_unsigned base = bv_unsigned rsp - 56 + (24 - L) :=
    u_Z2bv _ (by omega) (by omega)
  have hnw : bv_unsigned base + ((udec sum).length : Int) ≤ 2 ^ 64 := by
    rw [ub]; change _ + L ≤ _; omega
  have hw : word_to_nat (Z_to_bv 64 L) = (udec sum).length := by
    change (word_to_nat (Z_to_bv 64 L) : Int) = L at uL
    omega
  have hread : rdn source_segs Md base (udec sum).length = some (udec sum) :=
    rdn_wbytes_hit _ _ _ _ hnw
  have hMd (x : word) (hx : bv_unsigned rsp - 32 ≤ bv_unsigned x) : Md x = M x := by
    apply wbytes_above
    rw [ub]; change _ + L ≤ _; omega
  have hnlMd : Md (0x12000 : word) = none := by
    dsimp only [Md]
    rw [wbytes_below _ M base (0x12000 : word) hnw
      (by change (73728 : Int) < bv_unsigned base; rw [ub]; omega)]
    exact hnl
  change 1 ≤ (udec sum).length ∧ _
  refine ⟨hl1, ?_⟩
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 24)
    SF_110e4 (by decide) SD_110e4 (by decide) (by cat_regs; rfl))
  cat_step (step_add_at source_segs _ _ _ _ _ _ _ _ base
    SF_110e8 (by decide) SD_110e8 (by decide) (by
      cat_regs; rw [h11, h15]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 56)) +
        bv_unsigned (Z_to_bv 64 (24 - L))) = base
      rw [u_Z2bv _ (by omega) (by omega), uoff]))
  cat_step (step_sub_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 L)
    SF_110ec (by decide) SD_110ec (by decide) (by
      cat_regs; rw [h15]
      change Z_to_bv 64 (24 - bv_unsigned (Z_to_bv 64 (24 - L))) = _
      rw [uoff]; congr 1; omega))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 L)
    SF_110f0 (by decide) SD_110f0 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ base
    SF_110f4 (by decide) SD_110f4 (by decide) (by cat_regs; exact v_addi_0 _))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
    SF_110f8 (by decide) SD_110f8 (by decide) (by cat_regs; rfl))
  cat_step (step_jal_link source_segs _ _ _ _ _ _ _ SF_110fc (by decide) SD_110fc)
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  apply source_put inp rsp rrnd hsp_lo hsp_hi _ _ Md (udec sum) base
    (Z_to_bv 64 L) (0x11100 : word)
  · cat_regs; rfl
  · cat_regs; exact h2
  · cat_regs
  · cat_regs
  · cat_regs
  · rw [uL]; omega
  · rw [uL]; omega
  · rfl
  · rw [hw, read_over_spill rsp hsp_lo hsp_hi _ _ _ _
      (Or.inr (by rw [ub]; omega)) hnw]
    exact hread
  · exact mem_grows_trans _ _ _ hgrow (wbytes_grows _ _ _)
  · intro regsA memA n hn1 hn2 ha1 ha2 ha8 ha10 ha9 ha18 hgA hmA
    have hnlA : memA (0x12000 : word) = none := by
      rw [hmA _ (Or.inl (by change (73728 : Int) < _; omega))]
      exact hnlMd
    have hsaveA (x : word) (hx : bv_unsigned rsp - 32 ≤ bv_unsigned x) : memA x = M x := by
      rw [hmA x (Or.inr (by omega))]; exact hMd x hx
    apply src_put_loop1 inp rsp rrnd hsp_lo hsp_hi _ (udec sum).length
      (udec sum) base n regsA memA
    · exact Nat.le_refl _
    · exact hn1
    · exact hn2
    · omega
    · right; rw [ub]; constructor <;> dsimp only [L] at * <;> omega
    · exact ha1
    · exact ha2
    · rw [ha8]; cat_regs; rfl
    · rw [ha9]; cat_regs
    · exact ha10
    · exact hgA
    · rw [rdn_ext source_segs _ memA Md base hnw (by
        intro x hx; apply hmA; right; rw [ub] at hx; omega)]
      exact hread
    · intro regsB memB hb1 hb2 hb18 hgB hmB
      have hnlB : memB (0x12000 : word) = none := by
        rw [hmB _ (Or.inl (by change (73728 : Int) < _; omega))]; exact hnlA
      have hsaveB (x : word) (hx : bv_unsigned rsp - 32 ≤ bv_unsigned x) : memB x = M x := by
        rw [hmB x (Or.inr (by omega))]; exact hsaveA x hx
      change 1 ≤ ([Z_to_bv 8 10] : List byte).length ∧ _
      refine ⟨by decide, ?_⟩
      cat_step (step_lui_at source_segs _ _ _ _ _ _ _ (0x12000 : word)
        SF_11110 (by decide) SD_11110 (by decide) (by rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_11114 (by decide) SD_11114 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x12000 : word)
        SF_11118 (by decide) SD_11118 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_1111c (by decide) SD_1111c (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (0x12000 : word)
        SF_11120 (by decide) SD_11120 (by decide) (by cat_regs; exact v_addi_0 _))
      cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        SF_11124 (by decide) SD_11124 (by decide) (by cat_regs; rfl))
      cat_step (step_jal_link source_segs _ _ _ _ _ _ _ SF_11128 (by decide) SD_11128)
      simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      apply source_put inp rsp rrnd hsp_lo hsp_hi _ _ memB [Z_to_bv 8 10]
        (0x12000 : word) (Z_to_bv 64 1) (0x1112c : word)
      · cat_regs; rfl
      · cat_regs; exact hb2
      · cat_regs
      · cat_regs
      · cat_regs
      · decide
      · decide
      · rfl
      · change rdn source_segs _ (0x12000 : word) 1 = _
        rw [read_over_spill rsp hsp_lo hsp_hi _ _ _ _
          (Or.inl (by change (73728 : Int) + 1 ≤ _; omega)) (by decide)]
        exact read_newline _ hnlB
      · exact hgB
      · intro regsC memC nC hc1 hc2 hc_ra hc_sp hc8 hc10 hc9 hc18 hgC hmC
        have hnC : nC = 1 := by simp only [List.length_singleton] at hc2; omega
        subst nC
        simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at hc10 ⊢
        have hsaveC (x : word) (hx : bv_unsigned rsp - 32 ≤ bv_unsigned x) : memC x = M x := by
          rw [hmC x (Or.inr (by omega))]; exact hsaveB x hx
        cat_step (step_bge_ft source_segs _ _ _ _ _ _ _ _ SF_1112c (by decide) SD_1112c
          (by cat_regs; rw [hc10]; decide))
        cat_step (step_sub_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
          SF_11130 (by decide) SD_11130 (by decide)
          (by cat_regs; rw [hc9, hc10]; cat_regs; rfl))
        cat_step (step_add_at source_segs _ _ _ _ _ _ _ _
          (v_add (reg_get regsC 8) (reg_get regsC 10))
          SF_11134 (by decide) SD_11134 (by decide) (by cat_regs))
        cat_step (step_bne_ft source_segs _ _ _ _ _ _ _ _ SF_11138 (by decide) SD_11138
          (by cat_regs; exact c_eq_0_true))
        apply to_wall_tail.twt_done
        change to_wexit source_segs _ [] (Z_to_bv 64 0)
        cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
          SF_1113c (by decide) SD_1113c (by decide) (by cat_regs; rfl))
        cat_step (step_jal_x0 source_segs _ _ _ _ _ _ SF_11140 (by decide) SD_11140)
        apply source_epilogue rsp hsp_lo hsp_hi
        · cat_regs; exact hc_sp
        · cat_regs
        · decide
        · rw [rdn_ext source_segs 8 memC M _
            (by rw [u_Z2bv _ (by omega) (by omega)]; omega) (by
              intro x hx; apply hsaveC
              rw [u_Z2bv _ (by omega) (by omega)] at hx; omega)]
          exact hra
        · intro a ha
          have hab : bv_unsigned rsp - 32 ≤ bv_unsigned a ∧
              bv_unsigned a ≤ bv_unsigned rsp - 16 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl <;>
              rw [u_Z2bv _ (by omega) (by omega)] <;> constructor <;> omega
          rw [rdn_ext source_segs 8 memC M a (by omega) (by
            intro x hx; exact hsaveC x (by omega))]
          exact hslots a ha

/-- From `0x110d0` with the byte sum in `a5`: print it and exit 0. -/
theorem source_success (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hge2 : 2 ≤ inp.in_argv.length)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (M : word → Option byte)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h15 : reg_get regs 15 = Z_to_bv 64 (sumb (arg1 inp.in_argv)))
    (hnl : M (0x12000 : word) = none)
    (hra : rdn source_segs M (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)))
    (hslots : ∀ a : word,
      a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
        Z_to_bv 64 (bv_unsigned rsp - 32)] →
      rdn source_segs M a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (hgrow : mem_grows (oob_wmem inp rsp rrnd) M) :
    to_wallexit source_segs (Z_to_bv 64 1) (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0)
      (mkst regs 0x110d0 M rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hs0 := sumb_nonneg (arg1 inp.in_argv)
  have hs64 : sumb (arg1 inp.in_argv) < 2 ^ 64 := by
    have hn := nN_le inp.in_argv hva hge2
    have hs := sumb_le (arg1 inp.in_argv) (arg1_bytes inp.in_argv hva hge2)
    unfold nn at hn
    omega
  have us := u_Z2bv _ hs0 hs64
  have hl := udec_len_le (sumb (arg1 inp.in_argv)) hs0 hs64
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have next {ms ms' : machine_state}
      (hp : ms.ms_svc_pending = none)
      (he : step source_segs ms = MachineOk ms')
      (ht : to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms') :
      to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms :=
    msteps_to_wallexit _ _ _ _ _ _ (msteps.mst_step _ _ _ hp he (msteps.mst_refl _)) ht
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (dbuf rsp)
    SF_110d0 (by decide) SD_110d0 (by decide) (by
      cat_regs; rw [h2]
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + 24) = _
      rw [h80]; unfold dbuf; congr 1; omega)) ?_
  by_cases hz : sumb (arg1 inp.in_argv) = 0
  · have hd : udec (sumb (arg1 inp.in_argv)) = [Z_to_bv 8 48] := by
      rw [hz]; rfl
    refine next rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _
      SF_110d4 (by decide) SD_110d4
      (by cat_regs; rw [h15, hz]; exact c_eq_0_true)) ?_
    refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 48)
      SF_110d8 (by decide) SD_110d8 (by decide) (by cat_regs; rfl)) ?_
    refine next rfl (step_sb_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned rsp - 33)) (Z_to_bv 64 48) (Z_to_bv 8 48)
      SF_110dc (by decide) SD_110dc (by
        cat_regs; rw [h2]
        change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + 47) = _
        rw [h80]; congr 1; omega)
      (by cat_regs) (by rfl) (by
        apply store_ok_mono _ _ _ _ _ hgrow
        apply store_ok_wrap_window
        · rw [u_Z2bv _ (by omega) (by omega), stack_max_size_val]; omega
        · rw [u_Z2bv _ (by omega) (by omega)]; omega)) ?_
    refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 23)
      SF_110e0 (by decide) SD_110e0 (by decide) (by cat_regs; rfl)) ?_
    have hm : wbytes M
        (Z_to_bv 64 (bv_unsigned rsp - 56 +
          (24 - ((udec (sumb (arg1 inp.in_argv))).length : Int))))
        (udec (sumb (arg1 inp.in_argv))) =
        wbytes M (Z_to_bv 64 (bv_unsigned rsp - 33)) [Z_to_bv 8 48] := by
      rw [hd]
      simp only [List.length_singleton]
      congr 2
      omega
    rw [← hm]
    apply source_print_tail inp rsp rrnd hsp_lo hsp_hi _ M _ hs0 hs64
    · cat_regs; exact h2
    · cat_regs
    · cat_regs; rw [hd]; rfl
    · exact hnl
    · exact hra
    · exact hslots
    · exact hgrow
  · refine next rfl (step_bne_tk source_segs _ _ _ _ _ _ _ _
      SF_110d4 (by decide) SD_110d4
      (by cat_regs; rw [h15]; exact c_eq_0_false _ (by rw [us]; exact hz))) ?_
    refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 23)
      SF_11180 (by decide) SD_11180 (by decide) (by cat_regs; rfl)) ?_
    refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 10)
      SF_11184 (by decide) SD_11184 (by decide) (by cat_regs; rfl)) ?_
    refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 9)
      SF_11188 (by decide) SD_11188 (by decide) (by cat_regs; rfl)) ?_
    obtain ⟨regsU, hag, h14, hms⟩ := source_udec_loop inp rsp rrnd hsp_lo hsp_hi
      25 M (Z_to_bv 64 (sumb (arg1 inp.in_argv))) (Z_to_bv 64 23)
      (regupd (regupd (regupd (regupd regs 11 (dbuf rsp)) 13 (Z_to_bv 64 23))
        12 (Z_to_bv 64 10)) 10 (Z_to_bv 64 9))
      (by rw [us]; omega)
      (by rw [us]; omega)
      (by rw [us]; change _ + 1 ≤ (23 : Int); omega)
      (by decide)
      (by cat_regs; exact h2) (by cat_regs) (by cat_regs) (by cat_regs)
      (by cat_regs) (by cat_regs; exact h15) hgrow
    rw [us] at h14 hms
    change reg_get regsU 14 =
      Z_to_bv 64 (24 - ((udec (sumb (arg1 inp.in_argv))).length : Int)) at h14
    refine msteps_to_wallexit _ _ _ _ _ _ hms ?_
    refine next rfl (step_addiw_at source_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (24 - ((udec (sumb (arg1 inp.in_argv))).length : Int)))
      SF_111b0 (by decide) SD_111b0 (by decide) (by
        cat_regs; rw [h14]
        apply v_addiw_id
        rw [u_Z2bv _ (by omega) (by omega)]; omega)) ?_
    refine next rfl (step_jal_x0 source_segs _ _ _ _ _ _
      SF_111b4 (by decide) SD_111b4) ?_
    apply source_print_tail inp rsp rrnd hsp_lo hsp_hi _ M _ hs0 hs64
    · cat_regs
      rw [hag 2 (by decide) (by decide) (by decide) (by decide)]
      cat_regs; exact h2
    · cat_regs
      rw [hag 11 (by decide) (by decide) (by decide) (by decide)]
      cat_regs
    · cat_regs
    · exact hnl
    · exact hra
    · exact hslots
    · exact hgrow

theorem read_spill (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r : word) :
    rdn source_segs (fmem2 inp rsp rrnd r) (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 =
      some (word_to_le_bytes 8 (r + nN inp.in_argv)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  unfold fmem2
  apply rdn_wbytes_hit8
  rw [u_Z2bv _ (by omega) (by omega)]
  omega

/-- The empty-string run: no copy, no sum, print `0`. -/
theorem source_run_empty (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (_hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (hnn0 : nn inp.in_argv = 0)
    (regs5 : bvmap 5 word) (r : word)
    (_hrw : bv_unsigned r + (nn inp.in_argv : Int) < 2 ^ 64)
    (h1 : reg_get regs5 1 = (0x110b0 : word))
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h8 : reg_get regs5 8 = nN inp.in_argv)
    (_h18 : reg_get regs5 18 = ptr inp.in_argv inp.in_envp rsp) :
    to_wallexit source_segs (Z_to_bv 64 1) (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0)
      (mkst (regupd regs5 10 (r + nN inp.in_argv)) 0x1121c (fmem2 inp rsp rrnd r) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have harg : arg1 inp.in_argv = [] := List.length_eq_zero_iff.mp hnn0
  have hn0 : nN inp.in_argv = Z_to_bv 64 0 := by
    unfold nN
    rw [hnn0]
    rfl
  have next {ms ms' : machine_state}
      (hp : ms.ms_svc_pending = none)
      (he : step source_segs ms = MachineOk ms')
      (ht : to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms') :
      to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms :=
    msteps_to_wallexit _ _ _ _ _ _ (msteps.mst_step _ _ _ hp he (msteps.mst_refl _)) ht
  refine next rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110b0 : word)
    SF_1121c (by decide) SD_1121c (by cat_regs; exact h1)) ?_
  refine next rfl (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (r + nN inp.in_argv)) (r + nN inp.in_argv)
    SF_110b0 (by decide) SD_110b0 (by
      cat_regs
      rw [h2]
      have ha : v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 8 =
          Z_to_bv 64 (bv_unsigned rsp - 72) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1
        omega
      change rdn source_segs _ (v_addi _ 8) 8 = _
      rw [ha]
      exact read_spill inp rsp rrnd hsp_lo hsp_hi r)
    (bytes_le_to_Z_8 _)) ?_
  simp only [show bv_eqb (11 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110b4 (by decide) SD_110b4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _
    SF_110b8 (by decide) SD_110b8 (by cat_regs; exact c_eq_refl _)) ?_
  refine next rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _
    SF_110bc (by decide) SD_110bc
    (by cat_regs; rw [h8, hn0]; exact c_eq_0_true)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c0 (by decide) SD_110c0 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c4 (by decide) SD_110c4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 8)
    SF_110c8 (by decide) SD_110c8 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _
    SF_110cc (by decide) SD_110cc (by cat_regs; rw [h8, hn0]; decide)) ?_
  apply source_success inp rsp rrnd hva hge2 hsp_lo hsp_hi
  · cat_regs; exact h2
  · cat_regs; rw [harg]; rfl
  · apply fmem2_none inp rsp rrnd hsp_lo hsp_hi r
    · rw [stack_max_size_val]
      change (0x12000 : Int) < bv_unsigned rsp - 8388608
      omega
    · exact Or.inl (by decide)
  · exact read_slot_ra2 inp rsp rrnd hsp_lo hsp_hi r
  · exact read_slot_02 inp rsp rrnd hsp_lo hsp_hi r
  · unfold fmem2 fmem emem
    repeat apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
    exact mem_grows_refl _

/-- The successful run after the second `brk` granted `grant` zeroed bytes at `r`. -/
theorem source_run_success (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length)
    (regs5 : bvmap 5 word) (r grant : word)
    (hgrant : bv_unsigned (nN inp.in_argv) ≤ bv_unsigned grant)
    (htotalgrant : ((8 * ((nn inp.in_argv + 7) / 8) : Nat) : Int) ≤ bv_unsigned grant)
    (hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - stack_max_size)
    (hphysfree : region_free (segments_reserved source_segs) r grant = true)
    (hr0 : 0 < bv_unsigned r) (hnnz : nn inp.in_argv ≠ 0)
    (h1 : reg_get regs5 1 = (0x110b0 : word))
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h8 : reg_get regs5 8 = nN inp.in_argv) (h9 : reg_get regs5 9 = r)
    (h18 : reg_get regs5 18 = ptr inp.in_argv inp.in_envp rsp) :
    to_wallexit source_segs (Z_to_bv 64 1) (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0)
      (mkst (regupd regs5 10 (r + nN inp.in_argv)) 0x1121c
        (zmem (fmem2 inp rsp rrnd r) r grant) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hn := nN_le inp.in_argv hva hge2
  have hun := u_nN inp.in_argv hva hge2
  have hplo := ptr_lo inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  have hphi := ptr_hi inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  let chunks := (nn inp.in_argv + 7) / 8
  let total := 8 * chunks
  have hlast : 8 * (chunks - 1) < nn inp.in_argv := by
    dsimp only [chunks]
    omega
  have hntotal : nn inp.in_argv ≤ total := by
    dsimp only [total, chunks]
    omega
  have htotalbound : (total : Int) < 2 ^ 64 := by
    dsimp only [total, chunks]
    omega
  have hceil : bv_unsigned r + (nn inp.in_argv : Int) ≤
      bv_unsigned rsp - stack_max_size := by omega
  have htotalceil : bv_unsigned r + (total : Int) ≤
      bv_unsigned rsp - stack_max_size := by
    change (total : Int) ≤ bv_unsigned grant at htotalgrant
    omega
  have hfree := region_free_prefix _ r _ _ hgrant hphysfree
  have hphys : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - 8388608 :=
    hgrantceil
  have hrw : bv_unsigned r + (total : Int) < 2 ^ 64 := by
    rw [stack_max_size_val] at htotalceil
    omega
  let mem0 := zmem (fmem2 inp rsp rrnd r) r grant
  let M := wbytes mem0 r (arg1 inp.in_argv)
  have hstr : rdn source_segs mem0 (ptr inp.in_argv inp.in_envp rsp)
      (nn inp.in_argv + 1) = some (arg1 inp.in_argv ++ [Z_to_bv 8 0]) := by
    dsimp only [mem0]
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (Or.inr (by omega))]
    obtain ⟨tl, _, hread⟩ := read_str_f8_2 inp rsp rrnd hva hve hsp_lo hsp_hi hge2 r
    have ht := rdn_firstn source_segs _ _ _ _ (nn inp.in_argv + 1) hread (by omega)
    have he : nn inp.in_argv + 1 = (arg1 inp.in_argv ++ [Z_to_bv 8 0]).length := by
      simp only [nn, List.length_append, List.length_singleton]
    rw [he, List.take_left] at ht
    rw [← he] at ht
    exact ht
  have hbuf : rdn source_segs M r (nn inp.in_argv) = some (arg1 inp.in_argv) :=
    rdn_wbytes_hit _ _ _ _ (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)
  have hbyte : ∀ i, i < total → rdn source_segs M (r + nat_to_word i) 1 =
      some [(arg1 inp.in_argv).getD i (Z_to_bv 8 0)] := by
    intro i hi
    by_cases hin : i < nn inp.in_argv
    · exact rdn_nth _ _ _ _ _ _ hbuf hin
    · have hui : bv_unsigned (r + nat_to_word i) = bv_unsigned r + (i : Int) := by
        rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]
      have hout : (arg1 inp.in_argv).getD i (Z_to_bv 8 0) = Z_to_bv 8 0 := by
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show (arg1 inp.in_argv).length ≤ i by
            change nn inp.in_argv ≤ i; omega),
          Option.getD_none]
      rw [hout]
      dsimp only [M]
      rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; rw [hui]; omega)
        (by rw [hui]; omega)]
      apply rdn_zmem_in1
      rw [hui]
      constructor <;> omega
  have h72 := u_Z2bv (bv_unsigned rsp - 72) (by omega) (by omega)
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have hspill : rdn source_segs mem0 (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 =
      some (word_to_le_bytes 8 (r + nN inp.in_argv)) := by
    dsimp only [mem0]
    rw [rdn_zmem_out _ _ _ _ _ _ (by rw [h72]; omega) (Or.inr (by rw [h72]; omega))]
    exact read_spill inp rsp rrnd hsp_lo hsp_hi r
  have hframe (a : word) (ha : bv_unsigned rsp - 32 ≤ bv_unsigned a)
      (hnw : bv_unsigned a + 8 ≤ 2 ^ 64) :
      rdn source_segs M a 8 = rdn source_segs (fmem2 inp rsp rrnd r) a 8 := by
    apply rdn_ext _ _ _ _ _ hnw
    intro x hx
    dsimp only [M]
    rw [wbytes_above _ _ _ _ (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)]
    exact zmem_out _ _ _ _ (Or.inr (by omega))
  have next {ms ms' : machine_state}
      (hp : ms.ms_svc_pending = none)
      (he : step source_segs ms = MachineOk ms')
      (ht : to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms') :
      to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms :=
    msteps_to_wallexit _ _ _ _ _ _ (msteps.mst_step _ _ _ hp he (msteps.mst_refl _)) ht
  refine next rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110b0 : word)
    SF_1121c (by decide) SD_1121c (by cat_regs; exact h1)) ?_
  refine next rfl (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (r + nN inp.in_argv)) (r + nN inp.in_argv)
    SF_110b0 (by decide) SD_110b0 (by
      cat_regs; rw [h2]
      change rdn source_segs mem0 (Z_to_bv 64
        (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + 8)) 8 = _
      rw [h80]
      rw [show bv_unsigned rsp - 80 + 8 = bv_unsigned rsp - 72 by omega]
      exact hspill)
    (bytes_le_to_Z_8 _)) ?_
  simp only [show bv_eqb (11 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110b4 (by decide) SD_110b4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _
    SF_110b8 (by decide) SD_110b8 (by cat_regs; exact c_eq_refl _)) ?_
  obtain ⟨regsC, hagC, h15C, h9C, h8C, h18C, hmsC⟩ :=
    source_copy inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2 r mem0
      (store_grant_zmem_prefix _ _ _ _ _ hgrant (by omega)) hstr hfree hr0 hceil
      (nn inp.in_argv)
      (regupd (regupd (regupd regs5 10 (r + nN inp.in_argv)) 11 (r + nN inp.in_argv))
        15 (Z_to_bv 64 0))
      (Nat.le_refl _) (by cat_regs; exact h18) (by cat_regs; exact h9)
      (by cat_regs; exact h8) (by cat_regs; rw [Nat.sub_self]; rfl)
  simp only [Nat.sub_self, List.take_zero, wbytes] at hmsC
  refine msteps_to_wallexit _ _ _ _ _ _ hmsC ?_
  change to_wallexit _ _ _ _ (mkst regsC 0x110c0 M rrom)
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c0 (by decide) SD_110c0 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c4 (by decide) SD_110c4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 8)
    SF_110c8 (by decide) SD_110c8 (by decide) (by cat_regs; rfl)) ?_
  obtain ⟨regsS, hagS, h14S, h9S, h15S, h12S, h8S, hmsS⟩ :=
    source_sum inp.in_argv rsp hva hge2 hsp_lo hsp_hi r M total hbyte hr0 htotalceil
      chunks 0 (regupd (regupd (regupd regsC 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))
        12 (Z_to_bv 64 8))
      (by simpa only [Nat.zero_add] using hlast) (by rw [Nat.zero_add])
      (by cat_regs; rfl) (by cat_regs; exact h9C) (by cat_regs; rfl)
      (by cat_regs) (by cat_regs; exact h8C)
  refine msteps_to_wallexit _ _ _ _ _ _ hmsS ?_
  simp only [Nat.zero_add] at h14S h15S
  refine next rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _
    SF_110cc (by decide) SD_110cc (by
      cat_regs; rw [h14S, h8S, c_ltu_ltb, u_ntw _ htotalbound, hun]
      apply decide_eq_false
      omega)) ?_
  apply source_success inp rsp rrnd hva hge2 hsp_lo hsp_hi regsS M
  · rw [hagS 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    cat_regs
    rw [hagC 2 (by decide) (by decide) (by decide)]
    cat_regs
    exact h2
  · rw [h15S, List.take_of_length_le hntotal]
  · have hd := source_free_cases r grant hphysfree (by omega)
    have he : M (0x12000 : word) = fmem2 inp rsp rrnd r (0x12000 : word) := by
      dsimp only [M, mem0]
      rcases hd with hd | hd
      · rw [wbytes_above _ _ _ _ (by
          change bv_unsigned r + (nn inp.in_argv : Int) ≤ 0x12000; omega)]
        apply zmem_out
        right
        change bv_unsigned r + bv_unsigned grant ≤ 0x12000
        omega
      · rw [wbytes_below _ _ _ _ (by
          change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega) (by
          change (0x12000 : Int) < bv_unsigned r; omega)]
        apply zmem_out
        left
        change (0x12000 : Int) < bv_unsigned r
        omega
    rw [he]
    apply fmem2_none inp rsp rrnd hsp_lo hsp_hi
    · change (0x12000 : Int) < bv_unsigned rsp - stack_max_size
      rw [stack_max_size_val]; omega
    · exact Or.inl (by decide)
  · rw [hframe _ (by rw [u_Z2bv _ (by omega) (by omega)]; omega)
      (by rw [u_Z2bv _ (by omega) (by omega)]; omega)]
    exact read_slot_ra2 inp rsp rrnd hsp_lo hsp_hi r
  · intro a ha
    have hab : bv_unsigned rsp - 32 ≤ bv_unsigned a ∧
        bv_unsigned a ≤ bv_unsigned rsp - 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;>
        rw [u_Z2bv _ (by omega) (by omega)] <;> constructor <;> omega
    rw [hframe a hab.1 (by omega)]
    exact read_slot_02 inp rsp rrnd hsp_lo hsp_hi r a ha
  · have hz : mem_grows (fmem2 inp rsp rrnd r) mem0 := by
      intro x hx
      dsimp only [mem0, zmem]
      split
      · decide
      · exact hx
    apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
    apply mem_grows_trans _ _ _ ?_ hz
    unfold fmem2 fmem emem
    repeat apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
    exact mem_grows_refl _

theorem str_from_mem0 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (r : word) (_hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (nn inp.in_argv : Int) ≤ bv_unsigned rsp - stack_max_size) :
    rdn source_segs (zmem (fmem2 inp rsp rrnd r) r (nN inp.in_argv))
      (ptr inp.in_argv inp.in_envp rsp) (nn inp.in_argv + 1) =
      some (arg1 inp.in_argv ++ [Z_to_bv 8 0]) := by
  have hlo := ptr_lo inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  have hhi := ptr_hi inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  have hnw : bv_unsigned (ptr inp.in_argv inp.in_envp rsp) +
      ((nn inp.in_argv + 1 : Nat) : Int) ≤ 2 ^ 64 := by omega
  rw [rdn_zmem_out _ _ _ _ _ _ hnw (Or.inr (by
    rw [u_nN inp.in_argv hva hge2]
    have hs := stack_max_size_val
    omega))]
  rw [rdn_ext source_segs (nn inp.in_argv + 1) (fmem2 inp rsp rrnd r)
    (fmem inp rsp rrnd) (ptr inp.in_argv inp.in_envp rsp) hnw (by
      intro x hx
      exact fmem2_above inp rsp rrnd hsp_lo hsp_hi r x (by omega))]
  rw [rdn_fmem_above inp rsp rrnd hsp_lo hsp_hi _ _ hlo hnw,
    oob_rdn_wmem_stack inp rsp rrnd _ _ hlo hnw]
  obtain ⟨pre, post, he, hlen⟩ := bsb_byte_k source_phdrs rsp
    inp.in_argv inp.in_envp 1 inp.in_uid inp.in_hwcap rrnd (by omega)
  have hread := read_at_offset_image source_segs source_phdrs rsp
    inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd
    pre (arg1 inp.in_argv ++ [Z_to_bv 8 0]) post (nn inp.in_argv + 1) he
    (by simp only [nn, List.length_append, List.length_cons, List.length_nil])
    (source_bsb_nw inp rsp rrnd hva hve hsp_lo hsp_hi)
  rw [hlen] at hread
  rw [ptr, cat_argv_ptr_offset rsp inp.in_argv inp.in_envp 1 (by omega),
    cat_string_base, nat_to_word_add_merge]
  exact hread

theorem spill_from_mem0 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (_hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length) (r : word) (_hr0 : 0 < bv_unsigned r)
    (hrs : bv_unsigned r + (nn inp.in_argv : Int) ≤ bv_unsigned rsp - stack_max_size) :
    rdn source_segs (zmem (fmem2 inp rsp rrnd r) r (nN inp.in_argv))
      (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 =
      some (word_to_le_bytes 8 (r + nN inp.in_argv)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have ha := u_Z2bv (bv_unsigned rsp - 72) (by omega) (by omega)
  rw [rdn_zmem_out source_segs (fmem2 inp rsp rrnd r) r (nN inp.in_argv)
    (Z_to_bv 64 (bv_unsigned rsp - 72)) 8
    (by rw [ha]; omega)
    (by
      right
      rw [ha, u_nN inp.in_argv hva hge2]
      rw [stack_max_size_val] at hrs
      omega)]
  exact read_spill inp rsp rrnd hsp_lo hsp_hi r

/-- Retained but uncalled, as in Rocq: the `nn mod 8 ≠ 0` run is also a
success, the overread being defined under page-rounded grants. -/
theorem source_to_fault (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hge2 : 2 ≤ inp.in_argv.length)
    (regs5 : bvmap 5 word) (r grant : word)
    (hgrant : bv_unsigned (nN inp.in_argv) ≤ bv_unsigned grant)
    (htotalgrant : ((8 * ((nn inp.in_argv + 7) / 8) : Nat) : Int) ≤ bv_unsigned grant)
    (hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - stack_max_size)
    (hphysfree : region_free (segments_reserved source_segs) r grant = true)
    (hr0 : 0 < bv_unsigned r) (hmod : nn inp.in_argv % 8 ≠ 0)
    (h1 : reg_get regs5 1 = (0x110b0 : word))
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (h8 : reg_get regs5 8 = nN inp.in_argv) (h9 : reg_get regs5 9 = r)
    (h18 : reg_get regs5 18 = ptr inp.in_argv inp.in_envp rsp) :
    to_wallexit source_segs (Z_to_bv 64 1) (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0)
      (mkst (regupd regs5 10 (r + nN inp.in_argv)) 0x1121c
        (zmem (fmem2 inp rsp rrnd r) r grant) rrom) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hsms := stack_max_size_val
  have hun := u_nN inp.in_argv hva hge2
  have hnnz : nn inp.in_argv ≠ 0 := by
    intro hz
    apply hmod
    rw [hz]
  let chunks := (nn inp.in_argv + 7) / 8
  let total := 8 * chunks
  have hstop : 8 * (chunks - 1) < nn inp.in_argv ∧ nn inp.in_argv ≤ total := by
    dsimp only [chunks, total]
    omega
  have htotal : (total : Int) ≤ bv_unsigned grant := htotalgrant
  have hceil : bv_unsigned r + (nn inp.in_argv : Int) ≤
      bv_unsigned rsp - stack_max_size := by omega
  have htotalceil : bv_unsigned r + (total : Int) ≤
      bv_unsigned rsp - stack_max_size := by omega
  have hfree := region_free_prefix _ r _ _ hgrant hphysfree
  let mem0 := zmem (fmem2 inp rsp rrnd r) r grant
  let M := wbytes mem0 r (arg1 inp.in_argv)
  have hplo := ptr_lo inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  have hphi := ptr_hi inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2
  have hstr : rdn source_segs mem0 (ptr inp.in_argv inp.in_envp rsp)
      (nn inp.in_argv + 1) = some (arg1 inp.in_argv ++ [Z_to_bv 8 0]) := by
    unfold mem0
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (Or.inr (by omega))]
    rw [rdn_ext source_segs (nn inp.in_argv + 1) (fmem2 inp rsp rrnd r)
      (fmem inp rsp rrnd) _ (by omega) (by
        intro x hx
        exact fmem2_above inp rsp rrnd hsp_lo hsp_hi r x (by omega))]
    exact read_str_f inp rsp rrnd hva hve hsp_lo hsp_hi hge2
  have hbuf : rdn source_segs M r (nn inp.in_argv) = some (arg1 inp.in_argv) :=
    rdn_wbytes_hit _ _ _ _ (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)
  have hbyte (i : Nat) (hi : i < total) :
      rdn source_segs M (r + nat_to_word i) 1 =
        some [(arg1 inp.in_argv).getD i (Z_to_bv 8 0)] := by
    by_cases hin : i < nn inp.in_argv
    · exact rdn_nth _ _ _ _ _ _ hbuf hin
    · have hui : bv_unsigned (r + nat_to_word i) = bv_unsigned r + (i : Int) := by
        rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]
      unfold M
      rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega) (by omega)]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by change nn inp.in_argv ≤ i; omega), Option.getD_none]
      apply rdn_zmem_in1
      constructor <;> omega
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have h72 := u_Z2bv (bv_unsigned rsp - 72) (by omega) (by omega)
  have hspill : rdn source_segs mem0 (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 =
      some (word_to_le_bytes 8 (r + nN inp.in_argv)) := by
    unfold mem0
    rw [rdn_zmem_out _ _ _ _ _ _ (by rw [h72]; omega)
      (Or.inr (by rw [h72]; omega))]
    exact read_spill inp rsp rrnd hsp_lo hsp_hi r
  have next {ms ms' : machine_state}
      (hp : ms.ms_svc_pending = none)
      (he : step source_segs ms = MachineOk ms')
      (ht : to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms') :
      to_wallexit source_segs (Z_to_bv 64 1)
        (outbufs (arg1 inp.in_argv)) (Z_to_bv 64 0) ms :=
    msteps_to_wallexit _ _ _ _ _ _ (msteps.mst_step _ _ _ hp he (msteps.mst_refl _)) ht
  refine next rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110b0 : word)
    SF_1121c (by decide) SD_1121c (by cat_regs; exact h1)) ?_
  refine next rfl (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (r + nN inp.in_argv)) (r + nN inp.in_argv)
    SF_110b0 (by decide) SD_110b0 (by
      cat_regs; rw [h2]
      change rdn source_segs mem0
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 80)) + 8)) 8 = _
      rw [h80]
      rw [show bv_unsigned rsp - 80 + 8 = bv_unsigned rsp - 72 by omega]
      exact hspill)
    (bytes_le_to_Z_8 _)) ?_
  simp only [show bv_eqb (11 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110b4 (by decide) SD_110b4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _
    SF_110b8 (by decide) SD_110b8 (by cat_regs; exact c_eq_refl _)) ?_
  obtain ⟨regsC, hagC, _, h9C, h8C, _, hmsC⟩ :=
    source_copy inp.in_argv inp.in_envp rsp hva hve hsp_lo hsp_hi hge2 r mem0
      (store_grant_zmem_prefix _ _ _ _ _ hgrant (by omega)) hstr hfree hr0 hceil
      (nn inp.in_argv)
      (regupd (regupd (regupd regs5 10 (r + nN inp.in_argv))
        11 (r + nN inp.in_argv)) 15 (Z_to_bv 64 0)) (Nat.le_refl _)
      (by cat_regs; exact h18) (by cat_regs; exact h9) (by cat_regs; exact h8)
      (by cat_regs; rw [Nat.sub_self]; rfl)
  simp only [Nat.sub_self, List.take_zero, wbytes] at hmsC
  refine msteps_to_wallexit _ _ _ _ _ _ hmsC ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c0 (by decide) SD_110c0 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110c4 (by decide) SD_110c4 (by decide) (by cat_regs; rfl)) ?_
  refine next rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 8)
    SF_110c8 (by decide) SD_110c8 (by decide) (by cat_regs; rfl)) ?_
  obtain ⟨regsS, hagS, h14S, _, h15S, _, h8S, hmsS⟩ :=
    source_sum inp.in_argv rsp hva hge2 hsp_lo hsp_hi r M total hbyte hr0 htotalceil
      chunks 0 (regupd (regupd (regupd regsC 14 (Z_to_bv 64 0))
        15 (Z_to_bv 64 0)) 12 (Z_to_bv 64 8))
      (by simpa only [Nat.zero_add] using hstop.1) (by rw [Nat.zero_add])
      (by cat_regs; rfl) (by cat_regs; exact h9C) (by cat_regs; rfl)
      (by cat_regs) (by cat_regs; exact h8C)
  refine msteps_to_wallexit _ _ _ _ _ _ hmsS ?_
  refine next rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _
    SF_110cc (by decide) SD_110cc (by
      cat_regs; rw [h14S, h8S, c_ltu_ltb, u_ntw _ (by omega), hun, Nat.zero_add]
      simp only [decide_eq_false_iff_not]
      change ¬ (total : Int) < (nn inp.in_argv : Int)
      omega)) ?_
  have hframe (x : word) (hx : bv_unsigned rsp - 32 ≤ bv_unsigned x) :
      M x = fmem2 inp rsp rrnd r x := by
    unfold M
    rw [wbytes_above _ _ _ _ (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)]
    exact zmem_out _ _ _ _ (Or.inr (by omega))
  apply source_success inp rsp rrnd hva hge2 hsp_lo hsp_hi regsS M
  · rw [hagS 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    cat_regs
    rw [hagC 2 (by decide) (by decide) (by decide)]
    cat_regs; exact h2
  · rw [h15S, List.take_of_length_le (by change nn inp.in_argv ≤ 8 * (0 + chunks); omega)]
  · have hcases := source_free_cases r grant hphysfree (by omega)
    have hm : M (0x12000 : word) = fmem2 inp rsp rrnd r (0x12000 : word) := by
      unfold M
      rcases hcases with hc | hc
      · rw [wbytes_above _ _ _ _ (by
          change bv_unsigned r + (nn inp.in_argv : Int) ≤ (73728 : Int); omega)]
        exact zmem_out _ _ _ _ (Or.inr (by change _ ≤ (73728 : Int); omega))
      · rw [wbytes_below _ _ _ _ (by
          change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)
          (by change (73728 : Int) < _; omega)]
        exact zmem_out _ _ _ _ (Or.inl (by change (73728 : Int) < _; omega))
    rw [hm]
    exact fmem2_none inp rsp rrnd hsp_lo hsp_hi r _
      (by change (73728 : Int) < _; omega) (Or.inl (by decide))
  · rw [rdn_ext source_segs 8 M (fmem2 inp rsp rrnd r) _
      (by rw [u_Z2bv _ (by omega) (by omega)]; omega) (by
        intro x hx
        apply hframe
        rw [u_Z2bv _ (by omega) (by omega)] at hx
        omega)]
    exact read_slot_ra2 inp rsp rrnd hsp_lo hsp_hi r
  · intro a ha
    have hab : bv_unsigned rsp - 32 ≤ bv_unsigned a ∧
        bv_unsigned a ≤ bv_unsigned rsp - 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;>
        rw [u_Z2bv _ (by omega) (by omega)] <;> omega
    rw [rdn_ext source_segs 8 M (fmem2 inp rsp rrnd r) a
      (by omega) (by intro x hx; exact hframe x (by omega))]
    exact read_slot_02 inp rsp rrnd hsp_lo hsp_hi r a ha
  · have hg : mem_grows (oob_wmem inp rsp rrnd) (fmem2 inp rsp rrnd r) := by
      unfold fmem2 fmem emem
      repeat first
        | exact mem_grows_refl _
        | refine mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
    apply mem_grows_trans _ mem0 M ?_ (wbytes_grows _ _ _)
    intro x hx
    have hx' := hg x hx
    unfold mem0 zmem
    split
    · exact Option.some_ne_none _
    · exact hx'

/-- Retained but uncalled, as in Rocq. -/
theorem source_fault_step (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hva : valid_argv inp.in_argv) (hge2 : 2 ≤ inp.in_argv.length)
    (_hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (_hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (r grant : word)
    (hgrant : bv_unsigned (nN inp.in_argv) < bv_unsigned grant)
    (hrw : bv_unsigned r + bv_unsigned grant < 2 ^ 64) :
    rdn source_segs (wbytes (zmem (fmem2 inp rsp rrnd r) r grant) r (arg1 inp.in_argv))
      (r + nN inp.in_argv) 1 = some [Z_to_bv 8 0] := by
  have hn := u_nN inp.in_argv hva hge2
  have hrawnw : bv_unsigned r + bv_unsigned (nN inp.in_argv) < 2 ^ 64 := by
    omega
  have hadd := u_add_small r (nN inp.in_argv) hrawnw
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by change bv_unsigned r + (nn inp.in_argv : Int) ≤ _; omega)
    (by omega)]
  apply rdn_zmem_in1
  have hn0 : 0 ≤ (nn inp.in_argv : Int) := Int.natCast_nonneg _
  constructor <;> omega

/-- A failed second `brk` (the break did not move): exit 4. -/
theorem source_fail4 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs5 : bvmap 5 word) (r : word)
    (h1 : reg_get regs5 1 = (0x110b0 : word))
    (h2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (hne : bv_unsigned r ≠ bv_unsigned (r + nN inp.in_argv)) :
    to_wexit source_segs (mkst (regupd regs5 10 r) 0x1121c (fmem2 inp rsp rrnd r) rrom)
      [] (Z_to_bv 64 4) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have h80 := u_Z2bv (bv_unsigned rsp - 80) (by omega) (by omega)
  have h72 := u_Z2bv (bv_unsigned rsp - 72) (by omega) (by omega)
  have addr (k : Int) :
      v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) k =
        Z_to_bv 64 (bv_unsigned rsp - (80 - k)) := by
    unfold v_addi
    rw [h80]
    congr 1
    omega
  have saved (k : Int) (hk : 8 ≤ k ∧ k ≤ 32) :
      rdn source_segs (fmem2 inp rsp rrnd r)
        (Z_to_bv 64 (bv_unsigned rsp - k)) 8 =
      rdn source_segs (fmem inp rsp rrnd)
        (Z_to_bv 64 (bv_unsigned rsp - k)) 8 := by
    unfold fmem2
    apply rdn_wbytes_disjoint
    · rw [length_N_to_le_bytes, h72, u_Z2bv _ (by omega) (by omega)]
      omega
    · rw [u_Z2bv _ (by omega) (by omega)]
      omega
  have hra : rdn source_segs (fmem2 inp rsp rrnd r)
      (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111f4 : word)) := by
    rw [saved 8 (by omega)]
    exact read_slot_ra inp rsp rrnd hsp_lo hsp_hi
  have hslots (k : Int) (hk : k = 16 ∨ k = 24 ∨ k = 32) :
      rdn source_segs (fmem2 inp rsp rrnd r)
        (Z_to_bv 64 (bv_unsigned rsp - k)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
    rw [saved k (by omega)]
    apply read_slot_0 inp rsp rrnd hsp_lo hsp_hi
    rcases hk with rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, eq_self]
  cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110b0 : word)
    SF_1121c (by decide) SD_1121c (by cat_regs; exact h1))
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (r + nN inp.in_argv)) (r + nN inp.in_argv)
    SF_110b0 (by decide) SD_110b0
    (by
      cat_regs
      rw [h2, addr]
      exact rdn_wbytes_hit8 source_segs _ _ _ (by rw [h72]; omega))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (11 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    SF_110b4 (by decide) SD_110b4 (by decide) (by cat_regs; rfl))
  cat_step (step_bne_tk source_segs _ _ _ _ _ _ _ _
    SF_110b8 (by decide) SD_110b8 (by cat_regs; exact c_eq_neq _ _ (Ne.symm hne)))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 4)
    SF_11064 (by decide) SD_11064 (by decide) (by cat_regs; rfl))
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (0x111f4 : word)) (0x111f4 : word)
    SF_11068 (by decide) SD_11068
    (by cat_regs; rw [h2, addr]; exact hra) (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_1106c (by decide) SD_1106c
    (by cat_regs; rw [h2, addr]; exact hslots 16 (Or.inl rfl)) (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11070 (by decide) SD_11070
    (by cat_regs; rw [h2, addr]; exact hslots 24 (Or.inr (Or.inl rfl)))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (9 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_ld source_segs _ _ _ _ _ _ _ _
    (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    SF_11074 (by decide) SD_11074
    (by cat_regs; rw [h2, addr]; exact hslots 32 (Or.inr (Or.inr rfl)))
    (bytes_le_to_Z_8 _))
  simp only [show bv_eqb (18 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 80)) 80)
    SF_11078 (by decide) SD_11078 (by decide) (by cat_regs; rw [h2]; rfl))
  cat_step (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x111f4 : word)
    SF_1107c (by decide) SD_1107c (by cat_regs))
  cat_step (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
    SF_111f4 (by decide) SD_111f4 (by decide) (by cat_regs; rfl))
  cat_step (step_ecall source_segs _ _ _ _ _ SF_111f8 (by decide))
  apply tw_exit_coden
  · cat_regs; rfl
  · cat_regs
  · decide

/-! ### The outcome theorems -/

/-- The source's outcome set under the length cap. -/
theorem source_outcomes (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (rbrk rmb : word)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk)
    (hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max)
    (hge2 : 2 ≤ inp.in_argv.length)
    (hbrk_mod : bv_unsigned rbrk % page_size = 0)
    (hcap : (nn inp.in_argv : Int) ≤ 65536) :
    to_outcomes source_segs
      (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (oobU (nN inp.in_argv) (outbufs (arg1 inp.in_argv))) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hblo := rbrk_lo_num rbrk hbrk_lo
  have hbhi := rbrk_hi_num rbrk hbrk_hi
  have hsms := stack_max_size_val
  have hn := u_nN inp.in_argv hva hge2
  have hr0 : rbrk ≠ Z_to_bv 64 0 := by
    intro he
    have hu := congrArg bv_unsigned he
    change bv_unsigned rbrk = 0 at hu
    omega
  have hnw : bv_unsigned rbrk + (nn inp.in_argv : Int) < 2 ^ 64 := by omega
  have hurn : bv_unsigned (rbrk + nN inp.in_argv) =
      bv_unsigned rbrk + (nn inp.in_argv : Int) := by
    rw [u_add_small _ _ (by rw [hn]; exact hnw), hn]
  have hwant0 : rbrk + nN inp.in_argv ≠ Z_to_bv 64 0 := by
    intro he
    have hu := congrArg bv_unsigned he
    rw [hurn] at hu
    change bv_unsigned rbrk + (nn inp.in_argv : Int) = 0 at hu
    omega
  let model := init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp
  let ledger := VmMaps.mkVmMapsFull (segments_reserved source_segs) [] []
    rbrk rbrk source_alloc_limit rmb rsp
  have hquery : ∀ r, brk_resolution_ok model (Z_to_bv 64 0) r ↔ r = rbrk := by
    intro r
    change brk_r_ok ledger (Z_to_bv 64 0) r ↔ r = rbrk
    exact brk_r_ok_query_iff ledger r
  have hmodel : brk_model (Z_to_bv 64 0) rbrk model = model := by
    rw [brk_model_query rbrk model rfl]
    rfl
  have hfd : fd1chan model := init_model_fd1chan _ _ _ _ _ _
  obtain ⟨regs3, E1, E2, E8, E10, E17, E18, hms⟩ :=
    source_to_brk1 inp rsp rrnd hva hve hsp_lo hsp_hi hge2 hcap
  apply tou_msteps _ _ _ _ _ hms
  apply tou_brk_r (x8 := Z_to_bv 64 214)
    (T' := T1 (segments_reserved source_segs) source_alloc_limit
      (bv_unsigned rsp - stack_max_size) (nN inp.in_argv) (outbufs (arg1 inp.in_argv)))
    (Hsvc := rfl) (Hno := by decide)
  · intro r hok
    change brk_resolution_ok model (reg_get regs3 10) r at hok
    rw [E10] at hok
    have he := (hquery r).mp hok
    subst r
    change to_outcomes source_segs
      (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU rbrk []
        (Sys.Mm.Mmap.brk_zeros (reg_get regs3 10) rbrk rbrk) (Sys.Mm.Mmap.brk_unmaps rbrk rbrk) [] [])))
      (brk_model (reg_get regs3 10) rbrk model) _
    rw [E10, brk_zeros_query, brk_unmaps_keep, adv_brk, apply_zeros_nil, hmodel]
    obtain ⟨regs5, F1, F2, F8, F9, F10, F17, F18, hms2⟩ :=
      source_to_brk2 inp rsp rrnd hva hve hsp_lo hsp_hi hge2
        regs3 rbrk E1 E2 E8 E18 hr0 hnw
    apply tou_msteps _ _ _ _ _ hms2
    apply tou_brk_r (x8 := Z_to_bv 64 214)
      (T' := T2 (rbrk + nN inp.in_argv) (outbufs (arg1 inp.in_argv)))
      (Hsvc := rfl) (Hno := by decide)
    · intro r2 hok2
      change brk_r_ok ledger (reg_get regs5 10) r2 at hok2
      rw [F10] at hok2
      have hcases := (brk_r_ok_grow_iff _ _ _ _ _ _ _ _ _ _
        (by rw [hurn]; omega) (by rw [hurn]; omega) (by rw [hurn]; omega)).mp hok2
      change to_outcomes source_segs
        (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU r2 []
          (Sys.Mm.Mmap.brk_zeros (reg_get regs5 10) r2 rbrk) (Sys.Mm.Mmap.brk_unmaps r2 rbrk) [] [])))
        (brk_model (reg_get regs5 10) r2 model) _
      rw [F10]
      by_cases he : r2 = rbrk + nN inp.in_argv
      · subst r2
        rw [brk_unmaps_grow _ _ (by rw [hurn]; omega)]
        by_cases hz : nn inp.in_argv = 0
        · have hn0 : nN inp.in_argv = Z_to_bv 64 0 := by
            unfold nN
            rw [hz]
            rfl
          have hzs : Sys.Mm.Mmap.brk_zeros (rbrk + nN inp.in_argv)
              (rbrk + nN inp.in_argv) rbrk = [] := by
            rw [hn0, word_add_0_r, brk_zeros_keep]
          rw [hzs, adv_brk, apply_zeros_nil]
          apply tou_equiv (U := fun o => o = (outbufs (arg1 inp.in_argv), Z_to_bv 64 0))
          · apply tou_wexit_eq
            · exact fd1chan_brk_model _ _ _ hfd
            · exact source_run_empty inp rsp rrnd hva hve hsp_lo hsp_hi hge2
                hz regs5 rbrk hnw F1 F2 F8 F18
            · exact outbufs_modeled _
          · exact T2_succ_iff _ _
        · have hgrow := hcases.2
          rw [brk_grow_ok_aligned_grow ledger _ _ hwant0 (by change 0 < bv_unsigned rbrk; omega)
            (by change bv_unsigned rbrk < bv_unsigned (rbrk + nN inp.in_argv); rw [hurn]; omega)
            hbrk_mod] at hgrow
          simp only [ledger, List.append_nil, Bool.and_eq_true, decide_eq_true_eq] at hgrow
          obtain ⟨⟨hceil, hfree⟩, _⟩ := hgrow
          let grant := Z_to_bv 64
            (page_round_up_Z (bv_unsigned (rbrk + nN inp.in_argv)) - bv_unsigned rbrk)
          obtain ⟨hgu, hgrant, hphysceil, hrawceil, hrawfree, hgrantfree⟩ :=
            brk_aligned_grant_ok (segments_reserved source_segs) rbrk (nN inp.in_argv)
              grant (bv_unsigned rbrk + (nn inp.in_argv : Int))
              (bv_unsigned rsp - stack_max_size)
              (by rw [hurn, hn]) hurn rfl (by change _ + 4096 < _; omega) hceil hfree
          have htotal : ((8 * ((nn inp.in_argv + 7) / 8) : Nat) : Int) ≤ bv_unsigned grant := by
            rw [hgu, hurn]
            have hround := round8_le_page_grant (bv_unsigned rbrk)
              (nn inp.in_argv : Int) (by omega) (by omega) hbrk_mod
            omega
          rw [brk_zeros_aligned_grow _ _ _ hwant0 (by omega) (by rw [hurn]; omega)
            hbrk_mod, adv_brk, apply_zeros_one]
          apply tou_equiv (U := fun o => o = (outbufs (arg1 inp.in_argv), Z_to_bv 64 0))
          · apply tou_wexit_eq
            · exact fd1chan_brk_model _ _ _ hfd
            · exact source_run_success inp rsp rrnd hva hve hsp_lo hsp_hi hge2
                regs5 rbrk grant hgrant htotal hphysceil hgrantfree (by omega) hz
                F1 F2 F8 F9 F18
            · exact outbufs_modeled _
          · exact T2_succ_iff _ _
      · have hr2 : r2 = rbrk := hcases.1.resolve_left he
        subst r2
        rw [brk_zeros_keep, brk_unmaps_keep, adv_brk, apply_zeros_nil]
        apply tou_equiv (U := fun o => o = ([], Z_to_bv 64 4))
        · apply tou_wexit_eq
          · exact fd1chan_brk_model _ _ _ hfd
          · change to_wexit source_segs _ [] (Z_to_bv 64 4)
            apply source_fail4 inp rsp rrnd hsp_lo hsp_hi regs5 rbrk F1 F2
            intro hu
            exact he (bv_eq_of_unsigned _ _ hu)
          · intro b hb; cases hb
        · exact T2_fail_iff _ _ _ he
    · intro o
      change _ ↔ ∃ r2, brk_r_ok ledger (reg_get regs5 10) r2 ∧ _
      rw [F10]
      exact T1_iff_T2 _ _ rbrk rmb rsp _ _ rbrk hr0 (by omega) (by rw [hn]; exact hnw) o
  · intro o
    change _ ↔ ∃ r, brk_resolution_ok model (reg_get regs3 10) r ∧ _
    rw [E10]
    apply oobU_iff_T1 _ _ _ _ _ rbrk _ hquery
    refine ⟨hr0, ?_, ?_⟩
    · rw [hn]; exact hnw
    · by_cases hz : nn inp.in_argv = 0
      · left
        unfold nN
        rw [hz]
        rfl
      · right
        apply growable_aligned_grow _ _ _ _ _ hbrk_mod hbrk_lo
        · rw [hn]; omega
        · rw [hn]
          change _ + 4096 - 1 ≤ _
          omega
        · rw [hn]
          change _ ≤ (0x400000000 : Int)
          omega

/-- Retained but uncalled, as in Rocq: a compatibility spelling of
`source_outcomes` for non-multiples of eight. -/
theorem source_outcomes_mix (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (rbrk rmb : word)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk)
    (hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max)
    (hge2 : 2 ≤ inp.in_argv.length)
    (hbrk_mod : bv_unsigned rbrk % page_size = 0)
    (hcap : (nn inp.in_argv : Int) ≤ 65536) (_hmod : nn inp.in_argv % 8 ≠ 0) :
    to_outcomes source_segs
      (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (oobU (nN inp.in_argv) (outbufs (arg1 inp.in_argv))) :=
  source_outcomes inp rsp rrnd rbrk rmb hva hve hsp_lo hsp_hi hbrk_lo hbrk_hi hge2 hbrk_mod hcap

/-- Retained but uncalled, as in Rocq. -/
theorem source_escape (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (rbrk rmb : word)
    (hva : valid_argv inp.in_argv) (hve : valid_envp inp.in_envp)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk)
    (hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max)
    (hge2 : 2 ≤ inp.in_argv.length)
    (hbrk_mod : bv_unsigned rbrk % page_size = 0)
    (hcap : (nn inp.in_argv : Int) ≤ 65536) (_hmod : nn inp.in_argv % 8 ≠ 0) :
    to_outcomes source_segs
      (init_machine_state source_segs 0x111c8 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (oobU (nN inp.in_argv) (outbufs (arg1 inp.in_argv))) :=
  source_outcomes inp rsp rrnd rbrk rmb hva hve hsp_lo hsp_hi hbrk_lo hbrk_hi hge2 hbrk_mod hcap

end LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_source
