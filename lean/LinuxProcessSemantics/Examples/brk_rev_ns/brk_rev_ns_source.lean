import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs
import LinuxProcessSemantics.Examples.brk_rev_ns.SourceMemImage
import LinuxProcessSemantics.Examples.brk_rev_ns.TargetMemImage
import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_code
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.AllocSim2
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.MmapSim

/-! rocq-baseline: 3bd94f932fe0933df59ec88e6cc87819fee0d9d1 -/

/-! # brk-rev-ns source binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [SourceProof], generic over av/ev and the
    ASLR window sp):
    - [source_wexit_lt2]  : argc < 2            -> to_wexit [] 2
    - [source_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - [source_outcomes]   : argc >= 2, n <= 65536 ->
        to_outcomes (init) (init_model) (brkU (rev_buf argv[1])).

    Register invariants are [reg_get regs r = v] with sp-relative values
    in the canonical [Z_to_bv 64 (bv_unsigned rsp - k)] form, loop
    indices as [nat_to_word], counters/bounds in [Z].

    NOTE (compile flags): the reference sources are built with
    [-fno-builtin], so gcc 15 no longer recognizes the program's [slen]
    as the strlen idiom -- the binary keeps the hand-written byte-scan
    loop inline in main (0x1102c..0x11034 / 0x11090..0x11094) and musl's
    word-at-a-time [strlen] is gone from the image.  The walk is a plain
    per-byte induction ([source_scan]); no read ever goes past the
    terminating NUL. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_source

open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.Common
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.AllocSim2
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.Footprint
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap (brk_zeros brk_unmaps)
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.brk_rev_ns.SourceMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.TargetMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_code
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs

def rrom : word → Option byte := seg_rom source_segs

-- Open symbolic side conditions are closed without evaluating open bitvectors.
local macro "sc0" : tactic => `(tactic| first
  | rfl | (congr 1 <;> omega) | (apply bv_eq_of_unsigned; u_norm; omega))

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11134 := by
  rfl

theorem source_reserved_val :
    segments_reserved source_segs = [(0x10000, 0x1000), (0x11000, 0x1000), (0x12000, 0x1000), (0x13000, 0x1000)] := by
  decide

/-- Stores at/above the data segment's base are legal.  [-z separate-code]
    plus gcc 15's own [.eh_frame] LOAD give the image THREE read-only
    segments ([0x10000] headers/rodata, [0x11000] text, [0x12000]
    eh_frame) below the writable one at [0x13000]; the generic
    [range_avoids_ro_above] is keyed off that single bound, so the proof
    does not name the segments. -/
theorem source_avoids_stack : ∀ (a : word) (n : Int),
    0x13000 ≤ bv_unsigned a →
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true :=
  fun a n ha => range_avoids_ro_above source_segs 0x13000 (bv_unsigned a) n
    (by decide) ha

/-- The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every
    address in it (.bss is zero-filled in the .hex), so [wview] is
    defined there whatever the overlay holds — a store into .data/.bss
    needs no prior write.  That is the [store_ok] side condition
    machine stores now carry; stack targets go through the RLIMIT_STACK
    window ([solve_store_ok]) and heap targets through the grant's
    zero-fill ([store_ok_zmem]). -/
theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · rfl
  · decide
  · exact congrArg (fun x => [x]) SourceMemImage_seg_bytes_003_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    decide
  · decide

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : 0x13000 ≤ bv_unsigned a) (Hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true :=
  store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    (by decide) (by decide) (by decide) source_data_wseg Hlo Hhi


/-- The mirror image of [range_avoids_ro_above]: a range that ENDS at or
    below every read-only segment's base avoids them all. -/
theorem range_avoids_ro_below : ∀ (segs : List Segment) (top addr n : Int),
    segs.all (fun seg => seg_writable seg || decide (top ≤ (seg.seg_base : Int))) = true →
    addr + n ≤ top → range_avoids_ro_segs segs addr n = true :=
  fun segs top addr n habove hr => by
    simp only [range_avoids_ro_segs, List.all_eq_true]
    exact fun seg hin => by
      exact (fun (h : seg_writable seg = true ∨ top ≤ (seg.seg_base : Int)) => by
        simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        exact h.elim Or.inl (fun hbase => Or.inr (Or.inl (by omega))))
        ((Bool.or_eq_true_iff.mp ((List.all_eq_true.mp habove) seg hin)).elim
          Or.inl (fun h => Or.inr (of_decide_eq_true h)))

/-- A region [b, b+l) free against the page-rounded reservations avoids
    the read-only segments everywhere inside it: freedom against all FOUR
    page reservations forces the region entirely below 0x10000 or at/above
    0x14000. -/
theorem source_free_avoids : ∀ (b l : word),
    region_free (segments_reserved source_segs) b l = true →
    0 < bv_unsigned l → ∀ (a : word) (k : Int),
    bv_unsigned b ≤ bv_unsigned a →
    bv_unsigned a + k ≤ bv_unsigned b + bv_unsigned l →
    range_avoids_ro_segs source_segs (bv_unsigned a) k = true :=
  fun b l hfree hl a k hlo hhi => by
    rw [source_reserved_val] at hfree
    simp only [region_free, iv_overlap, Bool.and_true, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hfree
    exact (fun (h : (¬ bv_unsigned b < 0x10000 + 0x1000 ∨
          ¬ 0x10000 < bv_unsigned b + bv_unsigned l) ∧
        (¬ bv_unsigned b < 0x11000 + 0x1000 ∨
          ¬ 0x11000 < bv_unsigned b + bv_unsigned l) ∧
        (¬ bv_unsigned b < 0x12000 + 0x1000 ∨
          ¬ 0x12000 < bv_unsigned b + bv_unsigned l) ∧
        (¬ bv_unsigned b < 0x13000 + 0x1000 ∨
          ¬ 0x13000 < bv_unsigned b + bv_unsigned l)) => by
      exact (show bv_unsigned b + bv_unsigned l ≤ 0x10000 ∨
          0x14000 ≤ bv_unsigned b from by omega).elim
        (fun hbelow => range_avoids_ro_below source_segs 0x10000
          (bv_unsigned a) k (by decide) (by omega))
        (fun habove => source_avoids_stack a k (by omega))) hfree

section SourceProof

variable (inp : ProcInput)
variable (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (rsp : word)

/-! The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the bytes of the entry stack's
    last page above the block.  This proof may assume NOTHING about
    either, exactly as it may assume nothing about where the stack
    landed.  Quantified per binary, so the target's draw below is a
    different variable. -/
variable (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo

include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

/-! The quantified initial program break ([Run.valid_brk] window, like the
    SP above).  Its page alignment exposes the kernel's physical [brk]
    grant while the binary continues to use only its logical byte prefix. -/
variable (rbrk rmb : word)
variable (Hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk)
variable (Hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max)

theorem rtop_src_val : reserved_top (segments_reserved source_segs) = 0x14000 := by
  rw [source_reserved_val]
  rfl

include Hbrk_lo in
theorem rbrk_lo_num : 0x14000 ≤ bv_unsigned rbrk := by
  rw [← rtop_src_val]
  exact Hbrk_lo

include Hbrk_hi in
theorem rbrk_hi_num : bv_unsigned rbrk ≤ 0x14000 + 1073741824 := by
  rw [← rtop_src_val, ← brk_aslr_max_val]
  exact Hbrk_hi

include Hbrk_hi in
theorem rbrk_lt64 : bv_unsigned rbrk < 2 ^ 64 := by
  exact (fun h => by omega) (rbrk_hi_num rbrk Hbrk_hi)

include Hva Hve Hsp_hi in
/-- No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' new side conditions). -/
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap rrnd).length : Int) < 2 ^ 64 := by
  exact (fun hb hs => by omega)
    (bsb_bound source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve)
    (rsp_hi_num rsp Hsp_hi)

/-- environ pointer _start stores at 0x13000. -/
def envp_val : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (inp.in_argv.length : Int) + 8)

theorem envp_val_eq (inp : ProcInput) (Hva : valid_argv inp.in_argv) (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (ArgvEnv.argcN inp.in_argv) 3)) 8 =
      envp_val inp rsp := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hlen := valid_argv_len inp.in_argv Hva
  have Hs : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + 8)) = bv_unsigned rsp + 8 :=
    u_Z2bv _ (by omega) (by omega)
  have Ht : bv_unsigned (v_slli (ArgvEnv.argcN inp.in_argv) 3) = 8 * (inp.in_argv.length : Int) := by
    rw [v_slli_3 _ (by rw [ArgvEnv.u_argcN inp.in_argv Hva]; omega), ArgvEnv.u_argcN inp.in_argv Hva]
  apply bv_eq_of_unsigned
  unfold envp_val v_addi
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned,
    v_add_small _ _ (by rw [Hs, Ht]; omega), Hs, Ht]

/-- The executor's spelling of the same value: the log denotes the
    [slli]/[add]/[addi] chain with [alu64] and the REGISTER shift
    [v_sll _ (Z_to_bv 64 3)], not the [v_add]/[v_slli] of [envp_val_eq]. -/
theorem envp_val_sym (inp : ProcInput) (Hva : valid_argv inp.in_argv) (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (ArgvEnv.argcN inp.in_argv) (Z_to_bv 64 3))) + 8) = envp_val inp rsp := by
  rw [alu_add]
  exact envp_val_eq inp Hva rsp Hsp_lo Hsp_hi

/-- Memory after _start's environ store. -/
def emem : word → Option byte :=
  wbytes (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) (0x13000 : word) (word_to_le_bytes 8 (envp_val inp rsp))

/-- main()'s 64-byte frame (stores in execution order; sp = rsp - 64):
    s1@+40, ra@+56 (= 0x11160), s0@+48, s2@+32, s3@+24, s4@+16.  gcc 15
    keeps six callee-saves live across the inline scan loop, and uses +8
    (rsp-56) as a SCRATCH spill slot for the running pointer; +0 is never
    touched.  All stored callee-saves are 0 in the initial register file. -/
def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x11160 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))

theorem grows_fmem : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) (fmem inp rsp rrnd) :=
  mem_grows_trans _ _ _
    (mem_grows_trans _ _ _
      (mem_grows_trans _ _ _
        (mem_grows_trans _ _ _
          (mem_grows_trans _ _ _
            (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))
            (wbytes_grows _ _ _)) (wbytes_grows _ _ _)) (wbytes_grows _ _ _))
      (wbytes_grows _ _ _)) (wbytes_grows _ _ _)

theorem rdn_emem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (emem inp rsp rrnd) a n = rdn source_segs (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold emem
  rw [rdn_wbytes_disjoint]
  · rw [length_N_to_le_bytes]; imm_norm; omega
  · exact Hn

theorem rdn_fmem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (fmem inp rsp rrnd) a n = rdn source_segs (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]
  exact rdn_emem_above inp rsp rrnd Hsp_lo Hsp_hi a n Ha Hn

def arg1 : List byte := inp.in_argv.getD 1 []

def nn : Nat := (arg1 inp).length

def nN : word := nat_to_word (nn inp)

def ptr : word := cat_argv_ptr rsp inp.in_argv inp.in_envp 1

theorem read_slot_ra (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11160 : word)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

theorem read_slot_0 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (Ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)]) :
    rdn source_segs (fmem inp rsp rrnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
  rcases Ha with rfl | rfl | rfl | rfl | rfl
  all_goals repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

/-- From main's epilogue with ANY memory whose frame slots read back
    the initial values: exit with code = a0, no output. -/
theorem source_epilogue (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H10 : reg_get regs 10 = code) (Hc : bv_unsigned code < 256)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11160 : word)))
    (Hsl : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    to_wexit source_segs (mkst regs 0x11070 mem rrom) [] code := by
  -- The same six reloads, stack pop, return and li a7,93 as the Rocq block,
  -- expanded into steps using the generated fetch and decode proofs.
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  stepld SF_11070 SD_11070 (Z_to_bv 64 (bv_unsigned rsp - 8))
    (0x11160 : word) (exact Hra)
  stepld SF_11074 SD_11074 (Z_to_bv 64 (bv_unsigned rsp - 16))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inl True.intro))
  stepld SF_11078 SD_11078 (Z_to_bv 64 (bv_unsigned rsp - 24))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inl True.intro)))
  stepld SF_1107c SD_1107c (Z_to_bv 64 (bv_unsigned rsp - 32))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inl True.intro))))
  stepld SF_11080 SD_11080 (Z_to_bv 64 (bv_unsigned rsp - 40))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))
  stepld SF_11084 SD_11084 (Z_to_bv 64 (bv_unsigned rsp - 48))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inr (Or.inr True.intro)))))
  stepiv SF_11088 SD_11088 rsp
    (getr_resolve; regupd_resolve; rw [H2]; sp_norm; apply bv_eq_of_unsigned; u_norm; omega)
  stepjr SF_1108c SD_1108c (0x11160 : word) (getr_resolve; regupd_resolve; rfl)
  stepiv SF_11160 SD_11160 (Z_to_bv 64 93) (getr_resolve; bveq)
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ SF_11164 rfl
  apply tw_exit_coden
  · getr_resolve; regupd_resolve; decide +kernel
  · regupd_resolve; exact H10
  · exact Hc

include Hva Hve Hsp_lo Hsp_hi in
/-- argc < 2: no output, exit 2. -/
theorem source_wexit_lt2 (Hlt2 : inp.in_argv.length < 2) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  rw [init_mkst]
  norm_pc
  change to_wexit source_segs (mkst _ _ (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) rrom) _ _
  sym_block source_segs 20 [true] []
    [((2 : reg), EVar 32)] [rsp] [ArgvEnv.argcN inp.in_argv] R HR
  · have Hu := ArgvEnv.u_argcN inp.in_argv Hva
    refine ⟨?_, ⟨by omega, by omega, by omega⟩, ?_,
      ⟨by omega, by omega, by omega⟩, ?_⟩
    · sym_br
    · unfold ArgvEnv.wmem; apply source_store_ok <;> (u_norm; omega)
    · rw [Int.add_zero, show Z_to_bv 64 (bv_unsigned rsp) = rsp from v_addi_0 rsp]
      exact ⟨word_le8 (ArgvEnv.argcN inp.in_argv), ArgvEnv.read_argc_w source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_hi,
        bytes_le_n_to_le_8 _⟩
  · getr_resolve; rfl
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ SF_11164 rfl
  apply tw_exit_coden
  · sym_regs HR; decide +kernel
  · sym_regs HR; sym_close
  · decide

section Ge2Main

variable (Hge2 : 2 ≤ inp.in_argv.length)

include Hva Hge2 in
theorem nN_le : (nn inp : Int) ≤ 131071 :=
  valid_argv_str_len inp.in_argv 1 Hva (by omega)

include Hva Hge2 in
/-- The one buffer this program ever writes -- argv[1] reversed plus a
    newline -- is short enough for the model to transfer in one [write]:
    [valid_argv] caps a single argv string at 131071 bytes, and
    131071 + 1 = [rw_bytes_max]. -/
theorem bufs_modeled_out : bufs_modeled [rev_buf (arg1 inp)] := by
  exact bufs_modeled_single _ (by
    simp only [buf_modeled, length_rev_buf, Int.natCast_succ]
    exact (fun (h : ((arg1 inp).length : Int) ≤ 131071) => by
      exact (show ((arg1 inp).length : Int) + 1 ≤ 131072 from by omega))
      (nN_le inp Hva Hge2))

include Hva Hge2 in
theorem u_nN : bv_unsigned (nN inp) = (nn inp : Int) :=
  u_ntw (nn inp) (by exact (fun h => by omega) (nN_le inp Hva Hge2))

include Hva Hge2 in
theorem u_nN1 : bv_unsigned (nN inp + 1) = (nn inp : Int) + 1 := by
  exact (fun (h1 : bv_unsigned (1 : word) = 1) => by
    rw [u_add_small (nN inp) 1 (by
      rw [u_nN inp Hva Hge2, h1]
      exact (fun h => by omega) (nN_le inp Hva Hge2)), u_nN inp Hva Hge2, h1]) rfl

include Hva Hge2 in
theorem arg1_nz : ¬ (Z_to_bv 8 0) ∈ arg1 inp :=
  valid_argv_str_nz inp.in_argv 1 Hva (by omega)

include Hva Hve Hsp_hi Hge2 in
theorem ptr_bounds :
    bv_unsigned rsp ≤ bv_unsigned (ptr inp rsp) ∧
    bv_unsigned (ptr inp rsp) + (nn inp : Int) + 1 < 2 ^ 64 :=
  argv_ptr_bounds rsp inp.in_argv inp.in_envp 1 Hva Hve (by omega)
    (by simp only [argv_layout_slack]; exact (fun h => by omega) (rsp_hi_num rsp Hsp_hi))

include Hva Hve Hsp_hi Hge2 in
theorem ptr_lo : bv_unsigned rsp ≤ bv_unsigned (ptr inp rsp) :=
  (ptr_bounds inp Hva Hve rsp Hsp_hi Hge2).1

include Hva Hve Hsp_hi Hge2 in
theorem ptr_hi : bv_unsigned (ptr inp rsp) + (nn inp : Int) + 1 < 2 ^ 64 :=
  (ptr_bounds inp Hva Hve rsp Hsp_hi Hge2).2

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- argv[1] pointer slot at rsp + 16 (in the post-store memory). -/
theorem read_ptr1_f :
    rdn source_segs (fmem inp rsp rrnd) (rsp + nat_to_word (8 + 8 * 1)) 8 =
      some (word_le8 (ptr inp rsp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [ArgvEnv.rdn_wmem_stack source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1
    inp.in_uid inp.in_hwcap rrnd (by omega) (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- The whole NUL-terminated string at ptr. -/
theorem read_str_f :
    rdn source_segs (fmem inp rsp rrnd) (ptr inp rsp) (Nat.succ (nn inp)) =
      some (arg1 inp ++ [Z_to_bv 8 0]) := by
  have ⟨Hlo, Hhi⟩ := ptr_bounds inp Hva Hve rsp Hsp_hi Hge2
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ Hlo (by omega)]
  rw [ArgvEnv.rdn_wmem_stack source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd _ _ Hlo (by omega)]
  apply rdn_app (n1 := nn inp) (n2 := 1)
  · exact read_argv_str_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1
      inp.in_uid inp.in_hwcap rrnd (by omega) (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
  · have Hb := read_argv_byte_k source_phdrs source_segs rsp inp.in_argv inp.in_envp
      1 (nn inp) inp.in_uid inp.in_hwcap rrnd (by omega) (Nat.le_refl _)
      (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
    change rdn source_segs _ _ 1 = some [byte_at (arg1 inp) (nn inp)] at Hb
    rw [show byte_at (arg1 inp) (nn inp) = Z_to_bv 8 0 from byte_at_len (arg1 inp)] at Hb
    exact Hb

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- Every byte of the string, including the terminating NUL. -/
theorem read_byte_f (j : Nat) (Hj : j ≤ nn inp) :
    rdn source_segs (fmem inp rsp rrnd) (ptr inp rsp + nat_to_word j) 1 =
      some [byte_at (arg1 inp) j] := by
  have ⟨Hlo, Hhi⟩ := ptr_bounds inp Hva Hve rsp Hsp_hi Hge2
  have Hnn := nN_le inp Hva Hge2
  have Hptr := u64_range (ptr inp rsp)
  have Hu : bv_unsigned (ptr inp rsp + nat_to_word j) = bv_unsigned (ptr inp rsp) + (j : Int) := by
    rw [word_add_nat]; u_norm; rfl
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by rw [Hu]; omega) (by rw [Hu]; omega)]
  rw [ArgvEnv.rdn_wmem_stack source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd _ _ (by rw [Hu]; omega) (by rw [Hu]; omega)]
  exact read_argv_byte_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1 j
    inp.in_uid inp.in_hwcap rrnd (by omega) Hj (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)



include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- The scan loop gcc 15 emits for the program's own [slen] under
    [-fno-builtin]:

      0x1102c  add  s2,s4,s1        s2 := ptr + i
      0x11030  lbu  a5,0(s2)
      0x11034  bnez a5,0x11090  ->  0x11090 addi s1,s1,1 ; 0x11094 j 0x1102c

    The index lives in s1 and the string base in s4, so falling through
    the [bnez] lands at 0x11038 with s1 = n and s2 = ptr + n. -/
theorem source_scan (d i : Nat) (regs : bvmap 5 word)
    (Hid : i + d = nn inp) (H9 : reg_get regs 9 = nat_to_word i)
    (H20 : reg_get regs 20 = ptr inp rsp) :
    ∃ regs', (∀ r : reg, r ≠ 9 → r ≠ 15 → r ≠ 18 →
      reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 9 = nN inp ∧ reg_get regs' 18 = ptr inp rsp + nN inp ∧
      msteps source_segs (mkst regs 0x1102c (fmem inp rsp rrnd) rrom)
        (mkst regs' 0x11038 (fmem inp rsp rrnd) rrom) := by
  have Hnz := arg1_nz inp Hva Hge2
  induction d generalizing i regs with
  | zero =>
    have Hi : i = nn inp := by omega
    let regs1 := regupd regs 18 (ptr inp rsp + nat_to_word i)
    let regs2 := regupd regs1 15 (Z_to_bv 64 0)
    refine ⟨regs2, ?_, ?_, ?_, ?_⟩
    · intro r Hr9 Hr15 Hr18
      dsimp only [regs2, regs1]
      rw [regupd_other _ _ _ _ Hr15, regupd_other _ _ _ _ Hr18]
    · dsimp only [regs2, regs1]; regupd_resolve; rw [H9, Hi]; rfl
    · dsimp only [regs2, regs1]; regupd_resolve; rw [Hi]; rfl
    · stepiv SF_1102c SD_1102c (ptr inp rsp + nat_to_word i)
        (getr_resolve; rw [H20, H9]; exact alu_add _ _)
      chain_step
      · rfl
      · apply step_lbu (b := Z_to_bv 8 0) (hfetch := SF_11030)
          (hecall := rfl) (hdecode := SD_11030)
        getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
        have Hb := read_byte_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 i (by omega)
        rw [Hi, show byte_at (arg1 inp) (nn inp) = Z_to_bv 8 0 from byte_at_len _] at Hb
        rw [Hi]; exact Hb
      step_simpl
      chain_step
      · rfl
      · apply step_bne_ft (hf := SF_11034) (he := rfl) (hd := SD_11034)
        getr_resolve; regupd_resolve; exact c_eq_0_true
      norm_pc
      exact msteps.mst_refl _
  | succ d IH =>
    have Hilt : i < nn inp := by omega
    let b := byte_at (arg1 inp) i
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hnz Hilt
    let regs1 := regupd regs 18 (ptr inp rsp + nat_to_word i)
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 9 (nat_to_word (Nat.succ i))
    have Hms : msteps source_segs (mkst regs 0x1102c (fmem inp rsp rrnd) rrom)
        (mkst regs3 0x1102c (fmem inp rsp rrnd) rrom) := by
      stepiv SF_1102c SD_1102c (ptr inp rsp + nat_to_word i)
        (getr_resolve; rw [H20, H9]; exact alu_add _ _)
      chain_step
      · rfl
      · apply step_lbu (b := b) (hfetch := SF_11030) (hecall := rfl) (hdecode := SD_11030)
        getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
        exact read_byte_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 i (by omega)
      step_simpl
      chain_step
      · rfl
      · apply step_bne_tk (hf := SF_11034) (he := rfl) (hd := SD_11034)
        getr_resolve; regupd_resolve
        apply c_eq_0_false; rw [u_zext8]; exact byte_nz_u _ Hbnz
      norm_pc
      stepiv SF_11090 SD_11090 (nat_to_word (Nat.succ i))
        (getr_resolve; regupd_resolve; rw [H9]; imm_norm; exact nat_to_word_S i)
      stepj SF_11094 SD_11094
      exact msteps.mst_refl _
    obtain ⟨regs', Hag, H9f, H18f, Hms'⟩ := IH (Nat.succ i) regs3 (by omega)
      (by dsimp only [regs3]; exact regupd_same _ _ _)
      (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact H20)
    refine ⟨regs', ?_, H9f, H18f, msteps_trans _ _ _ _ Hms Hms'⟩
    intro r Hr9 Hr15 Hr18
    rw [Hag r Hr9 Hr15 Hr18]
    dsimp only [regs3, regs2, regs1]
    rw [regupd_other _ _ _ _ Hr9, regupd_other _ _ _ _ Hr15,
      regupd_other _ _ _ _ Hr18]

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- From the entry point to the scan loop's head, with main's frame
    pushed, s1 = 0 and s4 = argv[1]. -/
theorem source_to_loop :
    ∃ regsA, msteps source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (mkst regsA 0x1102c (fmem inp rsp rrnd) rrom) ∧
      reg_get regsA 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
      reg_get regsA 9 = nat_to_word 0 ∧ reg_get regsA 20 = ptr inp rsp := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 0x11134) (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) rrom)
    22 [false] [] [((2 : reg), EVar 32)] [rsp] [ArgvEnv.argcN inp.in_argv, ptr inp rsp] R HR Hms
  · have Hu := ArgvEnv.u_argcN inp.in_argv Hva
    repeat' apply And.intro
    all_goals first
      | omega
      | (unfold ArgvEnv.wmem; solve_store_ok)
      | (unfold ArgvEnv.wmem; apply source_store_ok <;> (u_norm; omega))
      | sym_br
      | (rw [show Z_to_bv 64 (bv_unsigned rsp + 16) = rsp + nat_to_word (8 + 8 * 1) from by
            rw [word_add_nat]; rfl]
         refine ⟨word_le8 (ptr inp rsp), ?_, bytes_le_n_to_le_8 _⟩
         rw [ArgvEnv.rdn_wmem_stack source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd _ _ (by rw [word_add_nat]; u_norm; omega)
           (by rw [word_add_nat]; u_norm; omega)]
         exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ (by omega)
           (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi))
      | (rw [Int.add_zero, show Z_to_bv 64 (bv_unsigned rsp) = rsp from v_addi_0 rsp]
         exact ⟨word_le8 (ArgvEnv.argcN inp.in_argv), ArgvEnv.read_argc_w source_segs source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_hi,
           bytes_le_n_to_le_8 _⟩)
  · getr_resolve; rfl
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · rw [init_mkst]
    norm_pc
    sym_chain Hms
    unfold fmem emem
    sym_mem_norm
    getr_resolve
    regupd_resolve
    rw [show Z_to_bv 64 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (ArgvEnv.argcN inp.in_argv) (Z_to_bv 64 3))) + 8) = envp_val inp rsp from
      envp_val_eq inp Hva rsp Hsp_lo Hsp_hi]
    exact msteps.mst_refl _
  · sym_regs HR; sc0
  · sym_regs HR <;> rfl
  · sym_regs HR

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- From the entry point to 0x11038 with s1 = n, s2 = ptr + n and
    s4 = argv[1]. -/
theorem source_to_len :
    ∃ regs1, msteps source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (mkst regs1 0x11038 (fmem inp rsp rrnd) rrom) ∧
      reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
      reg_get regs1 9 = nN inp ∧ reg_get regs1 18 = ptr inp rsp + nN inp ∧
      reg_get regs1 20 = ptr inp rsp := by
  obtain ⟨regsA, HmsA, H2, H9, H20⟩ := source_to_loop inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  obtain ⟨regsB, HagB, H9B, H18B, HmsB⟩ :=
    source_scan inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 (nn inp) 0 regsA (by omega) H9 H20
  refine ⟨regsB, msteps_trans _ _ _ _ HmsA HmsB, ?_, H9B, H18B, ?_⟩
  · rw [HagB 2 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H2
  · rw [HagB 20 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H20

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- n > 65536: no output, exit 3. -/
theorem source_wexit_cap (Hcap : 65536 < (nn inp : Int)) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 3) := by
  have HnnLe := nN_le inp Hva Hge2
  obtain ⟨regs1, Hms1, H2, H9, H18, H20⟩ :=
    source_to_len inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  apply msteps_to_wexit _ _ _ _ _ Hms1
  sym_block source_segs 3 [true] []
    [((2 : reg), EVar 32), ((9 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 64), nN inp] [] R HR
  · have Hu := u_nN inp Hva Hge2
    sym_br
  · exact H2
  · exact H9
  apply source_epilogue rsp Hsp_lo Hsp_hi
  · sym_regs HR
  · sym_regs HR <;> rfl
  · decide
  · exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
  · exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi

include Hsp_lo Hsp_hi in
theorem source_exit4 (regs : bvmap 5 word) (mem : word → Option byte)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11160 : word)))
    (Hsl : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    to_wexit source_segs (mkst regs 0x1106c mem rrom) [] (Z_to_bv 64 4) := by
  stepiv SF_1106c SD_1106c (Z_to_bv 64 4) (getr_resolve; bveq)
  apply source_epilogue rsp Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide
  · exact Hra
  · exact Hsl

include Hsp_lo Hsp_hi in
/-- The scratch spill slot at rsp-56 does not disturb the frame slots. -/
theorem spill_ra (v : word) :
    rdn source_segs
      (wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 v))
      (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 = some (word_to_le_bytes 8 (0x11160 : word)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
  exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi

include Hsp_lo Hsp_hi in
theorem spill_0 (v a : word)
    (Ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16), Z_to_bv 64 (bv_unsigned rsp - 24),
      Z_to_bv 64 (bv_unsigned rsp - 32), Z_to_bv 64 (bv_unsigned rsp - 40),
      Z_to_bv 64 (bv_unsigned rsp - 48)]) :
    rdn source_segs
      (wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 v))
      a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
      bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
    rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
  exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi a Ha

include Hva Hve Hsp_lo Hsp_hi Hge2 in
-- [store_grant_ok]: the loop's [sb]s are machine stores into the brk
-- grant, and [mem0] is abstract here, so the writability of the grant
-- has to come in as a hypothesis.
theorem source_copy (r : word) (mem0 : word → Option byte)
    (Hgok : store_grant_ok source_segs mem0 r (nN inp + 1))
    (Hstr : rdn source_segs mem0 (ptr inp rsp) (Nat.succ (nn inp)) =
      some (arg1 inp ++ [Z_to_bv 8 0]))
    (_Hfree : region_free (segments_reserved source_segs) r (nN inp + 1) = true)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + (nn inp : Int) + 1 ≤ bv_unsigned rsp - stack_max_size)
    (d : Nat) (regs : bvmap 5 word) (Hd : d ≤ nn inp)
    (Hr20 : reg_get regs 20 = ptr inp rsp)
    (Hr15 : reg_get regs 15 = ptr inp rsp + nat_to_word d)
    (Hr8 : reg_get regs 8 = r + nat_to_word (nn inp - d)) :
    ∃ regs', (∀ x : reg, x ≠ 15 → x ≠ 8 → x ≠ 14 →
      reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 15 = ptr inp rsp ∧ reg_get regs' 8 = r + nN inp ∧
      msteps source_segs
        (mkst regs 0x110d4 (wbytes mem0 r ((arg1 inp).reverse.take (nn inp - d))) rrom)
        (mkst regs' 0x110d4 (wbytes mem0 r (arg1 inp).reverse) rrom) := by
  have Hplo := ptr_lo inp Hva Hve rsp Hsp_hi Hge2
  have Hphi := ptr_hi inp Hva Hve rsp Hsp_hi Hge2
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HnnLe := nN_le inp Hva Hge2
  have Hur := u64_range r
  have HnnA : (arg1 inp).length = nn inp := rfl
  have Hsms := stack_max_size_val
  induction d generalizing regs with
  | zero =>
    refine ⟨regs, ?_, ?_, ?_, ?_⟩
    · intro x _ _ _; rfl
    · rw [Hr15, word_add_0]
    · rw [Hr8, Nat.sub_zero]; rfl
    · rw [Nat.sub_zero, show (arg1 inp).reverse.take (nn inp) = (arg1 inp).reverse from firstn_all_rev _]
      exact msteps.mst_refl _
  | succ d IH =>
    let memI := wbytes mem0 r ((arg1 inp).reverse.take (nn inp - Nat.succ d))
    let b := byte_at (arg1 inp) d
    have HlenF : ((arg1 inp).reverse.take (nn inp - Nat.succ d)).length =
        nn inp - Nat.succ d := by
      rw [List.length_take, List.length_reverse, Nat.min_eq_left (by omega)]
    have HuSd : bv_unsigned (ptr inp rsp + nat_to_word (Nat.succ d)) =
        bv_unsigned (ptr inp rsp) + (Nat.succ d : Int) := by
      rw [word_add_nat]; u_norm; rfl
    have Hud : bv_unsigned (ptr inp rsp + nat_to_word d) =
        bv_unsigned (ptr inp rsp) + (d : Int) := by
      rw [word_add_nat]; u_norm; rfl
    have HuW : bv_unsigned (r + nat_to_word (nn inp - Nat.succ d)) =
        bv_unsigned r + (nn inp - Nat.succ d : Nat) := by
      rw [word_add_nat]; u_norm; rfl
    let regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))
    let regs2 := regupd regs1 8 (r + nat_to_word (nn inp - d))
    let regs3 := regupd regs2 15 (ptr inp rsp + nat_to_word d)
    let memI' := wbytes mem0 r ((arg1 inp).reverse.take (nn inp - d))
    have Ew : wbytes memI (r + nat_to_word (nn inp - Nat.succ d)) [b] = memI' := by
      unfold memI' memI
      rw [show nn inp - d = Nat.succ (nn inp - Nat.succ d) by omega,
        firstn_rev_snoc _ _ (by omega), wbytes_app, HlenF]
      rw [show (arg1 inp).length - Nat.succ (nn inp - Nat.succ d) = d by omega]
      dsimp only [b]
      rw [nth_lt_byte_at (arg1 inp) d (by omega)]
    have Hms : msteps source_segs (mkst regs 0x110d4 memI rrom)
        (mkst regs3 0x110d4 memI' rrom) := by
      chain_step
      · rfl
      · apply step_bne_tk (hf := SF_110d4) (he := rfl) (hd := SD_110d4)
        getr_resolve; rw [Hr20, Hr15]
        apply c_eq_neq; rw [HuSd]; omega
      norm_pc
      chain_step
      · rfl
      · apply step_lbu (b := b) (hfetch := SF_11110) (hecall := rfl) (hdecode := SD_11110)
        getr_resolve; rw [Hr15]; imm_norm; rw [LinuxProcessSemantics.Common.StepTac.word_add_nat_m1]
        unfold memI
        rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [HlenF, Hud]; omega) (by rw [Hud]; omega)]
        exact rdn_nth _ _ _ _ _ d Hstr (by omega)
      step_simpl
      stepiv SF_11114 SD_11114 (r + nat_to_word (nn inp - d))
        (getr_resolve; regupd_resolve; rw [Hr8]; imm_norm;
         rw [LinuxProcessSemantics.Common.StepTac.word_add_nat_1]; exact congrArg (fun k => r + nat_to_word k) (by omega))
      stepiv SF_11118 SD_11118 (ptr inp rsp + nat_to_word d)
        (getr_resolve; regupd_resolve; rw [Hr15]; imm_norm; exact LinuxProcessSemantics.Common.StepTac.word_add_nat_m1 _ _)
      chain_step
      · rfl
      · apply LinuxProcessSemantics.Common.MmapSim.step_sb_at (Hv := rfl)
          (a := r + nat_to_word (nn inp - Nat.succ d)) (b := b)
          (Hf := SF_1111c) (He := rfl) (Hd := SD_1111c)
        · getr_resolve; regupd_resolve; imm_norm
          rw [show nn inp - d = Nat.succ (nn inp - Nat.succ d) by omega]
          exact LinuxProcessSemantics.Common.StepTac.word_add_nat_m1 _ _
        · getr_resolve; regupd_resolve; exact zext8_byte b
        · store_ok_peel
          apply Hgok
          all_goals simp only [u_nN1 inp Hva Hge2, HuW] <;> omega
      step_simpl
      rw [Ew]
      stepj SF_11120 SD_11120
      exact msteps.mst_refl _
    obtain ⟨regs', Hag, H15, H8, Hms'⟩ := IH regs3 (by omega)
      (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr20)
      (by dsimp only [regs3]; exact regupd_same _ _ _)
      (by dsimp only [regs3, regs2]; regupd_resolve; rfl)
    refine ⟨regs', ?_, H15, H8, msteps_trans _ _ _ _ Hms Hms'⟩
    intro x H15' H8' H14
    rw [Hag x H15' H8' H14]
    dsimp only [regs3, regs2, regs1]
    rw [regupd_other _ _ _ _ H15', regupd_other _ _ _ _ H8', regupd_other _ _ _ _ H14]

include Hsp_lo Hsp_hi in
/-- Every store the loop makes lands in main's frame or in musl's
    16-byte frame just below it, both inside the RLIMIT_STACK window. -/
theorem brk_sok8 (mem : word → Option byte) (a : word)
    (Hg : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) mem)
    (Hlo : bv_unsigned rsp - 96 ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp) : store_ok source_segs mem a 8 = true := by
  have Hspl := rsp_lo_num rsp Hsp_lo
  have Hsph := rsp_hi_num rsp Hsp_hi
  apply store_ok_mono _ _ _ _ _ Hg
  unfold ArgvEnv.wmem
  apply store_ok_wrap_window
  · unfold stack_max_size; omega
  · omega

local macro "bk_grows" : tactic => `(tactic| solve_mem_grows)
set_option hygiene false in
local macro "bk_sok" : tactic => `(tactic|
  (apply brk_sok8 inp rsp rrnd Hsp_lo Hsp_hi <;> first | (solve | bk_grows) | (u_norm; omega)))
local macro "bk_ssd" F:term:max D:term:max a:term:max v:term:max "(" vt:tacticSeq ")" : tactic =>
  `(tactic| stepsd $F $D $a $v ($vt) (bk_sok))
local macro "bk_sld" F:term:max D:term:max a:term:max v:term:max "(" rt:tacticSeq ")" : tactic =>
  `(tactic| stepld $F $D $a $v ($rt))

include Hsp_lo Hsp_hi in
/-- After a (possibly short) delivery of [n] bytes the machine sits at
    0x11218 — [__syscall_cp_c]'s post-ecall [ret] — with
    a0 = [len_word (firstn n rest)].  The run returns through musl's
    [write] wrapper and [__syscall_ret], reloads the buffer-pointer
    spill at rsp-56, decrements the running count in s3, bumps the
    pointer, and either falls into main's exit-0 tail (full delivery,
    [bnez s3] not taken) or respills and reissues the write.  Induction
    on [fuel >= length rest]; the remainder strictly shrinks because
    every delivery is nonempty. -/
theorem src_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 131073) (Hplo : 0 < bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) ≤ bv_unsigned rsp - 96)
    (H1 : reg_get regs 1 = (0x111b4 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80))
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H19 : reg_get regs 19 = len_word rest)
    (Hgrow : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) mem)
    (Hra72 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 72)) 8 =
      some (word_to_le_bytes 8 (0x110f4 : word)))
    (Hptr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 p))
    (Hslra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11160 : word)))
    (Hsl : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Hread : rdn source_segs mem p rest.length = some rest) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x11218 mem rrom)
      (rest.drop n) (to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    stepjr SF_11218 SD_11218 (0x111b4 : word) (getr_resolve; exact H1)
    bk_sld SF_111b4 SD_111b4 (Z_to_bv 64 (bv_unsigned rsp - 72))
      (0x110f4 : word) (exact Hra72)
    stepiv SF_111b8 SD_111b8 (Z_to_bv 64 (bv_unsigned rsp - 64))
      (getr_resolve; regupd_resolve; rw [H2]; sp_norm; sc0)
    stepj SF_111bc SD_111bc
    stepi SF_111c0 SD_111c0
    chain_step
    · rfl
    · apply step_bltu_ft (hf := SF_111c4) (he := rfl) (hd := SD_111c4)
      getr_resolve; regupd_resolve; rw [H10, c_ltu_ltb]
      change decide (18446744073709547520 < bv_unsigned (len_word (rest.take n))) = false
      rw [u_len_word_firstn _ _ Hn2 (by omega)]
      exact decide_eq_false (by omega)
    norm_pc
    stepjr SF_111c8 SD_111c8 (0x110f4 : word) (getr_resolve; regupd_resolve; rfl)
    chain_step
    · rfl
    · apply step_bge_ft (hf := SF_110f4) (he := rfl) (hd := SD_110f4)
      getr_resolve; regupd_resolve; rw [H10]
      apply c_lts_0_pos
      all_goals rw [u_len_word_firstn _ _ Hn2 (by omega)] <;> omega
    norm_pc
    bk_sld SF_110f8 SD_110f8 (Z_to_bv 64 (bv_unsigned rsp - 56)) p (exact Hptr)
    stepiv SF_110fc SD_110fc (len_word (rest.drop n))
      (getr_resolve; regupd_resolve; rw [H10, H19]; apply v_sub_len_firstn <;> omega)
    stepiv SF_11100 SD_11100 (Z_to_bv 64 (bv_unsigned p + (n : Int)))
      (getr_resolve; regupd_resolve; rw [H10]; apply v_add_len_firstn_Z <;> omega)
    by_cases Heq : n = rest.length
    · subst n
      rw [List.drop_length]
      chain_step
      · rfl
      · apply step_bne_ft (hf := SF_11104) (he := rfl) (hd := SD_11104)
        getr_resolve; regupd_resolve; apply c_eq_0_of_u; rfl
      norm_pc
      stepiv SF_11108 SD_11108 (Z_to_bv 64 0) (getr_resolve; bveq)
      stepj SF_1110c SD_1110c
      apply to_wall_tail.twt_done
      apply source_epilogue rsp Hsp_lo Hsp_hi
      · regupd_resolve; rfl
      · regupd_resolve; rfl
      · decide
      · exact Hslra
      · exact Hsl
    · have HpU : bv_unsigned (Z_to_bv 64 (bv_unsigned p + (n : Int))) = bv_unsigned p + (n : Int) :=
        u_Z2bv _ (by omega) (by omega)
      have HrestRead : rdn source_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (rest.drop n).length = some (rest.drop n) := by
        have Hsk := rdn_skipn source_segs mem rest.length p rest n Hread Hn2
        rw [word_add_nat_Z _ _ (by omega)] at Hsk
        rw [List.length_drop]; exact Hsk
      chain_step
      · rfl
      · apply step_bne_tk (hf := SF_11104) (he := rfl) (hd := SD_11104)
        getr_resolve; regupd_resolve; apply c_eq_0_false
        rw [u_len_word _ (by rw [List.length_drop]; omega), List.length_drop]; omega
      norm_pc
      stepiv SF_110e4 SD_110e4 (len_word (rest.drop n)) (getr_resolve; regupd_resolve; apply v_addi_0)
      stepiv SF_110e8 SD_110e8 (Z_to_bv 64 1) (getr_resolve; bveq)
      bk_ssd SF_110ec SD_110ec (Z_to_bv 64 (bv_unsigned rsp - 56))
        (Z_to_bv 64 (bv_unsigned p + (n : Int))) (getr_resolve; regupd_resolve; rfl)
      stepj SF_110f0 SD_110f0
      stepiv SF_1118c SD_1118c (Z_to_bv 64 (bv_unsigned rsp - 80))
        (getr_resolve; regupd_resolve; sp_norm; sc0)
      stepiv SF_11190 SD_11190 (len_word (rest.drop n)) (getr_resolve; apply v_addi_0)
      stepi SF_11194 SD_11194
      stepiv SF_11198 SD_11198 (Z_to_bv 64 (bv_unsigned p + (n : Int))) (getr_resolve; apply v_addi_0)
      stepi SF_1119c SD_1119c
      stepiv SF_111a0 SD_111a0 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
      stepi SF_111a4 SD_111a4
      stepiv SF_111a8 SD_111a8 (Z_to_bv 64 64) (getr_resolve; bveq)
      bk_ssd SF_111ac SD_111ac (Z_to_bv 64 (bv_unsigned rsp - 72))
        (0x110f4 : word) (getr_resolve; bveq)
      stepj SF_111b0 SD_111b0
      stepj SF_1121c SD_1121c
      stepiv SF_111f8 SD_111f8 (Z_to_bv 64 64) (getr_resolve; apply v_addi_0)
      stepiv SF_111fc SD_111fc (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
      stepiv SF_11200 SD_11200 (Z_to_bv 64 (bv_unsigned p + (n : Int))) (getr_resolve; apply v_addi_0)
      stepiv SF_11204 SD_11204 (len_word (rest.drop n)) (getr_resolve; apply v_addi_0)
      stepi SF_11208 SD_11208
      stepi SF_1120c SD_1120c
      stepi SF_11210 SD_11210
      apply to_wall_tail.twt_step _ _ _ _ rfl
      · exact step_ecall _ _ _ _ _ _ SF_11214 rfl
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      apply twl_write_rec source_segs (Z_to_bv 64 1)
      · getr_resolve; regupd_resolve; decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        change rdn source_segs _ _ (word_to_nat (len_word (rest.drop n))) = _
        rw [show word_to_nat (len_word (rest.drop n)) = (rest.drop n).length from by
          change (bv_unsigned (len_word (rest.drop n))).toNat = _
          rw [u_len_word _ (by rw [List.length_drop]; omega), Int.toNat_natCast]]
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by rw [List.length_drop]; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]
        exact HrestRead
      · rw [List.length_drop]; omega
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · rw [HpU]; omega
        · rw [HpU, List.length_drop]; omega
        · regupd_resolve; bveq
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · bk_grows
        · apply rdn_wbytes_hit8; u_norm; omega
        · rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          apply rdn_wbytes_hit8; u_norm; omega
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact Hslra
        · intro a Ha
          have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
              bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
            rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
          exact Hsl a Ha
        · repeat rw [rdn_wbytes_below _ _ _ _ _ _
            (by rw [HpU, List.length_drop]; u_norm; omega)
            (by rw [length_N_to_le_bytes]; u_norm; omega)]
          exact HrestRead

include Hva Hve Hsp_lo Hsp_hi Hge2 in
theorem source_success (regs : bvmap 5 word) (r grant : word)
    (Hgrant : bv_unsigned (nN inp + 1) ≤ bv_unsigned grant)
    (Hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - stack_max_size)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + (nn inp : Int) + 1 ≤ bv_unsigned rsp - stack_max_size)
    (Hfree : region_free (segments_reserved source_segs) r (nN inp + 1) = true)
    (H1 : reg_get regs 1 = (0x110c4 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H8 : reg_get regs 8 = r) (H9 : reg_get regs 9 = nN inp)
    (H10 : reg_get regs 10 = r + (nN inp + 1))
    (H18 : reg_get regs 18 = ptr inp rsp + nN inp)
    (H19 : reg_get regs 19 = nN inp + 1) (H20 : reg_get regs 20 = ptr inp rsp) :
    to_wallexit source_segs (Z_to_bv 64 1) [rev_buf (arg1 inp)] (Z_to_bv 64 0)
      (mkst regs 0x11188
        (zmem (wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 56))
          (word_to_le_bytes 8 (r + (nN inp + 1)))) r grant) rrom) := by
  constructor
  · rw [length_rev_buf]; omega
  have Hplo := ptr_lo inp Hva Hve rsp Hsp_hi Hge2
  have Hphi := ptr_hi inp Hva Hve rsp Hsp_hi Hge2
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have HnnLe := nN_le inp Hva Hge2
  have Hur := u64_range r
  have HnnA : (arg1 inp).length = nn inp := rfl
  have Hun1 := u_nN1 inp Hva Hge2
  have Hurn : bv_unsigned (r + nN inp) = bv_unsigned r + (nn inp : Int) := by
    rw [u_add_small _ _ (by rw [u_nN inp Hva Hge2]; omega), u_nN inp Hva Hge2]
  have Hurn1 : bv_unsigned (r + (nN inp + 1)) = bv_unsigned r + (nn inp : Int) + 1 := by
    rw [u_add_small _ _ (by rw [Hun1]; omega), Hun1]; omega
  let gmem := wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 56))
    (word_to_le_bytes 8 (r + (nN inp + 1)))
  let mem0 := zmem gmem r grant
  change to_wall_tail source_segs _ (mkst regs 0x11188 mem0 rrom) _ _
  sym_block source_segs 5 [false] [EVar 35]
    [((1 : reg), ELit 0x110c4), ((2 : reg), EVar 32), ((8 : reg), EVar 33),
     ((9 : reg), EVar 34), ((10 : reg), EVar 35), ((18 : reg), EVar 36), ((20 : reg), EVar 37)]
    [Z_to_bv 64 (bv_unsigned rsp - 64), r, nN inp, r + (nN inp + 1), ptr inp rsp + nN inp, ptr inp rsp]
    [r + (nN inp + 1)] R HR
  · repeat' apply And.intro
    all_goals first
      | (u_norm; omega)
      | sym_br
      | (refine ⟨word_to_le_bytes 8 (r + (nN inp + 1)), ?_, bytes_le_to_Z_8 _⟩
         unfold mem0
         rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
         unfold gmem
         apply rdn_wbytes_hit8; u_norm; omega)
  · exact H1
  · exact H2
  · exact H8
  · exact H9
  · exact H10
  · exact H18
  · exact H20
  have Hstr0 : rdn source_segs mem0 (ptr inp rsp) (Nat.succ (nn inp)) =
      some (arg1 inp ++ [Z_to_bv 8 0]) := by
    unfold mem0
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (by right; omega)]
    unfold gmem
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
    exact read_str_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  obtain ⟨regsC, HagC, H15C, H8C, HmsC⟩ :=
    source_copy inp Hva Hve rsp Hsp_lo Hsp_hi Hge2 r mem0
      (by unfold mem0; apply store_grant_zmem_prefix <;> omega)
      Hstr0 Hfree Hr0 Hceil (nn inp) R (Nat.le_refl _)
      (by sym_regs HR)
      (by sym_regs HR; exact v_addi_0 _)
      (by rw [Nat.sub_self, word_add_0]; sym_regs HR)
  simp only [Nat.sub_self, List.take_zero, wbytes] at HmsC
  apply msteps_to_wall_tail _ _ _ _ _ _ HmsC
  have Hc2 : reg_get regsC 2 = Z_to_bv 64 (bv_unsigned rsp - 64) := by
    rw [HagC 2 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; sym_regs HR
  have Hc9 : reg_get regsC 9 = nN inp := by
    rw [HagC 9 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; sym_regs HR
  have Hc11 : reg_get regsC 11 = r := by
    rw [HagC 11 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; sym_regs HR; exact v_addi_0 _
  have Hc19 : reg_get regsC 19 = nN inp + 1 := by
    rw [HagC 19 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; sym_regs HR; exact H19
  have Hc20 : reg_get regsC 20 = ptr inp rsp := by
    rw [HagC 20 (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; sym_regs HR
  let memB := wbytes mem0 r (rev_buf (arg1 inp))
  have Hgrowg : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) gmem :=
    mem_grows_trans _ _ _ (grows_fmem inp rsp rrnd) (wbytes_grows _ _ _)
  have Hgrow0 : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) mem0 :=
    mem_grows_trans _ _ _ Hgrowg (zmem_grows _ _ _)
  have HgrowB : mem_grows (ArgvEnv.wmem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd) memB :=
    mem_grows_trans _ _ _ Hgrow0 (wbytes_grows _ _ _)
  have HreadB : rdn source_segs memB r (rev_buf (arg1 inp)).length = some (rev_buf (arg1 inp)) := by
    apply rdn_wbytes_hit
    rw [length_rev_buf]; omega
  have HraB : rdn source_segs memB (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11160 : word)) := by
    unfold memB mem0
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_rev_buf]; u_norm; omega) (by u_norm; omega)]
    rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
    exact spill_ra inp rsp rrnd Hsp_lo Hsp_hi _
  have HslB : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs memB a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
    intro a Ha
    have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
        bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
      rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
    unfold memB mem0
    rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_rev_buf]; omega) (by omega)]
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (by right; omega)]
    exact spill_0 inp rsp rrnd Hsp_lo Hsp_hi _ a Ha
  sym_block source_segs 3 [false] []
    [((9 : reg), EVar 32), ((11 : reg), EVar 33), ((15 : reg), EVar 34), ((20 : reg), EVar 34)]
    [nN inp, r, ptr inp rsp] [] R1 HR1
  · sym_br
  · exact Hc9
  · exact Hc11
  · exact H15C
  · exact Hc20
  chain_step
  · rfl
  · apply LinuxProcessSemantics.Common.MmapSim.step_sb_at (Hv := rfl) (a := r + nN inp) (b := Z_to_bv 8 10)
      (Hf := SF_110e0) (He := rfl) (Hd := SD_110e0)
    · sym_regs HR1
      exact (v_addi_0 _).trans (alu_add _ _)
    · sym_regs HR1 <;> rfl
    · store_ok_peel; apply store_ok_zmem
      all_goals simp only [Hurn] <;> omega
  step_simpl
  rw [show wbytes (wbytes mem0 r (arg1 inp).reverse) (r + nN inp) [Z_to_bv 8 10] = memB from by
    unfold memB rev_buf; rw [wbytes_app, List.length_reverse]; rfl]
  sym_block source_segs 24 [] []
    [((2 : reg), EVar 32), ((11 : reg), EVar 33), ((19 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 64), r, nN inp + 1] [] R2 HR2
  · repeat' apply And.intro
    all_goals first | (u_norm; omega) | (apply brk_sok8 inp rsp rrnd Hsp_lo Hsp_hi <;>
      first | exact HgrowB | exact mem_grows_trans _ _ _ HgrowB (wbytes_grows _ _ _) | (u_norm; omega))
  · regupd_resolve; sym_regs HR1; exact Hc2
  · regupd_resolve; sym_regs HR1; exact Hc19
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ SF_11214 rfl
  apply to_wall_tail.twt_more
  · rw [length_rev_buf]; omega
  apply twl_write_rec source_segs (Z_to_bv 64 1)
  · sym_regs HR2; decide +kernel
  · sym_regs HR2 <;> rfl
  · rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
    sym_regs HR2
    change rdn source_segs _ (v_addi r 0) (word_to_nat (v_addi (nN inp + 1) 0)) = _
    rw [v_addi_0, v_addi_0]
    rw [show word_to_nat (nN inp + 1) = (rev_buf (arg1 inp)).length from by
      change (bv_unsigned (nN inp + 1)).toNat = _
      rw [Hun1, length_rev_buf]; omega]
    repeat rw [rdn_wbytes_below _ _ _ _ _ _
      (by rw [length_rev_buf]; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]
    exact HreadB
  · rw [length_rev_buf]; omega
  · intro n Hn1 Hn2
    norm_pc
    apply src_put_wall inp rsp rrnd Hsp_lo Hsp_hi (rev_buf (arg1 inp)).length (rev_buf (arg1 inp)) r n
    · omega
    · exact Hn1
    · exact Hn2
    · rw [length_rev_buf]; omega
    · exact Hr0
    · rw [length_rev_buf]; omega
    · regupd_resolve; sym_regs HR2 <;> rfl
    · regupd_resolve; sym_regs HR2
      apply bv_eq_of_unsigned; u_norm; omega
    · regupd_resolve; rfl
    · regupd_resolve; sym_regs HR2
      apply bv_eq_of_unsigned
      rw [Hun1, u_len_word _ (by rw [length_rev_buf]; omega), length_rev_buf]; omega
    · exact mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HgrowB (wbytes_grows _ _ _)) (wbytes_grows _ _ _)
    · apply rdn_wbytes_hit8; u_norm; omega
    · rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
      apply rdn_wbytes_hit8; u_norm; omega
    · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
      exact HraB
    · intro a Ha
      have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
          bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
        rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
      repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
      exact HslB a Ha
    · repeat rw [rdn_wbytes_below _ _ _ _ _ _
        (by rw [length_rev_buf]; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]
      exact HreadB

include Hva Hve Hsp_lo Hsp_hi Hge2 in
theorem source_to_brk1 (Hncap : (nn inp : Int) ≤ 65536) :
    ∃ regs3, msteps source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      { ms_regs := regs3, ms_fregs := bvmap_empty, ms_pc_val := 0x11184,
        ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := fmem inp rsp rrnd, ms_rom := rrom } ∧
      reg_get regs3 1 = (0x11064 : word) ∧
      reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
      reg_get regs3 9 = nN inp ∧ reg_get regs3 10 = Z_to_bv 64 0 ∧
      reg_get regs3 18 = ptr inp rsp + nN inp ∧ reg_get regs3 20 = ptr inp rsp := by
  have HnnLe := nN_le inp Hva Hge2
  obtain ⟨regs1, Hms1, H2, H9, H18, H20⟩ := source_to_len inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  sym_block_ex source_segs (mkst regs1 (Z_to_bv 64 0x11038) (fmem inp rsp rrnd) rrom)
    18 [false] []
    [((2 : reg), EVar 32), ((9 : reg), EVar 33), ((18 : reg), EVar 34), ((20 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 64), nN inp, ptr inp rsp + nN inp, ptr inp rsp] [] R HR Hms
  · have Hu := u_nN inp Hva Hge2
    sym_br
  · exact H2
  · exact H9
  · exact H18
  · exact H20
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply msteps_trans _ _ _ _ Hms1
    sym_chain Hms
    chain_step
    · rfl
    · exact step_ecall _ _ _ _ _ _ SF_11184 rfl
    have H17 : getr R 17 = Z_to_bv 64 214 := by sym_regs HR <;> rfl
    rw [H17]
    exact msteps.mst_refl _
  · sym_regs HR <;> rfl
  · sym_regs HR
  · sym_regs HR
  · sym_regs HR <;> rfl
  · sym_regs HR
  · sym_regs HR

include Hva Hsp_lo Hsp_hi Hge2 in
theorem source_to_brk2 (regs3 : bvmap 5 word) (r : word)
    (H1 : reg_get regs3 1 = (0x11064 : word))
    (H2 : reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H9 : reg_get regs3 9 = nN inp)
    (H18 : reg_get regs3 18 = ptr inp rsp + nN inp)
    (H20 : reg_get regs3 20 = ptr inp rsp)
    (Hrnz : r ≠ Z_to_bv 64 0) (Hw : bv_unsigned r + (nn inp : Int) + 1 < 2 ^ 64) :
    ∃ regs5, msteps source_segs
      (mkst (regupd regs3 10 r) 0x11188 (fmem inp rsp rrnd) rrom)
      { ms_regs := regs5, ms_fregs := bvmap_empty, ms_pc_val := 0x11184,
        ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := wbytes (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 56))
          (word_to_le_bytes 8 (r + (nN inp + 1))), ms_rom := rrom } ∧
      reg_get regs5 1 = (0x110c4 : word) ∧
      reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
      reg_get regs5 8 = r ∧ reg_get regs5 9 = nN inp ∧
      reg_get regs5 10 = r + (nN inp + 1) ∧
      reg_get regs5 18 = ptr inp rsp + nN inp ∧ reg_get regs5 19 = nN inp + 1 ∧
      reg_get regs5 20 = ptr inp rsp := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HnnLe := nN_le inp Hva Hge2
  have Hur := u64_range r
  have Hur0 := word_neq0_unsigned r Hrnz
  have Hun := u_nN inp Hva Hge2
  have Hun1 := u_nN1 inp Hva Hge2
  have Hurn1 : bv_unsigned (r + (nN inp + 1)) = bv_unsigned r + (nn inp : Int) + 1 := by
    rw [u_add_small _ _ (by rw [Hun1]; omega), Hun1]; omega
  have Hrn1s : Z_to_bv 64 (bv_unsigned r + (bv_unsigned (nN inp) + 1)) = r + (nN inp + 1) := by
    apply bv_eq_of_unsigned
    rw [Hurn1, u_Z2bv _ (by rw [Hun]; omega) (by rw [Hun]; omega), Hun]; omega
  have Hn1s : Z_to_bv 64 (bv_unsigned (nN inp) + 1) = nN inp + 1 := by
    apply bv_eq_of_unsigned
    rw [Hun1, u_Z2bv _ (by rw [Hun]; omega) (by rw [Hun]; omega), Hun]
  sym_block_ex source_segs
    (mkst (regupd regs3 10 r) (Z_to_bv 64 0x11188) (fmem inp rsp rrnd) rrom)
    21 [true, false] []
    [((1 : reg), ELit 0x11064), ((2 : reg), EVar 32), ((9 : reg), EVar 33),
     ((10 : reg), EVar 34), ((18 : reg), EVar 35), ((20 : reg), EVar 36)]
    [Z_to_bv 64 (bv_unsigned rsp - 64), nN inp, r, ptr inp rsp + nN inp, ptr inp rsp] [] R HR Hms
  · repeat' apply And.intro
    all_goals first
      | (u_norm; omega)
      | sym_br
      | (apply brk_sok8 inp rsp rrnd Hsp_lo Hsp_hi
         · exact grows_fmem inp rsp rrnd
         · u_norm; omega
         · u_norm; omega)
  · getr_resolve; regupd_resolve; exact H1
  · getr_resolve; regupd_resolve; exact H2
  · getr_resolve; regupd_resolve; exact H9
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; exact H18
  · getr_resolve; regupd_resolve; exact H20
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_chain Hms
    chain_step
    · rfl
    · exact step_ecall _ _ _ _ _ _ SF_11184 rfl
    have H17 : getr R 17 = Z_to_bv 64 214 := by sym_regs HR <;> rfl
    rw [H17]
    sym_mem_norm
    rw [Hrn1s]
    exact msteps.mst_refl _
  · sym_regs HR <;> rfl
  · sym_regs HR
  · sym_regs HR; exact v_addi_0 _
  · sym_regs HR
  · sym_regs HR
    exact (v_addi_0 _).trans Hrn1s
  · sym_regs HR
  · sym_regs HR; exact Hn1s
  · sym_regs HR

variable (Hbrk_mod : bv_unsigned rbrk % page_size = 0)

include Hva Hve Hsp_lo Hsp_hi Hbrk_lo Hbrk_hi Hge2 Hbrk_mod in
theorem source_outcomes (Hncap : (nn inp : Int) ≤ 65536) :
    to_outcomes source_segs
      (init_machine_state source_segs 0x11134 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (brkU (rev_buf (arg1 inp))) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have HnnLe := nN_le inp Hva Hge2
  have Hun1 := u_nN1 inp Hva Hge2
  let m0 := init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp
  let h0 := VmMaps.mkVmMapsFull (segments_reserved source_segs) [] [] rbrk rbrk source_alloc_limit rmb rsp
  obtain ⟨regs3, Hms, E1, E2, E9, E10, E18, E20⟩ :=
    source_to_brk1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 Hncap
  apply tou_msteps _ _ _ _ _ Hms
  apply tou_brk_r source_segs _ _ (Z_to_bv 64 214)
    (T1 (segments_reserved source_segs) source_alloc_limit
      (bv_unsigned rsp - stack_max_size) (nN inp + 1) [rev_buf (arg1 inp)])
  · rfl
  · decide +kernel
  · intro r Hok
    change brk_resolution_ok m0 (reg_get regs3 10) r at Hok
    rw [E10] at Hok
    change brk_r_ok h0 (Z_to_bv 64 0) r at Hok
    have Hquery : r = rbrk := (brk_r_ok_query_iff h0 r).mp Hok
    have Hblo := rbrk_lo_num rbrk Hbrk_lo
    have Hbhi := rbrk_hi_num rbrk Hbrk_hi
    have Hur : bv_unsigned r = bv_unsigned rbrk := congrArg bv_unsigned Hquery
    have Hrmod : bv_unsigned r % page_size = 0 := by rw [Hur]; exact Hbrk_mod
    have Hrnz : r ≠ Z_to_bv 64 0 := by
      intro He
      have := congrArg bv_unsigned He
      rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega
    have Hnw : bv_unsigned r + (nn inp : Int) + 1 < 2 ^ 64 := by omega
    have Hrtop : reserved_top (segments_reserved source_segs) ≤ bv_unsigned r := by
      rw [Hur]; exact Hbrk_lo
    have Hurn1 : bv_unsigned (r + (nN inp + 1)) = bv_unsigned r + (nn inp : Int) + 1 := by
      rw [u_add_small _ _ (by rw [Hun1]; omega), Hun1]; omega
    have Hwant0 : r + (nN inp + 1) ≠ Z_to_bv 64 0 := by
      intro He
      have := congrArg bv_unsigned He
      rw [Hurn1, show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega
    have Hne2 : r ≠ r + (nN inp + 1) := by
      intro He
      have := congrArg bv_unsigned He
      rw [Hurn1] at this
      omega
    change to_outcomes source_segs
      (advance_past_svc (apply_effect _
        (SyscallEffect.mkEffectU r [] (brk_zeros (reg_get regs3 10) r rbrk)
          (brk_unmaps r rbrk) [] []))) (brk_model (reg_get regs3 10) r m0) _
    rw [E10, brk_zeros_query, brk_unmaps_query h0 r Hquery, adv_brk, apply_zeros_nil]
    norm_pc
    rw [brk_model_query r m0 Hquery]
    let h1 := VmMaps.mkVmMapsFull (segments_reserved source_segs) [] [] rbrk r source_alloc_limit rmb rsp
    change to_outcomes source_segs (mkst (regupd regs3 10 r) 0x11188 (fmem inp rsp rrnd) rrom)
      (with_vmmaps h1 m0) _
    obtain ⟨regs5, Hms2, F1, F2, F8, F9, F10, F18, F19, F20⟩ :=
      source_to_brk2 inp Hva rsp rrnd Hsp_lo Hsp_hi Hge2 regs3 r E1 E2 E9 E18 E20 Hrnz Hnw
    apply tou_msteps _ _ _ _ _ Hms2
    apply tou_brk_r source_segs _ _ (Z_to_bv 64 214)
      (T2 (r + (nN inp + 1)) [rev_buf (arg1 inp)])
    · rfl
    · decide +kernel
    · intro r2 Hok2
      change brk_resolution_ok (with_vmmaps h1 m0) (reg_get regs5 10) r2 at Hok2
      rw [F10] at Hok2
      change brk_r_ok h1 (r + (nN inp + 1)) r2 at Hok2
      have Hcases := (brk_r_ok_grow_iff _ _ _ _ _ _ _ _ _ _
        (by rw [Hurn1]; omega) (by rw [Hurn1]; omega) (by rw [Hurn1]; omega)).mp Hok2
      change to_outcomes source_segs
        (advance_past_svc (apply_effect _
          (SyscallEffect.mkEffectU r2 [] (brk_zeros (reg_get regs5 10) r2 r)
            (brk_unmaps r2 r) [] []))) (brk_model (reg_get regs5 10) r2 (with_vmmaps h1 m0)) _
      rw [F10]
      by_cases Heq : r2 = r + (nN inp + 1)
      · subst r2
        obtain ⟨_, Hgrow2⟩ := Hcases
        rw [brk_grow_ok_aligned_grow _ _ _ Hwant0 (by change 0 < bv_unsigned r; omega)
          (by change bv_unsigned r < bv_unsigned (r + (nN inp + 1)); rw [Hurn1]; omega) Hrmod] at Hgrow2
        change ((decide (page_round_up_Z (bv_unsigned (r + (nN inp + 1))) ≤ bv_unsigned rsp - stack_max_size) &&
          region_free (segments_reserved source_segs ++ []) r
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + (nN inp + 1))) + page_size - bv_unsigned r))) &&
          _) = true at Hgrow2
        rw [List.append_nil] at Hgrow2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at Hgrow2
        obtain ⟨⟨Hle, Hfree⟩, _⟩ := Hgrow2
        let grant := Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + (nN inp + 1))) - bv_unsigned r)
        obtain ⟨_, Hgrant, Hphysceil, Hrawceil, Hrawfree, _⟩ :=
          brk_aligned_grant_ok _ r (nN inp + 1) grant _ _
            (u_add_small _ _ (by rw [Hun1]; omega)) Hurn1 rfl (alloc_top_page_lt h1) Hle Hfree
        change to_outcomes source_segs
          (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU _ []
            (Sys.Mm.Mmap.brk_zeros (r + (nN inp + 1)) (r + (nN inp + 1)) r)
            (Sys.Mm.Mmap.brk_unmaps (r + (nN inp + 1)) r) [] []))) _ _
        rw [brk_zeros_aligned_grow _ _ _ Hwant0 (by omega) (by rw [Hurn1]; omega) Hrmod,
          brk_unmaps_grow _ _ (by rw [Hurn1]; omega), adv_brk, apply_zeros_one]
        apply tou_equiv _ _ _ _ _ ?_ (T2_succ_iff (r + (nN inp + 1)) [rev_buf (arg1 inp)])
        apply tou_wexit_eq
        · apply fd1chan_brk_model
          apply fd1chan_with_vmmaps
          apply init_model_fd1chan
        · apply source_success inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
            (regupd regs5 10 (r + (nN inp + 1))) r grant Hgrant Hphysceil (by omega) Hrawceil Hrawfree
          · regupd_resolve; exact F1
          · regupd_resolve; exact F2
          · regupd_resolve; exact F8
          · regupd_resolve; exact F9
          · regupd_resolve; rfl
          · regupd_resolve; exact F18
          · regupd_resolve; exact F19
          · regupd_resolve; exact F20
        · exact bufs_modeled_out inp Hva Hge2
      · obtain ⟨Hcase, _⟩ := Hcases
        rcases Hcase with Hc | Hc
        · exact False.elim (Heq Hc)
        subst r2
        change to_outcomes source_segs
          (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU _ []
            (Sys.Mm.Mmap.brk_zeros (r + (nN inp + 1)) r r) (Sys.Mm.Mmap.brk_unmaps r r) [] []))) _ _
        rw [brk_zeros_keep, brk_unmaps_grow _ _ (by omega), adv_brk, apply_zeros_nil]
        apply tou_equiv _ _ _ _ _ ?_ (T2_fail_iff (r + (nN inp + 1)) [rev_buf (arg1 inp)] r Hne2)
        apply tou_wexit_eq
        · apply fd1chan_brk_model
          apply fd1chan_with_vmmaps
          apply init_model_fd1chan
        · change to_wexit source_segs _ [] (Z_to_bv 64 4)
          stepjr SF_11188 SD_11188 (0x110c4 : word) (getr_resolve; regupd_resolve; exact F1)
          stepld SF_110c4 SD_110c4 (Z_to_bv 64 (bv_unsigned rsp - 56)) (r + (nN inp + 1))
            (apply rdn_wbytes_hit8; u_norm; omega)
          chain_step
          · rfl
          · apply step_bne_tk (hf := SF_110c8) (he := rfl) (hd := SD_110c8)
            getr_resolve; regupd_resolve
            apply c_eq_neq; rw [Hurn1]; omega
          norm_pc
          apply source_exit4 rsp Hsp_lo Hsp_hi
          · regupd_resolve; exact F2
          · exact spill_ra inp rsp rrnd Hsp_lo Hsp_hi _
          · exact spill_0 inp rsp rrnd Hsp_lo Hsp_hi _
        · intro b Hb; exact False.elim (List.not_mem_nil Hb)
    · intro o
      change T1 _ _ _ _ _ _ o ↔ ∃ r2, brk_resolution_ok (with_vmmaps h1 m0) (reg_get regs5 10) r2 ∧ _
      rw [F10]
      change T1 _ _ _ _ _ _ o ↔ ∃ r2, brk_r_ok h1 (r + (nN inp + 1)) r2 ∧ _
      apply AllocSim.T1_iff_T2 (segments_reserved source_segs) source_alloc_limit rbrk rmb rsp
        (nN inp + 1) [rev_buf (arg1 inp)] r Hrnz (by omega)
      · rw [Hun1]; omega
  · intro o
    change brkU _ o ↔ ∃ r, brk_resolution_ok m0 (reg_get regs3 10) r ∧ _
    rw [E10]
    change brkU _ o ↔ ∃ r, brk_r_ok h0 (Z_to_bv 64 0) r ∧ _
    have Hblo := rbrk_lo_num rbrk Hbrk_lo
    have Hbhi := rbrk_hi_num rbrk Hbrk_hi
    apply brkU_iff_T1 (segments_reserved source_segs) source_alloc_limit
      (bv_unsigned rsp - stack_max_size) (nN inp) (rev_buf (arg1 inp)) rbrk
    · intro r0
      exact brk_r_ok_query_iff _ r0
    · refine ⟨?_, ?_, Or.inr ?_⟩
      · intro He
        have := congrArg bv_unsigned He
        rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
        omega
      · rw [Hun1]; omega
      · apply growable_aligned_grow
        · exact Hbrk_mod
        · exact Hbrk_lo
        · rw [Hun1]; omega
        · rw [Hun1]; unfold page_size; omega
        · change bv_unsigned (nN inp + 1) ≤ 0x400000000
          rw [Hun1]; omega
    · intro He
      have := congrArg bv_unsigned He
      rw [Hun1, show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega

end Ge2Main
end SourceProof

end LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_source
