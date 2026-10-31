import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatSim

/-! # Common.SeqExec — step and read-back theory for compiled binaries

Ported from `theories/Common/SeqExec.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.

Everything else in the Rocq file was left unported by that ticket;
cat1024_ns reaches none of it.  Sections appended at the end of this file
since, each headed by the ticket that added it, port some of it; after
E-grep_args_ns's section every Rocq declaration and `Ltac` of the file has a
Lean twin.  What that
ticket left includes: the remaining `_at` step lemmas (`lui`/`auipc`/`addiw`/
shifts/...), the `divu`/`remu` and `sw`/`sh` step groups, the derived
`to_wexit` lemmas `tw_write_ret` and `tw_exit_coden`, `argv_ptr_bounds` and
its arithmetic, `rdn_firstn`, the load-word/zero lemmas, `step_sb256`, and
the register-lookup tactics (Ltac: proof automation, not constants).

Rocq's `Z.ltb a b` is `decide (a < b)` here (`c_ltu_ltb`). -/

namespace LinuxProcessSemantics.Common.SeqExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec

/-! ## Value shapes -/

/-- The jalr target: (rs1 + imm) with bit 0 cleared.  Definitionally
equal to `PropExec.jalr_tgt`, so `step_jalr` composes with
`step_jalr_gen`'s conclusion. -/
def v_jalr (x : word) (imm : Int) : word := Z_to_bv 64 (jalr_tgtZ x imm)

/-! ## Per-instruction step lemmas -/

/-- Jal with a live link register: rd := pc + 4, jump to `btgt`.
(No `align4` hypothesis: the ISA model has no alignment check.) -/
theorem step_jal_link (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 21)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Jal rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (btgt pc (bv_signed imm)) mem rom) := by
  step_pipeline hfetch hecall hdecode
  show MachineOk (rset rd (pc + 4) (core.Core regs bvmap_empty (pc + sext 64 imm) 0 none),
    mem) = _
  rw [npc4, b_addsext, rset_mk]
  rfl

/-- Jalr: rd := pc + 4, jump to (rs1 + imm) & ~1.  Restatement of
`PropExec.step_jalr_gen` with the `v_jalr` value shape. -/
theorem step_jalr (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (v_jalr (getr regs rs1) (bv_signed imm)) mem rom) :=
  step_jalr_gen segs regs pc mem rom w rd rs1 imm hf he hd

/-! ## Value-precise store double -/

/-- Store double, stored VALUE exposed: mem := wbytes mem (rs1+imm)
(word_to_le_bytes 8 rs2), so a later reload sees the exact bytes. -/
theorem step_sd_val (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Store .SZ8 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 8 (getr regs rs2))) rom) := by
  step_pipeline hfetch hecall hdecode
  show interp_eff segs
    (.EStore 64 (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
      (rget (core.Core regs bvmap_empty pc 0 none) rs2)
      (.EDone (inval_resv (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
        (core.Core regs bvmap_empty (pc + 4) 0 none)))) mem = _
  simp only [rget_mk, b_addsext, npc4]
  rw [interp_store segs 64 _ _ _ mem hok, write_to_mem_wbytes]
  rfl

/-- `step_sd_val` with the store address and value pre-normalized, so the
chained machine state stays in `sp - k`-literal form. -/
theorem step_sd_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ8 rs1 rs2 imm, 4))
    (ha : v_addi (getr regs rs1) (bv_signed imm) = a)
    (hv : getr regs rs2 = v)
    (hok : store_ok segs mem a 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  rw [step_sd_val segs regs pc mem rom w rs1 rs2 imm hf he hd (by rw [ha]; exact hok), ha, hv]

/-- `step_addi` with the writeback value pre-normalized (the `addi`/`li`
analogue of `step_sd_at`): the chained machine state stays flat.
Without this, every `addi` in a long step chain embeds
`v_addi (getr <chain>) imm` in the written value — two references to
the previous state per step — and normalizing the final state explodes
exponentially once the initial sp is symbolic. -/
theorem step_addi_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_addi (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_addi segs regs pc mem rom w rd rs imm hf he hd, hrd, hv]
  rfl

/-- The `_at` (writeback pre-normalized) analogues of `step_addi_at` for the
remaining ALU instructions, so a step chain stays flat. -/
theorem step_add_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_ADD rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_add (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_add segs regs pc mem rom w rd rs1 rs2 hf he hd, hrd, hv]
  rfl

theorem step_sub_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SUB rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_sub (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_sub segs regs pc mem rom w rd rs1 rs2 hf he hd, hrd, hv]
  rfl

/-! ## `wbytes` read-back -/

/-- NEW no-overflow hypothesis (the `wbytes`/`rdn` address walks are
wrapping `bv` adds, mirroring `wbytes_below`/`rdn_ext`); trivially
discharged downstream — stack addresses sit far below 2^64. -/
theorem rdn_wbytes_hit (segs : List Segment) (bs : List byte) (m : word → Option byte)
    (a : word) (hnw : bv_unsigned a + (bs.length : Int) ≤ 2 ^ 64) :
    rdn segs (wbytes m a bs) a bs.length = some bs := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hnw
    have hm' : (fun x : word => if bv_eqb x a then some b else m x) a = some b := by
      simp only [PropExec.bv_eqb_refl, ↓reduceIte]
    cases rest with
    | nil =>
      simp only [List.length_cons, List.length_nil, wbytes, rdn, hm']
    | cons b' rest' =>
      have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by
        simp only [List.length_cons] at hnw; omega)
      have hread : wbytes (fun x : word => if bv_eqb x a then some b else m x) (a + 1)
          (b' :: rest') a = some b := by
        rw [wbytes_below (b' :: rest') _ (a + 1) a (by rw [hu1]; omega) (by omega)]
        exact hm'
      have hrest := ih (fun x : word => if bv_eqb x a then some b else m x) (a + 1)
        (by rw [hu1]; omega)
      simp only [wbytes] at hread hrest ⊢
      simp only [List.length_cons, rdn, hread] at hrest ⊢
      rw [hrest]

/-- Read a full 8-byte slot back. -/
theorem rdn_wbytes_hit8 (segs : List Segment) (m : word → Option byte) (a v : word)
    (hnw : bv_unsigned a + 8 ≤ 2 ^ 64) :
    rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8 = some (word_to_le_bytes 8 v) := by
  have h := rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a
  rw [length_N_to_le_bytes] at h
  exact h hnw

/-- Hypothesis-free: the `bv` bound is enforced by the type. -/
theorem bytes_le_to_Z_8 (v : word) : bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v := by
  rw [bytes_le_N]
  have h := u64_range v
  exact Int.emod_eq_of_lt h.1 (by omega)

/-! ## Value simplification -/

/-- `c_ltu` IS the unsigned `Z.ltb`; no range hypotheses
are needed, since the `bv` bounds are enforced by the type. -/
theorem c_ltu_ltb (x y : word) : c_ltu x y = decide (bv_unsigned x < bv_unsigned y) := by
  unfold c_ltu bv_ltu BitVec.ult bv_unsigned
  exact decide_eq_decide.2 Int.ofNat_lt.symm

/-- Jalr with rd = x0 (RISC-V `ret` / tail jump) and the target named.
(No `align4_jalr` hypothesis: dropped repo-wide.) -/
theorem step_jalr_x0 (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12) (tgt : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jalr 0 rs1 imm, 4))
    (ht : getr regs rs1 = tgt) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom) := by
  rw [step_jalr segs regs pc mem rom w 0 rs1 imm hf he hd, ht, PropExec.bv_eqb_refl]
  rfl

/-- Jalr with a live link register and the target named. -/
theorem step_jalr_link (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (tgt : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jalr rd rs1 imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (ht : getr regs rs1 = tgt) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom) := by
  rw [step_jalr segs regs pc mem rom w rd rs1 imm hf he hd, ht, hrd]
  rfl

theorem getr_zero (regs : bvmap 5 word) : getr regs 0 = Z_to_bv 64 0 := by
  simp only [getr, PropExec.bv_eqb_refl, ↓reduceIte]
  decide

/-- Store byte: the stored list is the exact single little-endian byte
of rs2 (`word_to_le_bytes 1`, = `bv_extract 0 8`); no `< 128` /
`< 256` value hypotheses are needed — the bv model stores the low
byte directly. -/
theorem step_sb (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Store .SZ1 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 1 (getr regs rs2))) rom) := by
  have hsb : ∀ u : word,
      Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u := by
    intro u
    unfold word_to_le_bytes
    simp only [Z_to_le_bytes, List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp only [Z_to_bv, bv_unsigned, bv_extract, BitVec.toNat_ofInt, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero]
    omega
  step_pipeline hfetch hecall hdecode
  show interp_eff segs
    (.EStore 8 (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
      (bv_extract 0 8 (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (.EDone (inval_resv (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
        (core.Core regs bvmap_empty (pc + 4) 0 none)))) mem = _
  simp only [rget_mk, b_addsext, npc4]
  rw [interp_store segs 8 _ _ _ mem hok, write_to_mem_wbytes]
  show MachineOk (_, wbytes mem _ (Z_to_le_bytes 1 _)) = _
  rw [hsb]
  rfl

/-- `addi` with a negative immediate (generic form of the per-problem
`v_addi_m16`/`v_addi_m64` locals).  The immediate is a `Z`, and the
conclusion is the `Z_to_bv`-normal form (the equation itself holds by
conversion — the hypotheses are kept so call sites survive and so the
RHS really is a non-wrapping difference). -/
theorem v_addi_m (x : word) (k : Int) (_hk : k ≤ bv_unsigned x) (_hpos : 0 < k) :
    v_addi x (-k) = Z_to_bv 64 (bv_unsigned x - k) := rfl

theorem rdn_skipn (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (k : Nat) (h : rdn segs mem a n = some bs) (hk : k ≤ n) :
    rdn segs mem (a + nat_to_word k) (n - k) = some (bs.drop k) := by
  have hntw : ∀ j, nat_to_word j = BitVec.ofNat 64 j := fun j => by
    unfold nat_to_word Z_to_bv
    exact BitVec.ofInt_natCast 64 j
  induction n generalizing a bs k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hntw, BitVec.add_zero]
    exact h
  | succ n ih =>
    cases k with
    | zero =>
      rw [hntw, BitVec.add_zero]
      simp only [Nat.sub_zero, List.drop_zero]
      exact h
    | succ k =>
      unfold rdn at h
      split at h
      · rename_i b hb
        split at h
        · rename_i rest hr
          cases h
          rw [hntw, ← add_offset_succ, ← hntw]
          simp only [Nat.add_sub_add_right, List.drop_succ_cons]
          exact ih (a + 1) rest k hr (by omega)
        · cases h
      · cases h

/-! ## Additions for ticket E-proof-library-2c: `argv_ptr_bounds` and `rdn_nth`

Ported from the same Rocq file at the baseline the header names, with the
Rocq statements, for `Common/MuslStrlen.lean` and `Common/ArgvEnv.lean`:
the generic argv-pointer bounds with their slack constant and the four
arithmetic cores Rocq declares `Local` (plain theorems here, under the same
names), and `rdn_nth`.  Rocq's comment gives a performance reason for the
separate cores: each `lia` then runs without the `valid_argv`/`valid_envp`
components in its context.  It calls those components' literals `nat`, but
at the baseline `Run.v` states each of their bounds in `%Z`, as `Run.lean`
does over `Int`; the cores are ported for their statements.  Rocq's
`nth j bs d` is `bs.getD j d`, and `Z.of_nat` is the `Nat`-to-`Int`
cast. -/

/-- The slack `argv_ptr_bounds` requires above `sp`
(`sp + argv_layout_slack < 2 ^ 64`).  It covers the three bounds that
proof sums: the maximal struct prefix (`argv_struct_arith`), all argv
string bytes (`argv_sum_arith`) and one string's length
(`argv_final_arith`). -/
def argv_layout_slack : Int := 4300000

theorem argv_struct_arith (a e : Int) (_h0 : 0 ≤ a) (h1 : a ≤ 1024) (_h2 : 0 ≤ e)
    (h3 : e ≤ 256) :
    8 + (a + 1) * 8 + (e + 1) * 8 + 160 ≤ 10424 := by
  omega

theorem argv_sum_arith (a b : Int) (h0 : a ≤ 10424) (h1 : b ≤ 2097152) :
    a + b ≤ 2107576 := by
  omega

theorem argv_mod_arith (s m : Int) (h0 : 0 ≤ s) (h1 : 0 ≤ m) (h2 : m ≤ 2107576)
    (h3 : s + 4300000 < 2 ^ 64) :
    0 ≤ s + m ∧ s + m < 2 ^ 64 := by
  omega

theorem argv_final_arith (s m l : Int) (h0 : 0 ≤ m) (h1 : 0 ≤ l) (h2 : m ≤ 2107576)
    (h3 : l ≤ 131071) (h4 : s + 4300000 < 2 ^ 64) :
    s ≤ s + m ∧ s + m + l + 1 < 2 ^ 64 := by
  omega

theorem argv_ptr_bounds (sp : word) (av ev : List (List byte)) (k : Nat)
    (hva : valid_argv av) (hve : valid_envp ev) (hk : k < av.length)
    (hsp : bv_unsigned sp + argv_layout_slack < 2 ^ 64) :
    bv_unsigned sp ≤ bv_unsigned (cat_argv_ptr sp av ev k) ∧
      bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 1 < 2 ^ 64 := by
  have havZ := valid_argv_len av hva
  have hnthZ := valid_argv_str_len av k hva hk
  have htot := hva.2.1
  have hevZ : (ev.length : Int) ≤ 256 := hve.1
  have htotZ : (total_arg_bytes_nat (av.take k) : Int) ≤ 2097152 := by
    rw [total_arg_bytes_Z] at htot
    have := total_arg_bytes_firstn_le k av
    omega
  have hA : (cat_struct_size av ev : Int) ≤ 10424 := by
    have := argv_struct_arith (av.length : Int) (ev.length : Int) (Int.natCast_nonneg _) havZ
      (Int.natCast_nonneg _) hevZ
    unfold cat_struct_size StackLayout.auxv_size
    omega
  have hptr : cat_argv_ptr sp av ev k =
      sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge]
  have hnZ : ((cat_struct_size av ev + total_arg_bytes_nat (av.take k) : Nat) : Int) ≤ 2107576 := by
    have := argv_sum_arith _ _ hA htotZ
    omega
  have hu : bv_unsigned (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)))
      = bv_unsigned sp +
        ((cat_struct_size av ev + total_arg_bytes_nat (av.take k) : Nat) : Int) := by
    rw [bv_unsigned_add, nat_to_word, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod,
      Int.add_emod_emod]
    have hu64 := u64_range sp
    unfold argv_layout_slack at hsp
    have hr := argv_mod_arith _ _ hu64.1 (Int.natCast_nonneg _) hnZ hsp
    exact Int.emod_eq_of_lt hr.1 hr.2
  rw [hptr, hu]
  unfold argv_layout_slack at hsp
  exact argv_final_arith _ _ _ (Int.natCast_nonneg _) (Int.natCast_nonneg _) hnZ hnthZ hsp

theorem rdn_nth (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (j : Nat) (h : rdn segs mem a n = some bs) (hj : j < n) :
    rdn segs mem (a + nat_to_word j) 1 = some [bs.getD j (Z_to_bv 8 0)] := by
  induction n generalizing a bs j with
  | zero => omega
  | succ n ih =>
    unfold rdn at h
    split at h
    · rename_i b hb
      split at h
      · rename_i rest hr
        cases h
        cases j with
        | zero =>
          rw [word_add_0, List.getD_cons_zero]
          simp only [rdn, hb]
        | succ j =>
          have heq : a + 1 + nat_to_word j = a + nat_to_word (j + 1) := by
            rw [word1_nat, nat_to_word_add_merge, Nat.add_comm 1 j]
          rw [List.getD_cons_succ, ← heq]
          exact ih (a + 1) rest j hr (by omega)
      · cases h
    · cases h

/-! ## Additions for ticket E-proof-library-2c: `land_255_small`

Ported from the same Rocq file at the baseline the header names, with the
Rocq statement.  Rocq's proof goes through `Z.land_ones` and `Z.mod_small`;
this one is the same argument on `BitVec.toNat`: masking with `2 ^ 8 - 1`
is taking the value mod `2 ^ 8`, which a value below 256 survives. -/

/-- Masking a small exit code with 255 is the identity; `CatSim.to_wexit`'s
`tw_exit` exit code is `bv_and _ 255`.  Rocq applies it in `tw_exit_coden`
(`SeqExec.v`, a derived `to_wexit` exit lemma, not ported here) and in the
FileSim, MmapSim and DrainSim proofs. -/
theorem land_255_small : ∀ c : word, bv_unsigned c < 256 → bv_and c (Z_to_bv 64 255) = c := by
  intro c hc
  have hc' : c.toNat < 256 := by
    unfold bv_unsigned at hc
    omega
  have h255 : (Z_to_bv 64 255 : word) = BitVec.ofNat 64 (2 ^ 8 - 1) := by
    apply BitVec.eq_of_toNat_eq
    rfl
  unfold bv_and
  rw [h255]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hm : (2 ^ 8 - 1) % 2 ^ 64 = 2 ^ 8 - 1 := by decide
  rw [hm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hc'

/-! ## Additions for ticket E-proof-library-2c: `step_lui_at` and `tw_write_ret`

Ported from the same Rocq file at the baseline the header names, with the
Rocq statements, for `Common/MuslCall.lean`.  `tw_write_ret` is stated over
`CatSim.to_wexit`, which is why this file imports `CatSim`.  Rocq's proof
of it rewrites the register indices with `arg_reg_0`, `arg_reg_1` and
`arg_reg_2` (`PropExec.v`, not ported); here the three index equalities are
closed by `decide`, as `WallSim.twl_write_rec` closes them. -/

open LinuxProcessSemantics.Common.CatSim

/-- `lui` with the writeback value named, as `step_addi_at` names it. -/
theorem step_lui_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Lui rd imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_lui (Z_shiftl (bv_signed imm) 12) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_lui segs regs pc mem rom w rd imm hf he hd, hrd, hv]
  rfl

/-- `CatSim.to_wexit`'s write node at the state `step_ecall` leaves: the
caller supplies the register facts and one continuation per delivered
length `n`. -/
theorem tw_write_ret (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = Z_to_bv 64 1)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom)
        bufs code) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (buf :: bufs) code := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  have E12 : (Z_to_bv 5 (10 + ((2 : Nat) : Int)) : reg) = 12 := by decide
  refine to_wexit.tw_write _ (getr regs 17) buf bufs code rfl H17 ?_ ?_ Hnb ?_
  · unfold ms_gpr
    rw [E10]
    exact H10
  · unfold ms_gpr
    rw [E11, E12]
    exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

end LinuxProcessSemantics.Common.SeqExec

/-! ## Additions for E-proof-library-2a (MmapSim)

Ported from `theories/Common/SeqExec.v` with the Rocq statements, for
ticket E-proof-library-2a, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file was read at 7ba58b45f (`nightly/09-28-2026`).

`Common/MmapSim.lean` reaches `N_to_le_bytes_1_small`, and the
`land_255_small` that ticket E-proof-library-2c's section above
declares. -/

namespace LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-- Collapse the singleton `word_to_le_bytes` list to the literal byte. -/
theorem N_to_le_bytes_1_small (v : word) :
    word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)] := rfl

/-! ## Additions for ticket E-grep_args_ns (SeqExec)

Ports the rest of `theories/Common/SeqExec.v` at
f44244ad6b8041aa83053d9ca91e090037ed743b (byte-identical to the header's
2cde689f94c0 baseline), with the Rocq statements, in Rocq order.
Rocq's `Z` is `Int`, width `N` is `Nat`, `Z.pow` with an integer exponent
is `Z_pow`, `Z.land`/`Z.lor` are `Z_land`/`Z_lor`, and `firstn` is `List.take`.

The `PropExec` value definitions these lemmas need are appended to
`PropExec.lean` in the same change.

The register tactics mirror Rocq's ordered rewrites; Lean's `decide`
closes their concrete five-bit register inequalities without searching
unrelated hypotheses. Like Rocq's resolvers, they may leave a rewritten
goal open, so the negative tests check failure to close with `rfl` too.
-/

open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim

theorem step_auipc_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Auipc rd imm, 4))
    (hrd : bv_eqb rd 0 = false) (hv : v_auipc pc (Z_shiftl (bv_signed imm) 12) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_auipc segs regs pc mem rom w rd imm hf he hd, hrd, hv]
  rfl

theorem step_addiw_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm32 rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_addiw (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : sext 64 (alu32 .ALU_ADD (low32 x) (sext 32 imm)) =
      v_addiw x (bv_signed imm) := by
    change sext 64 (low32 x + sext 32 imm) = _
    rw [sext_eq, bv_signed_swrap, bv_unsigned_add, sext_eq, Z_to_bv_unsigned]
    have hx : bv_unsigned (low32 x) = bv_wrap 32 (bv_unsigned x) := by
      simp only [low32, bv_unsigned, bv_extract, BitVec.extractLsb'_toNat,
        Nat.shiftRight_zero, bv_wrap, Int.natCast_emod, Int.natCast_pow]
      rfl
    rw [hx]
    unfold v_addiw bv_swrap bv_wrap
    simp only [Int.emod_add_emod, Int.add_emod_emod]
  rw [step_opimm32_gen segs regs pc mem rom w rd rs imm hf he hd, hb, hrd, hv]
  rfl

theorem step_sltiu_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_SLTU rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_sltiu (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_SLTU x (sext 64 imm) = v_sltiu x (bv_signed imm) := by
    have hi : bv_wrap 64 (bv_signed imm) = bv_unsigned (sext 64 imm) := by
      rw [sext_eq, Z_to_bv_unsigned]
    change (if c_ltu x (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0) = _
    rw [c_ltu_ltb, v_sltiu, hi]
  rw [step_opimm_gen segs regs pc mem rom w .ALU_SLTU rd rs imm hf he hd, hb, hrd, hv]
  rfl

theorem step_xori_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_XOR rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_xori (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_XOR x (sext 64 imm) = v_xori x (bv_signed imm) := by
    have hi : bv_wrap 64 (bv_signed imm) = bv_unsigned (sext 64 imm) := by
      rw [sext_eq, Z_to_bv_unsigned]
    unfold v_xori
    rw [hi]
    apply BitVec.eq_of_toNat_eq
    simp only [alu64, bv_unsigned, Z_lxor, Z_to_bv,
      BitVec.toNat_ofInt]
    exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt (sext 64 imm).isLt)).symm
  rw [step_opimm_gen segs regs pc mem rom w .ALU_XOR rd rs imm hf he hd, hb, hrd, hv]
  rfl

theorem step_mul_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MUL rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_mul (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x y : word) : mul_div .M_MUL x y = v_mul x y := by
    apply BitVec.eq_of_toNat_eq
    simp only [mul_div, v_mul, bv_unsigned, Z_to_bv, BitVec.toNat_mul,
      BitVec.toNat_ofInt, ← Int.natCast_mul, ← Int.natCast_emod, Int.toNat_natCast]
  rw [step_mul_gen segs regs pc mem rom w .M_MUL rd rs1 rs2 hf he hd, hb, hrd, hv]
  rfl

theorem step_andi_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_AND rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_andi (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_AND x (sext 64 imm) = v_andi x (bv_signed imm) := by
    have hi : bv_wrap 64 (bv_signed imm) = bv_unsigned (sext 64 imm) := by
      rw [sext_eq, Z_to_bv_unsigned]
    unfold v_andi
    rw [hi]
    apply BitVec.eq_of_toNat_eq
    simp only [alu64, bv_unsigned, Z_land, Z_to_bv, BitVec.toNat_ofInt]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left x.isLt)).symm
  rw [step_opimm_gen segs regs pc mem rom w .ALU_AND rd rs imm hf he hd, hb, hrd, hv]
  rfl

theorem step_ori_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_OR rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_ori (getr regs rs) (bv_signed imm) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_OR x (sext 64 imm) = v_ori x (bv_signed imm) := by
    have hi : bv_wrap 64 (bv_signed imm) = bv_unsigned (sext 64 imm) := by
      rw [sext_eq, Z_to_bv_unsigned]
    unfold v_ori
    rw [hi]
    apply BitVec.eq_of_toNat_eq
    simp only [alu64, bv_unsigned, Z_lor, Z_to_bv, BitVec.toNat_ofInt]
    exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.isLt (sext 64 imm).isLt)).symm
  rw [step_opimm_gen segs regs pc mem rom w .ALU_OR rd rs imm hf he hd, hb, hrd, hv]
  rfl

theorem step_slli_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SLL rd rs sh, 4))
    (hrd : bv_eqb rd 0 = false) (hv : v_slli (getr regs rs) (bv_unsigned sh) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_slli segs regs pc mem rom w rd rs sh hf he hd, hrd, hv]
  rfl

theorem step_srli_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SRL rd rs sh, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_srli (getr regs rs) (bv_unsigned sh) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_SRL x (zext 64 sh) = v_srli x (bv_unsigned sh) := by
    have hm : (bv_and (zext 64 sh) (Z_to_bv 64 63)).toNat = sh.toNat := by
      have h := shamt6_mask sh
      unfold bv_unsigned at h
      omega
    have hs (z : Int) (n : Nat) : Z_shiftl z (-(n : Int)) = z >>> n := by
      cases n with
      | zero => simp only [Int.natCast_zero, Int.neg_zero, Z_shiftl, Int.shiftLeft_zero,
          Int.shiftRight_zero]
      | succ n => rfl
    change x >>> (bv_and (zext 64 sh) (Z_to_bv 64 63)).toNat = _
    rw [hm]
    unfold v_srli bv_unsigned
    rw [hs, ← Int.natCast_shiftRight]
    apply BitVec.eq_of_toNat_eq
    simp only [Z_to_bv, BitVec.toNat_ofInt, BitVec.toNat_ushiftRight]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)).symm
  rw [step_shiftimm_gen segs regs pc mem rom w .ALU_SRL rd rs sh hf he hd, hb, hrd, hv]
  rfl

theorem step_srai_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SRA rd rs sh, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_srai (getr regs rs) (bv_unsigned sh) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hb (x : word) : alu64 .ALU_SRA x (zext 64 sh) = v_srai x (bv_unsigned sh) := by
    have hm : (bv_and (zext 64 sh) (Z_to_bv 64 63)).toNat = sh.toNat := by
      have h := shamt6_mask sh
      unfold bv_unsigned at h
      omega
    have hs (z : Int) (n : Nat) : Z_shiftl z (-(n : Int)) = z >>> n := by
      cases n with
      | zero => simp only [Int.natCast_zero, Int.neg_zero, Z_shiftl, Int.shiftLeft_zero,
          Int.shiftRight_zero]
      | succ n => rfl
    change x.sshiftRight (bv_and (zext 64 sh) (Z_to_bv 64 63)).toNat = _
    rw [hm, BitVec.sshiftRight_eq]
    unfold v_srai bv_unsigned bv_signed Z_to_bv
    rw [hs]
  rw [step_shiftimm_gen segs regs pc mem rom w .ALU_SRA rd rs sh hf he hd, hb, hrd, hv]
  rfl

theorem v_addiw_small (x : word) (imm : Int) (hlo : 0 ≤ bv_unsigned x + imm)
    (hhi : bv_unsigned x + imm < 2 ^ 31) (_himm : 0 ≤ imm) :
    bv_unsigned (v_addiw x imm) = bv_unsigned x + imm := by
  unfold v_addiw
  have hs : bv_swrap 32 (bv_unsigned x + imm) = bv_unsigned x + imm := by
    unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
    rw [show (2 : Int) ^ 32 / 2 = 2 ^ 31 by decide,
      Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [Z_to_bv_unsigned, hs, bv_wrap64_mod]
  exact Int.emod_eq_of_lt hlo (by omega)

theorem v_addiw_id (x : word) (hx : bv_unsigned x < 2 ^ 31) : v_addiw x 0 = x := by
  apply bv_eq_of_unsigned
  rw [v_addiw_small x 0 (by have := u64_range x; omega) (by omega) (by omega)]
  omega

theorem tw_exit_coden (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (c : word)
    (h17 : bv_unsigned (getr regs 17) = 93) (h10 : reg_get regs 10 = c)
    (hc : bv_unsigned c < 256) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } [] c := by
  have hg : bv_and (ms_gpr
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } 0)
      (Z_to_bv 64 255) = c := by
    unfold ms_gpr
    rw [show (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 by decide, h10]
    exact land_255_small c hc
  rw [← hg]
  exact to_wexit.tw_exit _ _ rfl (Or.inl h17)

/-- Twin of Rocq's `reg_neq_tac`: close an inequality of concrete register
literals. `decide` computes only the goal's five-bit equality. -/
macro "reg_neq_tac" : tactic => `(tactic| (intro h; exact absurd h (by decide)))

/-- Twin of Rocq's `getr_resolve`: rewrite lookups through a register-update
chain, then resolve x0 and nonzero base-register lookups. Side conditions
must be concrete register inequalities, closed by `reg_neq_tac`. -/
macro "getr_resolve" : tactic => `(tactic| (
  (repeat first
    | (focus (rewrite [getr_same]; rotate_left; reg_neq_tac))
    | (focus (rewrite [getr_other]; rotate_left; reg_neq_tac)));
  (repeat rewrite [getr_zero]);
  (repeat (focus (rewrite [getr_nz]; rotate_left; reg_neq_tac)))))

/-- Twin of Rocq's `regupd_resolve`: rewrite `reg_get` through a chain of
updates, using the matching update or skipping provably distinct literals. -/
macro "regupd_resolve" : tactic => `(tactic|
  repeat first
    | rewrite [regupd_same]
    | (focus (rewrite [regupd_other]; rotate_left; reg_neq_tac)))

example : (8 : reg) ≠ 9 := by reg_neq_tac
example : (8 : reg) = 8 := by
  fail_if_success have : (8 : reg) ≠ 8 := by reg_neq_tac
  rfl
example (regs : bvmap 5 word) (v : word) :
    getr (regupd (regupd regs 8 v) 9 v) 8 = v := by getr_resolve; with_reducible rfl
-- `with_reducible`: both goals below close by plain `rfl` with no rewrite at
-- all, so only a reducible `rfl` makes them test the `getr_zero` and
-- `getr_nz` steps.
example (regs : bvmap 5 word) (v : word) :
    getr (regupd regs 8 v) 0 = Z_to_bv 64 0 := by getr_resolve; with_reducible rfl
example (regs : bvmap 5 word) : getr regs 8 = reg_get regs 8 := by
  getr_resolve; with_reducible rfl
example (regs : bvmap 5 word) (v : word) (r s : reg) (h : s = r) (hn : r ≠ 0) :
    getr (regupd regs r v) s = v := by
  fail_if_success solve | getr_resolve; rfl
  subst s
  exact getr_same regs r v hn
-- The side condition holds, but only by a hypothesis: like Rocq's, the
-- tactic proves register inequalities by computation and never from context.
example (regs : bvmap 5 word) (v : word) (r s : reg) (h : s ≠ r) :
    getr (regupd regs r v) s = getr regs s := by
  fail_if_success solve | getr_resolve; with_reducible rfl
  exact getr_other regs r v s h
example (regs : bvmap 5 word) (v : word) :
    reg_get (regupd (regupd regs 8 v) 9 v) 8 = v := by regupd_resolve; with_reducible rfl
example (regs : bvmap 5 word) (v : word) (r s : reg) (h : s = r) :
    reg_get (regupd regs r v) s = v := by
  fail_if_success solve | regupd_resolve; rfl
  subst s
  exact regupd_same regs r v
example (regs : bvmap 5 word) (v : word) (r s : reg) (h : s ≠ r) :
    reg_get (regupd regs r v) s = reg_get regs s := by
  fail_if_success solve | regupd_resolve; with_reducible rfl
  exact regupd_other regs r v s h
-- The keywords are not reserved tokens: the names still parse as identifiers.
example (reg_neq_tac getr_resolve regupd_resolve : Nat)
    (h : reg_neq_tac + getr_resolve + regupd_resolve = 0) : reg_neq_tac = 0 := by
  omega

def v_divu (x y : word) : word := Z_to_bv 64 (bv_unsigned x / bv_unsigned y)
def v_remu (x y : word) : word := Z_to_bv 64 (bv_unsigned x % bv_unsigned y)

theorem m_divu (a b : word) (hb : bv_unsigned b ≠ 0) :
    mul_div .M_DIVU a b = v_divu a b := by
  have hn : b.toNat ≠ 0 := by unfold bv_unsigned at hb; omega
  simp only [mul_div, hn, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [bv_divu, v_divu, Z_to_bv, bv_unsigned,
    BitVec.toNat_ofInt]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)).symm

theorem m_remu (a b : word) (hb : bv_unsigned b ≠ 0) :
    mul_div .M_REMU a b = v_remu a b := by
  have hn : b.toNat ≠ 0 := by unfold bv_unsigned at hb; omega
  simp only [mul_div, hn, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [bv_modu, v_remu, Z_to_bv, bv_unsigned,
    BitVec.toNat_ofInt]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by omega)) b.isLt)).symm

theorem step_divu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_DIVU rd rs1 rs2, 4))
    (hnz : bv_unsigned (getr regs rs2) ≠ 0) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_DIVU rd rs1 rs2 hf he hd,
    m_divu _ _ hnz]

theorem step_remu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_REMU rd rs1 rs2, 4))
    (hnz : bv_unsigned (getr regs rs2) ≠ 0) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_REMU rd rs1 rs2 hf he hd,
    m_remu _ _ hnz]

theorem step_lw_zero (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Load .SZ4 true rd rs imm, 4))
    (hrd : bv_eqb rd 0 = false)
    (hr : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 =
      some [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom) := by
  have hv : sext 64 (bv_extract 0 32 (le_bytes_to_word
      [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0])) = Z_to_bv 64 0 := by decide
  step_pipeline hf he hd
  refine interp_load segs 32 _ [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0] _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 4 = _
    rw [rget_mk, b_addsext, ov_rdn]
    exact hr
  · show eff.EDone (rset rd (sext 64 (bv_extract 0 32 (le_bytes_to_word _)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [hv, npc4, rset_mk, hrd]
    rfl

theorem step_sb256 (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ1 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 1 (getr regs rs2))) rom) :=
  step_sb segs regs pc mem rom w rs1 rs2 imm hf he hd hok

theorem Zmod_pow2_div8 (z m : Int) (hm : 8 ≤ m) :
    z % Z_pow 2 m / 2 ^ 8 = (z / 2 ^ 8) % Z_pow 2 (m - 8) := by
  have hp : ∀ k : Int, 0 ≤ k → Z_pow 2 k = 2 ^ k.toNat := by
    intro k hk
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rfl
  rw [hp m (by omega), hp (m - 8) (by omega)]
  have hm' : m.toNat = (m - 8).toNat + 8 := by omega
  conv => lhs; rw [hm', Int.pow_add]
  change z % (2 ^ (m - 8).toNat * 256) / 256 = (z / 256) % 2 ^ (m - 8).toNat
  have hPpos : 0 < (2 : Int) ^ (m - 8).toNat := Int.pow_pos (by decide)
  generalize (2 : Int) ^ (m - 8).toNat = P at hPpos ⊢
  have hz := Int.emod_add_mul_ediv z 256
  have hr0 := Int.emod_nonneg z (show (256 : Int) ≠ 0 by decide)
  have hr1 := Int.emod_lt_of_pos z (show (0 : Int) < 256 by decide)
  have hq := Int.emod_add_mul_ediv (z / 256) P
  have ht0 := Int.emod_nonneg (z / 256) (Int.ne_of_gt hPpos)
  have ht1 := Int.emod_lt_of_pos (z / 256) hPpos
  generalize z % 256 = r at hz hr0 hr1
  generalize z / 256 = q at hz hq ht0 ht1 ⊢
  generalize q % P = t at hq ht0 ht1 ⊢
  generalize q / P = s at hq
  have hmod : z % (P * 256) = r + 256 * t := by
    have hu := (Int.ediv_emod_unique (a := z) (b := P * 256) (r := r + 256 * t) (q := s)
      (by omega)).2
    refine (hu ⟨?_, by omega, ?_⟩).2
    · rw [Int.mul_right_comm P 256 s]
      omega
    · have hmul := Int.mul_le_mul_of_nonneg_right (show t + 1 ≤ P by omega)
        (show (0 : Int) ≤ 256 by decide)
      omega
  rw [hmod]
  omega

theorem Z_to_le_bytes_wrap (n m : Nat) (z : Int) (hm : 8 * (n : Int) ≤ (m : Int)) :
    Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z := by
  induction n generalizing m z with
  | zero => rfl
  | succ n ih =>
    have h8 : 8 ≤ m := by omega
    simp only [Z_to_le_bytes]
    congr 1
    · apply bv_eq_of_unsigned
      simp only [Z_to_bv_unsigned, bv_wrap]
      apply Int.emod_emod_of_dvd
      refine ⟨2 ^ (m - 8), ?_⟩
      rw [← Int.pow_add]
      congr 1
      omega
    · have hs : (bv_wrap m z) >>> 8 = bv_wrap (m - 8) (z >>> 8) := by
        simp only [bv_wrap, Int.shiftRight_eq_div_pow]
        have h := Zmod_pow2_div8 z (m : Int) (by omega)
        have he : (m : Int) - 8 = ((m - 8 : Nat) : Int) := by omega
        rw [he] at h
        exact h
      rw [hs]
      exact ih (m - 8) (z >>> 8) (by omega)

theorem store_bytes_low16 (u : word) :
    Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u := by
  have he : bv_unsigned (bv_extract 0 16 u) = bv_wrap 16 (bv_unsigned u) := by
    simp only [bv_unsigned, bv_extract, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      bv_wrap, Int.natCast_emod, Int.natCast_pow]
    rfl
  rw [he]
  exact Z_to_le_bytes_wrap 2 16 (bv_unsigned u) (by decide)

theorem store_bytes_low32 (u : word) :
    Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u := by
  have he : bv_unsigned (low32 u) = bv_wrap 32 (bv_unsigned u) := by
    simp only [low32, bv_unsigned, bv_extract, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      bv_wrap, Int.natCast_emod, Int.natCast_pow]
    rfl
  rw [he]
  exact Z_to_le_bytes_wrap 4 32 (bv_unsigned u) (by decide)

theorem step_sw_val (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ4 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 4 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 4 (getr regs rs2))) rom) := by
  step_pipeline hf he hd
  show interp_eff segs
    (.EStore 32 (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (.EDone (inval_resv (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
        (core.Core regs bvmap_empty (pc + 4) 0 none)))) mem = _
  simp only [rget_mk, b_addsext, npc4]
  rw [interp_store segs 32 _ _ _ mem hok, write_to_mem_wbytes]
  show MachineOk (_, wbytes mem _ (Z_to_le_bytes 4 _)) = _
  rw [store_bytes_low32]
  rfl

theorem step_sw_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word) (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ4 rs1 rs2 imm, 4))
    (ha : v_addi (getr regs rs1) (bv_signed imm) = a) (hv : getr regs rs2 = v)
    (hok : store_ok segs mem a 4 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom) := by
  rw [step_sw_val segs regs pc mem rom w rs1 rs2 imm hf he hd
    (by rw [ha]; exact hok), ha, hv]

theorem step_sh_val (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ2 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 2 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 2 (getr regs rs2))) rom) := by
  step_pipeline hf he hd
  show interp_eff segs
    (.EStore 16 (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
      (bv_extract 0 16 (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (.EDone (inval_resv (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
        (core.Core regs bvmap_empty (pc + 4) 0 none)))) mem = _
  simp only [rget_mk, b_addsext, npc4]
  rw [interp_store segs 16 _ _ _ mem hok, write_to_mem_wbytes]
  show MachineOk (_, wbytes mem _ (Z_to_le_bytes 2 _)) = _
  rw [store_bytes_low16]
  rfl

theorem step_sh_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word) (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ2 rs1 rs2 imm, 4))
    (ha : v_addi (getr regs rs1) (bv_signed imm) = a) (hv : getr regs rs2 = v)
    (hok : store_ok segs mem a 2 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom) := by
  rw [step_sh_val segs regs pc mem rom w rs1 rs2 imm hf he hd
    (by rw [ha]; exact hok), ha, hv]

theorem v_divu_small (x y : word) (hy : 0 < bv_unsigned y) :
    bv_unsigned (v_divu x y) = bv_unsigned x / bv_unsigned y := by
  rw [v_divu, Z_to_bv_unsigned, bv_wrap64_mod]
  have hx := u64_range x
  apply Int.emod_eq_of_lt (Int.ediv_nonneg hx.1 (by omega))
  exact Int.lt_of_le_of_lt (Int.ediv_le_self _ hx.1) hx.2

theorem v_remu_small (x y : word) (hy : 0 < bv_unsigned y) :
    bv_unsigned (v_remu x y) = bv_unsigned x % bv_unsigned y := by
  rw [v_remu, Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt (Int.emod_nonneg _ (by omega))
    (Int.lt_trans (Int.emod_lt_of_pos _ hy) (u64_range y).2)

theorem v_subw_small (x y : word) (hle : bv_unsigned y ≤ bv_unsigned x)
    (hlt : bv_unsigned x - bv_unsigned y < 2 ^ 31) :
    bv_unsigned (v_subw x y) = bv_unsigned x - bv_unsigned y := by
  unfold v_subw
  have hs : bv_swrap 32 (bv_unsigned x - bv_unsigned y) = bv_unsigned x - bv_unsigned y := by
    unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
    rw [show (2 : Int) ^ 32 / 2 = 2 ^ 31 by decide,
      Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [Z_to_bv_unsigned, hs, bv_wrap64_mod]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem land_d48 (d : Int) (h0 : 0 ≤ d) (h : d < 16) : Z_land d 48 = 0 := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;> subst d <;> decide

theorem lor_small_add (d : Int) (h0 : 0 ≤ d) (h : d < 16) : Z_lor d 48 = d + 48 := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;> subst d <;> decide

theorem v_ori_lor (d : word) (hd : bv_unsigned d < 16) :
    v_ori d 48 = Z_to_bv 64 (bv_unsigned d + 48) := by
  unfold v_ori
  rw [show bv_wrap 64 48 = 48 by decide, lor_small_add _ (u64_range d).1 hd]

theorem rdn_app (segs : List Segment) (mem : word → Option byte) (n1 n2 : Nat)
    (a : word) (bs1 bs2 : List byte) (h1 : rdn segs mem a n1 = some bs1)
    (h2 : rdn segs mem (a + nat_to_word n1) n2 = some bs2) :
    rdn segs mem a (n1 + n2) = some (bs1 ++ bs2) := by
  induction n1 generalizing a bs1 with
  | zero =>
    cases h1
    rw [word_add_0] at h2
    simpa only [Nat.zero_add, List.nil_append] using h2
  | succ n1 ih =>
    unfold rdn at h1
    split at h1
    · rename_i b hb
      split at h1
      · rename_i rest hr
        cases h1
        have ht : a + 1 + nat_to_word n1 = a + nat_to_word (n1 + 1) := by
          rw [word1_nat, nat_to_word_add_merge, Nat.add_comm 1 n1]
        have hrec := ih (a + 1) rest hr (by rw [ht]; exact h2)
        simp only [Nat.succ_add, rdn, hb, hrec, List.cons_append]
      · cases h1
    · cases h1

theorem rdn_firstn (segs : List Segment) (mem : word → Option byte) (n : Nat)
    (a : word) (bs : List byte) (k : Nat) (h : rdn segs mem a n = some bs)
    (hk : k ≤ n) : rdn segs mem a k = some (bs.take k) := by
  induction n generalizing a bs k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    unfold rdn at h
    split at h
    · rename_i b hb
      split at h
      · rename_i rest hr
        cases h
        cases k with
        | zero => rfl
        | succ k =>
          simp only [rdn, hb, List.take_succ_cons, ih (a + 1) rest k hr (by omega)]
      · cases h
    · cases h

end LinuxProcessSemantics.Common.SeqExec
