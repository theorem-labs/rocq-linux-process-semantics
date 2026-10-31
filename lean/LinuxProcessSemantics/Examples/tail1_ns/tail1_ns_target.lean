import LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs
import LinuxProcessSemantics.Common.ListFacts
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/
/-! # tail1-ns, target binary (Zig ReleaseSmall, raw syscalls).

PROOF-SIDE FILE (not part of the trusted specification).

The target keeps everything in registers: a1 = rb, t0 = cur,
a6 = done, a3 = cur_n, a4 = done_n, a5 = 10. The loop head is
0x10011d4 (li a7,63 ; li a2,1024 ; li a0,0 ; ecall). A '\n' copies
cur into done with a pointer loop at 0x1001210 and appends the
newline; a long line exits 3 via 0x100125c; EOF writes the last line
with the helper at 0x10012b4 and exits 0 through 0x1001260.

Counts/indices are `nat_to_word`, walking pointers
are `base + nat_to_word j`, sp slots `Z_to_bv 64 (bv_unsigned tsp - k)`.

Every step simp of a non-`ecall` instruction also rewrites `!decide True`
(`decide_true`, `Bool.not_true`), so that the step's left side is headed by the
instruction's match rather than by `ite`.
Left as an `ite`, nanoda (nanoda_lib `4c544ed4099c8227f07d5de77ad1e69fb0740a27`) unfolds
`sym_exec` first and compares the match alternatives under their binders, where its
`try_reduce_nat` (`src/tc.rs`) refuses every term with a free variable, so the `% 2 ^ 64` of a
branch target runs through unary `Nat.modCore`. -/

namespace LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.DrainSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.ListFacts
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.tail1_ns.TargetMemImage
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_code
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs

def t_rb : word := 0x10022ec
def t_cur : word := 0x10026ec
def t_done : word := 0x10036ec

theorem u_t_rb : bv_unsigned t_rb = 0x10022ec := by decide
theorem u_t_cur : bv_unsigned t_cur = 0x10026ec := by decide
theorem u_t_done : bv_unsigned t_done = 0x10036ec := by decide

/-- Collapse `bv_unsigned` of the buffer bases, `base + nat_to_word j`
offsets and canonical sp-relative addresses to plain `Int`. -/
local macro "unormT" : tactic => `(tactic| (
  imm_norm
  have := u_t_rb
  have := u_t_cur
  have := u_t_done
  repeat rewrite [word_add_nat]
  repeat (focus (rewrite [u_Z2bv]; rotate_left <;>
    (try simp only [u_t_rb, u_t_cur, u_t_done]); omega; omega))
  try simp only [u_t_rb, u_t_cur, u_t_done]))

/- Spelling bridges between the reflective executor and the tactic
layer's memory lemmas.

The executor writes an address as `Z_to_bv 64 (bv_unsigned b + k)`
(the `saddr` normal form) and a stored byte as
`word_to_le_bytes 1 v`; the read-back lemmas are stated over the
base word and a singleton byte list. These three collapse the
difference, once, instead of a `replace` per access. -/
theorem u0_id (x : word) : Z_to_bv 64 (bv_unsigned x + 0) = x := by
  rw [Int.add_zero]
  apply bv_eq_of_unsigned
  exact u_Z2bv _ (u64_range x).1 (u64_range x).2

theorem wle1_byte (b : byte) :
    word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b] := by
  have hb := u8_range b
  rw [N_to_le_bytes_1_small, u_Z2bv _ (by omega) (by omega)]
  congr 1
  simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zext_byte_u (b : byte) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b := by
  have hb := u8_range b
  apply u_Z2bv <;> omega

/-- A buffer base held in a register as a LITERAL, indexed by a
`nat_to_word`: the executor's `saddr` normal form puts the literal in
the offset, the read-back lemmas put it in the base. -/
theorem addr_base_ntw (base : word) (z : Int) (n : Nat)
    (Hb : bv_unsigned base = z) (Hn : (n : Int) < 2 ^ 64) :
    Z_to_bv 64 (bv_unsigned (nat_to_word n) + z) = base + nat_to_word n := by
  rw [word_add_nat]
  congr 1
  rw [u_ntw n Hn]
  omega

/-- A register-register shift by a literal amount: the executor spells
every shift as the register form, the library's division lemma is
stated for the immediate form. -/
theorem v_srl_lit (x : word) (sh : Int) (Hsh : 0 ≤ sh ∧ sh < 64) :
    v_srl x (Z_to_bv 64 sh) = v_srli x sh := by
  unfold v_srl v_srli
  rw [u_Z2bv sh (by omega) (by omega), Int.emod_eq_of_lt Hsh.1 Hsh.2]

/-- The target's "is this line already 4096 bytes long" test, compiled as
`srli t1,a3,0xc ; bnez t1`. -/
local macro "srli_test" : tactic => `(tactic| (
  rewrite [bv_eqb_Z, v_srl_lit _ 12 (by omega)]
  focus (rewrite [v_srli_div]; rotate_left; omega)
  focus (rewrite [u_ntw]; rotate_left; omega)
  change decide (_ = (0 : Int)) = _))

/-- Resolve an `x0` read before closing a bitvector goal. Lean's `bveq`
tries only `rfl` on an open goal without unassigned metavariables and
reports `OPEN` if conversion fails (Common/StepTac.lean). -/
theorem getr_x0z (rs : bvmap 5 word) : getr rs 0 = Z_to_bv 64 0 := by rfl

/-- Collapse every `bv_unsigned` of a counter or literal to `Int`. -/
local macro "lenlia" : tactic => `(tactic| (
  try dsimp only [List.length_cons, List.length_nil] at *
  omega))
local macro "lennorm" : tactic => `(tactic| (
  try dsimp only [List.length_cons, List.length_nil] at *
  try omega))
local macro "numnorm" : tactic => `(tactic| (
  repeat (focus (rewrite [u_ntw]; rotate_left; lennorm))
  repeat (focus (
    rewrite [u_Z2bv]
    all_goals repeat (focus (rewrite [u_ntw]; rotate_left; lennorm))
    all_goals lennorm))
  try dsimp only [List.length_cons, List.length_nil] at *))

/-- The generic `SCBr` closer: push the comparison down to `Int` and hand
it to `omega`. The `rfl` alternative closes a branch whose operands
the pins made literal. -/
local macro "scbr" : tactic => `(tactic| first
  | rfl
  | (repeat with_reducible rewrite [Bool.not_eq_true']
     repeat with_reducible rewrite [Bool.not_eq_false']
     repeat first | rewrite [bv_lts_signed] | rewrite [bv_ltu_Z] | rewrite [bv_eqb_Z]
     repeat (focus (rewrite [bv_signed_small]; rotate_left; numnorm; omega))
     numnorm
     first | apply decide_eq_true | apply decide_eq_false
     omega))

/-- Closers for the two obligation shapes a counting loop leaves. -/
-- An `addi rd,rs,1` on a `nat_to_word` counter.
local macro "ntw_succ" : tactic => `(tactic| (
  change Z_to_bv 64 (bv_unsigned (nat_to_word _) + (1 : Int)) = nat_to_word _
  apply bv_eq_of_unsigned
  rewrite [u_Z2bv _ (by rewrite [u_ntw _ (by omega)]; omega)
    (by rewrite [u_ntw _ (by omega)]; omega)]
  repeat rewrite [u_ntw _ (by omega)]
  omega))

/- A `beq`/`bne` between two `nat_to_word` counters, possibly with a
literal displacement. -/
local macro "brz" : tactic => `(tactic| (
  repeat with_reducible rewrite [Bool.not_eq_true']
  repeat with_reducible rewrite [Bool.not_eq_false']
  rewrite [bv_eqb_Z]
  repeat rewrite [u_Z2bv _
    (by repeat rewrite [u_ntw _ (by omega)]; omega)
    (by repeat rewrite [u_ntw _ (by omega)]; omega)]
  repeat rewrite [u_ntw _ (by omega)]
  first | apply decide_eq_true | apply decide_eq_false
  omega))

/- A register the caller pinned as a LITERAL: the pin obligation is
stated against `Z_to_bv 64 z` and the caller's hypothesis against the
numeral the example gave the constant. -/
local macro "pin_lit " c:term : tactic => `(tactic| (
  conv => rhs; change $c))

/-- `sym_sc_auto` closes an `SCFlat` by `omega` once the address's base is
bounded; a buffer base plus an index is an opaque atom until the
range fact is posed. -/
local macro "scflat" : tactic => `(tactic| (
  repeat rewrite [u_ntw _ (by omega)]
  unormT
  run_tac Lean.Elab.Tactic.withMainContext do
    let xs ← IO.mkRef (#[] : Array Lean.Expr)
    let _ ← Lean.Meta.transform (← Lean.Elab.Tactic.getMainTarget) (pre := fun e => do
      if e.isAppOfArity ``bv_unsigned 2 then
        let x := e.appArg!
        if ← Lean.Meta.isDefEq (← Lean.Meta.inferType x) (Lean.mkConst ``word) then
          xs.modify (·.push x)
      return .continue)
    for x in ← xs.get do
      Lean.Elab.Tactic.withMainContext do
        let proof ← Lean.Meta.mkAppM ``u64_range #[x]
        let ty ← Lean.Meta.inferType proof
        let mut found := false
        for h in ← Lean.getLCtx do
          if ← Lean.Meta.isDefEq h.type ty then found := true
        unless found do
          let g ← Lean.Elab.Tactic.getMainGoal
          let g ← g.assert (← Lean.Core.mkFreshUserName `range) ty proof
          let (_, g) ← g.intro1P
          Lean.Elab.Tactic.replaceMainGoal [g]
  repeat' apply And.intro
  all_goals omega))

/-- The scripts obtain the block's `msteps` hypothesis from `sym_exec_ex`.
Normalize that hypothesis: unfold the valuation, put the
log's addresses into the tactic layer's spelling, and collapse the
one-byte stores. -/
local macro "hms_norm " H:ident : tactic => `(tactic| (
  try simp only [adenot_var, adenot_lit, bdenot_var, bdenot_lit,
    edenot_lit, edenot_var] at $H:ident
  try simp only [Eplus, Nat.blt, Nat.ble, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, Bool.false_eq_true, ite_true, ite_false,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    List.append_nil, List.cons_append, List.nil_append, Prod.fst, Prod.snd,
    saddr.a_base, saddr.a_off, sentry.e_addr, sentry.e_width, sentry.e_val] at $H:ident
  try simp only [u0_id, wle1_byte] at $H:ident))

/-! Each `tail1_TF_` lemma states the fetch of its generated `TF_` twin, proved
through `tail1_tgt_fetch` (see `tail1_hex_read`). -/

theorem tail1_TF_1001190 : fetch_word target_segs 0x1001190 = some 0xff010113 :=
  tail1_tgt_fetch 0x1001190 0x13 0x01 0x01 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001194 : fetch_word target_segs 0x1001194 = some 0x00113423 :=
  tail1_tgt_fetch 0x1001194 0x23 0x34 0x11 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001198 : fetch_word target_segs 0x1001198 = some 0x00000097 :=
  tail1_tgt_fetch 0x1001198 0x97 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100119c : fetch_word target_segs 0x100119c = some 0x010080e7 :=
  tail1_tgt_fetch 0x100119c 0xe7 0x80 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011a0 : fetch_word target_segs 0x10011a0 = some 0x05d00893 :=
  tail1_tgt_fetch 0x10011a0 0x93 0x08 0xd0 0x05 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011a4 : fetch_word target_segs 0x10011a4 = some 0x00000073 :=
  tail1_tgt_fetch 0x10011a4 0x73 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011a8 : fetch_word target_segs 0x10011a8 = some 0xff010113 :=
  tail1_tgt_fetch 0x10011a8 0x13 0x01 0x01 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011ac : fetch_word target_segs 0x10011ac = some 0x00113423 :=
  tail1_tgt_fetch 0x10011ac 0x23 0x34 0x11 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011b0 : fetch_word target_segs 0x10011b0 = some 0x00000713 :=
  tail1_tgt_fetch 0x10011b0 0x13 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011b4 : fetch_word target_segs 0x10011b4 = some 0x00000693 :=
  tail1_tgt_fetch 0x10011b4 0x93 0x06 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011b8 : fetch_word target_segs 0x10011b8 = some 0x010025b7 :=
  tail1_tgt_fetch 0x10011b8 0xb7 0x25 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011bc : fetch_word target_segs 0x10011bc = some 0x2ec58593 :=
  tail1_tgt_fetch 0x10011bc 0x93 0x85 0xc5 0x2e (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011c0 : fetch_word target_segs 0x10011c0 = some 0x00a00793 :=
  tail1_tgt_fetch 0x10011c0 0x93 0x07 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011c4 : fetch_word target_segs 0x10011c4 = some 0x01003837 :=
  tail1_tgt_fetch 0x10011c4 0x37 0x38 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011c8 : fetch_word target_segs 0x10011c8 = some 0x6ec80813 :=
  tail1_tgt_fetch 0x10011c8 0x13 0x08 0xc8 0x6e (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011cc : fetch_word target_segs 0x10011cc = some 0x010022b7 :=
  tail1_tgt_fetch 0x10011cc 0xb7 0x22 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011d0 : fetch_word target_segs 0x10011d0 = some 0x6ec28293 :=
  tail1_tgt_fetch 0x10011d0 0x93 0x82 0xc2 0x6e (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011d4 : fetch_word target_segs 0x10011d4 = some 0x03f00893 :=
  tail1_tgt_fetch 0x10011d4 0x93 0x08 0xf0 0x03 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011d8 : fetch_word target_segs 0x10011d8 = some 0x40000613 :=
  tail1_tgt_fetch 0x10011d8 0x13 0x06 0x00 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011dc : fetch_word target_segs 0x10011dc = some 0x00000513 :=
  tail1_tgt_fetch 0x10011dc 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011e0 : fetch_word target_segs 0x10011e0 = some 0x00000073 :=
  tail1_tgt_fetch 0x10011e0 0x73 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011e4 : fetch_word target_segs 0x10011e4 = some 0x08054463 :=
  tail1_tgt_fetch 0x10011e4 0x63 0x44 0x05 0x08 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011e8 : fetch_word target_segs 0x10011e8 = some 0x08050663 :=
  tail1_tgt_fetch 0x10011e8 0x63 0x06 0x05 0x08 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011ec : fetch_word target_segs 0x10011ec = some 0x00000613 :=
  tail1_tgt_fetch 0x10011ec 0x13 0x06 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011f0 : fetch_word target_segs 0x10011f0 = some 0xfe0502e3 :=
  tail1_tgt_fetch 0x10011f0 0xe3 0x02 0x05 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011f4 : fetch_word target_segs 0x10011f4 = some 0x00c588b3 :=
  tail1_tgt_fetch 0x10011f4 0xb3 0x88 0xc5 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011f8 : fetch_word target_segs 0x10011f8 = some 0x0008c883 :=
  tail1_tgt_fetch 0x10011f8 0x83 0xc8 0x08 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10011fc : fetch_word target_segs 0x10011fc = some 0x04f89063 :=
  tail1_tgt_fetch 0x10011fc 0x63 0x90 0xf8 0x04 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001200 : fetch_word target_segs 0x1001200 = some 0x00028713 :=
  tail1_tgt_fetch 0x1001200 0x13 0x87 0x02 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001204 : fetch_word target_segs 0x1001204 = some 0x00080893 :=
  tail1_tgt_fetch 0x1001204 0x93 0x08 0x08 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001208 : fetch_word target_segs 0x1001208 = some 0x00068313 :=
  tail1_tgt_fetch 0x1001208 0x13 0x83 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100120c : fetch_word target_segs 0x100120c = some 0x00068e63 :=
  tail1_tgt_fetch 0x100120c 0x63 0x8e 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001210 : fetch_word target_segs 0x1001210 = some 0x00074383 :=
  tail1_tgt_fetch 0x1001210 0x83 0x43 0x07 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001214 : fetch_word target_segs 0x1001214 = some 0xfff30313 :=
  tail1_tgt_fetch 0x1001214 0x13 0x03 0xf3 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001218 : fetch_word target_segs 0x1001218 = some 0x00788023 :=
  tail1_tgt_fetch 0x1001218 0x23 0x80 0x78 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100121c : fetch_word target_segs 0x100121c = some 0x00188893 :=
  tail1_tgt_fetch 0x100121c 0x93 0x88 0x18 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001220 : fetch_word target_segs 0x1001220 = some 0x00170713 :=
  tail1_tgt_fetch 0x1001220 0x13 0x07 0x17 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001224 : fetch_word target_segs 0x1001224 = some 0xfe0316e3 :=
  tail1_tgt_fetch 0x1001224 0xe3 0x16 0x03 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001228 : fetch_word target_segs 0x1001228 = some 0x00d80733 :=
  tail1_tgt_fetch 0x1001228 0x33 0x07 0xd8 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100122c : fetch_word target_segs 0x100122c = some 0x00f70023 :=
  tail1_tgt_fetch 0x100122c 0x23 0x00 0xf7 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001230 : fetch_word target_segs 0x1001230 = some 0x00168713 :=
  tail1_tgt_fetch 0x1001230 0x13 0x87 0x16 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001234 : fetch_word target_segs 0x1001234 = some 0x00000693 :=
  tail1_tgt_fetch 0x1001234 0x93 0x06 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001238 : fetch_word target_segs 0x1001238 = some 0x0180006f :=
  tail1_tgt_fetch 0x1001238 0x6f 0x00 0x80 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100123c : fetch_word target_segs 0x100123c = some 0x00c6d313 :=
  tail1_tgt_fetch 0x100123c 0x13 0xd3 0xc6 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001240 : fetch_word target_segs 0x1001240 = some 0x00031e63 :=
  tail1_tgt_fetch 0x1001240 0x63 0x1e 0x03 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001244 : fetch_word target_segs 0x1001244 = some 0x00d28333 :=
  tail1_tgt_fetch 0x1001244 0x33 0x83 0xd2 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001248 : fetch_word target_segs 0x1001248 = some 0x00168693 :=
  tail1_tgt_fetch 0x1001248 0x93 0x86 0x16 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100124c : fetch_word target_segs 0x100124c = some 0x01130023 :=
  tail1_tgt_fetch 0x100124c 0x23 0x00 0x13 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001250 : fetch_word target_segs 0x1001250 = some 0x00160613 :=
  tail1_tgt_fetch 0x1001250 0x13 0x06 0x16 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001254 : fetch_word target_segs 0x1001254 = some 0xf8a600e3 :=
  tail1_tgt_fetch 0x1001254 0xe3 0x00 0xa6 0xf8 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001258 : fetch_word target_segs 0x1001258 = some 0xf9dff06f :=
  tail1_tgt_fetch 0x1001258 0x6f 0xf0 0xdf 0xf9 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100125c : fetch_word target_segs 0x100125c = some 0x00300513 :=
  tail1_tgt_fetch 0x100125c 0x13 0x05 0x30 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001260 : fetch_word target_segs 0x1001260 = some 0x00813083 :=
  tail1_tgt_fetch 0x1001260 0x83 0x30 0x81 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001264 : fetch_word target_segs 0x1001264 = some 0x01010113 :=
  tail1_tgt_fetch 0x1001264 0x13 0x01 0x01 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001268 : fetch_word target_segs 0x1001268 = some 0x00008067 :=
  tail1_tgt_fetch 0x1001268 0x67 0x80 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001274 : fetch_word target_segs 0x1001274 = some 0x00068a63 :=
  tail1_tgt_fetch 0x1001274 0x63 0x8a 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001278 : fetch_word target_segs 0x1001278 = some 0x01002537 :=
  tail1_tgt_fetch 0x1001278 0x37 0x25 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100127c : fetch_word target_segs 0x100127c = some 0x6ec50513 :=
  tail1_tgt_fetch 0x100127c 0x13 0x05 0xc5 0x6e (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001280 : fetch_word target_segs 0x1001280 = some 0x00068593 :=
  tail1_tgt_fetch 0x1001280 0x93 0x85 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001284 : fetch_word target_segs 0x1001284 = some 0x0140006f :=
  tail1_tgt_fetch 0x1001284 0x6f 0x00 0x40 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001288 : fetch_word target_segs 0x1001288 = some 0x02070263 :=
  tail1_tgt_fetch 0x1001288 0x63 0x02 0x07 0x02 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100128c : fetch_word target_segs 0x100128c = some 0x01003537 :=
  tail1_tgt_fetch 0x100128c 0x37 0x35 0x00 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001290 : fetch_word target_segs 0x1001290 = some 0x6ec50513 :=
  tail1_tgt_fetch 0x1001290 0x13 0x05 0xc5 0x6e (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001294 : fetch_word target_segs 0x1001294 = some 0x00070593 :=
  tail1_tgt_fetch 0x1001294 0x93 0x05 0x07 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_1001298 : fetch_word target_segs 0x1001298 = some 0x00000097 :=
  tail1_tgt_fetch 0x1001298 0x97 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_100129c : fetch_word target_segs 0x100129c = some 0x01c080e7 :=
  tail1_tgt_fetch 0x100129c 0xe7 0x80 0xc0 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012a0 : fetch_word target_segs 0x10012a0 = some 0x00a03533 :=
  tail1_tgt_fetch 0x10012a0 0x33 0x35 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012a4 : fetch_word target_segs 0x10012a4 = some 0x00251513 :=
  tail1_tgt_fetch 0x10012a4 0x13 0x15 0x25 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012a8 : fetch_word target_segs 0x10012a8 = some 0xfb9ff06f :=
  tail1_tgt_fetch 0x10012a8 0x6f 0xf0 0x9f 0xfb (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012ac : fetch_word target_segs 0x10012ac = some 0x00000513 :=
  tail1_tgt_fetch 0x10012ac 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012b0 : fetch_word target_segs 0x10012b0 = some 0xfb1ff06f :=
  tail1_tgt_fetch 0x10012b0 0x6f 0xf0 0x1f 0xfb (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012b4 : fetch_word target_segs 0x10012b4 = some 0x00058613 :=
  tail1_tgt_fetch 0x10012b4 0x13 0x86 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012b8 : fetch_word target_segs 0x10012b8 = some 0x00050593 :=
  tail1_tgt_fetch 0x10012b8 0x93 0x05 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012bc : fetch_word target_segs 0x10012bc = some 0x04000893 :=
  tail1_tgt_fetch 0x10012bc 0x93 0x08 0x00 0x04 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012c0 : fetch_word target_segs 0x10012c0 = some 0x00060e63 :=
  tail1_tgt_fetch 0x10012c0 0x63 0x0e 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012c4 : fetch_word target_segs 0x10012c4 = some 0x00100513 :=
  tail1_tgt_fetch 0x10012c4 0x13 0x05 0x10 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012c8 : fetch_word target_segs 0x10012c8 = some 0x00000073 :=
  tail1_tgt_fetch 0x10012c8 0x73 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012cc : fetch_word target_segs 0x10012cc = some 0x00a05c63 :=
  tail1_tgt_fetch 0x10012cc 0x63 0x5c 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012d0 : fetch_word target_segs 0x10012d0 = some 0x00a585b3 :=
  tail1_tgt_fetch 0x10012d0 0xb3 0x85 0xa5 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012d4 : fetch_word target_segs 0x10012d4 = some 0x40a60633 :=
  tail1_tgt_fetch 0x10012d4 0x33 0x06 0xa6 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012d8 : fetch_word target_segs 0x10012d8 = some 0xfe0616e3 :=
  tail1_tgt_fetch 0x10012d8 0xe3 0x16 0x06 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012dc : fetch_word target_segs 0x10012dc = some 0x00000513 :=
  tail1_tgt_fetch 0x10012dc 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_TF_10012e0 : fetch_word target_segs 0x10012e0 = some 0x00008067 :=
  tail1_tgt_fetch 0x10012e0 0x67 0x80 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

section TargetProof

variable (av ev : List (List byte))
variable (tsp : word)
/- The target run's own AT_RANDOM draw, independent of the source's
(the `ed_random` half of `Run.ExecEntry`'s `en_draw`; see the source file).
Named `arnd` like every other target section, and deliberately NOT after
the stack pointer beside it: this file calls that one `tsp` where the
other twelve call it `asp`, and one file naming the draw differently is
exactly what would let a reader — or a grep for a cross-role mix-up — miss one. -/
variable (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned tsp)
variable (Hsp_hi : bv_unsigned tsp ≤ sp_window_hi)
variable (uid hw : word)

include Hsp_lo in
theorem tsp_lo_num : 0x7fff80000000 ≤ bv_unsigned tsp := by exact Hsp_lo
include Hsp_hi in
theorem tsp_hi_num : bv_unsigned tsp ≤ 0x800000000000 := by exact Hsp_hi

def twmem : word → Option byte := wrap_mem target_phdrs tsp av ev uid hw arnd
def trom : word → Option byte := seg_rom target_segs

/- Background memory: _start's and main's ra slots over twmem, in
execution order. `tsp-8` = 0 ; `tsp-24` = 0x10011a0. -/
def tgt_bg : word → Option byte :=
  wbytes (wbytes (twmem av ev tsp arnd uid hw)
    (Z_to_bv 64 (bv_unsigned tsp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned tsp - 24)) (word_to_le_bytes 8 (0x10011a0 : word))

/-- `bgt_ok mem`: `mem` agrees with `tgt_bg` at or above `tsp-32`, and
is still writable wherever `twmem` was. The loop-head predicates
quantify `mem` existentially, so the `store_ok` bound the stack
stores need has to travel with it; `mem_grows` is the weakest thing
that carries it (the overlay only ever gains addresses).

The two clauses sit under ONE `∀`, and `bgt_ok` is SEALED
(`irreducible`, just below the preservation lemmas). Both are needed to
keep `repeat split` — which the scripts below use to establish the
loop-head predicates, of which `bgt_ok` is a conjunct — from taking
it apart into halves that none of the preservation lemmas match. -/
def bgt_ok (mem : word → Option byte) : Prop :=
  ∀ (a : word) (n : Nat),
    (bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
     bv_unsigned tsp - 32 ≤ bv_unsigned a →
     rdn target_segs mem a n = rdn target_segs (tgt_bg av ev tsp arnd uid hw) a n) ∧
    (twmem av ev tsp arnd uid hw a ≠ none → mem a ≠ none)

/-- The two projections; `bgt_grows` is what the store-bound dispatcher
reaches for (via `store_ok_db`), and both are the only way past the
seal below. -/
theorem bgt_agree_of (mem : word → Option byte)
    (H : bgt_ok av ev tsp arnd uid hw mem) (a : word) (n : Nat) :
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    bv_unsigned tsp - 32 ≤ bv_unsigned a →
    rdn target_segs mem a n = rdn target_segs (tgt_bg av ev tsp arnd uid hw) a n := by
  exact (H a n).1

theorem bgt_grows (mem : word → Option byte)
    (H : bgt_ok av ev tsp arnd uid hw mem) :
    mem_grows (twmem av ev tsp arnd uid hw) mem := by
  intro x
  exact (H x 0).2

local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply bgt_grows; assumption))

theorem bgt_ok_bg : bgt_ok av ev tsp arnd uid hw (tgt_bg av ev tsp arnd uid hw) := by
  have Hg : mem_grows (twmem av ev tsp arnd uid hw) (tgt_bg av ev tsp arnd uid hw) := by
    unfold tgt_bg
    solve_mem_grows
  intro a n
  exact ⟨fun _ _ => rfl, Hg a⟩

theorem bgt_ok_wbytes_below (mem : word → Option byte) (addr : word) (bs : List byte)
    (Hm : bgt_ok av ev tsp arnd uid hw mem)
    (Hlt : bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned tsp - 32) :
    bgt_ok av ev tsp arnd uid hw (wbytes mem addr bs) := by
  have Hg := bgt_grows av ev tsp arnd uid hw mem Hm
  have Hg' : mem_grows (twmem av ev tsp arnd uid hw) (wbytes mem addr bs) := by
    solve_mem_grows
  intro a n
  refine ⟨?_, Hg' a⟩
  intro Hnw Ha
  rw [rdn_wbytes_disjoint target_segs bs mem addr a n (by omega) Hnw]
  exact bgt_agree_of av ev tsp arnd uid hw mem Hm a n Hnw Ha

theorem bgt_ok_wtm_below (mem : word → Option byte) (buf : word) (data : List byte)
    (Hm : bgt_ok av ev tsp arnd uid hw mem)
    (Hlt : bv_unsigned buf + (data.length : Int) ≤ bv_unsigned tsp - 32) :
    bgt_ok av ev tsp arnd uid hw (write_to_mem mem buf data) := by
  have Hg := bgt_grows av ev tsp arnd uid hw mem Hm
  have Hg' : mem_grows (twmem av ev tsp arnd uid hw) (write_to_mem mem buf data) := by
    solve_mem_grows
  intro a n
  refine ⟨?_, Hg' a⟩
  intro Hnw Ha
  have := u64_range tsp
  rw [rdn_wtm_out target_segs data mem buf a n Hnw (by omega) (Or.inl (by omega))]
  exact bgt_agree_of av ev tsp arnd uid hw mem Hm a n Hnw Ha

/- Everything below reaches `bgt_ok` only through the lemmas above; seal
it so `repeat split` leaves it alone (see the note at the definition). -/
attribute [irreducible] bgt_ok

include Hsp_lo Hsp_hi in
/-- Read main's saved ra back through any `bgt_ok` memory. -/
theorem bgt_read_ra (mem : word → Option byte)
    (Hm : bgt_ok av ev tsp arnd uid hw mem) :
    rdn target_segs mem (Z_to_bv 64 (bv_unsigned tsp - 24)) 8 =
      some (word_to_le_bytes 8 (0x10011a0 : word)) := by
  have := tsp_lo_num tsp Hsp_lo
  have := tsp_hi_num tsp Hsp_hi
  rw [bgt_agree_of av ev tsp arnd uid hw mem Hm _ _
    (by u_norm; omega) (by u_norm; omega)]
  unfold tgt_bg
  apply rdn_wbytes_hit8
  u_norm
  omega

include Hsp_lo Hsp_hi in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Exit tail: from 0x1001260 with a0 = code reach exit(code). -/
theorem tgt_exit_tail (code : word) (regs : bvmap 5 word) (mem : word → Option byte)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32))
    (H10 : reg_get regs 10 = code) (Hbg : bgt_ok av ev tsp arnd uid hw mem) :
    to_exit target_segs code (mkst regs 0x1001260 mem trom) := by
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  -- 0x1001260..0x10011a4: ld ra ; addi sp ; ret ; li a7,93 ; (ecall)
  have Hex (segs : List Segment)
      (F_1001260 : fetch_word segs (Z_to_bv 64 0x1001260) = some (0x00813083 : BitVec 32))
      (F_1001264 : fetch_word segs (Z_to_bv 64 0x1001264) = some (0x01010113 : BitVec 32))
      (F_1001268 : fetch_word segs (Z_to_bv 64 0x1001268) = some (0x00008067 : BitVec 32))
      (F_10011a0 : fetch_word segs (Z_to_bv 64 0x10011a0) = some (0x05d00893 : BitVec 32))
      (F_10011a4 : fetch_word segs (Z_to_bv 64 0x10011a4) = some (0x00000073 : BitVec 32))
  : sym_exec segs 5 [] [ELit 0x10011a0]
      (SS 0x1001260 (sr_pins [(2, EVar 32)] sr_id) [] 33) [] =
      (SS 0x10011a4
        (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu .ALU_ADD (EVar 32) (ELit 16)))
          1 (ELit 0x10011a0)) 17 (ELit 93)) [] 34,
       [SCFlat (SA (SBVar 32) 8) 8,
        SCReadBase (SA (SBVar 32) 8) 8 (ELit 0x10011a0)]) := by
    let ss0 := SS 0x1001260 (sr_pins [(2, EVar 32)] sr_id) [] 33
    let sr1 := sr_upd (sr_pins [(2, EVar 32)] sr_id) 1 (ELit 0x10011a0)
    let sr2 := sr_upd sr1 2 (EAlu .ALU_ADD (EVar 32) (ELit 16))
    let sr3 := sr_upd sr2 17 (ELit 93)
    let scs := [SCFlat (SA (SBVar 32) 8) 8,
      SCReadBase (SA (SBVar 32) 8) 8 (ELit 0x10011a0)]
    rewrite [sym_exec]
    conv => lhs; dsimp only [sym_state.s_pc]
    rewrite [F_1001260]
    conv => lhs; dsimp only
    conv => lhs; simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001260]
    rewrite [show sym_step (.Load .SZ8 true 1 2 8) ss0 [ELit 0x10011a0] =
        some (SS 0x1001264 sr1 [] 34, scs, []) from by rfl]
    conv => lhs; dsimp only
    rewrite [List.append_nil]
    rewrite [sym_exec]
    conv => lhs; dsimp only [sym_state.s_pc]
    rewrite [F_1001264]
    conv => lhs; dsimp only
    conv => lhs; simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001264]
    rewrite [show sym_step (.OpImm .ALU_ADD 2 2 16) (SS 0x1001264 sr1 [] 34) [] =
        some (SS 0x1001268 sr2 [] 34, [], []) from by rfl]
    conv => lhs; dsimp only
    rewrite [List.nil_append]
    rewrite [sym_exec]
    conv => lhs; dsimp only [sym_state.s_pc]
    rewrite [F_1001268]
    conv => lhs; dsimp only
    conv => lhs; simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001268]
    rewrite [show sym_step (.Jalr 0 1 0) (SS 0x1001268 sr2 [] 34) [] =
        some (SS 0x10011a0 sr2 [] 34, [], []) from by rfl]
    conv => lhs; dsimp only
    rewrite [List.nil_append]
    rewrite [sym_exec]
    conv => lhs; dsimp only [sym_state.s_pc]
    rewrite [F_10011a0]
    conv => lhs; dsimp only
    conv => lhs; simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x05d00893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011a0]
    rewrite [show sym_step (.OpImm .ALU_ADD 17 0 93) (SS 0x10011a0 sr2 [] 34) [] =
        some (SS 0x10011a4 sr3 [] 34, [], []) from by rfl]
    conv => lhs; dsimp only
    rewrite [List.nil_append]
    rewrite [sym_exec]
    conv => lhs; dsimp only [sym_state.s_pc]
    rewrite [F_10011a4]
    conv => lhs; dsimp only
    conv => lhs; simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000073 : BitVec 32) = true from by decide, ite_true]
    rfl
  let ss0 := SS 0x1001260 (sr_pins [(2, EVar 32)] sr_id) [] 33
  let ss1 := SS 0x10011a4
    (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu .ALU_ADD (EVar 32) (ELit 16)))
      1 (ELit 0x10011a0)) 17 (ELit 93)) [] 34
  let scs := [SCFlat (SA (SBVar 32) 8) 8,
    SCReadBase (SA (SBVar 32) 8) 8 (ELit 0x10011a0)]
  let E := Eplus regs [Z_to_bv 64 (bv_unsigned tsp - 32)]
  have Hsc : scs_denot target_segs mem E scs := by
    simp only [scs, scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
      dsimp only [E]
      sym_norm
      sym_sc_auto
    · dsimp only [sc_denot, adenot, bdenot, saddr.a_base, saddr.a_off, E]
      sym_norm
      refine ⟨word_to_le_bytes 8 (0x10011a0 : word), ?_, ?_⟩
      · exact bgt_read_ra av ev tsp arnd Hsp_lo Hsp_hi uid hw mem Hbg
      · decide +kernel
  have Hst : st_ok E mem trom ss0 (mkst regs 0x1001260 mem trom) := by
    refine ⟨regs, rfl, regs_ok_pins E [(2, EVar 32)] sr_id regs
      (regs_ok_Eplus regs [Z_to_bv 64 (bv_unsigned tsp - 32)]) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    dsimp only [E]
    sym_env_norm
    exact H2
  have Hexec : sym_exec target_segs 5 [] [ELit 0x10011a0] ss0 [] = (ss1, scs) := by
    apply Hex target_segs
    · exact (congrArg (fetch_word target_segs)
        (show Z_to_bv 64 0x1001260 = (0x1001260 : word) from by decide)).trans tail1_TF_1001260
    · exact (congrArg (fetch_word target_segs)
        (show Z_to_bv 64 0x1001264 = (0x1001264 : word) from by decide)).trans tail1_TF_1001264
    · exact (congrArg (fetch_word target_segs)
        (show Z_to_bv 64 0x1001268 = (0x1001268 : word) from by decide)).trans tail1_TF_1001268
    · exact (congrArg (fetch_word target_segs)
        (show Z_to_bv 64 0x10011a0 = (0x10011a0 : word) from by decide)).trans tail1_TF_10011a0
    · exact (congrArg (fetch_word target_segs)
        (show Z_to_bv 64 0x10011a4 = (0x10011a4 : word) from by decide)).trans tail1_TF_10011a4

  obtain ⟨R, HR, Hms⟩ := sym_exec_ex target_segs 5 [] [ELit 0x10011a0]
    ss0 [] ss1 scs E mem trom (mkst regs 0x1001260 mem trom) Hexec Hsc Hst
  dsimp only [ss0, ss1, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms HR
  sym_chain Hms
  apply to_exit.te_step _ _ rfl (step_ecall _ _ _ _ _ _ tail1_TF_10011a4 rfl)
  apply te_here_rec
  · sym_regs HR
    decide +kernel
  · sym_regs HR
    exact H10

/- `firstn_snoc_nth` (= ListFacts's `firstn_S_nth`), `firstn_all_len` and
`skipn_cons_nth` now come from Common/ListFacts; `procs_skipn_step`
stays local (uses the `procs` fold). -/
theorem procs_skipn_step (bs : List byte) (i : Nat) (a : A) (Hi : i < bs.length) :
    procs f a (bs.drop i) =
      match f a (bs.getD i (Z_to_bv 8 0)) with
      | some a' => procs f a' (bs.drop (Nat.succ i))
      | none => none := by
  rw [skipn_cons_nth bs i (Z_to_bv 8 0) Hi]
  simp only [procs, Nat.succ_eq_add_one]
  cases f a (bs.getD i (Z_to_bv 8 0)) with
  | none => rfl
  | some a' => cases a'; rfl

include Hsp_lo Hsp_hi in
/-- The pointer copy loop at 0x1001210: cur[j..) -> done[j..). -/
theorem copy_loop_t (k j : Nat) (cur : List byte) (R : bvmap 5 word)
    (mem : word → Option byte)
    (Hk : cur.length - Nat.succ j = k) (Hj : j < cur.length)
    (Hcap : (cur.length : Int) ≤ 4096)
    (H6 : reg_get R 6 = nat_to_word (cur.length - j))
    (H14 : reg_get R 14 = t_cur + nat_to_word j)
    (H17 : reg_get R 17 = t_done + nat_to_word j)
    (Hbg : bgt_ok av ev tsp arnd uid hw mem)
    (Hcur : rdn target_segs mem t_cur cur.length = some cur)
    (Hdone : rdn target_segs mem t_done j = some (cur.take j)) :
    ∃ mem', ∃ (R' : bvmap 5 word),
      msteps target_segs (mkst R 0x1001210 mem trom) (mkst R' 0x1001228 mem' trom) ∧
      reg_get R' 2 = reg_get R 2 ∧ reg_get R' 5 = reg_get R 5 ∧
      reg_get R' 10 = reg_get R 10 ∧ reg_get R' 11 = reg_get R 11 ∧
      reg_get R' 12 = reg_get R 12 ∧ reg_get R' 13 = reg_get R 13 ∧
      reg_get R' 15 = reg_get R 15 ∧ reg_get R' 16 = reg_get R 16 ∧
      bgt_ok av ev tsp arnd uid hw mem' ∧
      rdn target_segs mem' t_cur cur.length = some cur ∧
      rdn target_segs mem' t_done cur.length = some cur ∧
      (∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ bv_unsigned t_done →
        rdn target_segs mem' a n = rdn target_segs mem a n) := by
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  induction k generalizing j R mem with
  | zero =>
    have Hsj : Nat.succ j = cur.length := by omega
    let sr0 := sr_pins [(6, EVar 32), (14, EVar 33), (17, EVar 34)] sr_id
    let sr1 := sr_upd sr0 7 (EVar 35)
    let sr2 := sr_upd sr1 6 (EAlu .ALU_ADD (EVar 32) (ELit (-1)))
    let sr4 := sr_upd sr2 17 (EAlu .ALU_ADD (EVar 34) (ELit 1))
    let sr5 := sr_upd sr4 14 (EAlu .ALU_ADD (EVar 33) (ELit 1))
    have Hex (segs : List Segment)
        (F_1001210 : fetch_word segs (Z_to_bv 64 16781840) = some (0x00074383 : BitVec 32))
        (F_1001214 : fetch_word segs (Z_to_bv 64 16781844) = some (0xfff30313 : BitVec 32))
        (F_1001218 : fetch_word segs (Z_to_bv 64 16781848) = some (0x00788023 : BitVec 32))
        (F_100121c : fetch_word segs (Z_to_bv 64 16781852) = some (0x00188893 : BitVec 32))
        (F_1001220 : fetch_word segs (Z_to_bv 64 16781856) = some (0x00170713 : BitVec 32))
        (F_1001224 : fetch_word segs (Z_to_bv 64 16781860) = some (0xfe0316e3 : BitVec 32))
        : sym_exec segs 6 [false] [] (SS 16781840 sr0 [] 35) [] = ((SS 16781864 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36), [SCBr false .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)]) := by
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001210]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00074383 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001210]
      change sym_exec segs 5 [false] [] (SS 16781844 sr1 [] 36) [SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001214]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfff30313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001214]
      change sym_exec segs 4 [false] [] (SS 16781848 sr2 [] 36) [SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001218]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00788023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001218]
      change sym_exec segs 3 [false] [] (SS 16781852 sr2 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_100121c]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00188893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100121c]
      change sym_exec segs 2 [false] [] (SS 16781856 sr4 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001220]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00170713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001220]
      change sym_exec segs 1 [false] [] (SS 16781860 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001224]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe0316e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001224]
      rfl
    have Hexec : sym_exec target_segs 6 [false] [] (SS 16781840 sr0 [] 35) [] = ((SS 16781864 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36), [SCBr false .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)]) := by
      apply Hex target_segs
      · exact tail1_TF_1001210
      · exact tail1_TF_1001214
      · exact tail1_TF_1001218
      · exact tail1_TF_100121c
      · exact tail1_TF_1001220
      · exact tail1_TF_1001224
    have Hsc : scs_denot target_segs mem (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) [SCBr false .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] := by
      simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
      all_goals sym_norm
      all_goals try sym_sc_auto
      · rw [show cur.length - j = 1 from by omega]
        decide +kernel
      · scflat
      · rw [u0_id] <;> apply target_store_ok <;> unormT <;> omega
      · scflat
      · rw [u0_id]
        refine ⟨[cur.getD j (Z_to_bv 8 0)], rdn_nth target_segs mem cur.length t_cur cur j Hcur Hj, ?_⟩
        rw [bytes_le_to_Z_1]
        exact (zext_byte_u _).symm
    have Hst : st_ok (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) mem trom (SS 16781840 sr0 [] 35) (mkst R (Z_to_bv 64 16781840) mem trom) := by
      refine ⟨R, rfl, regs_ok_pins (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) [(6, EVar 32), (14, EVar 33), (17, EVar 34)] sr_id R
        (regs_ok_Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) ?_, True.intro⟩
      simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      all_goals repeat' apply And.intro
      all_goals (sym_env_norm <;> try sym_pin_auto)
      · exact H6
      · exact H14
      · exact H17
    obtain ⟨R2, HR2, Hms⟩ := sym_exec_ex target_segs 6 [false] [] (SS 16781840 sr0 [] 35) []
      (SS 16781864 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCBr false .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) mem trom (mkst R (Z_to_bv 64 16781840) mem trom) Hexec Hsc Hst
    dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms
    dsimp only [sym_state.s_regs, sr5, sr4, sr2, sr1, sr0] at HR2
    hms_norm Hms
    refine ⟨wbytes mem (t_done + nat_to_word j) [cur.getD j (Z_to_bv 8 0)], R2, Hms, ?_⟩
    repeat' apply And.intro
    all_goals try (sym_regs HR2 <;> rfl)
    · apply bgt_ok_wbytes_below av ev tsp arnd uid hw _ _ _ Hbg
      simp only [List.length_singleton]
      unormT <;> omega
    · rw [rdn_wbytes1_out _ _ _ _ _ _ (by unormT <;> omega) (Or.inr (by unormT <;> omega))]
      exact Hcur
    · have HdSj : rdn target_segs
          (wbytes mem (t_done + nat_to_word j) [cur.getD j (Z_to_bv 8 0)])
          t_done (Nat.succ j) = some (cur.take (Nat.succ j)) := by
        have Hlen : (cur.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega)]
        rw [firstn_S_nth byte cur j (Z_to_bv 8 0) Hj]
        simpa only [Hlen] using rdn_snoc_store target_segs mem t_done (cur.take j)
          (cur.getD j (Z_to_bv 8 0)) (by rw [u_t_done, Hlen] <;> omega)
          (by rw [Hlen] <;> exact Hdone)
      rw [Hsj, List.take_length] at HdSj
      exact HdSj
    · intro a n Ha
      rw [rdn_wbytes1_out _ _ _ _ _ _ (by rw [u_t_done] at Ha <;> omega)
        (Or.inr (by unormT <;> omega))]
  | succ k IH =>
    have Hsj : Nat.succ j < cur.length := by omega
    let mem' := wbytes mem (t_done + nat_to_word j) [cur.getD j (Z_to_bv 8 0)]
    let sr0 := sr_pins [(6, EVar 32), (14, EVar 33), (17, EVar 34)] sr_id
    let sr1 := sr_upd sr0 7 (EVar 35)
    let sr2 := sr_upd sr1 6 (EAlu .ALU_ADD (EVar 32) (ELit (-1)))
    let sr4 := sr_upd sr2 17 (EAlu .ALU_ADD (EVar 34) (ELit 1))
    let sr5 := sr_upd sr4 14 (EAlu .ALU_ADD (EVar 33) (ELit 1))
    have Hex (segs : List Segment)
        (F_1001210 : fetch_word segs (Z_to_bv 64 16781840) = some (0x00074383 : BitVec 32))
        (F_1001214 : fetch_word segs (Z_to_bv 64 16781844) = some (0xfff30313 : BitVec 32))
        (F_1001218 : fetch_word segs (Z_to_bv 64 16781848) = some (0x00788023 : BitVec 32))
        (F_100121c : fetch_word segs (Z_to_bv 64 16781852) = some (0x00188893 : BitVec 32))
        (F_1001220 : fetch_word segs (Z_to_bv 64 16781856) = some (0x00170713 : BitVec 32))
        (F_1001224 : fetch_word segs (Z_to_bv 64 16781860) = some (0xfe0316e3 : BitVec 32))
        : sym_exec segs 6 [true] [] (SS 16781840 sr0 [] 35) [] = ((SS 16781840 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36), [SCBr true .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)]) := by
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001210]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00074383 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001210]
      change sym_exec segs 5 [true] [] (SS 16781844 sr1 [] 36) [SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001214]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfff30313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001214]
      change sym_exec segs 4 [true] [] (SS 16781848 sr2 [] 36) [SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001218]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00788023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001218]
      change sym_exec segs 3 [true] [] (SS 16781852 sr2 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_100121c]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00188893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100121c]
      change sym_exec segs 2 [true] [] (SS 16781856 sr4 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001220]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00170713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001220]
      change sym_exec segs 1 [true] [] (SS 16781860 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] = _
      rewrite [sym_exec]
      conv => lhs <;> dsimp only [sym_state.s_pc]
      rewrite [F_1001224]
      conv => lhs <;> dsimp only
      conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe0316e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001224]
      rfl
    have Hexec : sym_exec target_segs 6 [true] [] (SS 16781840 sr0 [] 35) [] = ((SS 16781840 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36), [SCBr true .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)]) := by
      apply Hex target_segs
      · exact tail1_TF_1001210
      · exact tail1_TF_1001214
      · exact tail1_TF_1001218
      · exact tail1_TF_100121c
      · exact tail1_TF_1001220
      · exact tail1_TF_1001224
    have Hsc : scs_denot target_segs mem (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) [SCBr true .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] := by
      simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
      all_goals sym_norm
      all_goals try sym_sc_auto
      · rw [Bool.not_eq_true', bv_eqb_Z]
        rw [u_Z2bv _ (by rw [u_ntw _ (by omega)] <;> omega)
          (by rw [u_ntw _ (by omega)] <;> omega), u_ntw _ (by omega)]
        change decide ((_ : Int) = 0) = false
        apply decide_eq_false
        omega
      · scflat
      · rw [u0_id] <;> apply target_store_ok <;> unormT <;> omega
      · scflat
      · rw [u0_id]
        refine ⟨[cur.getD j (Z_to_bv 8 0)], rdn_nth target_segs mem cur.length t_cur cur j Hcur Hj, ?_⟩
        rw [bytes_le_to_Z_1]
        exact (zext_byte_u _).symm
    have Hst : st_ok (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) mem trom (SS 16781840 sr0 [] 35) (mkst R (Z_to_bv 64 16781840) mem trom) := by
      refine ⟨R, rfl, regs_ok_pins (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) [(6, EVar 32), (14, EVar 33), (17, EVar 34)] sr_id R
        (regs_ok_Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) ?_, True.intro⟩
      simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      all_goals repeat' apply And.intro
      all_goals (sym_env_norm <;> try sym_pin_auto)
      · exact H6
      · exact H14
      · exact H17
    obtain ⟨R2, HR2, Hms⟩ := sym_exec_ex target_segs 6 [true] [] (SS 16781840 sr0 [] 35) []
      (SS 16781840 sr5 [SE (SA (SBVar 34) 0) 1 (EVar 35)] 36) [SCBr true .BC_NE (EAlu .ALU_ADD (EVar 32) (ELit (-1))) (ELit 0), SCFlat (SA (SBVar 34) 0) 1, SCStoreOk (SA (SBVar 34) 0) 1, SCFlat (SA (SBVar 33) 0) 1, SCReadBase (SA (SBVar 33) 0) 1 (EVar 35)] (Eplus R ([nat_to_word (cur.length - j), t_cur + nat_to_word j, t_done + nat_to_word j] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) mem trom (mkst R (Z_to_bv 64 16781840) mem trom) Hexec Hsc Hst
    dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms
    dsimp only [sym_state.s_regs, sr5, sr4, sr2, sr1, sr0] at HR2
    hms_norm Hms
    have G6 : reg_get R2 6 = nat_to_word (cur.length - Nat.succ j) := by
      sym_regs HR2
      apply bv_eq_of_unsigned
      rw [u_Z2bv _ (by rw [u_ntw _ (by omega)] <;> omega) (by rw [u_ntw _ (by omega)] <;> omega)]
      repeat rw [u_ntw _ (by omega)]
      omega
    have G14 : reg_get R2 14 = t_cur + nat_to_word (Nat.succ j) := by
      sym_regs HR2
      repeat rw [word_add_nat]
      rw [u_Z2bv _ (by rw [u_t_cur] <;> omega) (by rw [u_t_cur] <;> omega)]
      congr 1 <;> omega
    have G17 : reg_get R2 17 = t_done + nat_to_word (Nat.succ j) := by
      sym_regs HR2
      repeat rw [word_add_nat]
      rw [u_Z2bv _ (by rw [u_t_done] <;> omega) (by rw [u_t_done] <;> omega)]
      congr 1 <;> omega
    have Hbg' : bgt_ok av ev tsp arnd uid hw mem' := by
      apply bgt_ok_wbytes_below av ev tsp arnd uid hw _ _ _ Hbg
      simp only [List.length_singleton]
      unormT <;> omega
    have Hcur' : rdn target_segs mem' t_cur cur.length = some cur := by
      unfold mem'
      rw [rdn_wbytes1_out _ _ _ _ _ _ (by unormT <;> omega) (Or.inr (by unormT <;> omega))]
      exact Hcur
    have Hdone' : rdn target_segs mem' t_done (Nat.succ j) = some (cur.take (Nat.succ j)) := by
      unfold mem'
      have Hlen : (cur.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega)]
      rw [firstn_S_nth byte cur j (Z_to_bv 8 0) Hj]
      simpa only [Hlen] using rdn_snoc_store target_segs mem t_done (cur.take j)
        (cur.getD j (Z_to_bv 8 0)) (by rw [u_t_done, Hlen] <;> omega)
        (by rw [Hlen] <;> exact Hdone)
    obtain ⟨mem'', R'', Hs'', E2, E5, E10, E11, E12, E13, E15, E16,
      Hbg'', Hcur'', Hdone'', Hframe''⟩ := IH (Nat.succ j) R2 mem'
        (by omega) Hsj G6 G14 G17 Hbg' Hcur' Hdone'
    refine ⟨mem'', R'', msteps_trans target_segs _ _ _ Hms Hs'', ?_⟩
    rw [E2, E5, E10, E11, E12, E13, E15, E16]
    repeat' apply And.intro
    all_goals try (sym_regs HR2 <;> rfl)
    all_goals try assumption
    intro a n Ha
    rw [Hframe'' a n Ha]
    unfold mem'
    rw [rdn_wbytes1_out _ _ _ _ _ _ (by rw [u_t_done] at Ha <;> omega)
      (Or.inr (by unormT <;> omega))]

include Hsp_lo Hsp_hi in
/-- The full copy phase: from the beqz at 0x100120c. -/
theorem copy_full_t (cur : List byte) (R : bvmap 5 word) (mem : word → Option byte)
    (Hcap : (cur.length : Int) ≤ 4096)
    (H6 : reg_get R 6 = nat_to_word cur.length)
    (H13 : reg_get R 13 = nat_to_word cur.length)
    (H14 : reg_get R 14 = t_cur) (H17 : reg_get R 17 = t_done)
    (Hbg : bgt_ok av ev tsp arnd uid hw mem)
    (Hcur : rdn target_segs mem t_cur cur.length = some cur) :
    ∃ mem', ∃ (R' : bvmap 5 word),
      msteps target_segs (mkst R 0x100120c mem trom) (mkst R' 0x1001228 mem' trom) ∧
      reg_get R' 2 = reg_get R 2 ∧ reg_get R' 5 = reg_get R 5 ∧
      reg_get R' 10 = reg_get R 10 ∧ reg_get R' 11 = reg_get R 11 ∧
      reg_get R' 12 = reg_get R 12 ∧ reg_get R' 13 = reg_get R 13 ∧
      reg_get R' 15 = reg_get R 15 ∧ reg_get R' 16 = reg_get R 16 ∧
      bgt_ok av ev tsp arnd uid hw mem' ∧
      rdn target_segs mem' t_cur cur.length = some cur ∧
      rdn target_segs mem' t_done cur.length = some cur ∧
      (∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ bv_unsigned t_done →
        rdn target_segs mem' a n = rdn target_segs mem a n) := by
  cases cur with
  | nil =>
    refine ⟨mem, R, ?_, ?_⟩
    · apply msteps.mst_step _ _ _ rfl
      · apply step_beq_tk _ _ _ _ _ _ _ _ _ tail1_TF_100120c rfl TD_100120c
        getr_resolve <;> rw [H13] <;> exact c_eq_0_true
      · norm_pc <;> apply msteps.mst_refl
    · repeat' apply And.intro
      all_goals first | rfl | assumption | (intro a n _ <;> rfl)
  | cons c0 curr =>
    have Hlen : 0 < (c0 :: curr).length := by simp only [List.length_cons] <;> omega
    have Hstep0 : msteps target_segs (mkst R 0x100120c mem trom)
        (mkst R 0x1001210 mem trom) := by
      apply msteps.mst_step _ _ _ rfl
      · apply step_beq_ft _ _ _ _ _ _ _ _ _ tail1_TF_100120c rfl TD_100120c
        getr_resolve <;> rw [H13] <;> apply c_eq_0_false
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc <;> apply msteps.mst_refl
    obtain ⟨mem', R', Hs, Hrest⟩ := copy_loop_t av ev tsp arnd Hsp_lo Hsp_hi uid hw
      ((c0 :: curr).length - 1) 0 (c0 :: curr) R mem (by omega) Hlen Hcap
      (by rw [Nat.sub_zero] <;> exact H6)
      (by rw [H14] <;> exact (word_add_0 _).symm)
      (by rw [H17] <;> exact (word_add_0 _).symm) Hbg Hcur rfl
    exact ⟨mem', R', msteps_trans target_segs _ _ _ Hstep0 Hs, Hrest⟩

/-- Loop-head predicate. -/
def tgt_LH (a : A) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x10011d4 mem trom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ∧
    reg_get regs 5 = t_cur ∧ reg_get regs 16 = t_done ∧
    reg_get regs 15 = Z_to_bv 64 10 ∧ reg_get regs 11 = t_rb ∧
    reg_get regs 13 = nat_to_word a.1.length ∧
    reg_get regs 14 = nat_to_word a.2.length ∧
    bgt_ok av ev tsp arnd uid hw mem ∧
    rdn target_segs mem t_cur a.1.length = some a.1 ∧
    rdn target_segs mem t_done a.2.length = some a.2 ∧
    (a.1.length : Int) ≤ 4096 ∧ (a.2.length : Int) ≤ 4097

/-- Byte-loop head predicate (at 0x10011f4). -/
def BLHt (cur done bs : List byte) (i : Nat) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x10011f4 mem trom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ∧
    reg_get regs 5 = t_cur ∧ reg_get regs 16 = t_done ∧
    reg_get regs 15 = Z_to_bv 64 10 ∧ reg_get regs 11 = t_rb ∧
    reg_get regs 13 = nat_to_word cur.length ∧
    reg_get regs 14 = nat_to_word done.length ∧
    reg_get regs 12 = nat_to_word i ∧
    reg_get regs 10 = nat_to_word bs.length ∧
    bgt_ok av ev tsp arnd uid hw mem ∧
    rdn target_segs mem t_rb bs.length = some bs ∧
    rdn target_segs mem t_cur cur.length = some cur ∧
    rdn target_segs mem t_done done.length = some done ∧
    (cur.length : Int) ≤ 4096 ∧ (done.length : Int) ≤ 4097 ∧
    (bs.length : Int) ≤ 1024 ∧ i < bs.length

/-- State at 0x1001250 (the a2 increment), after processing byte i. -/
def C4t (cur done bs : List byte) (i : Nat) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x1001250 mem trom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ∧
    reg_get regs 5 = t_cur ∧ reg_get regs 16 = t_done ∧
    reg_get regs 15 = Z_to_bv 64 10 ∧ reg_get regs 11 = t_rb ∧
    reg_get regs 13 = nat_to_word cur.length ∧
    reg_get regs 14 = nat_to_word done.length ∧
    reg_get regs 12 = nat_to_word i ∧
    reg_get regs 10 = nat_to_word bs.length ∧
    bgt_ok av ev tsp arnd uid hw mem ∧
    rdn target_segs mem t_rb bs.length = some bs ∧
    rdn target_segs mem t_cur cur.length = some cur ∧
    rdn target_segs mem t_done done.length = some done ∧
    (cur.length : Int) ≤ 4096 ∧ (done.length : Int) ≤ 4097 ∧
    (bs.length : Int) ≤ 1024 ∧ i < bs.length

theorem msteps_to_exit_t (code : word) (ms ms' : machine_state)
    (H : msteps target_segs ms ms') :
    to_exit target_segs code ms' → to_exit target_segs code ms := by
  induction H with
  | mst_refl => exact fun h => h
  | mst_step ms ms1 _ Hsvc Hstep _ IH =>
    intro Hex
    exact to_exit.te_step ms ms1 Hsvc Hstep (IH Hex)

include Hsp_lo Hsp_hi in
set_option maxHeartbeats 500000 in
/-- The byte loop. -/
theorem byte_loop_t (k : Nat) (cur done bs : List byte) (i : Nat) (ms : machine_state)
    (Hk : bs.length - i = k) (HBLH : BLHt av ev tsp arnd uid hw cur done bs i ms) :
    match procs f (cur, done) (bs.drop i) with
    | some a' => ∃ msL, msteps target_segs ms msL ∧ tgt_LH av ev tsp arnd uid hw a' msL
    | none => to_exit target_segs ec ms := by
  induction k generalizing cur done bs i ms with
  | zero =>
    obtain ⟨regs, mem, rfl, H2, H5, H16, H15, H11, H13, H14, H12, H10,
      Hbg, Hrb, Hcur, Hdone, Hcurcap, Hdonecap, Hbscap, Hi⟩ := HBLH
    omega
  | succ k IH =>
    obtain ⟨regs, mem, rfl, H2, H5, H16, H15, H11, H13, H14, H12, H10,
      Hbg, Hrb, Hcur, Hdone, Hcurcap, Hdonecap, Hbscap, Hi⟩ := HBLH
    have Hlo := tsp_lo_num tsp Hsp_lo
    have Hhi := tsp_hi_num tsp Hsp_hi
    let b := bs.getD i (Z_to_bv 8 0)
    -- Dispatch at 0x1001250, using the induction hypothesis.
    have Hdisp (cur' done' : List byte) (st : machine_state)
        (HC4 : C4t av ev tsp arnd uid hw cur' done' bs i st) :
        match procs f (cur', done') (bs.drop (Nat.succ i)) with
        | some a'' => ∃ msL, msteps target_segs st msL ∧ tgt_LH av ev tsp arnd uid hw a'' msL
        | none => to_exit target_segs ec st := by
      obtain ⟨rg, mm, rfl, G2, G5, G16, G15, G11, G13, G14, G12, G10,
        Hbg', Hrb', Hcur', Hdone', Hcurcap', Hdonecap', Hbscap', Hlt⟩ := HC4
      by_cases Heq : Nat.succ i = bs.length
      · rw [List.drop_eq_nil_of_le (by omega)]
        dsimp only [procs]
        let sr0 := sr_pins [(12, EVar 32), (10, EVar 33)] sr_id
        let sr1 := sr_upd sr0 12 (EAlu .ALU_ADD (EVar 32) (ELit 1))
        have Hex (segs : List Segment)
            (F_1001250 : fetch_word segs (Z_to_bv 64 16781904) = some (0x00160613 : BitVec 32))
            (F_1001254 : fetch_word segs (Z_to_bv 64 16781908) = some (0xf8a600e3 : BitVec 32))
            : sym_exec segs 2 [true] [] (SS 16781904 sr0 [] 34) [] = ((SS 16781780 sr1 [] 34), [SCBr true .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)]) := by
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001250]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00160613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001250]
          change sym_exec segs 1 [true] [] (SS 16781908 sr1 [] 34) [] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001254]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xf8a600e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001254]
          rfl
        have Hexec : sym_exec target_segs 2 [true] [] (SS 16781904 sr0 [] 34) [] = ((SS 16781780 sr1 [] 34), [SCBr true .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)]) := by
          apply Hex target_segs
          · exact tail1_TF_1001250
          · exact tail1_TF_1001254
        have Hsc : scs_denot target_segs mm (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) [SCBr true .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)] := by
          simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
          all_goals sym_norm
          all_goals try sym_sc_auto
          · brz <;> omega
        have Hst : st_ok (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) mm trom (SS 16781904 sr0 [] 34) (mkst rg (Z_to_bv 64 16781904) mm trom) := by
          refine ⟨rg, rfl, regs_ok_pins (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) [(12, EVar 32), (10, EVar 33)] sr_id rg
            (regs_ok_Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals repeat' apply And.intro
          all_goals (sym_env_norm <;> try sym_pin_auto)
          · exact G12
          · exact G10
        obtain ⟨Rn, HRn, Hms⟩ := sym_exec_ex target_segs 2 [true] [] (SS 16781904 sr0 [] 34) []
          (SS 16781780 sr1 [] 34) [SCBr true .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)] (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) mm trom (mkst rg (Z_to_bv 64 16781904) mm trom) Hexec Hsc Hst
        dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms
        dsimp only [sym_state.s_regs, sr1, sr0] at HRn
        hms_norm Hms
        refine ⟨mkst Rn 0x10011d4 mm trom, Hms, Rn, mm, rfl, ?_⟩
        dsimp only [Prod.fst, Prod.snd]
        repeat' apply And.intro
        all_goals first | assumption | (sym_regs HRn <;> first | rfl | assumption | ntw_succ)
      · have Hlt2 : Nat.succ i < bs.length := by omega
        let sr0 := sr_pins [(12, EVar 32), (10, EVar 33)] sr_id
        let sr1 := sr_upd sr0 12 (EAlu .ALU_ADD (EVar 32) (ELit 1))
        have Hex (segs : List Segment)
            (F_1001250 : fetch_word segs (Z_to_bv 64 16781904) = some (0x00160613 : BitVec 32))
            (F_1001254 : fetch_word segs (Z_to_bv 64 16781908) = some (0xf8a600e3 : BitVec 32))
            (F_1001258 : fetch_word segs (Z_to_bv 64 16781912) = some (0xf9dff06f : BitVec 32))
            : sym_exec segs 3 [false] [] (SS 16781904 sr0 [] 34) [] = ((SS 16781812 sr1 [] 34), [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)]) := by
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001250]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00160613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001250]
          change sym_exec segs 2 [false] [] (SS 16781908 sr1 [] 34) [] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001254]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xf8a600e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001254]
          change sym_exec segs 1 [] [] (SS 16781912 sr1 [] 34) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001258]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xf9dff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001258]
          rfl
        have Hexec : sym_exec target_segs 3 [false] [] (SS 16781904 sr0 [] 34) [] = ((SS 16781812 sr1 [] 34), [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)]) := by
          apply Hex target_segs
          · exact tail1_TF_1001250
          · exact tail1_TF_1001254
          · exact tail1_TF_1001258
        have Hsc : scs_denot target_segs mm (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)] := by
          simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
          all_goals sym_norm
          all_goals try sym_sc_auto
          · brz <;> omega
        have Hst : st_ok (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) mm trom (SS 16781904 sr0 [] 34) (mkst rg (Z_to_bv 64 16781904) mm trom) := by
          refine ⟨rg, rfl, regs_ok_pins (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) [(12, EVar 32), (10, EVar 33)] sr_id rg
            (regs_ok_Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals repeat' apply And.intro
          all_goals (sym_env_norm <;> try sym_pin_auto)
          · exact G12
          · exact G10
        obtain ⟨Rn, HRn, Hms⟩ := sym_exec_ex target_segs 3 [false] [] (SS 16781904 sr0 [] 34) []
          (SS 16781812 sr1 [] 34) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 1)) (EVar 33)] (Eplus rg ([nat_to_word i, nat_to_word bs.length] ++ [])) mm trom (mkst rg (Z_to_bv 64 16781904) mm trom) Hexec Hsc Hst
        dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms
        dsimp only [sym_state.s_regs, sr1, sr0] at HRn
        hms_norm Hms
        have HB2 : BLHt av ev tsp arnd uid hw cur' done' bs (Nat.succ i)
            (mkst Rn 0x10011f4 mm trom) := by
          refine ⟨Rn, mm, rfl, ?_⟩
          repeat' apply And.intro
          all_goals first | assumption | omega | (sym_regs HRn <;> first | rfl | assumption | ntw_succ)
        have Hih := IH cur' done' bs (Nat.succ i) (mkst Rn 0x10011f4 mm trom) (by omega) HB2
        cases He : procs f (cur', done') (bs.drop (Nat.succ i)) with
        | some a'' =>
          rw [He] at Hih
          obtain ⟨msL, Hs, HL⟩ := Hih
          exact ⟨msL, msteps_trans target_segs _ _ _ Hms Hs, HL⟩
        | none =>
          rw [He] at Hih
          exact msteps_to_exit_t ec _ _ Hms Hih
    cases Eb : bv_eqb b (Z_to_bv 8 10) with
    | true =>
      have Hf : f (cur, done) b = some ([], cur ++ [Z_to_bv 8 10]) := by
        unfold f <;> rw [Eb] <;> rfl
      rw [procs_skipn_step bs i (cur, done) Hi]
      change (match (match f (cur, done) b with
        | some a' => procs f a' (bs.drop (Nat.succ i)) | none => none) with
        | some a' => ∃ msL, msteps target_segs (mkst regs 0x10011f4 mem trom) msL ∧
            tgt_LH av ev tsp arnd uid hw a' msL
        | none => to_exit target_segs ec (mkst regs 0x10011f4 mem trom))
      rw [Hf]
      dsimp only
      let sr0 := sr_pins [(11, ELit 16786156), (15, ELit 10), (5, ELit 16787180), (16, ELit 16791276),
               (12, EVar 32), (13, EVar 33)] sr_id
      let sr1 := sr_upd sr0 17 (EAlu .ALU_ADD (ELit 16786156) (EVar 32))
      let sr2 := sr_upd sr1 17 (EVar 34)
      let sr4 := sr_upd sr2 14 (ELit 16787180)
      let sr5 := sr_upd sr4 17 (ELit 16791276)
      let sr6 := sr_upd sr5 6 (EAlu .ALU_ADD (EVar 33) (ELit 0))
      have Hex (segs : List Segment)
          (F_10011f4 : fetch_word segs (Z_to_bv 64 16781812) = some (0x00c588b3 : BitVec 32))
          (F_10011f8 : fetch_word segs (Z_to_bv 64 16781816) = some (0x0008c883 : BitVec 32))
          (F_10011fc : fetch_word segs (Z_to_bv 64 16781820) = some (0x04f89063 : BitVec 32))
          (F_1001200 : fetch_word segs (Z_to_bv 64 16781824) = some (0x00028713 : BitVec 32))
          (F_1001204 : fetch_word segs (Z_to_bv 64 16781828) = some (0x00080893 : BitVec 32))
          (F_1001208 : fetch_word segs (Z_to_bv 64 16781832) = some (0x00068313 : BitVec 32))
          : sym_exec segs 6 [false] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781836 sr6 [] 35), [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_10011f4]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c588b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f4]
        change sym_exec segs 5 [false] [] (SS 16781816 sr1 [] 34) [] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_10011f8]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0008c883 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f8]
        change sym_exec segs 4 [false] [] (SS 16781820 sr2 [] 35) [SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_10011fc]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04f89063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011fc]
        change sym_exec segs 3 [] [] (SS 16781824 sr2 [] 35) [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001200]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00028713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001200]
        change sym_exec segs 2 [] [] (SS 16781828 sr4 [] 35) [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001204]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001204]
        change sym_exec segs 1 [] [] (SS 16781832 sr5 [] 35) [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001208]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001208]
        rfl
      have Hexec : sym_exec target_segs 6 [false] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781836 sr6 [] 35), [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
        apply Hex target_segs
        · exact tail1_TF_10011f4
        · exact tail1_TF_10011f8
        · exact tail1_TF_10011fc
        · exact tail1_TF_1001200
        · exact tail1_TF_1001204
        · exact tail1_TF_1001208
      have Hsc : scs_denot target_segs mem (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] := by
        simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
        refine ⟨?_, ?_, ?_⟩
        all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
        all_goals sym_norm
        all_goals try sym_sc_auto
        · rw [Bool.not_eq_false']
          change c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 10) = true
          rw [c_eq_zext10] <;> exact Eb
        · scflat
        · rw [addr_base_ntw t_rb 16786156 i u_t_rb (by omega)]
          refine ⟨[b], rdn_nth target_segs mem bs.length t_rb bs i Hrb Hi, ?_⟩
          rw [bytes_le_to_Z_1] <;> exact (zext_byte_u _).symm
      have Hst : st_ok (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (SS 16781812 sr0 [] 34) (mkst regs (Z_to_bv 64 16781812) mem trom) := by
        refine ⟨regs, rfl, regs_ok_pins (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [(11, ELit 16786156), (15, ELit 10), (5, ELit 16787180), (16, ELit 16791276),
               (12, EVar 32), (13, EVar 33)] sr_id regs
          (regs_ok_Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
        all_goals repeat' apply And.intro
        all_goals (sym_env_norm <;> try sym_pin_auto)
        · pin_lit t_rb <;> exact H11
        · exact H15
        · pin_lit t_cur <;> exact H5
        · pin_lit t_done <;> exact H16
        · exact H12
        · exact H13
      obtain ⟨Rac, HRac, Hms_ac⟩ := sym_exec_ex target_segs 6 [false] [] (SS 16781812 sr0 [] 34) []
        (SS 16781836 sr6 [] 35) [SCBr false .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (mkst regs (Z_to_bv 64 16781812) mem trom) Hexec Hsc Hst
      dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms_ac
      dsimp only [sym_state.s_regs, sr6, sr5, sr4, sr2, sr1, sr0] at HRac
      hms_norm Hms_ac
      have GRac6 : reg_get Rac 6 = nat_to_word cur.length := by sym_regs HRac <;> first | rfl | exact u0_id _
      have GRac13 : reg_get Rac 13 = nat_to_word cur.length := by sym_regs HRac <;> first | rfl | exact u0_id _
      have GRac14 : reg_get Rac 14 = t_cur := by sym_regs HRac <;> bveq
      have GRac17 : reg_get Rac 17 = t_done := by sym_regs HRac <;> bveq
      obtain ⟨mem_c, Rc, Hcopy, Cc2, Cc5, Cc10, Cc11, Cc12, Cc13, Cc15, Cc16,
        Hbg_c, Hcur_c, Hdone_c, Hframe_c⟩ :=
        copy_full_t av ev tsp arnd Hsp_lo Hsp_hi uid hw cur Rac mem Hcurcap
          GRac6 GRac13 GRac14 GRac17 Hbg Hcur
      let memD := wbytes mem_c (t_done + nat_to_word cur.length) [Z_to_bv 8 10]
      let sr0 := sr_pins [(16, ELit 16791276), (15, ELit 10), (13, EVar 32)] sr_id
      let sr1 := sr_upd sr0 14 (EAlu .ALU_ADD (ELit 16791276) (EVar 32))
      let sr3 := sr_upd sr1 14 (EAlu .ALU_ADD (EVar 32) (ELit 1))
      let sr4 := sr_upd sr3 13 (ELit 0)
      have Hex (segs : List Segment)
          (F_1001228 : fetch_word segs (Z_to_bv 64 16781864) = some (0x00d80733 : BitVec 32))
          (F_100122c : fetch_word segs (Z_to_bv 64 16781868) = some (0x00f70023 : BitVec 32))
          (F_1001230 : fetch_word segs (Z_to_bv 64 16781872) = some (0x00168713 : BitVec 32))
          (F_1001234 : fetch_word segs (Z_to_bv 64 16781876) = some (0x00000693 : BitVec 32))
          (F_1001238 : fetch_word segs (Z_to_bv 64 16781880) = some (0x0180006f : BitVec 32))
          : sym_exec segs 5 [] [] (SS 16781864 sr0 [] 33) [] = ((SS 16781904 sr4 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33), [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1]) := by
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001228]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00d80733 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001228]
        change sym_exec segs 4 [] [] (SS 16781868 sr1 [] 33) [] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_100122c]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00f70023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100122c]
        change sym_exec segs 3 [] [] (SS 16781872 sr1 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33) [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001230]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00168713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001230]
        change sym_exec segs 2 [] [] (SS 16781876 sr3 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33) [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001234]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001234]
        change sym_exec segs 1 [] [] (SS 16781880 sr4 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33) [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1] = _
        rewrite [sym_exec]
        conv => lhs <;> dsimp only [sym_state.s_pc]
        rewrite [F_1001238]
        conv => lhs <;> dsimp only
        conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0180006f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001238]
        rfl
      have Hexec : sym_exec target_segs 5 [] [] (SS 16781864 sr0 [] 33) [] = ((SS 16781904 sr4 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33), [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1]) := by
        apply Hex target_segs
        · exact tail1_TF_1001228
        · exact tail1_TF_100122c
        · exact tail1_TF_1001230
        · exact tail1_TF_1001234
        · exact tail1_TF_1001238
      have Hsc : scs_denot target_segs mem_c (Eplus Rc ([nat_to_word cur.length] ++ [])) [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1] := by
        simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
        refine ⟨?_, ?_⟩
        all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
        all_goals sym_norm
        all_goals try sym_sc_auto
        · scflat
        · rw [addr_base_ntw t_done 16791276 cur.length u_t_done (by omega)]
          apply target_store_ok <;> unormT <;> omega
      have Hst : st_ok (Eplus Rc ([nat_to_word cur.length] ++ [])) mem_c trom (SS 16781864 sr0 [] 33) (mkst Rc (Z_to_bv 64 16781864) mem_c trom) := by
        refine ⟨Rc, rfl, regs_ok_pins (Eplus Rc ([nat_to_word cur.length] ++ [])) [(16, ELit 16791276), (15, ELit 10), (13, EVar 32)] sr_id Rc
          (regs_ok_Eplus Rc ([nat_to_word cur.length] ++ [])) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
        all_goals repeat' apply And.intro
        all_goals (sym_env_norm <;> try sym_pin_auto)
        · pin_lit t_done <;> getr_resolve <;> rw [Cc16] <;> sym_regs HRac <;> bveq
        · getr_resolve <;> rw [Cc15] <;> sym_regs HRac <;> rfl
        · exact Cc13.trans GRac13
      obtain ⟨Rd, HRd, Hms_d⟩ := sym_exec_ex target_segs 5 [] [] (SS 16781864 sr0 [] 33) []
        (SS 16781904 sr4 [SE (SA (SBVar 32) 16791276) 1 (ELit 10)] 33) [SCFlat (SA (SBVar 32) 16791276) 1, SCStoreOk (SA (SBVar 32) 16791276) 1] (Eplus Rc ([nat_to_word cur.length] ++ [])) mem_c trom (mkst Rc (Z_to_bv 64 16781864) mem_c trom) Hexec Hsc Hst
      dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms_d
      dsimp only [sym_state.s_regs, sr4, sr3, sr1, sr0] at HRd
      hms_norm Hms_d
      rw [addr_base_ntw t_done 16791276 cur.length u_t_done (by omega)] at Hms_d
      have HC4 : C4t av ev tsp arnd uid hw [] (cur ++ [Z_to_bv 8 10]) bs i
          (mkst Rd 0x1001250 memD trom) := by
        refine ⟨Rd, memD, rfl, ?_⟩
        repeat' apply And.intro
        · sym_regs HRd <;> getr_resolve <;> rw [Cc2] <;> sym_regs HRac <;> exact H2
        · sym_regs HRd <;> getr_resolve <;> rw [Cc5] <;> sym_regs HRac <;> bveq
        · sym_regs HRd <;> bveq
        · sym_regs HRd <;> rfl
        · sym_regs HRd <;> getr_resolve <;> rw [Cc11] <;> sym_regs HRac <;> bveq
        · sym_regs HRd <;> rfl
        · sym_regs HRd
          simp only [List.length_append, List.length_singleton]
          ntw_succ
        · sym_regs HRd <;> getr_resolve <;> rw [Cc12] <;> sym_regs HRac <;> rfl
        · sym_regs HRd <;> getr_resolve <;> rw [Cc10] <;> sym_regs HRac <;> exact H10
        · apply bgt_ok_wbytes_below av ev tsp arnd uid hw _ _ _ Hbg_c
          simp only [List.length_singleton] <;> unormT <;> omega
        · unfold memD
          rw [rdn_wbytes1_out _ _ _ _ _ _ (by unormT <;> omega) (Or.inr (by unormT <;> omega))]
          rw [Hframe_c t_rb bs.length (by unormT <;> omega)]
          exact Hrb
        · rfl
        · unfold memD
          simp only [List.length_append, List.length_singleton]
          exact rdn_snoc_store _ _ _ _ _ (by rw [u_t_done] <;> omega) Hdone_c
        · simp only [List.length_nil] <;> omega
        · simp only [List.length_append, List.length_singleton] <;> omega
        · exact Hbscap
        · exact Hi
      have Hd := Hdisp [] (cur ++ [Z_to_bv 8 10]) (mkst Rd 0x1001250 memD trom) HC4
      have Hall : msteps target_segs (mkst regs 0x10011f4 mem trom)
          (mkst Rd 0x1001250 memD trom) :=
        msteps_trans target_segs _ _ _ Hms_ac (msteps_trans target_segs _ _ _ Hcopy Hms_d)
      cases He : procs f ([], cur ++ [Z_to_bv 8 10]) (bs.drop (Nat.succ i)) with
      | some a'' =>
        rw [He] at Hd
        obtain ⟨msL, Hs, HL⟩ := Hd
        exact ⟨msL, msteps_trans target_segs _ _ _ Hall Hs, HL⟩
      | none =>
        rw [He] at Hd
        exact msteps_to_exit_t ec _ _ Hall Hd
    | false =>
      by_cases Hge : 4096 ≤ (cur.length : Int)
      · have Hf : f (cur, done) b = none := by
          unfold f
          rw [Eb]
          simp only [Bool.false_eq_true, ite_false]
          exact ite_eq_left Hge
        rw [procs_skipn_step bs i (cur, done) Hi]
        change (match (match f (cur, done) b with
          | some a' => procs f a' (bs.drop (Nat.succ i)) | none => none) with
          | some a' => ∃ msL, msteps target_segs (mkst regs 0x10011f4 mem trom) msL ∧
              tgt_LH av ev tsp arnd uid hw a' msL
          | none => to_exit target_segs ec (mkst regs 0x10011f4 mem trom))
        rw [Hf]
        dsimp only
        have Hc4096 : (cur.length : Int) = 4096 := by omega
        let sr0 := sr_pins [(11, ELit 16786156), (15, ELit 10), (12, EVar 32), (13, EVar 33)] sr_id
        let sr1 := sr_upd sr0 17 (EAlu .ALU_ADD (ELit 16786156) (EVar 32))
        let sr2 := sr_upd sr1 17 (EVar 34)
        let sr4 := sr_upd sr2 6 (EAlu .ALU_SRL (EVar 33) (ELit 12))
        let sr6 := sr_upd sr4 10 (ELit 3)
        have Hex (segs : List Segment)
            (F_10011f4 : fetch_word segs (Z_to_bv 64 16781812) = some (0x00c588b3 : BitVec 32))
            (F_10011f8 : fetch_word segs (Z_to_bv 64 16781816) = some (0x0008c883 : BitVec 32))
            (F_10011fc : fetch_word segs (Z_to_bv 64 16781820) = some (0x04f89063 : BitVec 32))
            (F_100123c : fetch_word segs (Z_to_bv 64 16781884) = some (0x00c6d313 : BitVec 32))
            (F_1001240 : fetch_word segs (Z_to_bv 64 16781888) = some (0x00031e63 : BitVec 32))
            (F_100125c : fetch_word segs (Z_to_bv 64 16781916) = some (0x00300513 : BitVec 32))
            : sym_exec segs 6 [true, true] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781920 sr6 [] 35), [SCBr true .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011f4]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c588b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f4]
          change sym_exec segs 5 [true, true] [] (SS 16781816 sr1 [] 34) [] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011f8]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0008c883 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f8]
          change sym_exec segs 4 [true, true] [] (SS 16781820 sr2 [] 35) [SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011fc]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04f89063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011fc]
          change sym_exec segs 3 [true] [] (SS 16781884 sr2 [] 35) [SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_100123c]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c6d313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100123c]
          change sym_exec segs 2 [true] [] (SS 16781888 sr4 [] 35) [SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001240]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00031e63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001240]
          change sym_exec segs 1 [] [] (SS 16781916 sr4 [] 35) [SCBr true .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_100125c]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00300513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100125c]
          rfl
        have Hexec : sym_exec target_segs 6 [true, true] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781920 sr6 [] 35), [SCBr true .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
          apply Hex target_segs
          · exact tail1_TF_10011f4
          · exact tail1_TF_10011f8
          · exact tail1_TF_10011fc
          · exact tail1_TF_100123c
          · exact tail1_TF_1001240
          · exact tail1_TF_100125c
        have Hsc : scs_denot target_segs mem (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [SCBr true .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] := by
          simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
          all_goals sym_norm
          all_goals try sym_sc_auto
          · rw [Bool.not_eq_true'] <;> srli_test
            rw [Hc4096] <;> decide
          · rw [Bool.not_eq_true']
            change c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 10) = false
            rw [c_eq_zext10] <;> exact Eb
          · scflat
          · rw [addr_base_ntw t_rb 16786156 i u_t_rb (by omega)]
            refine ⟨[b], rdn_nth target_segs mem bs.length t_rb bs i Hrb Hi, ?_⟩
            rw [bytes_le_to_Z_1] <;> exact (zext_byte_u _).symm
        have Hst : st_ok (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (SS 16781812 sr0 [] 34) (mkst regs (Z_to_bv 64 16781812) mem trom) := by
          refine ⟨regs, rfl, regs_ok_pins (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [(11, ELit 16786156), (15, ELit 10), (12, EVar 32), (13, EVar 33)] sr_id regs
            (regs_ok_Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals repeat' apply And.intro
          all_goals (sym_env_norm <;> try sym_pin_auto)
          · pin_lit t_rb <;> exact H11
          · exact H15
          · exact H12
          · exact H13
        obtain ⟨Rx, HRx, Hblock⟩ := sym_exec_ex target_segs 6 [true, true] [] (SS 16781812 sr0 [] 34) []
          (SS 16781920 sr6 [] 35) [SCBr true .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (mkst regs (Z_to_bv 64 16781812) mem trom) Hexec Hsc Hst
        dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hblock
        dsimp only [sym_state.s_regs, sr6, sr4, sr2, sr1, sr0] at HRx
        sym_chain Hblock
        apply tgt_exit_tail av ev tsp arnd Hsp_lo Hsp_hi uid hw
        · sym_regs HRx <;> exact H2
        · sym_regs HRx <;> rfl
        · exact Hbg
      · have Hlt : (cur.length : Int) < 4096 := by omega
        have Hf : f (cur, done) b = some (cur ++ [b], done) := by
          unfold f
          rw [Eb]
          simp only [Bool.false_eq_true, ite_false]
          exact ite_eq_right Hge
        rw [procs_skipn_step bs i (cur, done) Hi]
        change (match (match f (cur, done) b with
          | some a' => procs f a' (bs.drop (Nat.succ i)) | none => none) with
          | some a' => ∃ msL, msteps target_segs (mkst regs 0x10011f4 mem trom) msL ∧
              tgt_LH av ev tsp arnd uid hw a' msL
          | none => to_exit target_segs ec (mkst regs 0x10011f4 mem trom))
        rw [Hf]
        dsimp only
        let memC := wbytes mem (t_cur + nat_to_word cur.length) [b]
        let sr0 := sr_pins [(11, ELit 16786156), (15, ELit 10), (5, ELit 16787180), (12, EVar 32), (13, EVar 33)] sr_id
        let sr1 := sr_upd sr0 17 (EAlu .ALU_ADD (ELit 16786156) (EVar 32))
        let sr2 := sr_upd sr1 17 (EVar 34)
        let sr4 := sr_upd sr2 6 (EAlu .ALU_SRL (EVar 33) (ELit 12))
        let sr6 := sr_upd sr4 6 (EAlu .ALU_ADD (ELit 16787180) (EVar 33))
        let sr7 := sr_upd sr6 13 (EAlu .ALU_ADD (EVar 33) (ELit 1))
        have Hex (segs : List Segment)
            (F_10011f4 : fetch_word segs (Z_to_bv 64 16781812) = some (0x00c588b3 : BitVec 32))
            (F_10011f8 : fetch_word segs (Z_to_bv 64 16781816) = some (0x0008c883 : BitVec 32))
            (F_10011fc : fetch_word segs (Z_to_bv 64 16781820) = some (0x04f89063 : BitVec 32))
            (F_100123c : fetch_word segs (Z_to_bv 64 16781884) = some (0x00c6d313 : BitVec 32))
            (F_1001240 : fetch_word segs (Z_to_bv 64 16781888) = some (0x00031e63 : BitVec 32))
            (F_1001244 : fetch_word segs (Z_to_bv 64 16781892) = some (0x00d28333 : BitVec 32))
            (F_1001248 : fetch_word segs (Z_to_bv 64 16781896) = some (0x00168693 : BitVec 32))
            (F_100124c : fetch_word segs (Z_to_bv 64 16781900) = some (0x01130023 : BitVec 32))
            : sym_exec segs 8 [true, false] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781904 sr7 [SE (SA (SBVar 33) 16787180) 1 (EVar 34)] 35), [SCFlat (SA (SBVar 33) 16787180) 1, SCStoreOk (SA (SBVar 33) 16787180) 1, SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011f4]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c588b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f4]
          change sym_exec segs 7 [true, false] [] (SS 16781816 sr1 [] 34) [] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011f8]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0008c883 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f8]
          change sym_exec segs 6 [true, false] [] (SS 16781820 sr2 [] 35) [SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_10011fc]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04f89063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011fc]
          change sym_exec segs 5 [false] [] (SS 16781884 sr2 [] 35) [SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_100123c]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c6d313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100123c]
          change sym_exec segs 4 [false] [] (SS 16781888 sr4 [] 35) [SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001240]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00031e63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001240]
          change sym_exec segs 3 [] [] (SS 16781892 sr4 [] 35) [SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001244]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00d28333 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001244]
          change sym_exec segs 2 [] [] (SS 16781896 sr6 [] 35) [SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_1001248]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00168693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001248]
          change sym_exec segs 1 [] [] (SS 16781900 sr7 [] 35) [SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] = _
          rewrite [sym_exec]
          conv => lhs <;> dsimp only [sym_state.s_pc]
          rewrite [F_100124c]
          conv => lhs <;> dsimp only
          conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01130023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100124c]
          rfl
        have Hexec : sym_exec target_segs 8 [true, false] [] (SS 16781812 sr0 [] 34) [] = ((SS 16781904 sr7 [SE (SA (SBVar 33) 16787180) 1 (EVar 34)] 35), [SCFlat (SA (SBVar 33) 16787180) 1, SCStoreOk (SA (SBVar 33) 16787180) 1, SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)]) := by
          apply Hex target_segs
          · exact tail1_TF_10011f4
          · exact tail1_TF_10011f8
          · exact tail1_TF_10011fc
          · exact tail1_TF_100123c
          · exact tail1_TF_1001240
          · exact tail1_TF_1001244
          · exact tail1_TF_1001248
          · exact tail1_TF_100124c
        have Hsc : scs_denot target_segs mem (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [SCFlat (SA (SBVar 33) 16787180) 1, SCStoreOk (SA (SBVar 33) 16787180) 1, SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] := by
          simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
          all_goals sym_norm
          all_goals try sym_sc_auto
          · scflat
          · rw [addr_base_ntw t_cur 16787180 cur.length u_t_cur (by omega)]
            apply target_store_ok <;> unormT <;> omega
          · rw [Bool.not_eq_false'] <;> srli_test
            apply decide_eq_true
            change (cur.length : Int) / 4096 = 0
            apply Int.ediv_eq_zero_of_lt <;> omega
          · rw [Bool.not_eq_true']
            change c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 10) = false
            rw [c_eq_zext10] <;> exact Eb
          · scflat
          · rw [addr_base_ntw t_rb 16786156 i u_t_rb (by omega)]
            refine ⟨[b], rdn_nth target_segs mem bs.length t_rb bs i Hrb Hi, ?_⟩
            rw [bytes_le_to_Z_1] <;> exact (zext_byte_u _).symm
        have Hst : st_ok (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (SS 16781812 sr0 [] 34) (mkst regs (Z_to_bv 64 16781812) mem trom) := by
          refine ⟨regs, rfl, regs_ok_pins (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) [(11, ELit 16786156), (15, ELit 10), (5, ELit 16787180), (12, EVar 32), (13, EVar 33)] sr_id regs
            (regs_ok_Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
          all_goals repeat' apply And.intro
          all_goals (sym_env_norm <;> try sym_pin_auto)
          · pin_lit t_rb <;> exact H11
          · exact H15
          · pin_lit t_cur <;> exact H5
          · exact H12
          · exact H13
        obtain ⟨Rd, HRd, Hms_d⟩ := sym_exec_ex target_segs 8 [true, false] [] (SS 16781812 sr0 [] 34) []
          (SS 16781904 sr7 [SE (SA (SBVar 33) 16787180) 1 (EVar 34)] 35) [SCFlat (SA (SBVar 33) 16787180) 1, SCStoreOk (SA (SBVar 33) 16787180) 1, SCBr false .BC_NE (EAlu .ALU_SRL (EVar 33) (ELit 12)) (ELit 0), SCBr true .BC_NE (EVar 34) (ELit 10), SCFlat (SA (SBVar 32) 16786156) 1, SCReadBase (SA (SBVar 32) 16786156) 1 (EVar 34)] (Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) mem trom (mkst regs (Z_to_bv 64 16781812) mem trom) Hexec Hsc Hst
        dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms_d
        dsimp only [sym_state.s_regs, sr7, sr6, sr4, sr2, sr1, sr0] at HRd
        hms_norm Hms_d
        rw [addr_base_ntw t_cur 16787180 cur.length u_t_cur (by omega)] at Hms_d
        have HC4 : C4t av ev tsp arnd uid hw (cur ++ [b]) done bs i
            (mkst Rd 0x1001250 memC trom) := by
          refine ⟨Rd, memC, rfl, ?_⟩
          repeat' apply And.intro
          · sym_regs HRd <;> exact H2
          · sym_regs HRd <;> bveq
          · sym_regs HRd <;> exact H16
          · sym_regs HRd <;> rfl
          · sym_regs HRd <;> bveq
          · sym_regs HRd
            simp only [List.length_append, List.length_singleton]
            ntw_succ
          · sym_regs HRd <;> exact H14
          · sym_regs HRd <;> rfl
          · sym_regs HRd <;> exact H10
          · apply bgt_ok_wbytes_below av ev tsp arnd uid hw _ _ _ Hbg
            simp only [List.length_singleton] <;> unormT <;> omega
          · unfold memC
            rw [rdn_wbytes1_out _ _ _ _ _ _ (by unormT <;> omega) (Or.inr (by unormT <;> omega))]
            exact Hrb
          · unfold memC
            simp only [List.length_append, List.length_singleton]
            exact rdn_snoc_store _ _ _ _ _ (by rw [u_t_cur] <;> omega) Hcur
          · unfold memC
            rw [rdn_wbytes1_out _ _ _ _ _ _ (by unormT <;> omega) (Or.inl (by unormT <;> omega))]
            exact Hdone
          · simp only [List.length_append, List.length_singleton] <;> omega
          · exact Hdonecap
          · exact Hbscap
          · exact Hi
        have Hd := Hdisp (cur ++ [b]) done (mkst Rd 0x1001250 memC trom) HC4
        cases He : procs f (cur ++ [b], done) (bs.drop (Nat.succ i)) with
        | some a'' =>
          rw [He] at Hd
          obtain ⟨msL, Hs, HL⟩ := Hd
          exact ⟨msL, msteps_trans target_segs _ _ _ Hms_d Hs, HL⟩
        | none =>
          rw [He] at Hd
          exact msteps_to_exit_t ec _ _ Hms_d Hd

include Hsp_lo Hsp_hi in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- The write helper at 0x10012b4 issues its `ecall` at 0x10012c8 and
then loops: `blez a0` (whose error arm is dead — every delivery is
nonempty), `add a1,a1,a0`, `sub a2,a2,a0`, `bnez a2` back to the
`li a0,1` at 0x10012c4. The loop is REGISTER-ONLY, so memory is
untouched throughout and the whole remainder `rest.drop n` leaves
across one or more possibly-short channel writes. On the last
delivery the helper returns 0 to its `ra` (always 0x10012a0, the
single `jalr` call site at 0x100129c), whence main's
`snez a0,a0 ; slliw a0,a0,2` computes exit code 0 and falls into
the exit tail.

Induction on `fuel ≥ rest.length`; the remainder strictly shrinks
because every delivery is nonempty. -/
theorem tgt_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) < 2 ^ 63)
    (H1 : reg_get regs 1 = (0x10012a0 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32))
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H11 : reg_get regs 11 = p) (H12 : reg_get regs 12 = len_word rest)
    (H17 : bv_unsigned (reg_get regs 17) = 64)
    (H17w : reg_get regs 17 = Z_to_bv 64 64)
    (Hbg : bgt_ok av ev tsp arnd uid hw mem)
    (Hread : rdn target_segs mem p rest.length = some rest) :
    to_wall_tail target_segs (Z_to_bv 64 1)
      (mkst regs 0x10012cc mem trom) (rest.drop n)
      (to_exit target_segs (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    -- 0x10012cc: blez a0 falls through — the delivery is nonempty.
    chain_step
    · rfl
    · apply step_bge_ft _ _ _ _ _ _ _ _ _ tail1_TF_10012cc rfl TD_10012cc
      getr_resolve
      rw [H10]
      apply c_lts_0_pos <;> rw [u_len_word_firstn n rest Hn2 (by omega)] <;> omega
    norm_pc
    -- 0x10012d0: add a1,a1,a0 — bump the pointer.
    stepiv tail1_TF_10012d0 TD_10012d0 (p + nat_to_word n)
      (getr_resolve; rw [H11, H10]; apply v_add_len_firstn; omega)
    -- 0x10012d4: sub a2,a2,a0 — decrement the count.
    stepiv tail1_TF_10012d4 TD_10012d4 (len_word (rest.drop n))
      (getr_resolve; rw [H12, H10]; apply v_sub_len_firstn <;> omega)
    by_cases Heq : n = rest.length
    · -- Full delivery: bnez not taken, the helper returns 0.
      subst n
      rw [List.drop_length]
      chain_step
      · rfl
      · apply step_bne_ft _ _ _ _ _ _ _ _ _ tail1_TF_10012d8 rfl TD_10012d8
        getr_resolve
        apply c_eq_0_of_u
        rfl
      norm_pc
      -- 0x10012dc: li a0,0 ; 0x10012e0: ret.
      stepiv tail1_TF_10012dc TD_10012dc (Z_to_bv 64 0) (getr_resolve; bveq)
      stepjr tail1_TF_10012e0 TD_10012e0 (0x10012a0 : word)
        (getr_resolve; regupd_resolve; exact H1)
      apply to_wall_tail.twt_done
      -- 0x10012a0..0x10012a8: snez a0,a0 ; slliw a0,a0,2 ; j exit tail.
      stepi tail1_TF_10012a0 TD_10012a0
      stepi tail1_TF_10012a4 TD_10012a4
      stepj tail1_TF_10012a8 TD_10012a8
      apply tgt_exit_tail av ev tsp arnd Hsp_lo Hsp_hi uid hw
      · regupd_resolve; exact H2
      · getr_resolve; regupd_resolve; bveq
      · exact Hbg
    · -- Short delivery: bnez taken, reissue on the remainder.
      chain_step
      · rfl
      · apply step_bne_tk _ _ _ _ _ _ _ _ _ tail1_TF_10012d8 rfl TD_10012d8
        getr_resolve
        apply c_eq_0_false
        rw [u_len_word _ (by rw [List.length_drop]; omega), List.length_drop]
        omega
      norm_pc
      -- 0x10012c4: li a0,1.
      stepiv tail1_TF_10012c4 TD_10012c4 (Z_to_bv 64 1) (getr_resolve; bveq)
      -- 0x10012c8: the reissued write.
      apply to_wall_tail.twt_step _ _ _ _ rfl
        (step_ecall _ _ _ _ _ _ tail1_TF_10012c8 rfl)
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      apply twl_write_rec target_segs (Z_to_bv 64 1)
      · getr_resolve; regupd_resolve; exact H17
      · regupd_resolve; rfl
      · regupd_resolve
        change ms_read_bytes _ (p + nat_to_word n) (len_word (rest.drop n)) = _
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem (p + nat_to_word n)
          (word_to_nat (len_word (rest.drop n))) = some (rest.drop n)
        have Hcount : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          unfold word_to_nat
          change Int.toNat (bv_unsigned (len_word (rest.drop n))) = _
          rw [u_len_word _ (by rw [List.length_drop]; omega), Int.toNat_natCast]
        rw [Hcount]
        have Hsk := LinuxProcessSemantics.Common.SeqExec.rdn_skipn
          target_segs mem rest.length p rest n Hread Hn2
        rw [List.length_drop]
        exact Hsk
      · rw [List.length_drop]; omega
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop n) (p + nat_to_word n) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · regupd_resolve; exact H1
        · regupd_resolve; exact H2
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact H17
        · regupd_resolve; exact H17w
        · exact Hbg
        · have Hsk := LinuxProcessSemantics.Common.SeqExec.rdn_skipn
            target_segs mem rest.length p rest n Hread Hn2
          rw [List.length_drop]
          exact Hsk

include Hsp_lo Hsp_hi in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
/-- EOF continuation: from the post-read state (a0 = 0, pc 0x10011e4)
write the last line (if any) and exit 0. -/
theorem tgt_eof_to_out (R : bvmap 5 word) (mem : word → Option byte)
    (cur done : List byte)
    (H2 : reg_get R 2 = Z_to_bv 64 (bv_unsigned tsp - 32))
    (H10 : reg_get R 10 = Z_to_bv 64 0)
    (H13 : reg_get R 13 = nat_to_word cur.length)
    (H14 : reg_get R 14 = nat_to_word done.length)
    (Hbg : bgt_ok av ev tsp arnd uid hw mem)
    (Hcur : rdn target_segs mem t_cur cur.length = some cur)
    (Hdone : rdn target_segs mem t_done done.length = some done)
    (Hcurcap : (cur.length : Int) ≤ 4096) (Hdonecap : (done.length : Int) ≤ 4097) :
    to_out target_segs (out (cur, done)) (mkst R 0x10011e4 mem trom) := by
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  cases cur with
  | nil =>
    -- cur empty: the last line is done.
    cases done with
    | nil =>
      -- Nothing at all: exit 0 with no write. 0x10011e4..0x10012b0 runs
      -- straight through to the exit tail.
      change to_out target_segs [] _
      apply to_out.tout_exit
      have Hex (segs : List Segment)
          (F_10011e4 : fetch_word segs (Z_to_bv 64 0x10011e4) = some (0x08054463 : BitVec 32))
          (F_10011e8 : fetch_word segs (Z_to_bv 64 0x10011e8) = some (0x08050663 : BitVec 32))
          (F_1001274 : fetch_word segs (Z_to_bv 64 0x1001274) = some (0x00068a63 : BitVec 32))
          (F_1001288 : fetch_word segs (Z_to_bv 64 0x1001288) = some (0x02070263 : BitVec 32))
          (F_10012ac : fetch_word segs (Z_to_bv 64 0x10012ac) = some (0x00000513 : BitVec 32))
          (F_10012b0 : fetch_word segs (Z_to_bv 64 0x10012b0) = some (0xfb1ff06f : BitVec 32))
          : sym_exec segs 6 [false, true, true, true] []
          (SS 0x10011e4 (sr_pins [(10, ELit 0), (13, ELit 0), (14, ELit 0)] sr_id) [] 32) [] =
          (SS 0x1001260 [EVar 0, EVar 1, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 0, EVar 11, EVar 12, ELit 0, ELit 0, EVar 15, EVar 16, EVar 17, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 32,
           [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]) := by
        let sr0 := sr_pins [(10, ELit 0), (13, ELit 0), (14, ELit 0)] sr_id
        let sr1 := sr_upd sr0 10 (ELit 0)
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10011e4]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x08054463 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e4]
        change sym_exec segs 5 [true, true, true] []
          (SS 0x10011e8 sr0 [] 32) [SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10011e8]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x08050663 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e8]
        change sym_exec segs 4 [true, true] []
          (SS 0x1001274 sr0 [] 32) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001274]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00068a63 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001274]
        change sym_exec segs 3 [true] []
          (SS 0x1001288 sr0 [] 32) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001288]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x02070263 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001288]
        change sym_exec segs 2 [] []
          (SS 0x10012ac sr0 [] 32) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012ac]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00000513 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012ac]
        change sym_exec segs 1 [] []
          (SS 0x10012b0 sr1 [] 32) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012b0]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0xfb1ff06f : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012b0]
        change sym_exec segs 0 [] []
          (SS 0x1001260 sr1 [] 32) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rfl
      let ss0 := SS 0x10011e4 (sr_pins [(10, ELit 0), (13, ELit 0), (14, ELit 0)] sr_id) [] 32
      let ss1 := SS 0x1001260 [EVar 0, EVar 1, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 0, EVar 11, EVar 12, ELit 0, ELit 0, EVar 15, EVar 16, EVar 17, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 32
      let scs := [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]
      let E := Eplus R []
      have Hsc : scs_denot target_segs mem E scs := by
        simp only [scs, scs_denot, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [sc_denot, branch_taken, E]; sym_norm)
        all_goals (scbr <;> omega)
      have Hst : st_ok E mem trom ss0 (mkst R 0x10011e4 mem trom) := by
        refine ⟨R, rfl, regs_ok_pins E [(10, ELit 0), (13, ELit 0), (14, ELit 0)] sr_id R
          (regs_ok_Eplus R []) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [E]; sym_env_norm)
        all_goals first | exact H10 | exact H13 | exact H14
      have Hexec : sym_exec target_segs 6 [false, true, true, true] [] ss0 [] = (ss1, scs) := by
        apply Hex target_segs
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10011e4 = (0x10011e4 : word) from by decide)).trans tail1_TF_10011e4
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10011e8 = (0x10011e8 : word) from by decide)).trans tail1_TF_10011e8
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001274 = (0x1001274 : word) from by decide)).trans tail1_TF_1001274
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001288 = (0x1001288 : word) from by decide)).trans tail1_TF_1001288
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012ac = (0x10012ac : word) from by decide)).trans tail1_TF_10012ac
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012b0 = (0x10012b0 : word) from by decide)).trans tail1_TF_10012b0
      obtain ⟨Rx, HRx, Hms⟩ := sym_exec_ex target_segs 6 [false, true, true, true] []
        ss0 [] ss1 scs E mem trom (mkst R 0x10011e4 mem trom) Hexec Hsc Hst
      dsimp only [ss0, ss1, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot, E] at Hms HRx
      sym_chain Hms
      apply tgt_exit_tail av ev tsp arnd Hsp_lo Hsp_hi uid hw
      · sym_regs HRx; exact H2
      · sym_regs HRx; sym_close
      · exact Hbg
    | cons d done' =>
      -- Write done, then exit 0. 0x10011e4..0x10012c4 is one block
      -- across the jalr into the write helper.
      change to_out target_segs (d :: done') _
      have Hex (segs : List Segment)
          (F_10011e4 : fetch_word segs (Z_to_bv 64 0x10011e4) = some (0x08054463 : BitVec 32))
          (F_10011e8 : fetch_word segs (Z_to_bv 64 0x10011e8) = some (0x08050663 : BitVec 32))
          (F_1001274 : fetch_word segs (Z_to_bv 64 0x1001274) = some (0x00068a63 : BitVec 32))
          (F_1001288 : fetch_word segs (Z_to_bv 64 0x1001288) = some (0x02070263 : BitVec 32))
          (F_100128c : fetch_word segs (Z_to_bv 64 0x100128c) = some (0x01003537 : BitVec 32))
          (F_1001290 : fetch_word segs (Z_to_bv 64 0x1001290) = some (0x6ec50513 : BitVec 32))
          (F_1001294 : fetch_word segs (Z_to_bv 64 0x1001294) = some (0x00070593 : BitVec 32))
          (F_1001298 : fetch_word segs (Z_to_bv 64 0x1001298) = some (0x00000097 : BitVec 32))
          (F_100129c : fetch_word segs (Z_to_bv 64 0x100129c) = some (0x01c080e7 : BitVec 32))
          (F_10012b4 : fetch_word segs (Z_to_bv 64 0x10012b4) = some (0x00058613 : BitVec 32))
          (F_10012b8 : fetch_word segs (Z_to_bv 64 0x10012b8) = some (0x00050593 : BitVec 32))
          (F_10012bc : fetch_word segs (Z_to_bv 64 0x10012bc) = some (0x04000893 : BitVec 32))
          (F_10012c0 : fetch_word segs (Z_to_bv 64 0x10012c0) = some (0x00060e63 : BitVec 32))
          (F_10012c4 : fetch_word segs (Z_to_bv 64 0x10012c4) = some (0x00100513 : BitVec 32))
          : sym_exec segs 14 [false, true, true, false, false] []
          (SS 0x10011e4 (sr_pins [(10, ELit 0), (13, ELit 0), (14, EVar 32)] sr_id) [] 33) [] =
          (SS 0x10012c8 [EVar 0, ELit 16781984, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 1, ELit 16791276, EAlu .ALU_ADD (EVar 32) (ELit 0), ELit 0, EVar 32, EVar 15, EVar 16, ELit 64, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 33,
           [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]) := by
        let sr0 := sr_pins [(10, ELit 0), (13, ELit 0), (14, EVar 32)] sr_id
        let sr1 := sr_upd sr0 10 (ELit 16789504)
        let sr2 := sr_upd sr1 10 (ELit 16791276)
        let sr3 := sr_upd sr2 11 (EAlu .ALU_ADD (EVar 32) (ELit 0))
        let sr4 := sr_upd sr3 1 (ELit 16781976)
        let sr5 := sr_upd sr4 1 (ELit 16781984)
        let sr6 := sr_upd sr5 12 (EAlu .ALU_ADD (EVar 32) (ELit 0))
        let sr7 := sr_upd sr6 11 (ELit 16791276)
        let sr8 := sr_upd sr7 17 (ELit 64)
        let sr9 := sr_upd sr8 10 (ELit 1)
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10011e4]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x08054463 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e4]
        change sym_exec segs 13 [true, true, false, false] []
          (SS 0x10011e8 sr0 [] 33) [SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10011e8]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x08050663 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e8]
        change sym_exec segs 12 [true, false, false] []
          (SS 0x1001274 sr0 [] 33) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001274]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00068a63 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001274]
        change sym_exec segs 11 [false, false] []
          (SS 0x1001288 sr0 [] 33) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001288]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x02070263 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001288]
        change sym_exec segs 10 [false] []
          (SS 0x100128c sr0 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_100128c]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x01003537 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100128c]
        change sym_exec segs 9 [false] []
          (SS 0x1001290 sr1 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001290]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x6ec50513 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001290]
        change sym_exec segs 8 [false] []
          (SS 0x1001294 sr2 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001294]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00070593 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001294]
        change sym_exec segs 7 [false] []
          (SS 0x1001298 sr3 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_1001298]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00000097 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001298]
        change sym_exec segs 6 [false] []
          (SS 0x100129c sr4 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_100129c]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x01c080e7 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100129c]
        change sym_exec segs 5 [false] []
          (SS 0x10012b4 sr5 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012b4]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00058613 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012b4]
        change sym_exec segs 4 [false] []
          (SS 0x10012b8 sr6 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012b8]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00050593 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012b8]
        change sym_exec segs 3 [false] []
          (SS 0x10012bc sr7 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012bc]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x04000893 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012bc]
        change sym_exec segs 2 [false] []
          (SS 0x10012c0 sr8 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012c0]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00060e63 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012c0]
        change sym_exec segs 1 [] []
          (SS 0x10012c4 sr8 [] 33) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rewrite [sym_exec]
        conv => lhs; dsimp only [sym_state.s_pc]
        rewrite [F_10012c4]
        conv => lhs; dsimp only
        conv => lhs; simp (config := { implicitDefEqProofs := false }) only
          [show is_ecall (0x00100513 : BitVec 32) = false from by decide,
           decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012c4]
        change sym_exec segs 0 [] []
          (SS 0x10012c8 sr9 [] 33) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
        rfl
      let ss0 := SS 0x10011e4 (sr_pins [(10, ELit 0), (13, ELit 0), (14, EVar 32)] sr_id) [] 33
      let ss1 := SS 0x10012c8 [EVar 0, ELit 16781984, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 1, ELit 16791276, EAlu .ALU_ADD (EVar 32) (ELit 0), ELit 0, EVar 32, EVar 15, EVar 16, ELit 64, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 33
      let scs := [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]
      let E := Eplus R [nat_to_word (d :: done').length]
      have Hsc : scs_denot target_segs mem E scs := by
        simp only [scs, scs_denot, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [sc_denot, branch_taken, E]; sym_norm)
        all_goals (scbr <;> omega)
      have Hst : st_ok E mem trom ss0 (mkst R 0x10011e4 mem trom) := by
        refine ⟨R, rfl, regs_ok_pins E [(10, ELit 0), (13, ELit 0), (14, EVar 32)] sr_id R
          (regs_ok_Eplus R [nat_to_word (d :: done').length]) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [E]; sym_env_norm)
        all_goals first | exact H10 | exact H13 | exact H14
      have Hexec : sym_exec target_segs 14 [false, true, true, false, false] [] ss0 [] = (ss1, scs) := by
        apply Hex target_segs
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10011e4 = (0x10011e4 : word) from by decide)).trans tail1_TF_10011e4
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10011e8 = (0x10011e8 : word) from by decide)).trans tail1_TF_10011e8
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001274 = (0x1001274 : word) from by decide)).trans tail1_TF_1001274
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001288 = (0x1001288 : word) from by decide)).trans tail1_TF_1001288
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x100128c = (0x100128c : word) from by decide)).trans tail1_TF_100128c
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001290 = (0x1001290 : word) from by decide)).trans tail1_TF_1001290
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001294 = (0x1001294 : word) from by decide)).trans tail1_TF_1001294
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x1001298 = (0x1001298 : word) from by decide)).trans tail1_TF_1001298
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x100129c = (0x100129c : word) from by decide)).trans tail1_TF_100129c
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012b4 = (0x10012b4 : word) from by decide)).trans tail1_TF_10012b4
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012b8 = (0x10012b8 : word) from by decide)).trans tail1_TF_10012b8
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012bc = (0x10012bc : word) from by decide)).trans tail1_TF_10012bc
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012c0 = (0x10012c0 : word) from by decide)).trans tail1_TF_10012c0
        · exact (congrArg (fetch_word target_segs)
            (show Z_to_bv 64 0x10012c4 = (0x10012c4 : word) from by decide)).trans tail1_TF_10012c4
      obtain ⟨Rx, HRx, Hms⟩ := sym_exec_ex target_segs 14 [false, true, true, false, false] []
        ss0 [] ss1 scs E mem trom (mkst R 0x10011e4 mem trom) Hexec Hsc Hst
      dsimp only [ss0, ss1, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot, E] at Hms HRx
      sym_chain Hms
      apply to_out.tout_step _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_TF_10012c8 rfl)
      apply tout_wr_rec
      · sym_regs HRx; decide +kernel
      · sym_regs HRx; sym_close
      · have Q11 : reg_get Rx 11 = t_done := by sym_regs HRx; bveq
        have Q12 : reg_get Rx 12 = nat_to_word (d :: done').length := by
          sym_regs HRx; exact u0_id _
        rw [Q11, Q12, ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem t_done (word_to_nat (nat_to_word (d :: done').length)) = _
        rw [word_to_nat_ntw _ (by lenlia)]
        exact Hdone
      · dsimp only [List.length_cons]; omega
      · -- 0x10012cc: the put-style retry loop, per delivered length.
        have Q11 : reg_get Rx 11 = t_done := by sym_regs HRx; bveq
        have Q12 : reg_get Rx 12 = nat_to_word (d :: done').length := by
          sym_regs HRx; exact u0_id _
        intro n Hn1 Hn2
        norm_pc
        apply tgt_put_wall av ev tsp arnd Hsp_lo Hsp_hi uid hw
          (d :: done').length (d :: done') t_done n
        · omega
        · exact Hn1
        · exact Hn2
        · dsimp only [List.length_cons] at *; omega
        · regupd_resolve; sym_regs HRx; sym_close
        · regupd_resolve; sym_regs HRx; exact H2
        · regupd_resolve; rfl
        · regupd_resolve; exact Q11
        · regupd_resolve; exact Q12
        · regupd_resolve; sym_regs HRx; decide +kernel
        · regupd_resolve; sym_regs HRx; sym_close
        · exact Hbg
        · exact Hdone
  | cons c cur' =>
    -- cur nonempty: the last line is cur.
    change to_out target_segs (c :: cur') _
    have Hex (segs : List Segment)
        (F_10011e4 : fetch_word segs (Z_to_bv 64 0x10011e4) = some (0x08054463 : BitVec 32))
        (F_10011e8 : fetch_word segs (Z_to_bv 64 0x10011e8) = some (0x08050663 : BitVec 32))
        (F_1001274 : fetch_word segs (Z_to_bv 64 0x1001274) = some (0x00068a63 : BitVec 32))
        (F_1001278 : fetch_word segs (Z_to_bv 64 0x1001278) = some (0x01002537 : BitVec 32))
        (F_100127c : fetch_word segs (Z_to_bv 64 0x100127c) = some (0x6ec50513 : BitVec 32))
        (F_1001280 : fetch_word segs (Z_to_bv 64 0x1001280) = some (0x00068593 : BitVec 32))
        (F_1001284 : fetch_word segs (Z_to_bv 64 0x1001284) = some (0x0140006f : BitVec 32))
        (F_1001298 : fetch_word segs (Z_to_bv 64 0x1001298) = some (0x00000097 : BitVec 32))
        (F_100129c : fetch_word segs (Z_to_bv 64 0x100129c) = some (0x01c080e7 : BitVec 32))
        (F_10012b4 : fetch_word segs (Z_to_bv 64 0x10012b4) = some (0x00058613 : BitVec 32))
        (F_10012b8 : fetch_word segs (Z_to_bv 64 0x10012b8) = some (0x00050593 : BitVec 32))
        (F_10012bc : fetch_word segs (Z_to_bv 64 0x10012bc) = some (0x04000893 : BitVec 32))
        (F_10012c0 : fetch_word segs (Z_to_bv 64 0x10012c0) = some (0x00060e63 : BitVec 32))
        (F_10012c4 : fetch_word segs (Z_to_bv 64 0x10012c4) = some (0x00100513 : BitVec 32))
        : sym_exec segs 14 [false, true, false, false] []
        (SS 0x10011e4 (sr_pins [(10, ELit 0), (13, EVar 32)] sr_id) [] 33) [] =
        (SS 0x10012c8 [EVar 0, ELit 16781984, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 1, ELit 16787180, EAlu .ALU_ADD (EVar 32) (ELit 0), EVar 32, EVar 14, EVar 15, EVar 16, ELit 64, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 33,
         [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]) := by
      let sr0 := sr_pins [(10, ELit 0), (13, EVar 32)] sr_id
      let sr1 := sr_upd sr0 10 (ELit 16785408)
      let sr2 := sr_upd sr1 10 (ELit 16787180)
      let sr3 := sr_upd sr2 11 (EAlu .ALU_ADD (EVar 32) (ELit 0))
      let sr4 := sr_upd sr3 1 (ELit 16781976)
      let sr5 := sr_upd sr4 1 (ELit 16781984)
      let sr6 := sr_upd sr5 12 (EAlu .ALU_ADD (EVar 32) (ELit 0))
      let sr7 := sr_upd sr6 11 (ELit 16787180)
      let sr8 := sr_upd sr7 17 (ELit 64)
      let sr9 := sr_upd sr8 10 (ELit 1)
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10011e4]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x08054463 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e4]
      change sym_exec segs 13 [true, false, false] []
        (SS 0x10011e8 sr0 [] 33) [SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10011e8]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x08050663 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e8]
      change sym_exec segs 12 [false, false] []
        (SS 0x1001274 sr0 [] 33) [SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_1001274]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00068a63 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001274]
      change sym_exec segs 11 [false] []
        (SS 0x1001278 sr0 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_1001278]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x01002537 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001278]
      change sym_exec segs 10 [false] []
        (SS 0x100127c sr1 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_100127c]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x6ec50513 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100127c]
      change sym_exec segs 9 [false] []
        (SS 0x1001280 sr2 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_1001280]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00068593 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001280]
      change sym_exec segs 8 [false] []
        (SS 0x1001284 sr3 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_1001284]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x0140006f : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001284]
      change sym_exec segs 7 [false] []
        (SS 0x1001298 sr3 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_1001298]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00000097 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001298]
      change sym_exec segs 6 [false] []
        (SS 0x100129c sr4 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_100129c]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x01c080e7 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100129c]
      change sym_exec segs 5 [false] []
        (SS 0x10012b4 sr5 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10012b4]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00058613 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012b4]
      change sym_exec segs 4 [false] []
        (SS 0x10012b8 sr6 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10012b8]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00050593 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012b8]
      change sym_exec segs 3 [false] []
        (SS 0x10012bc sr7 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10012bc]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x04000893 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012bc]
      change sym_exec segs 2 [false] []
        (SS 0x10012c0 sr8 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10012c0]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00060e63 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012c0]
      change sym_exec segs 1 [] []
        (SS 0x10012c4 sr8 [] 33) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rewrite [sym_exec]
      conv => lhs; dsimp only [sym_state.s_pc]
      rewrite [F_10012c4]
      conv => lhs; dsimp only
      conv => lhs; simp (config := { implicitDefEqProofs := false }) only
        [show is_ecall (0x00100513 : BitVec 32) = false from by decide,
         decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10012c4]
      change sym_exec segs 0 [] []
        (SS 0x10012c8 sr9 [] 33) [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)] = _
      rfl
    let ss0 := SS 0x10011e4 (sr_pins [(10, ELit 0), (13, EVar 32)] sr_id) [] 33
    let ss1 := SS 0x10012c8 [EVar 0, ELit 16781984, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7, EVar 8, EVar 9, ELit 1, ELit 16787180, EAlu .ALU_ADD (EVar 32) (ELit 0), EVar 32, EVar 14, EVar 15, EVar 16, ELit 64, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23, EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31] [] 33
    let scs := [SCBr false .BC_EQ (EAlu .ALU_ADD (EVar 32) (ELit 0)) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr true .BC_EQ (ELit 0) (ELit 0), SCBr false .BC_LT (ELit 0) (ELit 0)]
    let E := Eplus R [nat_to_word (c :: cur').length]
    have Hsc : scs_denot target_segs mem E scs := by
      simp only [scs, scs_denot, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals (dsimp only [sc_denot, branch_taken, E]; sym_norm)
      all_goals (scbr <;> omega)
    have Hst : st_ok E mem trom ss0 (mkst R 0x10011e4 mem trom) := by
      refine ⟨R, rfl, regs_ok_pins E [(10, ELit 0), (13, EVar 32)] sr_id R
        (regs_ok_Eplus R [nat_to_word (c :: cur').length]) ?_, True.intro⟩
      simp only [pins_ok, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals (dsimp only [E]; sym_env_norm)
      all_goals first | exact H10 | exact H13 | exact H14
    have Hexec : sym_exec target_segs 14 [false, true, false, false] [] ss0 [] = (ss1, scs) := by
      apply Hex target_segs
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10011e4 = (0x10011e4 : word) from by decide)).trans tail1_TF_10011e4
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10011e8 = (0x10011e8 : word) from by decide)).trans tail1_TF_10011e8
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x1001274 = (0x1001274 : word) from by decide)).trans tail1_TF_1001274
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x1001278 = (0x1001278 : word) from by decide)).trans tail1_TF_1001278
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x100127c = (0x100127c : word) from by decide)).trans tail1_TF_100127c
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x1001280 = (0x1001280 : word) from by decide)).trans tail1_TF_1001280
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x1001284 = (0x1001284 : word) from by decide)).trans tail1_TF_1001284
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x1001298 = (0x1001298 : word) from by decide)).trans tail1_TF_1001298
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x100129c = (0x100129c : word) from by decide)).trans tail1_TF_100129c
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10012b4 = (0x10012b4 : word) from by decide)).trans tail1_TF_10012b4
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10012b8 = (0x10012b8 : word) from by decide)).trans tail1_TF_10012b8
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10012bc = (0x10012bc : word) from by decide)).trans tail1_TF_10012bc
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10012c0 = (0x10012c0 : word) from by decide)).trans tail1_TF_10012c0
      · exact (congrArg (fetch_word target_segs)
          (show Z_to_bv 64 0x10012c4 = (0x10012c4 : word) from by decide)).trans tail1_TF_10012c4
    obtain ⟨Rx, HRx, Hms⟩ := sym_exec_ex target_segs 14 [false, true, false, false] []
      ss0 [] ss1 scs E mem trom (mkst R 0x10011e4 mem trom) Hexec Hsc Hst
    dsimp only [ss0, ss1, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot, E] at Hms HRx
    sym_chain Hms
    apply to_out.tout_step _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_TF_10012c8 rfl)
    apply tout_wr_rec
    · sym_regs HRx; decide +kernel
    · sym_regs HRx; sym_close
    · have Q11 : reg_get Rx 11 = t_cur := by sym_regs HRx; bveq
      have Q12 : reg_get Rx 12 = nat_to_word (c :: cur').length := by
        sym_regs HRx; exact u0_id _
      rw [Q11, Q12, ms_read_bytes_rdn target_segs _ _ _ rfl]
      change rdn target_segs mem t_cur (word_to_nat (nat_to_word (c :: cur').length)) = _
      rw [word_to_nat_ntw _ (by lenlia)]
      exact Hcur
    · dsimp only [List.length_cons]; omega
    · -- 0x10012cc: the put-style retry loop, per delivered length.
      have Q11 : reg_get Rx 11 = t_cur := by sym_regs HRx; bveq
      have Q12 : reg_get Rx 12 = nat_to_word (c :: cur').length := by
        sym_regs HRx; exact u0_id _
      intro n Hn1 Hn2
      norm_pc
      apply tgt_put_wall av ev tsp arnd Hsp_lo Hsp_hi uid hw
        (c :: cur').length (c :: cur') t_cur n
      · omega
      · exact Hn1
      · exact Hn2
      · dsimp only [List.length_cons] at *; omega
      · regupd_resolve; sym_regs HRx; sym_close
      · regupd_resolve; sym_regs HRx; exact H2
      · regupd_resolve; rfl
      · regupd_resolve; exact Q11
      · regupd_resolve; exact Q12
      · regupd_resolve; sym_regs HRx; decide +kernel
      · regupd_resolve; sym_regs HRx; sym_close
      · exact Hbg
      · exact Hcur

include Hsp_lo Hsp_hi in
/-- Per-block continuation: from the post-read state (a0 = |bs|,
pc 0x10011e4) fold the block and reach the loop head or exit 3. -/
theorem tgt_post_read_dispatch (R : bvmap 5 word) (mem : word → Option byte)
    (cur done bs : List byte)
    (H2 : reg_get R 2 = Z_to_bv 64 (bv_unsigned tsp - 32))
    (H5 : reg_get R 5 = t_cur) (H16 : reg_get R 16 = t_done)
    (H15 : reg_get R 15 = Z_to_bv 64 10) (H11 : reg_get R 11 = t_rb)
    (H13 : reg_get R 13 = nat_to_word cur.length)
    (H14 : reg_get R 14 = nat_to_word done.length)
    (H10 : reg_get R 10 = nat_to_word bs.length)
    (Hbg : bgt_ok av ev tsp arnd uid hw mem)
    (Hrb : rdn target_segs mem t_rb bs.length = some bs)
    (Hcur : rdn target_segs mem t_cur cur.length = some cur)
    (Hdone : rdn target_segs mem t_done done.length = some done)
    (Hcurcap : (cur.length : Int) ≤ 4096) (Hdonecap : (done.length : Int) ≤ 4097)
    (Hblo : 1 ≤ (bs.length : Int)) (Hbhi : (bs.length : Int) ≤ 1024) :
    match procs f (cur, done) bs with
    | some a' => lh_next target_segs (tgt_LH av ev tsp arnd uid hw) a' (mkst R 0x10011e4 mem trom)
    | none => to_exit target_segs ec (mkst R 0x10011e4 mem trom) := by
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  -- The non-EOF tests, then the byte index is zeroed.
  let sr0 := sr_pins [(10, EVar 32)] sr_id
  let sr3 := sr_upd sr0 12 (ELit 0)
  have Hex (segs : List Segment)
      (F_10011e4 : fetch_word segs (Z_to_bv 64 16781796) = some (0x08054463 : BitVec 32))
      (F_10011e8 : fetch_word segs (Z_to_bv 64 16781800) = some (0x08050663 : BitVec 32))
      (F_10011ec : fetch_word segs (Z_to_bv 64 16781804) = some (0x00000613 : BitVec 32))
      (F_10011f0 : fetch_word segs (Z_to_bv 64 16781808) = some (0xfe0502e3 : BitVec 32))
      : sym_exec segs 4 [false, false, false] [] (SS 16781796 sr0 [] 33) [] = ((SS 16781812 sr3 [] 33), [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)]) := by
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011e4]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x08054463 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e4]
    change sym_exec segs 3 [false, false] [] (SS 16781800 sr0 [] 33) [SCBr false .BC_LT (EVar 32) (ELit 0)] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011e8]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x08050663 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011e8]
    change sym_exec segs 2 [false] [] (SS 16781804 sr0 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011ec]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011ec]
    change sym_exec segs 1 [false] [] (SS 16781808 sr3 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011f0]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe0502e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011f0]
    rfl
  have Hexec : sym_exec target_segs 4 [false, false, false] [] (SS 16781796 sr0 [] 33) [] = ((SS 16781812 sr3 [] 33), [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)]) := by
    apply Hex target_segs
    · exact tail1_TF_10011e4
    · exact tail1_TF_10011e8
    · exact tail1_TF_10011ec
    · exact tail1_TF_10011f0
  have Hsc : scs_denot target_segs mem (Eplus R ([nat_to_word bs.length] ++ [])) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)] := by
    simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
    all_goals sym_norm
    all_goals try sym_sc_auto
    · scbr
    · scbr
    · rw [bv_lts_signed, bv_signed_small _ (by rw [u_ntw _ (by omega)] <;> omega), u_ntw _ (by omega)]
      change decide ((bs.length : Int) < 0) = false
      apply decide_eq_false <;> omega
  have Hst : st_ok (Eplus R ([nat_to_word bs.length] ++ [])) mem trom (SS 16781796 sr0 [] 33) (mkst R (Z_to_bv 64 16781796) mem trom) := by
    refine ⟨R, rfl, regs_ok_pins (Eplus R ([nat_to_word bs.length] ++ [])) [(10, EVar 32)] sr_id R
      (regs_ok_Eplus R ([nat_to_word bs.length] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    all_goals repeat' apply And.intro
    all_goals (sym_env_norm <;> try sym_pin_auto)
    · exact H10
  obtain ⟨RG, HRG, Hms⟩ := sym_exec_ex target_segs 4 [false, false, false] [] (SS 16781796 sr0 [] 33) []
    (SS 16781812 sr3 [] 33) [SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_EQ (EVar 32) (ELit 0), SCBr false .BC_LT (EVar 32) (ELit 0)] (Eplus R ([nat_to_word bs.length] ++ [])) mem trom (mkst R (Z_to_bv 64 16781796) mem trom) Hexec Hsc Hst
  dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hms
  dsimp only [sym_state.s_regs, sr3, sr0] at HRG
  have HBLH : BLHt av ev tsp arnd uid hw cur done bs 0 (mkst RG 0x10011f4 mem trom) := by
    refine ⟨RG, mem, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | assumption | omega | (sym_regs HRG <;> first | assumption | sym_close)
  have Hbl := byte_loop_t av ev tsp arnd Hsp_lo Hsp_hi uid hw bs.length cur done bs 0
    (mkst RG 0x10011f4 mem trom) (by omega) HBLH
  rw [List.drop_zero] at Hbl
  cases He : procs f (cur, done) bs with
  | some a' =>
    rw [He] at Hbl
    obtain ⟨msL, HmsL, HL⟩ := Hbl
    exact ⟨msL, msteps_trans target_segs _ _ _ Hms HmsL, HL⟩
  | none =>
    rw [He] at Hbl
    exact msteps_to_exit_t ec _ _ Hms Hbl

include Hsp_lo Hsp_hi in
/-- One loop iteration: the DrainSim per-binary obligation. -/
theorem tgt_LH_to_rd (a : A) (ms : machine_state)
    (HLH : tgt_LH av ev tsp arnd uid hw a ms) :
    to_rd target_segs (Z_to_bv 64 1024) f out ec (tgt_LH av ev tsp arnd uid hw) a ms := by
  rcases a with ⟨cur, done⟩
  obtain ⟨regs, mem, rfl, H2, H5, H16, H15, H11, H13, H14,
    Hbg, Hcur, Hdone, Hcurcap, Hdonecap⟩ := HLH
  dsimp only [Prod.fst, Prod.snd] at *
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  -- li a7,63 ; li a2,1024 ; li a0,0 ; (ecall).
  let sr0 := sr_pins [] sr_id
  let sr1 := sr_upd sr0 17 (ELit 63)
  let sr2 := sr_upd sr1 12 (ELit 1024)
  let sr3 := sr_upd sr2 10 (ELit 0)
  have Hex (segs : List Segment)
      (F_10011d4 : fetch_word segs (Z_to_bv 64 16781780) = some (0x03f00893 : BitVec 32))
      (F_10011d8 : fetch_word segs (Z_to_bv 64 16781784) = some (0x40000613 : BitVec 32))
      (F_10011dc : fetch_word segs (Z_to_bv 64 16781788) = some (0x00000513 : BitVec 32))
      : sym_exec segs 3 [] [] (SS 16781780 sr0 [] 32) [] = ((SS 16781792 sr3 [] 32), []) := by
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011d4]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x03f00893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011d4]
    change sym_exec segs 2 [] [] (SS 16781784 sr1 [] 32) [] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011d8]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x40000613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011d8]
    change sym_exec segs 1 [] [] (SS 16781788 sr2 [] 32) [] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011dc]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011dc]
    rfl
  have Hexec : sym_exec target_segs 3 [] [] (SS 16781780 sr0 [] 32) [] = ((SS 16781792 sr3 [] 32), []) := by
    apply Hex target_segs
    · exact tail1_TF_10011d4
    · exact tail1_TF_10011d8
    · exact tail1_TF_10011dc
  have Hsc : scs_denot target_segs mem (Eplus regs ([] ++ [])) [] := by
    simp only [scs_denot, List.not_mem_nil, false_implies, implies_true]
  have Hst : st_ok (Eplus regs ([] ++ [])) mem trom (SS 16781780 sr0 [] 32) (mkst regs (Z_to_bv 64 16781780) mem trom) := by
    refine ⟨regs, rfl, regs_ok_pins (Eplus regs ([] ++ [])) [] sr_id regs
      (regs_ok_Eplus regs ([] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.not_mem_nil, false_implies, implies_true]
    all_goals repeat' apply And.intro
    all_goals (sym_env_norm <;> try sym_pin_auto)
  obtain ⟨RG, HRG, Hblock⟩ := sym_exec_ex target_segs 3 [] [] (SS 16781780 sr0 [] 32) []
    (SS 16781792 sr3 [] 32) [] (Eplus regs ([] ++ [])) mem trom (mkst regs (Z_to_bv 64 16781780) mem trom) Hexec Hsc Hst
  dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hblock
  dsimp only [sym_state.s_regs, sr3, sr2, sr1, sr0] at HRG
  sym_chain Hblock
  apply to_rd.trd_step _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ tail1_TF_10011e0 rfl
  apply trd_here_rec _ _ _ _ _ _ _ _ _ _ _ t_rb
  · sym_regs HRG <;> decide +kernel
  · sym_regs HRG <;> sym_close
  · sym_regs HRG <;> exact H11
  · sym_regs HRG <;> sym_close
  · exact target_rb_wseg
  · -- The link-time constant buffer is far below TASK_SIZE.
    apply LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.access_okb_intro
    rw [u_t_rb]
    change (0x10022ec : Int) + 1024 ≤ TASK_SIZE
    unfold TASK_SIZE
    omega
  · norm_pc
    apply tgt_eof_to_out av ev tsp arnd Hsp_lo Hsp_hi uid hw
    · sym_regs HRG <;> exact H2
    · sym_regs HRG <;> sym_close
    · sym_regs HRG <;> exact H13
    · sym_regs HRG <;> exact H14
    · exact Hbg
    · exact Hcur
    · exact Hdone
    · exact Hcurcap
    · exact Hdonecap
  · exact out_modeled cur done Hcurcap Hdonecap
  · intro bs Hblo Hbhi
    wlits
    have Hdispatch := tgt_post_read_dispatch av ev tsp arnd Hsp_lo Hsp_hi uid hw
      (regupd RG 10 (len_word bs)) (write_to_mem mem t_rb bs) cur done bs
      (by regupd_resolve; sym_regs HRG <;> exact H2)
      (by regupd_resolve; sym_regs HRG <;> exact H5)
      (by regupd_resolve; sym_regs HRG <;> exact H16)
      (by regupd_resolve; sym_regs HRG <;> exact H15)
      (by regupd_resolve; sym_regs HRG <;> exact H11)
      (by regupd_resolve; sym_regs HRG <;> exact H13)
      (by regupd_resolve; sym_regs HRG <;> exact H14)
      (by regupd_resolve; exact len_word_nat bs)
      (by apply bgt_ok_wtm_below av ev tsp arnd uid hw _ _ _ Hbg; unormT; omega)
      (by apply rdn_write_to_mem; unormT; omega)
      (by
        rw [rdn_wtm_out _ _ _ _ _ _ (by unormT; omega) (by unormT; omega)
          (Or.inl (by unormT; omega))]
        exact Hcur)
      (by
        rw [rdn_wtm_out _ _ _ _ _ _ (by unormT; omega) (by unormT; omega)
          (Or.inl (by unormT; omega))]
        exact Hdone)
      Hcurcap Hdonecap Hblo Hbhi
    cases He : procs f (cur, done) bs with
    | some a' =>
      rw [He] at Hdispatch
      exact Hdispatch
    | none =>
      rw [He] at Hdispatch
      exact Hdispatch

include Hsp_lo Hsp_hi in
/-- From the initial state to the loop head. -/
theorem tgt_init_to_rd :
    to_rd target_segs (Z_to_bv 64 1024) f out ec (tgt_LH av ev tsp arnd uid hw) a0
      (init_machine_state target_segs 0x1001190 target_phdrs tsp arnd av ev uid hw) := by
  have Hlo := tsp_lo_num tsp Hsp_lo
  have Hhi := tsp_hi_num tsp Hsp_hi
  rw [init_mkst]
  norm_pc
  -- _start's frame and call into main, then main's frame and register setup.
  -- The block crosses jalr; its exit memory is tgt_bg.
  let sr0 := sr_pins [(1, ELit 0), (2, EVar 32)] sr_id
  let sr1 := sr_upd sr0 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))
  let sr3 := sr_upd sr1 1 (ELit 16781720)
  let sr4 := sr_upd sr3 1 (ELit 16781728)
  let sr5 := sr_upd sr4 2 (EAlu .ALU_ADD (EVar 32) (ELit (-32)))
  let sr7 := sr_upd sr5 14 (ELit 0)
  let sr8 := sr_upd sr7 13 (ELit 0)
  let sr9 := sr_upd sr8 11 (ELit 16785408)
  let sr10 := sr_upd sr9 11 (ELit 16786156)
  let sr11 := sr_upd sr10 15 (ELit 10)
  let sr12 := sr_upd sr11 16 (ELit 16789504)
  let sr13 := sr_upd sr12 16 (ELit 16791276)
  let sr14 := sr_upd sr13 5 (ELit 16785408)
  let sr15 := sr_upd sr14 5 (ELit 16787180)
  have Hex (segs : List Segment)
      (F_1001190 : fetch_word segs (Z_to_bv 64 16781712) = some (0xff010113 : BitVec 32))
      (F_1001194 : fetch_word segs (Z_to_bv 64 16781716) = some (0x00113423 : BitVec 32))
      (F_1001198 : fetch_word segs (Z_to_bv 64 16781720) = some (0x00000097 : BitVec 32))
      (F_100119c : fetch_word segs (Z_to_bv 64 16781724) = some (0x010080e7 : BitVec 32))
      (F_10011a8 : fetch_word segs (Z_to_bv 64 16781736) = some (0xff010113 : BitVec 32))
      (F_10011ac : fetch_word segs (Z_to_bv 64 16781740) = some (0x00113423 : BitVec 32))
      (F_10011b0 : fetch_word segs (Z_to_bv 64 16781744) = some (0x00000713 : BitVec 32))
      (F_10011b4 : fetch_word segs (Z_to_bv 64 16781748) = some (0x00000693 : BitVec 32))
      (F_10011b8 : fetch_word segs (Z_to_bv 64 16781752) = some (0x010025b7 : BitVec 32))
      (F_10011bc : fetch_word segs (Z_to_bv 64 16781756) = some (0x2ec58593 : BitVec 32))
      (F_10011c0 : fetch_word segs (Z_to_bv 64 16781760) = some (0x00a00793 : BitVec 32))
      (F_10011c4 : fetch_word segs (Z_to_bv 64 16781764) = some (0x01003837 : BitVec 32))
      (F_10011c8 : fetch_word segs (Z_to_bv 64 16781768) = some (0x6ec80813 : BitVec 32))
      (F_10011cc : fetch_word segs (Z_to_bv 64 16781772) = some (0x010022b7 : BitVec 32))
      (F_10011d0 : fetch_word segs (Z_to_bv 64 16781776) = some (0x6ec28293 : BitVec 32))
      : sym_exec segs 15 [] [] (SS 16781712 sr0 [] 33) [] = ((SS 16781780 sr15 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33), [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]) := by
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_1001190]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001190]
    change sym_exec segs 14 [] [] (SS 16781716 sr1 [] 33) [] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_1001194]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001194]
    change sym_exec segs 13 [] [] (SS 16781720 sr1 [SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_1001198]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000097 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_1001198]
    change sym_exec segs 12 [] [] (SS 16781724 sr3 [SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_100119c]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x010080e7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_100119c]
    change sym_exec segs 11 [] [] (SS 16781736 sr4 [SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011a8]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011a8]
    change sym_exec segs 10 [] [] (SS 16781740 sr5 [SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011ac]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011ac]
    change sym_exec segs 9 [] [] (SS 16781744 sr5 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011b0]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011b0]
    change sym_exec segs 8 [] [] (SS 16781748 sr7 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011b4]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011b4]
    change sym_exec segs 7 [] [] (SS 16781752 sr8 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011b8]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x010025b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011b8]
    change sym_exec segs 6 [] [] (SS 16781756 sr9 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011bc]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x2ec58593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011bc]
    change sym_exec segs 5 [] [] (SS 16781760 sr10 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011c0]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a00793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011c0]
    change sym_exec segs 4 [] [] (SS 16781764 sr11 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011c4]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01003837 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011c4]
    change sym_exec segs 3 [] [] (SS 16781768 sr12 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011c8]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x6ec80813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011c8]
    change sym_exec segs 2 [] [] (SS 16781772 sr13 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011cc]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x010022b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011cc]
    change sym_exec segs 1 [] [] (SS 16781776 sr14 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] = _
    rewrite [sym_exec]
    conv => lhs <;> dsimp only [sym_state.s_pc]
    rewrite [F_10011d0]
    conv => lhs <;> dsimp only
    conv => lhs <;> simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x6ec28293 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, TD_10011d0]
    rfl
  have Hexec : sym_exec target_segs 15 [] [] (SS 16781712 sr0 [] 33) [] = ((SS 16781780 sr15 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33), [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]) := by
    apply Hex target_segs
    · exact tail1_TF_1001190
    · exact tail1_TF_1001194
    · exact tail1_TF_1001198
    · exact tail1_TF_100119c
    · exact tail1_TF_10011a8
    · exact tail1_TF_10011ac
    · exact tail1_TF_10011b0
    · exact tail1_TF_10011b4
    · exact tail1_TF_10011b8
    · exact tail1_TF_10011bc
    · exact tail1_TF_10011c0
    · exact tail1_TF_10011c4
    · exact tail1_TF_10011c8
    · exact tail1_TF_10011cc
    · exact tail1_TF_10011d0
  have Hsc : scs_denot target_segs (twmem av ev tsp arnd uid hw) (Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) ([tsp] ++ [])) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] := by
    simp only [scs_denot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]
    all_goals sym_norm
    all_goals try sym_sc_auto
    · solve_store_ok_inv
    · solve_store_ok_inv
  have Hst : st_ok (Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) ([tsp] ++ [])) (twmem av ev tsp arnd uid hw) trom (SS 16781712 sr0 [] 33) (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) (Z_to_bv 64 16781712) (twmem av ev tsp arnd uid hw) trom) := by
    refine ⟨(regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp), rfl, regs_ok_pins (Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) ([tsp] ++ [])) [(1, ELit 0), (2, EVar 32)] sr_id (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp)
      (regs_ok_Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) ([tsp] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    all_goals repeat' apply And.intro
    all_goals (sym_env_norm <;> try sym_pin_auto)
    all_goals (getr_resolve <;> rfl)
  obtain ⟨RG, HRG, Hblock⟩ := sym_exec_ex target_segs 15 [] [] (SS 16781712 sr0 [] 33) []
    (SS 16781780 sr15 [SE (SA (SBVar 32) (-24)) 8 (ELit 16781728), SE (SA (SBVar 32) (-8)) 8 (ELit 0)] 33) [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8, SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8] (Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) ([tsp] ++ [])) (twmem av ev tsp arnd uid hw) trom (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 tsp) (Z_to_bv 64 16781712) (twmem av ev tsp arnd uid hw) trom) Hexec Hsc Hst
  dsimp only [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at Hblock
  dsimp only [sym_state.s_regs, sr15, sr14, sr13, sr12, sr11, sr10, sr9, sr8, sr7, sr5, sr4, sr3, sr1, sr0] at HRG
  sym_chain Hblock
  apply tgt_LH_to_rd av ev tsp arnd Hsp_lo Hsp_hi uid hw
  refine ⟨RG, _, rfl, ?_⟩
  dsimp only [a0, Prod.fst, Prod.snd, List.length_nil]
  repeat' apply And.intro
  all_goals first
    | (sym_regs HRG <;> first | rfl | sym_close)
    | exact bgt_ok_bg av ev tsp arnd uid hw
    | rfl
    | omega

end TargetProof
end LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_target
