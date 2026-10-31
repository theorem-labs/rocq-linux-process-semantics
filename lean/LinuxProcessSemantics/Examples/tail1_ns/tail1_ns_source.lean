import LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs
import LinuxProcessSemantics.Common.ListFacts
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # tail1-ns, source binary (musl-gcc -Os). PROOF-SIDE FILE.

Conventions: bytes are `byte = bv 8`, machine values `word = bv 64`;
counts/indices live in registers as `nat_to_word`; sp-relative
addresses in the canonical `Z_to_bv 64 (bv_unsigned rsp - k)` form.

Each step simp after a `rewrite [SD_x]` rewrites `is_ecall` and `!decide True`
(`decide_true`, `Bool.not_true`), so that the step's left side is headed by the
instruction's match rather than by `ite`. Left as an `ite`, nanoda (nanoda_lib
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`) unfolds `sym_exec` first and compares the match
alternatives under their binders, where its `try_reduce_nat` (`src/tc.rs`) refuses every term
with a free variable, so the `% 2 ^ 64` of a branch target runs through unary `Nat.modCore`. -/

namespace LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.DrainSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.ListFacts
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.tail1_ns.SourceMemImage
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_code
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs

def rb_base : word := 0x13008
def cur_base : word := 0x14410
def done_base : word := 0x13408

theorem u_rb_base : bv_unsigned rb_base = 0x13008 := by decide
theorem u_cur_base : bv_unsigned cur_base = 0x14410 := by decide
theorem u_done_base : bv_unsigned done_base = 0x13408 := by decide

/-- Collapse `bv_unsigned` of the buffer bases, `base + nat_to_word j`
offsets and canonical sp-relative addresses to plain `Int` (window
bounds and index bounds must be in context for the arithmetic sides). -/
local macro "unorm" : tactic => `(tactic| (
  imm_norm
  have := u_rb_base
  have := u_cur_base
  have := u_done_base
  repeat rewrite [word_add_nat]
  repeat (focus (rewrite [u_Z2bv]; rotate_left;
                 (try simp only [u_rb_base, u_cur_base, u_done_base]); omega
                 (try simp only [u_rb_base, u_cur_base, u_done_base]); omega))
  try simp only [u_rb_base, u_cur_base, u_done_base]))

/- Spelling bridges between the reflective executor and the tactic
layer's memory lemmas.

The executor writes an address as `Z_to_bv 64 (bv_unsigned b + k)`
(the `saddr` normal form) and a stored byte as `word_to_le_bytes 1 v`;
the read-back lemmas are stated over the base word and a singleton byte
list. These three collapse the difference, once, instead of a `replace`
per access. -/
theorem u0_id (x : word) : Z_to_bv 64 (bv_unsigned x + 0) = x := by
  rw [Int.add_zero]
  apply bv_eq_of_unsigned
  exact u_Z2bv _ (u64_range x).1 (u64_range x).2

theorem wle1_byte (b : byte) :
    word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b] := by
  have hb := u8_range b
  rw [N_to_le_bytes_1_small, u_Z2bv _ (by omega) (by omega)]
  congr 1
  change BitVec.ofInt 8 (b.toNat : Int) = b
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

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
every shift as the register form, `_start`'s `slli a0,3` included. -/
theorem v_sll_lit (x : word) (sh : Int) (Hsh : 0 ≤ sh ∧ sh < 64) :
    v_sll x (Z_to_bv 64 sh) = v_slli x sh := by
  unfold v_sll v_slli
  rw [u_Z2bv sh (by omega) (by omega), Int.emod_eq_of_lt Hsh.1 Hsh.2]

/-- Resolve an `x0` read before closing a bitvector goal. Lean's `bveq`
tries only `rfl` on an open goal without unassigned metavariables and
reports `OPEN` if conversion fails (Common/StepTac.lean). -/
theorem getr_x0z (rs : bvmap 5 word) : getr rs 0 = Z_to_bv 64 0 := by rfl

/-- Collapse every `bv_unsigned` of a counter or literal to `Int`. -/
local macro "lenlia" : tactic => `(tactic| (
  (try dsimp only [List.length_cons, List.length_nil] at *)
  omega))

local macro "lennorm" : tactic => `(tactic| (
  (try dsimp only [List.length_cons, List.length_nil] at *)
  try omega))

local macro "numnorm" : tactic => `(tactic| (
  repeat (focus (rewrite [u_ntw]; rotate_left; solve | lennorm))
  repeat (focus (rewrite [u_Z2bv]; rotate_left; (repeat (focus (rewrite [u_ntw]; rotate_left; solve | lennorm))); (solve | lennorm); (repeat (focus (rewrite [u_ntw]; rotate_left; solve | lennorm))); solve | lennorm))
  try dsimp only [List.length_cons, List.length_nil] at *))

/-- The generic `SCBr` closer: push the comparison down to `Int` and hand
it to arithmetic. The `rfl` alternative closes a branch whose operands
the pins made literal. -/
local macro "scbr" : tactic => `(tactic| first
  | rfl
  | ((repeat with_reducible rewrite [Bool.not_eq_true'])
     (repeat with_reducible rewrite [Bool.not_eq_false'])
     (repeat rewrite [bv_lts_signed])
     (repeat rewrite [bv_ltu_Z])
     (repeat rewrite [bv_eqb_Z])
     (repeat (focus (rewrite [LinuxProcessSemantics.Common.PropExec.bv_signed_small]; rotate_left; numnorm <;> omega)))
     numnorm
     first | apply decide_eq_true | apply decide_eq_false
     omega))

/- Closers for the two obligation shapes a counting loop leaves. -/
/- An `addi rd,rs,1` on a `nat_to_word` counter. -/
local macro "ntw_succ" : tactic => `(tactic| (
  apply bv_eq_of_unsigned
  simp only [nat_to_word, Z_to_bv_unsigned, bv_wrap64_mod, Int.ofNat_eq_natCast]
  omega))

/- A `beq`/`bne` between two `nat_to_word` counters, possibly with a
literal displacement. -/
local macro "brz" : tactic => `(tactic| (
  (repeat with_reducible rewrite [Bool.not_eq_true'])
  (repeat with_reducible rewrite [Bool.not_eq_false'])
  (repeat rewrite [bv_eqb_Z])
  (repeat (focus (rewrite [u_Z2bv]; rotate_left; (repeat (focus (rewrite [u_ntw]; rotate_left; omega))); omega; (repeat (focus (rewrite [u_ntw]; rotate_left; omega))); omega)))
  (repeat (focus (rewrite [u_ntw]; rotate_left; omega)))
  first | apply decide_eq_true | apply decide_eq_false
  omega))

/- A register the caller pinned as a LITERAL: the pin obligation is
stated against `Z_to_bv 64 z` and the caller's hypothesis against the
numeral the example gave the constant. -/
local macro "pin_lit" c:term:max : tactic => `(tactic| (
  conv => rhs; tactic => exact (show _ = $c from by bveq)))

/-- `sym_sc_auto` closes an `SCFlat` by arithmetic once the address's base
is bounded; a buffer base plus an index is an opaque atom until the
range fact is posed. -/
local macro "scflat" : tactic => `(tactic| (
  (repeat (focus (rewrite [u_ntw]; rotate_left; omega)))
  unorm
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let target ← Lean.Elab.Tactic.getMainTarget
      let mut seen : Array Lean.Expr := #[]
      while let some e := target.find? (fun e =>
          e.isAppOfArity ``bv_unsigned 2 && (e.getArg! 0).nat? == some 64 &&
          !seen.contains e) do
        seen := seen.push e
        let mut bounded := false
        for h in ← Lean.getLCtx do
          let t := h.type
          if t.isAppOfArity ``And 2 then
            let lower := t.getArg! 0
            let upper := t.getArg! 1
            if lower.isAppOfArity ``LE.le 4 && lower.appArg! == e &&
                upper.isAppOfArity ``LT.lt 4 && upper.getArg! 2 == e &&
                (← Lean.Meta.isDefEq (lower.getArg! 2) (Lean.mkIntLit 0)) then
              bounded := true
        unless bounded do
          let p ← Lean.Meta.mkAppM ``u64_range #[e.appArg!]
          let g ← Lean.Elab.Tactic.getMainGoal
          let (_, g') ← (← g.assert (← Lean.mkFreshUserName `Hrange)
            (← Lean.Meta.inferType p) p).intro1P
          Lean.Elab.Tactic.replaceMainGoal [g']
  (repeat' apply And.intro) <;> omega))

/-- The scripts extract the block's `msteps` hypothesis from `sym_exec_ex`
using `Exists.elim` and `obtain`. Normalize that hypothesis: unfold the
valuation, put the log's addresses into the tactic layer's spelling,
and collapse the one-byte stores. -/
local macro "hms_norm" H:ident : tactic => `(tactic| (
  (repeat rewrite [adenot_var] at $H:ident)
  (repeat rewrite [adenot_lit] at $H:ident)
  (repeat rewrite [bdenot_var] at $H:ident)
  (repeat rewrite [bdenot_lit] at $H:ident)
  (repeat rewrite [edenot_lit] at $H:ident)
  (repeat rewrite [edenot_var] at $H:ident)
  try simp only [Eplus, Nat.blt, Nat.ble, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, Bool.false_eq_true, ite_true, ite_false,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    List.append_nil, List.cons_append, List.nil_append, Prod.fst, Prod.snd,
    saddr.a_base, saddr.a_off, sentry.e_addr, sentry.e_width, sentry.e_val] at $H:ident
  (repeat rewrite [u0_id] at $H:ident)
  (repeat rewrite [wle1_byte] at $H:ident)))

/-! Each `tail1_SF_` lemma states the fetch of its generated `SF_` twin, proved
through `tail1_src_fetch` (see `tail1_hex_read`). -/

theorem tail1_SF_11000 : fetch_word source_segs 0x11000 = some 0xfd010113 :=
  tail1_src_fetch 0x11000 0x13 0x01 0x01 0xfd (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11004 : fetch_word source_segs 0x11004 = some 0x01213823 :=
  tail1_src_fetch 0x11004 0x23 0x38 0x21 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11008 : fetch_word source_segs 0x11008 = some 0x01313423 :=
  tail1_src_fetch 0x11008 0x23 0x34 0x31 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1100c : fetch_word source_segs 0x1100c = some 0x00014937 :=
  tail1_src_fetch 0x1100c 0x37 0x49 0x01 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11010 : fetch_word source_segs 0x11010 = some 0x000139b7 :=
  tail1_src_fetch 0x11010 0xb7 0x39 0x01 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11014 : fetch_word source_segs 0x11014 = some 0x02813023 :=
  tail1_src_fetch 0x11014 0x23 0x30 0x81 0x02 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11018 : fetch_word source_segs 0x11018 = some 0x00913c23 :=
  tail1_src_fetch 0x11018 0x23 0x3c 0x91 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1101c : fetch_word source_segs 0x1101c = some 0x02113423 :=
  tail1_src_fetch 0x1101c 0x23 0x34 0x11 0x02 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11020 : fetch_word source_segs 0x11020 = some 0x00000493 :=
  tail1_src_fetch 0x11020 0x93 0x04 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11024 : fetch_word source_segs 0x11024 = some 0x00000413 :=
  tail1_src_fetch 0x11024 0x13 0x04 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11028 : fetch_word source_segs 0x11028 = some 0x41090913 :=
  tail1_src_fetch 0x11028 0x13 0x09 0x09 0x41 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1102c : fetch_word source_segs 0x1102c = some 0x40898993 :=
  tail1_src_fetch 0x1102c 0x93 0x89 0x89 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11030 : fetch_word source_segs 0x11030 = some 0x80818593 :=
  tail1_src_fetch 0x11030 0x93 0x85 0x81 0x80 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11034 : fetch_word source_segs 0x11034 = some 0x40000613 :=
  tail1_src_fetch 0x11034 0x13 0x06 0x00 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11038 : fetch_word source_segs 0x11038 = some 0x00000513 :=
  tail1_src_fetch 0x11038 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1103c : fetch_word source_segs 0x1103c = some 0x170000ef :=
  tail1_src_fetch 0x1103c 0xef 0x00 0x00 0x17 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11040 : fetch_word source_segs 0x11040 = some 0x10054263 :=
  tail1_src_fetch 0x11040 0x63 0x42 0x05 0x10 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11044 : fetch_word source_segs 0x11044 = some 0x06050863 :=
  tail1_src_fetch 0x11044 0x63 0x08 0x05 0x06 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11048 : fetch_word source_segs 0x11048 = some 0x00000713 :=
  tail1_src_fetch 0x11048 0x13 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1104c : fetch_word source_segs 0x1104c = some 0x00a00693 :=
  tail1_src_fetch 0x1104c 0x93 0x06 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11050 : fetch_word source_segs 0x11050 = some 0x00001637 :=
  tail1_src_fetch 0x11050 0x37 0x16 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11054 : fetch_word source_segs 0x11054 = some 0x80818593 :=
  tail1_src_fetch 0x11054 0x93 0x85 0x81 0x80 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11058 : fetch_word source_segs 0x11058 = some 0x00e587b3 :=
  tail1_src_fetch 0x11058 0xb3 0x87 0xe5 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1105c : fetch_word source_segs 0x1105c = some 0x0007c783 :=
  tail1_src_fetch 0x1105c 0x83 0xc7 0x07 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11060 : fetch_word source_segs 0x11060 = some 0x04d79063 :=
  tail1_src_fetch 0x11060 0x63 0x90 0xd7 0x04 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11064 : fetch_word source_segs 0x11064 = some 0x00000793 :=
  tail1_src_fetch 0x11064 0x93 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11068 : fetch_word source_segs 0x11068 = some 0x0180006f :=
  tail1_src_fetch 0x11068 0x6f 0x00 0x80 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1106c : fetch_word source_segs 0x1106c = some 0x012788b3 :=
  tail1_src_fetch 0x1106c 0xb3 0x88 0x27 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11070 : fetch_word source_segs 0x11070 = some 0x0008c883 :=
  tail1_src_fetch 0x11070 0x83 0xc8 0x08 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11074 : fetch_word source_segs 0x11074 = some 0x00f98833 :=
  tail1_src_fetch 0x11074 0x33 0x88 0xf9 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11078 : fetch_word source_segs 0x11078 = some 0x00178793 :=
  tail1_src_fetch 0x11078 0x93 0x87 0x17 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1107c : fetch_word source_segs 0x1107c = some 0x01180023 :=
  tail1_src_fetch 0x1107c 0x23 0x00 0x18 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11080 : fetch_word source_segs 0x11080 = some 0xfe8796e3 :=
  tail1_src_fetch 0x11080 0xe3 0x96 0x87 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11084 : fetch_word source_segs 0x11084 = some 0x008987b3 :=
  tail1_src_fetch 0x11084 0xb3 0x87 0x89 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11088 : fetch_word source_segs 0x11088 = some 0x00140493 :=
  tail1_src_fetch 0x11088 0x93 0x04 0x14 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1108c : fetch_word source_segs 0x1108c = some 0x00d78023 :=
  tail1_src_fetch 0x1108c 0x23 0x80 0xd7 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11090 : fetch_word source_segs 0x11090 = some 0x00000413 :=
  tail1_src_fetch 0x11090 0x13 0x04 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11094 : fetch_word source_segs 0x11094 = some 0x00170713 :=
  tail1_src_fetch 0x11094 0x13 0x07 0x17 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11098 : fetch_word source_segs 0x11098 = some 0xfca740e3 :=
  tail1_src_fetch 0x11098 0xe3 0x40 0xa7 0xfc (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1109c : fetch_word source_segs 0x1109c = some 0xf95ff06f :=
  tail1_src_fetch 0x1109c 0x6f 0xf0 0x5f 0xf9 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110a0 : fetch_word source_segs 0x110a0 = some 0x0ac40663 :=
  tail1_src_fetch 0x110a0 0x63 0x06 0xc4 0x0a (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110a4 : fetch_word source_segs 0x110a4 = some 0x00890833 :=
  tail1_src_fetch 0x110a4 0x33 0x08 0x89 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110a8 : fetch_word source_segs 0x110a8 = some 0x00f80023 :=
  tail1_src_fetch 0x110a8 0x23 0x00 0xf8 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110ac : fetch_word source_segs 0x110ac = some 0x00140413 :=
  tail1_src_fetch 0x110ac 0x13 0x04 0x14 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110b0 : fetch_word source_segs 0x110b0 = some 0xfe5ff06f :=
  tail1_src_fetch 0x110b0 0x6f 0xf0 0x5f 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110b4 : fetch_word source_segs 0x110b4 = some 0x04040a63 :=
  tail1_src_fetch 0x110b4 0x63 0x0a 0x04 0x04 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110b8 : fetch_word source_segs 0x110b8 = some 0x000144b7 :=
  tail1_src_fetch 0x110b8 0xb7 0x44 0x01 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110bc : fetch_word source_segs 0x110bc = some 0x41048493 :=
  tail1_src_fetch 0x110bc 0x93 0x84 0x04 0x41 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110c0 : fetch_word source_segs 0x110c0 = some 0x00040613 :=
  tail1_src_fetch 0x110c0 0x13 0x06 0x04 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110c4 : fetch_word source_segs 0x110c4 = some 0x00048593 :=
  tail1_src_fetch 0x110c4 0x93 0x85 0x04 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110c8 : fetch_word source_segs 0x110c8 = some 0x00100513 :=
  tail1_src_fetch 0x110c8 0x13 0x05 0x10 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110cc : fetch_word source_segs 0x110cc = some 0x114000ef :=
  tail1_src_fetch 0x110cc 0xef 0x00 0x40 0x11 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110d0 : fetch_word source_segs 0x110d0 = some 0x06a05663 :=
  tail1_src_fetch 0x110d0 0x63 0x56 0xa0 0x06 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110d4 : fetch_word source_segs 0x110d4 = some 0x40a40433 :=
  tail1_src_fetch 0x110d4 0x33 0x04 0xa4 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110d8 : fetch_word source_segs 0x110d8 = some 0x00a484b3 :=
  tail1_src_fetch 0x110d8 0xb3 0x84 0xa4 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110dc : fetch_word source_segs 0x110dc = some 0xfe0412e3 :=
  tail1_src_fetch 0x110dc 0xe3 0x12 0x04 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110e0 : fetch_word source_segs 0x110e0 = some 0x00000513 :=
  tail1_src_fetch 0x110e0 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110e4 : fetch_word source_segs 0x110e4 = some 0x00a03533 :=
  tail1_src_fetch 0x110e4 0x33 0x35 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110e8 : fetch_word source_segs 0x110e8 = some 0x0025151b :=
  tail1_src_fetch 0x110e8 0x1b 0x15 0x25 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110ec : fetch_word source_segs 0x110ec = some 0x02813083 :=
  tail1_src_fetch 0x110ec 0x83 0x30 0x81 0x02 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110f0 : fetch_word source_segs 0x110f0 = some 0x02013403 :=
  tail1_src_fetch 0x110f0 0x03 0x34 0x01 0x02 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110f4 : fetch_word source_segs 0x110f4 = some 0x01813483 :=
  tail1_src_fetch 0x110f4 0x83 0x34 0x81 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110f8 : fetch_word source_segs 0x110f8 = some 0x01013903 :=
  tail1_src_fetch 0x110f8 0x03 0x39 0x01 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_110fc : fetch_word source_segs 0x110fc = some 0x00813983 :=
  tail1_src_fetch 0x110fc 0x83 0x39 0x81 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11100 : fetch_word source_segs 0x11100 = some 0x03010113 :=
  tail1_src_fetch 0x11100 0x13 0x01 0x01 0x03 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11104 : fetch_word source_segs 0x11104 = some 0x00008067 :=
  tail1_src_fetch 0x11104 0x67 0x80 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11108 : fetch_word source_segs 0x11108 = some 0x00000513 :=
  tail1_src_fetch 0x11108 0x13 0x05 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1110c : fetch_word source_segs 0x1110c = some 0xfe0480e3 :=
  tail1_src_fetch 0x1110c 0xe3 0x80 0x04 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11110 : fetch_word source_segs 0x11110 = some 0x00013437 :=
  tail1_src_fetch 0x11110 0x37 0x34 0x01 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11114 : fetch_word source_segs 0x11114 = some 0x40840413 :=
  tail1_src_fetch 0x11114 0x13 0x04 0x84 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11118 : fetch_word source_segs 0x11118 = some 0x00048613 :=
  tail1_src_fetch 0x11118 0x13 0x86 0x04 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1111c : fetch_word source_segs 0x1111c = some 0x00040593 :=
  tail1_src_fetch 0x1111c 0x93 0x05 0x04 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11120 : fetch_word source_segs 0x11120 = some 0x00100513 :=
  tail1_src_fetch 0x11120 0x13 0x05 0x10 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11124 : fetch_word source_segs 0x11124 = some 0x0bc000ef :=
  tail1_src_fetch 0x11124 0xef 0x00 0xc0 0x0b (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11128 : fetch_word source_segs 0x11128 = some 0x00a05a63 :=
  tail1_src_fetch 0x11128 0x63 0x5a 0xa0 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1112c : fetch_word source_segs 0x1112c = some 0x40a484b3 :=
  tail1_src_fetch 0x1112c 0xb3 0x84 0xa4 0x40 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11130 : fetch_word source_segs 0x11130 = some 0x00a40433 :=
  tail1_src_fetch 0x11130 0x33 0x04 0xa4 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11134 : fetch_word source_segs 0x11134 = some 0xfe0492e3 :=
  tail1_src_fetch 0x11134 0xe3 0x92 0x04 0xfe (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11138 : fetch_word source_segs 0x11138 = some 0xfa9ff06f :=
  tail1_src_fetch 0x11138 0x6f 0xf0 0x9f 0xfa (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1114c : fetch_word source_segs 0x1114c = some 0x00300513 :=
  tail1_src_fetch 0x1114c 0x13 0x05 0x30 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11150 : fetch_word source_segs 0x11150 = some 0xf9dff06f :=
  tail1_src_fetch 0x11150 0x6f 0xf0 0xdf 0xf9 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11154 : fetch_word source_segs 0x11154 = some 0x00002197 :=
  tail1_src_fetch 0x11154 0x97 0x21 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11158 : fetch_word source_segs 0x11158 = some 0x6ac18193 :=
  tail1_src_fetch 0x11158 0x93 0x81 0xc1 0x6a (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1115c : fetch_word source_segs 0x1115c = some 0x00013503 :=
  tail1_src_fetch 0x1115c 0x03 0x35 0x01 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11160 : fetch_word source_segs 0x11160 = some 0x00810593 :=
  tail1_src_fetch 0x11160 0x93 0x05 0x81 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11164 : fetch_word source_segs 0x11164 = some 0x00351293 :=
  tail1_src_fetch 0x11164 0x93 0x12 0x35 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11168 : fetch_word source_segs 0x11168 = some 0x00558633 :=
  tail1_src_fetch 0x11168 0x33 0x86 0x55 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1116c : fetch_word source_segs 0x1116c = some 0x00860613 :=
  tail1_src_fetch 0x1116c 0x13 0x06 0x86 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11170 : fetch_word source_segs 0x11170 = some 0x00002317 :=
  tail1_src_fetch 0x11170 0x17 0x23 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11174 : fetch_word source_segs 0x11174 = some 0xe9030313 :=
  tail1_src_fetch 0x11174 0x13 0x03 0x03 0xe9 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11178 : fetch_word source_segs 0x11178 = some 0x00c33023 :=
  tail1_src_fetch 0x11178 0x23 0x30 0xc3 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1117c : fetch_word source_segs 0x1117c = some 0xe85ff0ef :=
  tail1_src_fetch 0x1117c 0xef 0xf0 0x5f 0xe8 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11180 : fetch_word source_segs 0x11180 = some 0x05d00893 :=
  tail1_src_fetch 0x11180 0x93 0x08 0xd0 0x05 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11184 : fetch_word source_segs 0x11184 = some 0x00000073 :=
  tail1_src_fetch 0x11184 0x73 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111ac : fetch_word source_segs 0x111ac = some 0xff010113 :=
  tail1_src_fetch 0x111ac 0x13 0x01 0x01 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111b0 : fetch_word source_segs 0x111b0 = some 0x00060693 :=
  tail1_src_fetch 0x111b0 0x93 0x06 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111b4 : fetch_word source_segs 0x111b4 = some 0x00000813 :=
  tail1_src_fetch 0x111b4 0x13 0x08 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111b8 : fetch_word source_segs 0x111b8 = some 0x00058613 :=
  tail1_src_fetch 0x111b8 0x13 0x86 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111bc : fetch_word source_segs 0x111bc = some 0x00000793 :=
  tail1_src_fetch 0x111bc 0x93 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111c0 : fetch_word source_segs 0x111c0 = some 0x00050593 :=
  tail1_src_fetch 0x111c0 0x93 0x05 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111c4 : fetch_word source_segs 0x111c4 = some 0x00000713 :=
  tail1_src_fetch 0x111c4 0x13 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111c8 : fetch_word source_segs 0x111c8 = some 0x03f00513 :=
  tail1_src_fetch 0x111c8 0x13 0x05 0xf0 0x03 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111cc : fetch_word source_segs 0x111cc = some 0x00113423 :=
  tail1_src_fetch 0x111cc 0x23 0x34 0x11 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111d0 : fetch_word source_segs 0x111d0 = some 0x0a0000ef :=
  tail1_src_fetch 0x111d0 0xef 0x00 0x00 0x0a (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111d4 : fetch_word source_segs 0x111d4 = some 0x00813083 :=
  tail1_src_fetch 0x111d4 0x83 0x30 0x81 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111d8 : fetch_word source_segs 0x111d8 = some 0x01010113 :=
  tail1_src_fetch 0x111d8 0x13 0x01 0x01 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111dc : fetch_word source_segs 0x111dc = some 0x0380006f :=
  tail1_src_fetch 0x111dc 0x6f 0x00 0x80 0x03 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111e0 : fetch_word source_segs 0x111e0 = some 0xff010113 :=
  tail1_src_fetch 0x111e0 0x13 0x01 0x01 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111e4 : fetch_word source_segs 0x111e4 = some 0x00060693 :=
  tail1_src_fetch 0x111e4 0x93 0x06 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111e8 : fetch_word source_segs 0x111e8 = some 0x00000813 :=
  tail1_src_fetch 0x111e8 0x13 0x08 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111ec : fetch_word source_segs 0x111ec = some 0x00058613 :=
  tail1_src_fetch 0x111ec 0x13 0x86 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111f0 : fetch_word source_segs 0x111f0 = some 0x00000793 :=
  tail1_src_fetch 0x111f0 0x93 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111f4 : fetch_word source_segs 0x111f4 = some 0x00050593 :=
  tail1_src_fetch 0x111f4 0x93 0x05 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111f8 : fetch_word source_segs 0x111f8 = some 0x00000713 :=
  tail1_src_fetch 0x111f8 0x13 0x07 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_111fc : fetch_word source_segs 0x111fc = some 0x04000513 :=
  tail1_src_fetch 0x111fc 0x13 0x05 0x00 0x04 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11200 : fetch_word source_segs 0x11200 = some 0x00113423 :=
  tail1_src_fetch 0x11200 0x23 0x34 0x11 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11204 : fetch_word source_segs 0x11204 = some 0x06c000ef :=
  tail1_src_fetch 0x11204 0xef 0x00 0xc0 0x06 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11208 : fetch_word source_segs 0x11208 = some 0x00813083 :=
  tail1_src_fetch 0x11208 0x83 0x30 0x81 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1120c : fetch_word source_segs 0x1120c = some 0x01010113 :=
  tail1_src_fetch 0x1120c 0x13 0x01 0x01 0x01 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11210 : fetch_word source_segs 0x11210 = some 0x0040006f :=
  tail1_src_fetch 0x11210 0x6f 0x00 0x40 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11214 : fetch_word source_segs 0x11214 = some 0xfffff7b7 :=
  tail1_src_fetch 0x11214 0xb7 0xf7 0xff 0xff (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11218 : fetch_word source_segs 0x11218 = some 0x00a7e463 :=
  tail1_src_fetch 0x11218 0x63 0xe4 0xa7 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1121c : fetch_word source_segs 0x1121c = some 0x00008067 :=
  tail1_src_fetch 0x1121c 0x67 0x80 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1124c : fetch_word source_segs 0x1124c = some 0x00050893 :=
  tail1_src_fetch 0x1124c 0x93 0x08 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11250 : fetch_word source_segs 0x11250 = some 0x00058513 :=
  tail1_src_fetch 0x11250 0x13 0x85 0x05 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11254 : fetch_word source_segs 0x11254 = some 0x00060593 :=
  tail1_src_fetch 0x11254 0x93 0x05 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11258 : fetch_word source_segs 0x11258 = some 0x00068613 :=
  tail1_src_fetch 0x11258 0x13 0x86 0x06 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1125c : fetch_word source_segs 0x1125c = some 0x00070693 :=
  tail1_src_fetch 0x1125c 0x93 0x06 0x07 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11260 : fetch_word source_segs 0x11260 = some 0x00078713 :=
  tail1_src_fetch 0x11260 0x13 0x87 0x07 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11264 : fetch_word source_segs 0x11264 = some 0x00080793 :=
  tail1_src_fetch 0x11264 0x93 0x07 0x08 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11268 : fetch_word source_segs 0x11268 = some 0x00000073 :=
  tail1_src_fetch 0x11268 0x73 0x00 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_1126c : fetch_word source_segs 0x1126c = some 0x00008067 :=
  tail1_src_fetch 0x1126c 0x67 0x80 0x00 0x00 (by decide +kernel) rfl (by decide +kernel)

theorem tail1_SF_11270 : fetch_word source_segs 0x11270 = some 0xfddff06f :=
  tail1_src_fetch 0x11270 0x6f 0xf0 0xdf 0xfd (by decide +kernel) rfl (by decide +kernel)

section SourceProof

variable (av ev : List (List byte))
variable (Hva : valid_argv av) (Hve : valid_envp ev)
variable (rsp : word)

/- The entry stack draw this run was started with
(`Run.ExecEntry`'s `en_draw`): the 16 AT_RANDOM bytes the kernel
picks afresh at every `execve` (`fs/binfmt_elf.c`, `create_elf_tables`,
Linux v6.18.46 at 1f99e9ab748f: `get_random_bytes` into
`k_rand_bytes[16]`), and the bytes of the entry stack's
last page above the block. This proof may assume NOTHING about
either, exactly as it may assume nothing about where the stack
landed. Quantified per binary, so the target's draw below is a
different variable. -/
variable (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
variable (uid hw : word)

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := by exact Hsp_lo

include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := by exact Hsp_hi

-- Rocq: tail1_ns_source.v's argcN (renamed: Common/ArgvEnv.lean declares the same short name).
def tail1_argcN : word := len_word av
-- Rocq: tail1_ns_source.v's wmem (renamed: Common/ArgvEnv.lean declares the same short name).
def tail1_wmem : word → Option byte := wrap_mem source_phdrs rsp av ev uid hw rrnd
def rrom : word → Option byte := seg_rom source_segs

include Hva in
-- Rocq: tail1_ns_source.v's u_argcN (renamed: Common/ArgvEnv.lean declares the same short name).
theorem tail1_u_argcN : bv_unsigned (tail1_argcN av) = (av.length : Int) := by
  have Hlen := valid_argv_len av Hva
  unfold tail1_argcN len_word
  apply u_Z2bv <;> omega

include Hva Hve Hsp_hi in
/-- No-overflow bound for the initial stack image (feeds the stack-read
lemmas' side conditions). -/
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev uid hw rrnd).length : Int)
      < 2 ^ 64 := by
  have Hbsb := bsb_bound source_phdrs rsp av ev uid hw rrnd Hva Hve
  have Hhi := rsp_hi_num rsp Hsp_hi
  omega

/-- The pointer _start stores into musl's `environ` slot at 0x13000. -/
-- Rocq: tail1_ns_source.v's envp_ptr (renamed: Common/ArgvEnv.lean declares the same short name).
def tail1_envp_ptr : word := Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (av.length : Int) + 8)

include Hva Hsp_lo Hsp_hi in
-- Rocq: tail1_ns_source.v's envp_ptr_eq (renamed: Common/ArgvEnv.lean declares the same short name).
theorem tail1_envp_ptr_eq :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (tail1_argcN av) (Z_to_bv 64 3))) + 8) = tail1_envp_ptr av rsp := by
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hlo := rsp_lo_num rsp Hsp_lo
  rw [alu_add, v_sll_lit (tail1_argcN av) 3 (by omega)]
  have Hlen := valid_argv_len av Hva
  apply bv_eq_of_unsigned
  unfold tail1_envp_ptr
  repeat rewrite [Z_to_bv_unsigned]
  rw [v_add_small _ _ (by
    rw [u_Z2bv _ (by omega) (by omega),
      v_slli_3 _ (by rw [tail1_u_argcN av Hva]; omega), tail1_u_argcN av Hva]
    omega)]
  rewrite [u_Z2bv _ (by omega) (by omega),
    v_slli_3 _ (by rw [tail1_u_argcN av Hva]; omega), tail1_u_argcN av Hva]
  congr 1 <;> omega

/-- Background memory: _start's environ store and main's saved-register
frame over tail1_wmem, in execution order.
`environ @ 0x13000 = tail1_envp_ptr ; ra @ rsp-8 = 0x11180 ;`
`s0..s3 @ rsp-16 .. rsp-40 = 0`. (gcc 15 saves only ra/s0..s3;
the 48-byte frame's bottom slot `0(sp) = rsp-48` is never touched.) -/
def src_bg : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (tail1_wmem av ev rsp rrnd uid hw)
    0x13000 (word_to_le_bytes 8 (tail1_envp_ptr av rsp)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x11180 : word))

/-- `bg_ok mem`: `mem` agrees with `src_bg` on everything at or above the
frame bottom `rsp-48`. All wrapper scratch and all buffer stores lie
strictly below `rsp-48`, so this is preserved throughout.
(New no-overflow premise, inherited from `rdn_ext`.)

…and it is still writable wherever `tail1_wmem` was: every machine store
targets the frame or the wrapper scratch, i.e. the RLIMIT_STACK
window `tail1_wmem` zero-maps, and `mem` is quantified existentially in
`src_LH`, so the `store_ok` bound has to travel with it.

The two clauses sit under ONE `forall`, and `bg_ok` is SEALED
(`irreducible`, just below the preservation lemmas). Both are needed to
keep repeated splitting — which the scripts below use to establish the
loop-head predicates, of which `bg_ok` is a conjunct — from taking
it apart into halves that none of the preservation lemmas match. -/
def bg_ok (mem : word → Option byte) : Prop :=
  ∀ (a : word) (n : Nat),
    (bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      bv_unsigned rsp - 48 ≤ bv_unsigned a →
      rdn source_segs mem a n = rdn source_segs (src_bg av ev rsp rrnd uid hw) a n) ∧
    (tail1_wmem av ev rsp rrnd uid hw a ≠ none → mem a ≠ none)

/-- The two projections; `bg_grows` is what the store-bound dispatcher
reaches for (via `store_ok_db`), and both are the only way past the
seal below. -/
theorem bg_agree_of (mem : word → Option byte) (H : bg_ok av ev rsp rrnd uid hw mem)
    (a : word) (n : Nat) (Hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (Ha : bv_unsigned rsp - 48 ≤ bv_unsigned a) :
    rdn source_segs mem a n = rdn source_segs (src_bg av ev rsp rrnd uid hw) a n := by
  exact (H a n).1 Hnw Ha

theorem bg_grows (mem : word → Option byte) (H : bg_ok av ev rsp rrnd uid hw mem) :
    mem_grows (tail1_wmem av ev rsp rrnd uid hw) mem := by
  intro x
  exact (H x 0).2

local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply bg_grows; assumption))

theorem bg_ok_bg : bg_ok av ev rsp rrnd uid hw (src_bg av ev rsp rrnd uid hw) := by
  have Hg : mem_grows (tail1_wmem av ev rsp rrnd uid hw) (src_bg av ev rsp rrnd uid hw) := by
    unfold src_bg
    solve_mem_grows
  intro a n
  exact ⟨fun _ _ => rfl, Hg a⟩

theorem bg_ok_wbytes_below (mem : word → Option byte) (addr : word) (bs : List byte)
    (Hm : bg_ok av ev rsp rrnd uid hw mem)
    (Hlt : bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned rsp - 48) :
    bg_ok av ev rsp rrnd uid hw (wbytes mem addr bs) := by
  have Hg := bg_grows av ev rsp rrnd uid hw mem Hm
  have Hg' : mem_grows (tail1_wmem av ev rsp rrnd uid hw) (wbytes mem addr bs) := by
    solve_mem_grows
  intro a n
  refine ⟨?_, Hg' a⟩
  intro Hnw Ha
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by omega) Hnw]
  exact bg_agree_of av ev rsp rrnd uid hw mem Hm a n Hnw Ha

theorem bg_ok_wtm_below (mem : word → Option byte) (buf : word) (data : List byte)
    (Hm : bg_ok av ev rsp rrnd uid hw mem)
    (Hlt : bv_unsigned buf + (data.length : Int) ≤ bv_unsigned rsp - 48) :
    bg_ok av ev rsp rrnd uid hw (write_to_mem mem buf data) := by
  have Hg := bg_grows av ev rsp rrnd uid hw mem Hm
  have Hg' : mem_grows (tail1_wmem av ev rsp rrnd uid hw) (write_to_mem mem buf data) := by
    solve_mem_grows
  intro a n
  refine ⟨?_, Hg' a⟩
  intro Hnw Ha
  have := u64_range rsp
  rw [rdn_wtm_out _ _ _ _ _ _ Hnw (by omega) (Or.inl (by omega))]
  exact bg_agree_of av ev rsp rrnd uid hw mem Hm a n Hnw Ha

/-- 8-byte scratch stores below the frame preserve bg_ok. -/
theorem bg_ok_scr8 (mem : word → Option byte) (a v : word)
    (Hm : bg_ok av ev rsp rrnd uid hw mem)
    (Ha : bv_unsigned a + 8 ≤ bv_unsigned rsp - 48) :
    bg_ok av ev rsp rrnd uid hw (wbytes mem a (word_to_le_bytes 8 v)) := by
  apply bg_ok_wbytes_below av ev rsp rrnd uid hw _ _ _ Hm
  rw [length_N_to_le_bytes]
  exact Ha

attribute [irreducible] bg_ok

/- Frame-slot reads through a bg_ok memory. -/
local macro "slot_read" : tactic => `(tactic| (
  unfold src_bg
  repeat first
    | (focus (rewrite [rdn_wbytes_below]; rotate_left; (repeat rewrite [length_N_to_le_bytes]); imm_norm; u_norm; omega; (repeat rewrite [length_N_to_le_bytes]); imm_norm; u_norm; omega))
    | (focus (rewrite [rdn_wbytes_disjoint]; rotate_left; (repeat rewrite [length_N_to_le_bytes]); imm_norm; u_norm; omega; (repeat rewrite [length_N_to_le_bytes]); imm_norm; u_norm; omega))
  apply rdn_wbytes_hit8
  u_norm
  omega))

include Hsp_lo Hsp_hi in
theorem bg_read_ra (mem : word → Option byte) (Hm : bg_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x11180 : word)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [bg_agree_of av ev rsp rrnd uid hw mem Hm _ _ (by u_norm; omega) (by u_norm; omega)]
  slot_read

include Hsp_lo Hsp_hi in
theorem bg_read_s0 (mem : word → Option byte) (Hm : bg_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [bg_agree_of av ev rsp rrnd uid hw mem Hm _ _ (by u_norm; omega) (by u_norm; omega)]
  slot_read

include Hsp_lo Hsp_hi in
theorem bg_read_s1 (mem : word → Option byte) (Hm : bg_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [bg_agree_of av ev rsp rrnd uid hw mem Hm _ _ (by u_norm; omega) (by u_norm; omega)]
  slot_read

include Hsp_lo Hsp_hi in
theorem bg_read_s2 (mem : word → Option byte) (Hm : bg_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [bg_agree_of av ev rsp rrnd uid hw mem Hm _ _ (by u_norm; omega) (by u_norm; omega)]
  slot_read

include Hsp_lo Hsp_hi in
theorem bg_read_s3 (mem : word → Option byte) (Hm : bg_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [bg_agree_of av ev rsp rrnd uid hw mem Hm _ _ (by u_norm; omega) (by u_norm; omega)]
  slot_read

include Hsp_lo Hsp_hi in
/-- The copy loop: cur[0..|cur|) -> done[0..|cur|). -/
theorem copy_loop (k j : Nat) (cur : List byte) (R : bvmap 5 word) (mem : word → Option byte)
    (Hk : cur.length - j = k) (Hj : j ≤ cur.length) (Hcap : (cur.length : Int) ≤ 4096)
    (H15 : reg_get R 15 = nat_to_word j) (H8 : reg_get R 8 = nat_to_word cur.length)
    (H18 : reg_get R 18 = cur_base) (H19 : reg_get R 19 = done_base)
    (Hbg : bg_ok av ev rsp rrnd uid hw mem)
    (Hcur : rdn source_segs mem cur_base cur.length = some cur)
    (Hdone : rdn source_segs mem done_base j = some (cur.take j)) :
    ∃ (mem' : word → Option byte) (R' : bvmap 5 word),
      msteps source_segs (mkst R 0x11080 mem rrom) (mkst R' 0x11084 mem' rrom) ∧
      reg_get R' 2 = reg_get R 2 ∧ reg_get R' 3 = reg_get R 3 ∧
      reg_get R' 8 = reg_get R 8 ∧ reg_get R' 9 = reg_get R 9 ∧
      reg_get R' 18 = reg_get R 18 ∧ reg_get R' 19 = reg_get R 19 ∧
      reg_get R' 10 = reg_get R 10 ∧ reg_get R' 14 = reg_get R 14 ∧
      reg_get R' 11 = reg_get R 11 ∧ reg_get R' 12 = reg_get R 12 ∧
      reg_get R' 13 = reg_get R 13 ∧ bg_ok av ev rsp rrnd uid hw mem' ∧
      rdn source_segs mem' cur_base cur.length = some cur ∧
      rdn source_segs mem' done_base cur.length = some cur ∧
      (∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ bv_unsigned done_base →
        rdn source_segs mem' a n = rdn source_segs mem a n) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  induction k generalizing j R mem with
  | zero =>
    have Hjeq : j = cur.length := by omega
    subst j
    rw [List.take_length] at Hdone
    refine ⟨mem, R, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Hbg, Hcur, Hdone, fun _ _ _ => rfl⟩
    apply msteps.mst_step _ _ _ rfl
    · apply step_bne_ft _ _ _ _ _ _ _ _ _ tail1_SF_11080 rfl SD_11080
      getr_resolve
      rw [H15, H8]
      apply c_eq_refl
    · norm_pc
      apply msteps.mst_refl
  | succ k IH =>
    have Hjlt : j < cur.length := by omega
    let mem' := wbytes mem (done_base + nat_to_word j) [cur.getD j (Z_to_bv 8 0)]
    have Hpre : ∃ rg, msteps source_segs (mkst R 0x11080 mem rrom)
        (mkst rg 0x11080 mem' rrom) ∧
        reg_get rg 15 = nat_to_word (j + 1) ∧
        reg_get rg 8 = reg_get R 8 ∧ reg_get rg 18 = reg_get R 18 ∧
        reg_get rg 19 = reg_get R 19 ∧
        reg_get rg 2 = reg_get R 2 ∧ reg_get rg 3 = reg_get R 3 ∧
        reg_get rg 9 = reg_get R 9 ∧
        reg_get rg 10 = reg_get R 10 ∧ reg_get rg 14 = reg_get R 14 ∧
        reg_get rg 11 = reg_get R 11 ∧ reg_get rg 12 = reg_get R 12 ∧
        reg_get rg 13 = reg_get R 13 := by
      let ss0 := SS 69760 (sr_pins [(15, EVar 32), (8, EVar 33), (18, ELit 82960), (19, ELit 78856)] sr_id) [] 34
      let ss1 := SS 69740 ss0.s_regs [] 34
      let ss2 := SS 69744 (sr_upd ss1.s_regs 17 (EAlu .ALU_ADD (EVar 32) (ELit 82960))) [] 34
      let ss3 := SS 69748 (sr_upd ss2.s_regs 17 (EVar 34)) [] 35
      let ss4 := SS 69752 (sr_upd ss3.s_regs 16 (EAlu .ALU_ADD (ELit 78856) (EVar 32))) [] 35
      let ss5 := SS 69756 (sr_upd ss4.s_regs 15 (EAlu .ALU_ADD (EVar 32) (ELit 1))) [] 35
      let ss6 := SS 69760 ss5.s_regs [SE (SA (SBVar 32) 78856) 1 (EVar 34)] 35
      let c0 := [SCBr true .BC_NE (EVar 32) (EVar 33)]
      let c2 := [SCFlat (SA (SBVar 32) 82960) 1, SCReadBase (SA (SBVar 32) 82960) 1 (EVar 34)]
      let c5 := [SCFlat (SA (SBVar 32) 78856) 1, SCStoreOk (SA (SBVar 32) 78856) 1]
      let scs := c5 ++ c2 ++ c0
      have Hexec (segs : List Segment)
          (F0 : fetch_word segs (Z_to_bv 64 69760) = some 0xfe8796e3)
          (F1 : fetch_word segs (Z_to_bv 64 69740) = some 0x012788b3)
          (F2 : fetch_word segs (Z_to_bv 64 69744) = some 0x0008c883)
          (F3 : fetch_word segs (Z_to_bv 64 69748) = some 0x00f98833)
          (F4 : fetch_word segs (Z_to_bv 64 69752) = some 0x00178793)
          (F5 : fetch_word segs (Z_to_bv 64 69756) = some 0x01180023) : sym_exec segs 6 [true] [] ss0 [] = (ss6, scs) := by
        rewrite [sym_exec, F0]
        dsimp only []
        rewrite [SD_11080]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe8796e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 5 [] [] ss1 (c0) = _
        rewrite [sym_exec, F1]
        dsimp only []
        rewrite [SD_1106c]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x012788b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 4 [] [] ss2 (c0) = _
        rewrite [sym_exec, F2]
        dsimp only []
        rewrite [SD_11070]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0008c883 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 3 [] [] ss3 (c2 ++ c0) = _
        rewrite [sym_exec, F3]
        dsimp only []
        rewrite [SD_11074]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00f98833 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 2 [] [] ss4 (c2 ++ c0) = _
        rewrite [sym_exec, F4]
        dsimp only []
        rewrite [SD_11078]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00178793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 1 [] [] ss5 (c2 ++ c0) = _
        rewrite [sym_exec, F5]
        dsimp only []
        rewrite [SD_1107c]
        rfl
      let E := Eplus R ([nat_to_word j, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])
      refine Exists.elim (sym_exec_ex source_segs 6 [true] [] ss0 [] ss6 scs E
        mem rrom (mkst R (Z_to_bv 64 69760) mem rrom) (Hexec source_segs tail1_SF_11080 tail1_SF_1106c tail1_SF_11070 tail1_SF_11074 tail1_SF_11078 tail1_SF_1107c) ?sc ?st) ?cont
      case' cont =>
        intro R2 HH
        obtain ⟨HR2, Hms⟩ := HH
        dsimp only [ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR2 Hms
      case' st =>
        refine ⟨R, rfl, regs_ok_pins E [(15, EVar 32), (8, EVar 33), (18, ELit 82960), (19, ELit 78856)] sr_id R
          (regs_ok_Eplus R ([nat_to_word j, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned (cur.getD j (Z_to_bv 8 0)))])) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
      case' sc =>
        dsimp only [scs, c0, c2, c5, List.cons_append, List.nil_append]
        simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
        all_goals sym_norm
        all_goals try sym_sc_auto
      · scflat
      · rw [addr_base_ntw done_base 78856 j u_done_base (by omega)]
        apply source_store_ok <;> unorm <;> omega
      · scflat
      · rw [addr_base_ntw cur_base 82960 j u_cur_base (by omega)]
        refine ⟨[cur.getD j (Z_to_bv 8 0)], rdn_nth _ _ _ _ _ _ Hcur Hjlt, ?_⟩
        rw [bytes_le_to_Z_1]
        exact (zext_byte_u _).symm
      · brz
      · exact H15
      · exact H8
      · pin_lit cur_base
        exact H18
      · pin_lit done_base
        exact H19
      · hms_norm Hms
        rw [addr_base_ntw done_base 78856 j u_done_base (by omega)] at Hms
        refine ⟨R2, Hms, ?_⟩
        repeat' apply And.intro
        all_goals sym_regs HR2
        all_goals repeat (focus (rewrite [getr_nz]; rotate_left; reg_neq_tac))
        all_goals first | rfl | (symm; assumption) | (rw [H18]; bveq) | (rw [H19]; bveq) | ntw_succ
    obtain ⟨rg, Hpre, Hrg15, Hrg8, Hrg18, Hrg19, Hrg2, Hrg3,
      Hrg9, Hrg10, Hrg14, Hrg11, Hrg12, Hrg13⟩ := Hpre
    have Hbg' : bg_ok av ev rsp rrnd uid hw mem' := by
      apply bg_ok_wbytes_below av ev rsp rrnd uid hw _ _ _ Hbg
      simp only [List.length_singleton]
      unorm
      omega
    have Hcur' : rdn source_segs mem' cur_base cur.length = some cur := by
      unfold mem'
      rw [rdn_wbytes1_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega)]
      exact Hcur
    have Hdone' : rdn source_segs mem' done_base (j + 1) = some (cur.take (j + 1)) := by
      unfold mem'
      have Hlen : (cur.take j).length = j := by rw [List.length_take, Nat.min_eq_left Hj]
      rw [firstn_S_nth byte cur j (Z_to_bv 8 0) Hjlt]
      conv => lhs; arg 2; arg 2; rw [← Hlen]
      conv => lhs; arg 4; rw [← Hlen]
      apply rdn_snoc_store
      · rw [u_done_base, Hlen]
        omega
      · rw [Hlen]
        exact Hdone
    obtain ⟨mem'', R'', Hstep'', E2, E3, E8, E9, E18, E19, E10, E14,
      E11, E12, E13, Hbg'', Hcur'', Hdone'', Hframe''⟩ :=
      IH (j + 1) rg mem' (by omega) (by omega) Hrg15 (Hrg8.trans H8)
        (Hrg18.trans H18) (Hrg19.trans H19) Hbg' Hcur' Hdone'
    refine ⟨mem'', R'', msteps_trans _ _ _ _ Hpre Hstep'',
      E2.trans Hrg2, E3.trans Hrg3, E8.trans Hrg8, E9.trans Hrg9,
      E18.trans Hrg18, E19.trans Hrg19, E10.trans Hrg10, E14.trans Hrg14,
      E11.trans Hrg11, E12.trans Hrg12, E13.trans Hrg13, Hbg'', Hcur'', Hdone'', ?_⟩
    intro a n Ha
    rw [Hframe'' a n Ha]
    unfold mem'
    rw [rdn_wbytes1_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega)]

/-- Loop-head predicate. -/
def src_LH (a : A) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x11030 mem rrom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs 3 = (0x13800 : word) ∧
    reg_get regs 8 = nat_to_word a.1.length ∧
    reg_get regs 9 = nat_to_word a.2.length ∧
    reg_get regs 18 = cur_base ∧ reg_get regs 19 = done_base ∧
    bg_ok av ev rsp rrnd uid hw mem ∧
    rdn source_segs mem cur_base a.1.length = some a.1 ∧
    rdn source_segs mem done_base a.2.length = some a.2 ∧
    (a.1.length : Int) ≤ 4096 ∧ (a.2.length : Int) ≤ 4097

/- `bltu a0,-4096` on a small non-negative count: __syscall_ret's error
test, which every in-model return falls through. -/
local macro "sysret_ok" : tactic => `(tactic| (
  rewrite [bv_ltu_Z]
  rewrite [show bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 from (by decide)]
  rewrite [u_ntw]
  rotate_left;
  · lenlia
  · apply decide_eq_false
    lenlia))

/- A reloaded frame slot: the executor's `SCReadBase` obligation, closed
by the slot's read-back lemma. -/
local macro "eslot" v:term:max lem:term:max Hbg:term:max : tactic => `(tactic| (
  refine ⟨word_to_le_bytes 8 $v, ?_, ?_⟩
  · apply $lem
    exact $Hbg
  · decide +kernel))

include Hsp_lo Hsp_hi in
/-- Epilogue: from 0x110ec (a0 = code, sp = rsp-48) reach exit(code). -/
theorem epilogue_exit (code : word) (regs : bvmap 5 word) (mem : word → Option byte)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = code) (Hbg : bg_ok av ev rsp rrnd uid hw mem) :
    to_exit source_segs code (mkst regs 0x110ec mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  /- 0x110ec..0x11180: reload ra/s0..s3, pop the frame, `ret` into
  _start's tail, li a7,93 — one block across the return. -/
  let ss0 := SS 0x110ec (sr_pins [(2, EVar 32)] sr_id) [] 33
  let ss1 := SS 0x110f0 (sr_upd ss0.s_regs 1 (ELit 70016)) [] 34
  let ss2 := SS 0x110f4 (sr_upd ss1.s_regs 8 (EVar 34)) [] 35
  let ss3 := SS 0x110f8 (sr_upd ss2.s_regs 9 (EVar 35)) [] 36
  let ss4 := SS 0x110fc (sr_upd ss3.s_regs 18 (EVar 36)) [] 37
  let ss5 := SS 0x11100 (sr_upd ss4.s_regs 19 (EVar 37)) [] 38
  let ss6 := SS 0x11104 (sr_upd ss5.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit 48))) [] 38
  let ss7 := SS 0x11180 ss6.s_regs [] 38
  let ss8 := SS 0x11184 (sr_upd ss7.s_regs 17 (ELit 93)) [] 38
  let c0 := [SCFlat (SA (SBVar 32) 40) 8, SCReadBase (SA (SBVar 32) 40) 8 (ELit 70016)]
  let c1 := [SCFlat (SA (SBVar 32) 32) 8, SCReadBase (SA (SBVar 32) 32) 8 (EVar 34)]
  let c2 := [SCFlat (SA (SBVar 32) 24) 8, SCReadBase (SA (SBVar 32) 24) 8 (EVar 35)]
  let c3 := [SCFlat (SA (SBVar 32) 16) 8, SCReadBase (SA (SBVar 32) 16) 8 (EVar 36)]
  let c4 := [SCFlat (SA (SBVar 32) 8) 8, SCReadBase (SA (SBVar 32) 8) 8 (EVar 37)]
  let scs := c4 ++ c3 ++ c2 ++ c1 ++ c0
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 ss0.s_pc) = some 0x02813083)
      (F1 : fetch_word segs (Z_to_bv 64 ss1.s_pc) = some 0x02013403)
      (F2 : fetch_word segs (Z_to_bv 64 ss2.s_pc) = some 0x01813483)
      (F3 : fetch_word segs (Z_to_bv 64 ss3.s_pc) = some 0x01013903)
      (F4 : fetch_word segs (Z_to_bv 64 ss4.s_pc) = some 0x00813983)
      (F5 : fetch_word segs (Z_to_bv 64 ss5.s_pc) = some 0x03010113)
      (F6 : fetch_word segs (Z_to_bv 64 ss6.s_pc) = some 0x00008067)
      (F7 : fetch_word segs (Z_to_bv 64 ss7.s_pc) = some 0x05d00893)
      (F8 : fetch_word segs (Z_to_bv 64 ss8.s_pc) = some 0x00000073) : sym_exec segs 9 [] [ELit 70016] ss0 [] = (ss8, scs) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_110ec]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x02813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 8 [] [] ss1 c0 = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_110f0]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x02013403 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 7 [] [] ss2 (c1 ++ c0) = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_110f4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01813483 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 6 [] [] ss3 (c2 ++ c1 ++ c0) = _
    rewrite [sym_exec, F3]
    dsimp only []
    rewrite [SD_110f8]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01013903 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 5 [] [] ss4 (c3 ++ c2 ++ c1 ++ c0) = _
    rewrite [sym_exec, F4]
    dsimp only []
    rewrite [SD_110fc]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813983 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 4 [] [] ss5 scs = _
    rewrite [sym_exec, F5]
    dsimp only []
    rewrite [SD_11100]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x03010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 3 [] [] ss6 scs = _
    rewrite [sym_exec, F6]
    dsimp only []
    rewrite [SD_11104]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [] [] ss7 scs = _
    rewrite [sym_exec, F7]
    dsimp only []
    rewrite [SD_11180]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x05d00893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [] [] ss8 scs = _
    rewrite [sym_exec, F8]
    rfl
  let E := Eplus regs [Z_to_bv 64 (bv_unsigned rsp - 48)]
  have Hsc : scs_denot source_segs mem E scs := by
    dsimp only [scs, c4, c3, c2, c1, c0, List.cons_append, List.nil_append]
    simp only [scs_denot, List.forall_mem_cons]
    dsimp only [sc_denot, sc_flat, adenot, bdenot, a_base, a_off, E]
    sym_norm
    repeat' apply And.intro
    all_goals try omega
    · eslot (Z_to_bv 64 0) (bg_read_s3 av ev rsp rrnd Hsp_lo Hsp_hi uid hw) Hbg
    · eslot (Z_to_bv 64 0) (bg_read_s2 av ev rsp rrnd Hsp_lo Hsp_hi uid hw) Hbg
    · eslot (Z_to_bv 64 0) (bg_read_s1 av ev rsp rrnd Hsp_lo Hsp_hi uid hw) Hbg
    · eslot (Z_to_bv 64 0) (bg_read_s0 av ev rsp rrnd Hsp_lo Hsp_hi uid hw) Hbg
    · eslot (0x11180 : word) (bg_read_ra av ev rsp rrnd Hsp_lo Hsp_hi uid hw) Hbg
    · intro s hs
      cases hs
  have Hst : st_ok E mem rrom ss0 (mkst regs 0x110ec mem rrom) := by
    refine ⟨regs, rfl, regs_ok_pins E [(2, EVar 32)] sr_id regs
      (regs_ok_Eplus regs [Z_to_bv 64 (bv_unsigned rsp - 48)]) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons]
    constructor
    · dsimp only [E]
      sym_env_norm
      exact H2
    · intro p hp
      cases hp
  obtain ⟨R, HR, Hms⟩ := sym_exec_ex source_segs 9 [] [ELit 70016] ss0 [] ss8 scs E
    mem rrom (mkst regs 0x110ec mem rrom) (Hexec source_segs tail1_SF_110ec tail1_SF_110f0 tail1_SF_110f4 tail1_SF_110f8 tail1_SF_110fc tail1_SF_11100 tail1_SF_11104 tail1_SF_11180 tail1_SF_11184) Hsc Hst
  dsimp only [ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E,
    sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR Hms
  chain_mst
  · exact Hms
  · norm_pc
    apply to_exit.te_step _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11184 rfl)
    apply te_here_rec
    · sym_regs HR
      decide +kernel
    · sym_regs HR
      exact H10

include Hsp_lo Hsp_hi in
/-- The success return path: `li a0,0 ; snez a0,a0 ; slliw a0,a0,2`
computes the exit code 0 from the put-loop's `w` result before
falling into the epilogue. (gcc 15 shares this tail with the
write-error path, which enters at 0x110e4 with a0 = -1 and so
yields 4 — dead in this model.) -/
theorem epilogue_exit0 (regs : bvmap 5 word) (mem : word → Option byte)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (Hbg : bg_ok av ev rsp rrnd uid hw mem) :
    to_exit source_segs (Z_to_bv 64 0) (mkst regs 0x110e0 mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let ss0 := SS 0x110e0 sr_id [] 32
  let ss1 := SS 0x110e4 (sr_upd sr_id 10 (ELit 0)) [] 32
  let ss2 := SS 0x110e8 (sr_upd ss1.s_regs 10 (EAlu .ALU_SLTU (ELit 0) (ELit 0))) [] 32
  let ss3 := SS 0x110ec (sr_upd ss2.s_regs 10
    (EAluw .ALU_SLL (EAlu .ALU_SLTU (ELit 0) (ELit 0)) (ELit 2))) [] 32
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 ss0.s_pc) = some 0x00000513)
      (F1 : fetch_word segs (Z_to_bv 64 ss1.s_pc) = some 0x00a03533)
      (F2 : fetch_word segs (Z_to_bv 64 ss2.s_pc) = some 0x0025151b) : sym_exec segs 3 [] [] ss0 [] = (ss3, []) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_110e0]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [] [] ss1 [] = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_110e4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a03533 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [] [] ss2 [] = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_110e8]
    rfl
  have Hst : st_ok (Eplus regs []) mem rrom ss0 (mkst regs 0x110e0 mem rrom) :=
    ⟨regs, rfl, regs_ok_Eplus regs [], True.intro⟩
  obtain ⟨R, HR, Hms⟩ := sym_exec_ex source_segs 3 [] [] ss0 [] ss3 [] (Eplus regs [])
    mem rrom (mkst regs 0x110e0 mem rrom) (Hexec source_segs tail1_SF_110e0 tail1_SF_110e4 tail1_SF_110e8) (by intro s hs; cases hs) Hst
  dsimp only [ss3, ss2, ss1, ss0, sym_state.s_pc, sym_state.s_regs,
    sym_state.s_log, mem_denot] at HR Hms
  chain_mst
  · exact Hms
  · norm_pc
    apply epilogue_exit av ev rsp rrnd Hsp_lo Hsp_hi uid hw
    · sym_regs HR
      exact H2
    · sym_regs HR
      repeat rewrite [getr_x0z]
      bveq
    · exact Hbg

theorem procs_skipn_step (bs : List byte) (i : Nat) (a : A) (Hi : i < bs.length) :
    procs f a (bs.drop i) =
      match f a (bs.getD i (Z_to_bv 8 0)) with
      | some a' => procs f a' (bs.drop (i + 1))
      | none => none := by
  rw [skipn_cons_nth bs i (Z_to_bv 8 0) Hi]
  simp only [procs]
  cases f a (bs.getD i (Z_to_bv 8 0)) <;> rfl

/-- Byte-loop head predicate (at 0x11058). -/
def BLH (cur done bs : List byte) (i : Nat) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x11058 mem rrom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs 3 = (0x13800 : word) ∧
    reg_get regs 8 = nat_to_word cur.length ∧
    reg_get regs 9 = nat_to_word done.length ∧
    reg_get regs 18 = cur_base ∧ reg_get regs 19 = done_base ∧
    reg_get regs 10 = nat_to_word bs.length ∧
    reg_get regs 14 = nat_to_word i ∧
    reg_get regs 11 = rb_base ∧ reg_get regs 12 = Z_to_bv 64 4096 ∧
    reg_get regs 13 = Z_to_bv 64 10 ∧
    bg_ok av ev rsp rrnd uid hw mem ∧
    rdn source_segs mem rb_base bs.length = some bs ∧
    rdn source_segs mem cur_base cur.length = some cur ∧
    rdn source_segs mem done_base done.length = some done ∧
    (cur.length : Int) ≤ 4096 ∧ (done.length : Int) ≤ 4097 ∧
    (bs.length : Int) ≤ 1024 ∧ i < bs.length

/-- State at 0x11098 (the blt loop-back test), after processing byte i-1. -/
def C4 (cur done bs : List byte) (i : Nat) (ms : machine_state) : Prop :=
  ∃ regs mem,
    ms = mkst regs 0x11098 mem rrom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs 3 = (0x13800 : word) ∧
    reg_get regs 8 = nat_to_word cur.length ∧
    reg_get regs 9 = nat_to_word done.length ∧
    reg_get regs 18 = cur_base ∧ reg_get regs 19 = done_base ∧
    reg_get regs 10 = nat_to_word bs.length ∧
    reg_get regs 14 = nat_to_word i ∧
    reg_get regs 11 = rb_base ∧ reg_get regs 12 = Z_to_bv 64 4096 ∧
    reg_get regs 13 = Z_to_bv 64 10 ∧
    bg_ok av ev rsp rrnd uid hw mem ∧
    rdn source_segs mem rb_base bs.length = some bs ∧
    rdn source_segs mem cur_base cur.length = some cur ∧
    rdn source_segs mem done_base done.length = some done ∧
    (cur.length : Int) ≤ 4096 ∧ (done.length : Int) ≤ 4097 ∧
    (bs.length : Int) ≤ 1024 ∧ i ≤ bs.length

-- Rocq: tail1_ns_source.v's msteps_to_exit (renamed: Common/SymTac.lean declares the same short name).
theorem tail1_msteps_to_exit (code : word) (ms ms' : machine_state)
    (H : msteps source_segs ms ms') :
    to_exit source_segs code ms' → to_exit source_segs code ms := by
  induction H with
  | mst_refl ms => exact fun Hex => Hex
  | mst_step ms ms1 ms2 Hsvc Hstep H IH =>
    intro Hex
    exact to_exit.te_step ms ms1 Hsvc Hstep (IH Hex)

include Hsp_lo Hsp_hi in
theorem byte_loop (k : Nat) (cur done bs : List byte) (i : Nat) (ms : machine_state)
    (Hk : bs.length - i = k) (HBLH : BLH av ev rsp rrnd uid hw cur done bs i ms) :
    match procs f (cur, done) (bs.drop i) with
    | some a' => ∃ msL, msteps source_segs ms msL ∧ src_LH av ev rsp rrnd uid hw a' msL
    | none => to_exit source_segs ec ms := by
  induction k generalizing cur done i ms with
  | zero =>
    obtain ⟨regs, mem, rfl, H2, H3, H8, H9, H18, H19, H10, H14, H11, H12, H13,
      Hbg, Hrb, Hcur, Hdone, Hcurcap, Hdonecap, Hbscap, Hi⟩ := HBLH
    omega
  | succ k IH =>
    obtain ⟨regs, mem, rfl, H2, H3, H8, H9, H18, H19, H10, H14, H11, H12, H13,
      Hbg, Hrb, Hcur, Hdone, Hcurcap, Hdonecap, Hbscap, Hi⟩ := HBLH
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    let b := bs.getD i (Z_to_bv 8 0)
    have Hdisp : ∀ cur' done' st, C4 av ev rsp rrnd uid hw cur' done' bs (i + 1) st →
        match procs f (cur', done') (bs.drop (i + 1)) with
        | some a'' => ∃ msL, msteps source_segs st msL ∧ src_LH av ev rsp rrnd uid hw a'' msL
        | none => to_exit source_segs ec st := by
      intro cur' done' st HC4
      obtain ⟨rg, mm, rfl, G2, G3, G8, G9, G18, G19, G10, G14, G11, G12, G13,
        Hbg', Hrb', Hcur', Hdone', Hcurcap', Hdonecap', Hbscap', Hle⟩ := HC4
      by_cases Heq : i + 1 = bs.length
      · rw [List.drop_eq_nil_of_le (by omega)]
        dsimp only [procs]
        refine ⟨mkst rg 0x11030 mm rrom, ?_, rg, mm, rfl, G2, G3, G8, G9,
          G18, G19, Hbg', Hcur', Hdone', Hcurcap', Hdonecap'⟩
        apply msteps.mst_step _ _ _ rfl
        · apply step_blt_ft _ _ _ _ _ _ _ _ _ tail1_SF_11098 rfl SD_11098
          getr_resolve
          rw [G14, G10, c_lts_ntw _ _ (by omega) (by omega)]
          exact decide_eq_false (by omega)
        · norm_pc
          stepj tail1_SF_1109c SD_1109c
          apply msteps.mst_refl
      · have Hlt2 : i + 1 < bs.length := by omega
        have HBLH' : BLH av ev rsp rrnd uid hw cur' done' bs (i + 1) (mkst rg 0x11058 mm rrom) :=
          ⟨rg, mm, rfl, G2, G3, G8, G9, G18, G19, G10, G14, G11, G12, G13,
            Hbg', Hrb', Hcur', Hdone', Hcurcap', Hdonecap', Hbscap', Hlt2⟩
        have Hbody : msteps source_segs (mkst rg 0x11098 mm rrom) (mkst rg 0x11058 mm rrom) := by
          apply msteps.mst_step _ _ _ rfl
          · apply step_blt_tk _ _ _ _ _ _ _ _ _ tail1_SF_11098 rfl SD_11098
            getr_resolve
            rw [G14, G10, c_lts_ntw _ _ (by omega) (by omega)]
            exact decide_eq_true (by omega)
          · norm_pc
            apply msteps.mst_refl
        have Hih := IH cur' done' (i + 1) (mkst rg 0x11058 mm rrom) (by omega) HBLH'
        cases Ep : procs f (cur', done') (bs.drop (i + 1)) with
        | some a'' =>
          rw [Ep] at Hih
          obtain ⟨msL, Hs, HL⟩ := Hih
          exact ⟨msL, msteps_trans _ _ _ _ Hbody Hs, HL⟩
        | none =>
          rw [Ep] at Hih
          exact tail1_msteps_to_exit _ _ _ Hbody Hih
    cases Eb : bv_eqb b (Z_to_bv 8 10) with
    | true =>
      have Hf : f (cur, done) b = some ([], cur ++ [Z_to_bv 8 10]) := by
        simp only [f, Eb, ↓reduceIte]
        rfl
      rw [procs_skipn_step bs i (cur, done) Hi, Hf]
      dsimp only []
      have Hac : ∃ Rac, msteps source_segs (mkst regs 0x11058 mem rrom) (mkst Rac 0x11080 mem rrom) ∧
          reg_get Rac 15 = nat_to_word 0 ∧
          reg_get Rac 8 = nat_to_word cur.length ∧
          reg_get Rac 18 = cur_base ∧ reg_get Rac 19 = done_base ∧
          reg_get Rac 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
          reg_get Rac 3 = (0x13800 : word) ∧ reg_get Rac 9 = nat_to_word done.length ∧
          reg_get Rac 10 = nat_to_word bs.length ∧ reg_get Rac 14 = nat_to_word i ∧
          reg_get Rac 11 = rb_base ∧ reg_get Rac 12 = Z_to_bv 64 4096 ∧
          reg_get Rac 13 = Z_to_bv 64 10 := by
        let ss0 := SS 69720 (sr_pins [(11, ELit 77832), (13, ELit 10), (14, EVar 32)] sr_id) [] 33
        let ss1 := SS 69724 (sr_upd ss0.s_regs 15 (EAlu .ALU_ADD (ELit 77832) (EVar 32))) [] 33
        let ss2 := SS 69728 (sr_upd ss1.s_regs 15 (EVar 33)) [] 34
        let ss3 := SS 69732 ss2.s_regs [] 34
        let ss4 := SS 69736 (sr_upd ss3.s_regs 15 (ELit 0)) [] 34
        let ss5 := SS 69760 ss4.s_regs [] 34
        let c1 := [SCFlat (SA (SBVar 32) 77832) 1, SCReadBase (SA (SBVar 32) 77832) 1 (EVar 33)]
        let c2 := [SCBr false .BC_NE (EVar 33) (ELit 10)]
        let scs := c2 ++ c1
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69720) = some 0x00e587b3)
            (F1 : fetch_word segs (Z_to_bv 64 69724) = some 0x0007c783)
            (F2 : fetch_word segs (Z_to_bv 64 69728) = some 0x04d79063)
            (F3 : fetch_word segs (Z_to_bv 64 69732) = some 0x00000793)
            (F4 : fetch_word segs (Z_to_bv 64 69736) = some 0x0180006f) : sym_exec segs 5 [false] [] ss0 [] = (ss5, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_11058]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00e587b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 4 [false] [] ss1 ([]) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_1105c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0007c783 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 3 [false] [] ss2 (c1) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_11060]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04d79063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 2 [] [] ss3 (c2 ++ c1) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_11064]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 1 [] [] ss4 (c2 ++ c1) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_11068]
          rfl
        let E := Eplus regs ([nat_to_word i] ++ [Z_to_bv 64 (bv_unsigned b)])
        refine Exists.elim (sym_exec_ex source_segs 5 [false] [] ss0 [] ss5 scs E
          mem rrom (mkst regs (Z_to_bv 64 69720) mem rrom) (Hexec source_segs tail1_SF_11058 tail1_SF_1105c tail1_SF_11060 tail1_SF_11064 tail1_SF_11068) ?sc1 ?st1) ?cont1
        case' cont1 =>
          intro Rac HH
          obtain ⟨HRac, Hms⟩ := HH
          dsimp only [ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRac Hms
        case' st1 =>
          refine ⟨regs, rfl, regs_ok_pins E [(11, ELit 77832), (13, ELit 10), (14, EVar 32)] sr_id regs
            (regs_ok_Eplus regs ([nat_to_word i] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc1 =>
          dsimp only [scs, c1, c2, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
        · with_reducible rw [Bool.not_eq_false']
          exact (c_eq_zext10 b).trans Eb
        · scflat
        · rw [addr_base_ntw rb_base 77832 i u_rb_base (by omega)]
          refine ⟨[b], rdn_nth _ _ _ _ _ _ Hrb Hi, ?_⟩
          rw [bytes_le_to_Z_1]
          exact (zext_byte_u _).symm
        · pin_lit rb_base
          exact H11
        · exact H13
        · exact H14
        · hms_norm Hms
          refine ⟨Rac, Hms, ?_⟩
          repeat' apply And.intro
          all_goals sym_regs HRac
          all_goals repeat (focus (rewrite [getr_nz]; rotate_left; reg_neq_tac))
          all_goals first | rfl | assumption | bveq
      obtain ⟨Rac, Hms_ac, GRac15, GRac8, GRac18, GRac19, GRac2, GRac3, GRac9,
        GRac10, GRac14, GRac11, GRac12, GRac13⟩ := Hac
      obtain ⟨mem_c, Rc, Hcopy, Cc2, Cc3, Cc8, Cc9, Cc18, Cc19, Cc10, Cc14,
        Cc11, Cc12, Cc13, Hbg_c, Hcur_c, Hdone_c, Hframe_c⟩ :=
        copy_loop av ev rsp rrnd Hsp_lo Hsp_hi uid hw cur.length 0 cur Rac mem
          (by omega) (by omega) Hcurcap GRac15 GRac8 GRac18 GRac19 Hbg Hcur rfl
      let memD := wbytes mem_c (done_base + nat_to_word cur.length) [Z_to_bv 8 10]
      have Hc4 : ∃ Rd, msteps source_segs (mkst Rc 0x11084 mem_c rrom) (mkst Rd 0x11098 memD rrom) ∧
          reg_get Rd 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
          reg_get Rd 3 = (0x13800 : word) ∧ reg_get Rd 8 = nat_to_word 0 ∧
          reg_get Rd 9 = nat_to_word (cur.length + 1) ∧
          reg_get Rd 18 = cur_base ∧ reg_get Rd 19 = done_base ∧
          reg_get Rd 10 = nat_to_word bs.length ∧ reg_get Rd 14 = nat_to_word (i + 1) ∧
          reg_get Rd 11 = rb_base ∧ reg_get Rd 12 = Z_to_bv 64 4096 ∧
          reg_get Rd 13 = Z_to_bv 64 10 := by
        let ss0 := SS 69764 (sr_pins [(19, ELit 78856), (8, EVar 32), (13, ELit 10), (14, EVar 33)] sr_id) [] 34
        let ss1 := SS 69768 (sr_upd ss0.s_regs 15 (EAlu .ALU_ADD (ELit 78856) (EVar 32))) [] 34
        let ss2 := SS 69772 (sr_upd ss1.s_regs 9 (EAlu .ALU_ADD (EVar 32) (ELit 1))) [] 34
        let ss3 := SS 69776 ss2.s_regs [SE (SA (SBVar 32) 78856) 1 (ELit 10)] 34
        let ss4 := SS 69780 (sr_upd ss3.s_regs 8 (ELit 0)) [SE (SA (SBVar 32) 78856) 1 (ELit 10)] 34
        let ss5 := SS 69784 (sr_upd ss4.s_regs 14 (EAlu .ALU_ADD (EVar 33) (ELit 1))) [SE (SA (SBVar 32) 78856) 1 (ELit 10)] 34
        let c2 := [SCFlat (SA (SBVar 32) 78856) 1, SCStoreOk (SA (SBVar 32) 78856) 1]
        let scs := c2
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69764) = some 0x008987b3)
            (F1 : fetch_word segs (Z_to_bv 64 69768) = some 0x00140493)
            (F2 : fetch_word segs (Z_to_bv 64 69772) = some 0x00d78023)
            (F3 : fetch_word segs (Z_to_bv 64 69776) = some 0x00000413)
            (F4 : fetch_word segs (Z_to_bv 64 69780) = some 0x00170713) : sym_exec segs 5 [] [] ss0 [] = (ss5, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_11084]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x008987b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 4 [] [] ss1 ([]) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_11088]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00140493 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 3 [] [] ss2 ([]) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_1108c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00d78023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 2 [] [] ss3 (c2) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_11090]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000413 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 1 [] [] ss4 (c2) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_11094]
          rfl
        let E := Eplus Rc ([nat_to_word cur.length, nat_to_word i] ++ [])
        refine Exists.elim (sym_exec_ex source_segs 5 [] [] ss0 [] ss5 scs E
          mem_c rrom (mkst Rc (Z_to_bv 64 69764) mem_c rrom) (Hexec source_segs tail1_SF_11084 tail1_SF_11088 tail1_SF_1108c tail1_SF_11090 tail1_SF_11094) ?sc2 ?st2) ?cont2
        case' cont2 =>
          intro Rd HH
          obtain ⟨HRd, Hms⟩ := HH
          dsimp only [ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRd Hms
        case' st2 =>
          refine ⟨Rc, rfl, regs_ok_pins E [(19, ELit 78856), (8, EVar 32), (13, ELit 10), (14, EVar 33)] sr_id Rc
            (regs_ok_Eplus Rc ([nat_to_word cur.length, nat_to_word i] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc2 =>
          dsimp only [scs, c2, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
        · scflat
        · rw [addr_base_ntw done_base 78856 cur.length u_done_base (by omega)]
          apply source_store_ok <;> unorm <;> omega
        · pin_lit done_base
          exact Cc19.trans GRac19
        · exact Cc8.trans GRac8
        · exact Cc13.trans GRac13
        · exact Cc14.trans GRac14
        · hms_norm Hms
          rw [addr_base_ntw done_base 78856 cur.length u_done_base (by omega)] at Hms
          refine ⟨Rd, Hms, ?_⟩
          repeat' apply And.intro
          all_goals sym_regs HRd
          all_goals repeat (focus (rewrite [getr_nz]; rotate_left; reg_neq_tac))
          all_goals (repeat rewrite [Cc2]); (repeat rewrite [Cc3]); (repeat rewrite [Cc8]); (repeat rewrite [Cc9]); (repeat rewrite [Cc18]); (repeat rewrite [Cc19]); (repeat rewrite [Cc10]); (repeat rewrite [Cc14]); (repeat rewrite [Cc11]); (repeat rewrite [Cc12]); (repeat rewrite [Cc13])
          all_goals first | rfl | ntw_succ | assumption | bveq
      obtain ⟨Rd, Hms_d, GRd2, GRd3, GRd8, GRd9, GRd18, GRd19, GRd10, GRd14,
        GRd11, GRd12, GRd13⟩ := Hc4
      have HC4 : C4 av ev rsp rrnd uid hw [] (cur ++ [Z_to_bv 8 10]) bs (i + 1)
          (mkst Rd 0x11098 memD rrom) := by
        refine ⟨Rd, memD, rfl, GRd2, GRd3, GRd8, ?_, GRd18, GRd19, GRd10, GRd14,
          GRd11, GRd12, GRd13, ?_, ?_, rfl, ?_, ?_, ?_, Hbscap, by omega⟩
        · simpa only [List.length_append, List.length_singleton] using GRd9
        · apply bg_ok_wbytes_below av ev rsp rrnd uid hw _ _ _ Hbg_c
          simp only [List.length_singleton]
          unorm
          omega
        · unfold memD
          rw [rdn_wbytes1_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega)]
          rw [Hframe_c rb_base bs.length (by unorm; omega)]
          exact Hrb
        · unfold memD
          simp only [List.length_append, List.length_singleton]
          exact rdn_snoc_store _ _ _ _ _ (by rw [u_done_base]; omega) Hdone_c
        · simp only [List.length_nil]; omega
        · simp only [List.length_append, List.length_singleton]; omega
      have Hd := Hdisp [] (cur ++ [Z_to_bv 8 10]) (mkst Rd 0x11098 memD rrom) HC4
      have Hall := msteps_trans _ _ _ _ Hms_ac (msteps_trans _ _ _ _ Hcopy Hms_d)
      cases Ep : procs f ([], cur ++ [Z_to_bv 8 10]) (bs.drop (i + 1)) with
      | some a'' =>
        rw [Ep] at Hd
        obtain ⟨msL, Hs, HL⟩ := Hd
        exact ⟨msL, msteps_trans _ _ _ _ Hall Hs, HL⟩
      | none =>
        rw [Ep] at Hd
        exact tail1_msteps_to_exit _ _ _ Hall Hd
    | false =>
      by_cases Hge : 4096 ≤ (cur.length : Int)
      · have Hf : f (cur, done) b = none := by simp only [f, Eb, Bool.false_eq_true, ↓reduceIte, Hge]
        rw [procs_skipn_step bs i (cur, done) Hi, Hf]
        dsimp only []
        let ss0 := SS 69720 (sr_pins [(11, ELit 77832), (13, ELit 10), (14, EVar 32), (8, EVar 33), (12, ELit 4096)] sr_id) [] 34
        let ss1 := SS 69724 (sr_upd ss0.s_regs 15 (EAlu .ALU_ADD (ELit 77832) (EVar 32))) [] 34
        let ss2 := SS 69728 (sr_upd ss1.s_regs 15 (EVar 34)) [] 35
        let ss3 := SS 69792 ss2.s_regs [] 35
        let ss4 := SS 69964 ss3.s_regs [] 35
        let ss5 := SS 69968 (sr_upd ss4.s_regs 10 (ELit 3)) [] 35
        let ss6 := SS 69868 ss5.s_regs [] 35
        let c1 := [SCFlat (SA (SBVar 32) 77832) 1, SCReadBase (SA (SBVar 32) 77832) 1 (EVar 34)]
        let c2 := [SCBr true .BC_NE (EVar 34) (ELit 10)]
        let c3 := [SCBr true .BC_EQ (EVar 33) (ELit 4096)]
        let scs := c3 ++ c2 ++ c1
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69720) = some 0x00e587b3)
            (F1 : fetch_word segs (Z_to_bv 64 69724) = some 0x0007c783)
            (F2 : fetch_word segs (Z_to_bv 64 69728) = some 0x04d79063)
            (F3 : fetch_word segs (Z_to_bv 64 69792) = some 0x0ac40663)
            (F4 : fetch_word segs (Z_to_bv 64 69964) = some 0x00300513)
            (F5 : fetch_word segs (Z_to_bv 64 69968) = some 0xf9dff06f) : sym_exec segs 6 [true, true] [] ss0 [] = (ss6, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_11058]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00e587b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 5 [true, true] [] ss1 ([]) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_1105c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0007c783 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 4 [true, true] [] ss2 (c1) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_11060]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04d79063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 3 [true] [] ss3 (c2 ++ c1) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_110a0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0ac40663 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 2 [] [] ss4 (c3 ++ c2 ++ c1) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_1114c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00300513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 1 [] [] ss5 (c3 ++ c2 ++ c1) = _
          rewrite [sym_exec, F5]
          dsimp only []
          rewrite [SD_11150]
          rfl
        let E := Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])
        refine Exists.elim (sym_exec_ex source_segs 6 [true, true] [] ss0 [] ss6 scs E
          mem rrom (mkst regs (Z_to_bv 64 69720) mem rrom) (Hexec source_segs tail1_SF_11058 tail1_SF_1105c tail1_SF_11060 tail1_SF_110a0 tail1_SF_1114c tail1_SF_11150) ?sc3 ?st3) ?cont3
        case' cont3 =>
          intro Rx HH
          obtain ⟨HRx, Hblock⟩ := HH
          dsimp only [ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRx Hblock
          sym_pc_Z
          chain_mst
          focus exact Hblock
          try sym_mem_norm
          norm_pc
          sym_pc_lit
        case' st3 =>
          refine ⟨regs, rfl, regs_ok_pins E [(11, ELit 77832), (13, ELit 10), (14, EVar 32), (8, EVar 33), (12, ELit 4096)] sr_id regs
            (regs_ok_Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc3 =>
          dsimp only [scs, c1, c2, c3, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
        · scbr
        · with_reducible rw [Bool.not_eq_true']
          exact (c_eq_zext10 b).trans Eb
        · scflat
        · rw [addr_base_ntw rb_base 77832 i u_rb_base (by omega)]
          refine ⟨[b], rdn_nth _ _ _ _ _ _ Hrb Hi, ?_⟩
          rw [bytes_le_to_Z_1]
          exact (zext_byte_u _).symm
        · pin_lit rb_base
          exact H11
        · exact H13
        · exact H14
        · exact H8
        · exact H12
        · apply epilogue_exit av ev rsp rrnd Hsp_lo Hsp_hi uid hw
          · sym_regs HRx; exact H2
          · sym_regs HRx; sym_close
          · exact Hbg
      · have Hf : f (cur, done) b = some (cur ++ [b], done) := by
          simp only [f, Eb, Bool.false_eq_true, ↓reduceIte, Hge]
          rfl
        rw [procs_skipn_step bs i (cur, done) Hi, Hf]
        dsimp only []
        let memC := wbytes mem (cur_base + nat_to_word cur.length) [b]
        have Hc4 : ∃ Rd, msteps source_segs (mkst regs 0x11058 mem rrom) (mkst Rd 0x11098 memC rrom) ∧
            reg_get Rd 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
            reg_get Rd 3 = (0x13800 : word) ∧ reg_get Rd 8 = nat_to_word (cur.length + 1) ∧
            reg_get Rd 9 = nat_to_word done.length ∧
            reg_get Rd 18 = cur_base ∧ reg_get Rd 19 = done_base ∧
            reg_get Rd 10 = nat_to_word bs.length ∧ reg_get Rd 14 = nat_to_word (i + 1) ∧
            reg_get Rd 11 = rb_base ∧ reg_get Rd 12 = Z_to_bv 64 4096 ∧
            reg_get Rd 13 = Z_to_bv 64 10 := by
          let ss0 := SS 69720 (sr_pins [(11, ELit 77832), (13, ELit 10), (14, EVar 32), (8, EVar 33),
                        (12, ELit 4096), (18, ELit 82960)] sr_id) [] 34
          let ss1 := SS 69724 (sr_upd ss0.s_regs 15 (EAlu .ALU_ADD (ELit 77832) (EVar 32))) [] 34
          let ss2 := SS 69728 (sr_upd ss1.s_regs 15 (EVar 34)) [] 35
          let ss3 := SS 69792 ss2.s_regs [] 35
          let ss4 := SS 69796 ss3.s_regs [] 35
          let ss5 := SS 69800 (sr_upd ss4.s_regs 16 (EAlu .ALU_ADD (ELit 82960) (EVar 33))) [] 35
          let ss6 := SS 69804 ss5.s_regs [SE (SA (SBVar 33) 82960) 1 (EVar 34)] 35
          let ss7 := SS 69808 (sr_upd ss6.s_regs 8 (EAlu .ALU_ADD (EVar 33) (ELit 1))) [SE (SA (SBVar 33) 82960) 1 (EVar 34)] 35
          let ss8 := SS 69780 ss7.s_regs [SE (SA (SBVar 33) 82960) 1 (EVar 34)] 35
          let ss9 := SS 69784 (sr_upd ss8.s_regs 14 (EAlu .ALU_ADD (EVar 32) (ELit 1))) [SE (SA (SBVar 33) 82960) 1 (EVar 34)] 35
          let c1 := [SCFlat (SA (SBVar 32) 77832) 1, SCReadBase (SA (SBVar 32) 77832) 1 (EVar 34)]
          let c2 := [SCBr true .BC_NE (EVar 34) (ELit 10)]
          let c3 := [SCBr false .BC_EQ (EVar 33) (ELit 4096)]
          let c5 := [SCFlat (SA (SBVar 33) 82960) 1, SCStoreOk (SA (SBVar 33) 82960) 1]
          let scs := c5 ++ c3 ++ c2 ++ c1
          have Hexec (segs : List Segment)
              (F0 : fetch_word segs (Z_to_bv 64 69720) = some 0x00e587b3)
              (F1 : fetch_word segs (Z_to_bv 64 69724) = some 0x0007c783)
              (F2 : fetch_word segs (Z_to_bv 64 69728) = some 0x04d79063)
              (F3 : fetch_word segs (Z_to_bv 64 69792) = some 0x0ac40663)
              (F4 : fetch_word segs (Z_to_bv 64 69796) = some 0x00890833)
              (F5 : fetch_word segs (Z_to_bv 64 69800) = some 0x00f80023)
              (F6 : fetch_word segs (Z_to_bv 64 69804) = some 0x00140413)
              (F7 : fetch_word segs (Z_to_bv 64 69808) = some 0xfe5ff06f)
              (F8 : fetch_word segs (Z_to_bv 64 69780) = some 0x00170713) : sym_exec segs 9 [true, false] [] ss0 [] = (ss9, scs) := by
            rewrite [sym_exec, F0]
            dsimp only []
            rewrite [SD_11058]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00e587b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 8 [true, false] [] ss1 ([]) = _
            rewrite [sym_exec, F1]
            dsimp only []
            rewrite [SD_1105c]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0007c783 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 7 [true, false] [] ss2 (c1) = _
            rewrite [sym_exec, F2]
            dsimp only []
            rewrite [SD_11060]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04d79063 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 6 [false] [] ss3 (c2 ++ c1) = _
            rewrite [sym_exec, F3]
            dsimp only []
            rewrite [SD_110a0]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0ac40663 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 5 [] [] ss4 (c3 ++ c2 ++ c1) = _
            rewrite [sym_exec, F4]
            dsimp only []
            rewrite [SD_110a4]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00890833 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 4 [] [] ss5 (c3 ++ c2 ++ c1) = _
            rewrite [sym_exec, F5]
            dsimp only []
            rewrite [SD_110a8]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00f80023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 3 [] [] ss6 (c5 ++ c3 ++ c2 ++ c1) = _
            rewrite [sym_exec, F6]
            dsimp only []
            rewrite [SD_110ac]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00140413 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 2 [] [] ss7 (c5 ++ c3 ++ c2 ++ c1) = _
            rewrite [sym_exec, F7]
            dsimp only []
            rewrite [SD_110b0]
            simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe5ff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
            change sym_exec segs 1 [] [] ss8 (c5 ++ c3 ++ c2 ++ c1) = _
            rewrite [sym_exec, F8]
            dsimp only []
            rewrite [SD_11094]
            rfl
          let E := Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])
          refine Exists.elim (sym_exec_ex source_segs 9 [true, false] [] ss0 [] ss9 scs E
            mem rrom (mkst regs (Z_to_bv 64 69720) mem rrom) (Hexec source_segs tail1_SF_11058 tail1_SF_1105c tail1_SF_11060 tail1_SF_110a0 tail1_SF_110a4 tail1_SF_110a8 tail1_SF_110ac tail1_SF_110b0 tail1_SF_11094) ?sc4 ?st4) ?cont4
          case' cont4 =>
            intro Rd HH
            obtain ⟨HRd, Hms⟩ := HH
            dsimp only [ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRd Hms
          case' st4 =>
            refine ⟨regs, rfl, regs_ok_pins E [(11, ELit 77832), (13, ELit 10), (14, EVar 32), (8, EVar 33),
                        (12, ELit 4096), (18, ELit 82960)] sr_id regs
              (regs_ok_Eplus regs ([nat_to_word i, nat_to_word cur.length] ++ [Z_to_bv 64 (bv_unsigned b)])) ?_, True.intro⟩
            simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
            repeat' apply And.intro
            all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
          case' sc4 =>
            dsimp only [scs, c1, c2, c3, c5, List.cons_append, List.nil_append]
            simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
            all_goals sym_norm
            all_goals try sym_sc_auto
          · scflat
          · rw [addr_base_ntw cur_base 82960 cur.length u_cur_base (by omega)]
            apply source_store_ok <;> unorm <;> omega
          · scbr
          · with_reducible rw [Bool.not_eq_true']
            exact (c_eq_zext10 b).trans Eb
          · scflat
          · rw [addr_base_ntw rb_base 77832 i u_rb_base (by omega)]
            refine ⟨[b], rdn_nth _ _ _ _ _ _ Hrb Hi, ?_⟩
            rw [bytes_le_to_Z_1]
            exact (zext_byte_u _).symm
          · pin_lit rb_base
            exact H11
          · exact H13
          · exact H14
          · exact H8
          · exact H12
          · pin_lit cur_base
            exact H18
          · hms_norm Hms
            rw [addr_base_ntw cur_base 82960 cur.length u_cur_base (by omega)] at Hms
            refine ⟨Rd, Hms, ?_⟩
            repeat' apply And.intro
            all_goals sym_regs HRd
            all_goals repeat (focus (rewrite [getr_nz]; rotate_left; reg_neq_tac))
            all_goals first | rfl | ntw_succ | assumption | bveq
        obtain ⟨Rd, Hms_d, GRd2, GRd3, GRd8, GRd9, GRd18, GRd19, GRd10, GRd14,
          GRd11, GRd12, GRd13⟩ := Hc4
        have HC4 : C4 av ev rsp rrnd uid hw (cur ++ [b]) done bs (i + 1)
            (mkst Rd 0x11098 memC rrom) := by
          refine ⟨Rd, memC, rfl, GRd2, GRd3, ?_, GRd9, GRd18, GRd19, GRd10, GRd14,
            GRd11, GRd12, GRd13, ?_, ?_, ?_, ?_, ?_, Hdonecap, Hbscap, by omega⟩
          · simpa only [List.length_append, List.length_singleton] using GRd8
          · apply bg_ok_wbytes_below av ev rsp rrnd uid hw _ _ _ Hbg
            simp only [List.length_singleton]
            unorm
            omega
          · unfold memC
            rw [rdn_wbytes1_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega)]
            exact Hrb
          · unfold memC
            simp only [List.length_append, List.length_singleton]
            exact rdn_snoc_store _ _ _ _ _ (by rw [u_cur_base]; omega) Hcur
          · unfold memC
            rw [rdn_wbytes1_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega)]
            exact Hdone
          · simp only [List.length_append, List.length_singleton]; omega
        have Hd := Hdisp (cur ++ [b]) done (mkst Rd 0x11098 memC rrom) HC4
        cases Ep : procs f (cur ++ [b], done) (bs.drop (i + 1)) with
        | some a'' =>
          rw [Ep] at Hd
          obtain ⟨msL, Hs, HL⟩ := Hd
          exact ⟨msL, msteps_trans _ _ _ _ Hms_d Hs, HL⟩
        | none =>
          rw [Ep] at Hd
          exact tail1_msteps_to_exit _ _ _ Hms_d Hd

/-- The `sub`/`add` the retry loop performs on its count/pointer, in
the `nat_to_word` spelling the symbolic pins use (the `len_word`
forms are `WallSim`'s `v_sub_len_firstn`/`v_add_len_firstn`). -/
theorem v_sub_ntw (m k : Nat) (Hk : k ≤ m) (Hm : (m : Int) < 2 ^ 64) :
    v_sub (nat_to_word m) (nat_to_word k) = nat_to_word (m - k) := by
  apply bv_eq_of_unsigned
  rw [v_sub_small _ _ (by rw [u_ntw m Hm, u_ntw k (by omega)]; omega)]
  rw [u_ntw m Hm, u_ntw k (by omega), u_ntw (m - k) (by omega)]
  omega

theorem v_add_ntw (p : word) (k : Nat) :
    v_add p (nat_to_word k) = p + nat_to_word k := by
  unfold v_add
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, bv_unsigned_add]

include Hsp_lo Hsp_hi in
/-- gcc compiles the two EOF writes as two copies of the same put-style
retry loop, differing only in which callee-saved register holds the
pointer and which the count:

  done: head 0x11118 (a2=s1 count, a1=s0 ptr), ra = 0x11128
  cur : head 0x110c0 (a2=s0 count, a1=s1 ptr), ra = 0x110d0

Both call musl's `write` at 0x111e0, so each iteration runs the
wrapper frame/shuffle, `__syscall_cp`'s trampoline and its seven
shuffles down to the `ecall` at 0x11268, and comes back at 0x1126c
through `__syscall_ret`'s error test into `blez a0 ; sub ; add ;
bnez`. Every delivery is nonempty, so the remainder strictly
shrinks; the loop's only memory effect is the wrapper's `sd ra,8(sp)`
at `rsp-56`, below the `bg_ok` window. On the last delivery both
fall into 0x110e0, the exit-code-0 tail.

The Lean proofs use explicit `sym_exec_ex` scripts. From the
short-delivery `sym_exec_ex` call to the recursive call, the differing
lines are the application line (starting PC and `Hexec` fetch list),
the `regs_ok_pins` list (registers 8 and 9 swap), and the pin-closing
alternatives (`exact Q8` and `exact Q9` swap order). The preceding
symbolic states, fetch hypotheses and decoder rewrites also differ
for the two loop heads.

Induction on `fuel >= length rest`. -/
theorem src_put_wall_done (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 4097) (Hplo : 0x13000 ≤ bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) ≤ 0x16000)
    (H1 : reg_get regs 1 = (0x11208 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H8 : reg_get regs 8 = p) (H9 : reg_get regs 9 = nat_to_word rest.length)
    (H10 : reg_get regs 10 = nat_to_word n) (Hbg : bg_ok av ev rsp rrnd uid hw mem)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 (0x11128 : word)))
    (Hread : rdn source_segs mem p rest.length = some rest) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x1126c mem rrom) (rest.drop n)
      (to_exit source_segs (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    have Hpn : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
      rw [word_add_nat]
      apply u_Z2bv <;> omega
    let ss0 := SS 70252 (sr_pins [(1, ELit 70152), (2, EVar 32), (8, EVar 33), (9, EVar 34), (10, EVar 35)] sr_id) [] 36
    let ss1 := SS 70152 ss0.s_regs [] 36
    let ss2 := SS 70156 (sr_upd ss1.s_regs 1 (ELit 69928)) [] 37
    let ss3 := SS 70160 (sr_upd ss2.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit 16))) [] 37
    let ss4 := SS 70164 ss3.s_regs [] 37
    let ss5 := SS 70168 (sr_upd ss4.s_regs 15 (ELit (-4096))) [] 37
    let ss6 := SS 70172 ss5.s_regs [] 37
    let ss7 := SS 69928 ss6.s_regs [] 37
    let ss8 := SS 69932 ss7.s_regs [] 37
    let ss9 := SS 69936 (sr_upd ss8.s_regs 9 (EAlu .ALU_SUB (EVar 34) (EVar 35))) [] 37
    let ss10 := SS 69940 (sr_upd ss9.s_regs 8 (EAlu .ALU_ADD (EVar 33) (EVar 35))) [] 37
    let c1 := [SCFlat (SA (SBVar 32) 8) 8, SCReadBase (SA (SBVar 32) 8) 8 (ELit 69928)]
    let c5 := [SCBr false .BC_LTU (ELit (-4096)) (EVar 35)]
    let c7 := [SCBr false .BC_GE (ELit 0) (EVar 35)]
    let scs := c7 ++ c5 ++ c1
    have Hexec (segs : List Segment)
        (F0 : fetch_word segs (Z_to_bv 64 70252) = some 0x00008067)
        (F1 : fetch_word segs (Z_to_bv 64 70152) = some 0x00813083)
        (F2 : fetch_word segs (Z_to_bv 64 70156) = some 0x01010113)
        (F3 : fetch_word segs (Z_to_bv 64 70160) = some 0x0040006f)
        (F4 : fetch_word segs (Z_to_bv 64 70164) = some 0xfffff7b7)
        (F5 : fetch_word segs (Z_to_bv 64 70168) = some 0x00a7e463)
        (F6 : fetch_word segs (Z_to_bv 64 70172) = some 0x00008067)
        (F7 : fetch_word segs (Z_to_bv 64 69928) = some 0x00a05a63)
        (F8 : fetch_word segs (Z_to_bv 64 69932) = some 0x40a484b3)
        (F9 : fetch_word segs (Z_to_bv 64 69936) = some 0x00a40433) : sym_exec segs 10 [false, false] [ELit 69928] ss0 [] = (ss10, scs) := by
      rewrite [sym_exec, F0]
      dsimp only []
      rewrite [SD_1126c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 9 [false, false] [(ELit 69928)] ss1 ([]) = _
      rewrite [sym_exec, F1]
      dsimp only []
      rewrite [SD_11208]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 8 [false, false] [] ss2 (c1) = _
      rewrite [sym_exec, F2]
      dsimp only []
      rewrite [SD_1120c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 7 [false, false] [] ss3 (c1) = _
      rewrite [sym_exec, F3]
      dsimp only []
      rewrite [SD_11210]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0040006f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 6 [false, false] [] ss4 (c1) = _
      rewrite [sym_exec, F4]
      dsimp only []
      rewrite [SD_11214]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfffff7b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 5 [false, false] [] ss5 (c1) = _
      rewrite [sym_exec, F5]
      dsimp only []
      rewrite [SD_11218]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a7e463 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 4 [false] [] ss6 (c5 ++ c1) = _
      rewrite [sym_exec, F6]
      dsimp only []
      rewrite [SD_1121c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 3 [false] [] ss7 (c5 ++ c1) = _
      rewrite [sym_exec, F7]
      dsimp only []
      rewrite [SD_11128]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a05a63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 2 [] [] ss8 (c7 ++ c5 ++ c1) = _
      rewrite [sym_exec, F8]
      dsimp only []
      rewrite [SD_1112c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x40a484b3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 1 [] [] ss9 (c7 ++ c5 ++ c1) = _
      rewrite [sym_exec, F9]
      dsimp only []
      rewrite [SD_11130]
      rfl
    let E := Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 64), p, nat_to_word rest.length, nat_to_word n] ++ [])
    refine Exists.elim (sym_exec_ex source_segs 10 [false, false] [ELit 69928] ss0 [] ss10 scs E
      mem rrom (mkst regs (Z_to_bv 64 70252) mem rrom) (Hexec source_segs tail1_SF_1126c tail1_SF_11208 tail1_SF_1120c tail1_SF_11210 tail1_SF_11214 tail1_SF_11218 tail1_SF_1121c tail1_SF_11128 tail1_SF_1112c tail1_SF_11130) ?sc1 ?st1) ?cont1
    case' cont1 =>
      intro RB HH
      obtain ⟨HRB, Hblock⟩ := HH
      dsimp only [ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRB Hblock
      sym_pc_Z
      chain_mst
      focus exact Hblock
      try sym_mem_norm
      norm_pc
      sym_pc_lit
    case' st1 =>
      refine ⟨regs, rfl, regs_ok_pins E [(1, ELit 70152), (2, EVar 32), (8, EVar 33), (9, EVar 34), (10, EVar 35)] sr_id regs
        (regs_ok_Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 64), p, nat_to_word rest.length, nat_to_word n] ++ [])) ?_, True.intro⟩
      simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
    case' sc1 =>
      dsimp only [scs, c1, c5, c7, List.cons_append, List.nil_append]
      simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
      all_goals sym_norm
      all_goals try sym_sc_auto
    all_goals try first
      | scbr | sysret_ok
      | exact ⟨word_to_le_bytes 8 (0x11128 : word), Hra, by decide +kernel⟩
      | (pin_lit (0x11208 : word); exact H1)
      | exact H2 | exact H8 | exact H9 | exact H10
    have Q2 : reg_get RB 2 = Z_to_bv 64 (bv_unsigned rsp - 48) := by
      sym_regs HRB
      congr 1
      change bv_unsigned rsp - 64 + 16 = bv_unsigned rsp - 48
      omega
    have Q8 : reg_get RB 8 = p + nat_to_word n := by sym_regs HRB; apply v_add_ntw
    have Q9 : reg_get RB 9 = nat_to_word (rest.length - n) := by
      sym_regs HRB
      apply v_sub_ntw <;> omega
    by_cases Hne : n = rest.length
    · subst n
      rw [List.drop_length]
      step_intro
      · rfl
      · apply step_bne_ft _ _ _ _ _ _ _ _ _ tail1_SF_11134 rfl SD_11134
        getr_resolve
        rw [Q9]
        apply c_eq_0_of_u
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc
        stepj tail1_SF_11138 SD_11138
        apply to_wall_tail.twt_done
        exact epilogue_exit0 av ev rsp rrnd Hsp_lo Hsp_hi uid hw _ _ Q2 Hbg
    · step_intro
      · rfl
      · apply step_bne_tk _ _ _ _ _ _ _ _ _ tail1_SF_11134 rfl SD_11134
        getr_resolve
        rw [Q9]
        apply c_eq_0_false
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc
        let ss0 := SS 69912 (sr_pins [(2, EVar 32), (8, EVar 33), (9, EVar 34)] sr_id) [] 35
        let ss1 := SS 69916 (sr_upd ss0.s_regs 12 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [] 35
        let ss2 := SS 69920 (sr_upd ss1.s_regs 11 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 35
        let ss3 := SS 69924 (sr_upd ss2.s_regs 10 (ELit 1)) [] 35
        let ss4 := SS 70112 (sr_upd ss3.s_regs 1 (ELit 69928)) [] 35
        let ss5 := SS 70116 (sr_upd ss4.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))) [] 35
        let ss6 := SS 70120 (sr_upd ss5.s_regs 13 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [] 35
        let ss7 := SS 70124 (sr_upd ss6.s_regs 16 (ELit 0)) [] 35
        let ss8 := SS 70128 (sr_upd ss7.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 35
        let ss9 := SS 70132 (sr_upd ss8.s_regs 15 (ELit 0)) [] 35
        let ss10 := SS 70136 (sr_upd ss9.s_regs 11 (ELit 1)) [] 35
        let ss11 := SS 70140 (sr_upd ss10.s_regs 14 (ELit 0)) [] 35
        let ss12 := SS 70144 (sr_upd ss11.s_regs 10 (ELit 64)) [] 35
        let ss13 := SS 70148 ss12.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss14 := SS 70256 (sr_upd ss13.s_regs 1 (ELit 70152)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss15 := SS 70220 ss14.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss16 := SS 70224 (sr_upd ss15.s_regs 17 (ELit 64)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss17 := SS 70228 (sr_upd ss16.s_regs 10 (ELit 1)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss18 := SS 70232 (sr_upd ss17.s_regs 11 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss19 := SS 70236 (sr_upd ss18.s_regs 12 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss20 := SS 70240 (sr_upd ss19.s_regs 13 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss21 := SS 70244 (sr_upd ss20.s_regs 14 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let ss22 := SS 70248 (sr_upd ss21.s_regs 15 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 35
        let c12 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
        let scs := c12
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69912) = some 0x00048613)
            (F1 : fetch_word segs (Z_to_bv 64 69916) = some 0x00040593)
            (F2 : fetch_word segs (Z_to_bv 64 69920) = some 0x00100513)
            (F3 : fetch_word segs (Z_to_bv 64 69924) = some 0x0bc000ef)
            (F4 : fetch_word segs (Z_to_bv 64 70112) = some 0xff010113)
            (F5 : fetch_word segs (Z_to_bv 64 70116) = some 0x00060693)
            (F6 : fetch_word segs (Z_to_bv 64 70120) = some 0x00000813)
            (F7 : fetch_word segs (Z_to_bv 64 70124) = some 0x00058613)
            (F8 : fetch_word segs (Z_to_bv 64 70128) = some 0x00000793)
            (F9 : fetch_word segs (Z_to_bv 64 70132) = some 0x00050593)
            (F10 : fetch_word segs (Z_to_bv 64 70136) = some 0x00000713)
            (F11 : fetch_word segs (Z_to_bv 64 70140) = some 0x04000513)
            (F12 : fetch_word segs (Z_to_bv 64 70144) = some 0x00113423)
            (F13 : fetch_word segs (Z_to_bv 64 70148) = some 0x06c000ef)
            (F14 : fetch_word segs (Z_to_bv 64 70256) = some 0xfddff06f)
            (F15 : fetch_word segs (Z_to_bv 64 70220) = some 0x00050893)
            (F16 : fetch_word segs (Z_to_bv 64 70224) = some 0x00058513)
            (F17 : fetch_word segs (Z_to_bv 64 70228) = some 0x00060593)
            (F18 : fetch_word segs (Z_to_bv 64 70232) = some 0x00068613)
            (F19 : fetch_word segs (Z_to_bv 64 70236) = some 0x00070693)
            (F20 : fetch_word segs (Z_to_bv 64 70240) = some 0x00078713)
            (F21 : fetch_word segs (Z_to_bv 64 70244) = some 0x00080793)
            (F22 : fetch_word segs (Z_to_bv 64 70248) = some 0x00000073) : sym_exec segs 40 [] [] ss0 [] = (ss22, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_11118]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00048613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 39 [] [] ss1 ([]) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_1111c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00040593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 38 [] [] ss2 ([]) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_11120]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00100513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 37 [] [] ss3 ([]) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_11124]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0bc000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 36 [] [] ss4 ([]) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_111e0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 35 [] [] ss5 ([]) = _
          rewrite [sym_exec, F5]
          dsimp only []
          rewrite [SD_111e4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 34 [] [] ss6 ([]) = _
          rewrite [sym_exec, F6]
          dsimp only []
          rewrite [SD_111e8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 33 [] [] ss7 ([]) = _
          rewrite [sym_exec, F7]
          dsimp only []
          rewrite [SD_111ec]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 32 [] [] ss8 ([]) = _
          rewrite [sym_exec, F8]
          dsimp only []
          rewrite [SD_111f0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 31 [] [] ss9 ([]) = _
          rewrite [sym_exec, F9]
          dsimp only []
          rewrite [SD_111f4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 30 [] [] ss10 ([]) = _
          rewrite [sym_exec, F10]
          dsimp only []
          rewrite [SD_111f8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 29 [] [] ss11 ([]) = _
          rewrite [sym_exec, F11]
          dsimp only []
          rewrite [SD_111fc]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 28 [] [] ss12 ([]) = _
          rewrite [sym_exec, F12]
          dsimp only []
          rewrite [SD_11200]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 27 [] [] ss13 (c12) = _
          rewrite [sym_exec, F13]
          dsimp only []
          rewrite [SD_11204]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06c000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 26 [] [] ss14 (c12) = _
          rewrite [sym_exec, F14]
          dsimp only []
          rewrite [SD_11270]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfddff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 25 [] [] ss15 (c12) = _
          rewrite [sym_exec, F15]
          dsimp only []
          rewrite [SD_1124c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 24 [] [] ss16 (c12) = _
          rewrite [sym_exec, F16]
          dsimp only []
          rewrite [SD_11250]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 23 [] [] ss17 (c12) = _
          rewrite [sym_exec, F17]
          dsimp only []
          rewrite [SD_11254]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 22 [] [] ss18 (c12) = _
          rewrite [sym_exec, F18]
          dsimp only []
          rewrite [SD_11258]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 21 [] [] ss19 (c12) = _
          rewrite [sym_exec, F19]
          dsimp only []
          rewrite [SD_1125c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00070693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 20 [] [] ss20 (c12) = _
          rewrite [sym_exec, F20]
          dsimp only []
          rewrite [SD_11260]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00078713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 19 [] [] ss21 (c12) = _
          rewrite [sym_exec, F21]
          dsimp only []
          rewrite [SD_11264]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 18 [] [] ss22 (c12) = _
          rewrite [sym_exec, F22]
          rfl
        let E := Eplus RB ([Z_to_bv 64 (bv_unsigned rsp - 48), p + nat_to_word n,
                    nat_to_word (rest.length - n)] ++ [])
        refine Exists.elim (sym_exec_ex source_segs 40 [] [] ss0 [] ss22 scs E
          mem rrom (mkst RB (Z_to_bv 64 69912) mem rrom) (Hexec source_segs tail1_SF_11118 tail1_SF_1111c tail1_SF_11120 tail1_SF_11124 tail1_SF_111e0 tail1_SF_111e4 tail1_SF_111e8 tail1_SF_111ec tail1_SF_111f0 tail1_SF_111f4 tail1_SF_111f8 tail1_SF_111fc tail1_SF_11200 tail1_SF_11204 tail1_SF_11270 tail1_SF_1124c tail1_SF_11250 tail1_SF_11254 tail1_SF_11258 tail1_SF_1125c tail1_SF_11260 tail1_SF_11264 tail1_SF_11268) ?sc2 ?st2) ?cont2
        case' cont2 =>
          intro RC HH
          obtain ⟨HRC, Hblock⟩ := HH
          dsimp only [ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRC Hblock
          sym_pc_Z
          chain_mst
          focus exact Hblock
          try sym_mem_norm
          norm_pc
          sym_pc_lit
        case' st2 =>
          refine ⟨RB, rfl, regs_ok_pins E [(2, EVar 32), (8, EVar 33), (9, EVar 34)] sr_id RB
            (regs_ok_Eplus RB ([Z_to_bv 64 (bv_unsigned rsp - 48), p + nat_to_word n,
                    nat_to_word (rest.length - n)] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc2 =>
          dsimp only [scs, c12, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
        all_goals try first
          | (apply source_store_ok <;> imm_norm <;> u_norm <;> omega)
          | solve_store_ok_inv
          | exact Q2 | exact Q8 | exact Q9
        apply to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11268 rfl)
        apply to_wall_tail.twt_more
        · rw [List.length_drop]; omega
        · apply twl_write_rec source_segs (Z_to_bv 64 1)
          · sym_regs HRC; decide +kernel
          · sym_regs HRC; sym_close
          · have Q11 : reg_get RC 11 = p + nat_to_word n := by sym_regs HRC; exact u0_id _
            have Q12 : reg_get RC 12 = nat_to_word (rest.length - n) := by sym_regs HRC; exact u0_id _
            rw [Q11, Q12, ms_read_bytes_rdn source_segs _ _ _ rfl]
            dsimp only [machine_state.ms_mem]
            rw [word_to_nat_ntw _ (by omega)]
            rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega)
              (by rw [length_N_to_le_bytes]; u_norm; omega)]
            exact rdn_skipn source_segs mem rest.length p rest n Hread Hn2
          · rw [List.length_drop]; omega
          · intro m Hm1 Hm2
            norm_pc
            apply IH (rest.drop n) (p + nat_to_word n) m
            · rw [List.length_drop]; omega
            · exact Hm1
            · exact Hm2
            · rw [List.length_drop]; omega
            · omega
            · rw [List.length_drop]; omega
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC
              all_goals rw [List.length_drop]
              all_goals sym_close
            · regupd_resolve; exact len_word_firstn_nat _ _ Hm2
            · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
              u_norm; omega
            · apply rdn_wbytes_hit8
              u_norm; omega
            · rw [rdn_wbytes_below _ _ _ _ _ _ (by rw [List.length_drop]; u_norm; omega)
                (by rw [length_N_to_le_bytes]; u_norm; omega)]
              rw [List.length_drop]
              exact rdn_skipn source_segs mem rest.length p rest n Hread Hn2

include Hsp_lo Hsp_hi in
theorem src_put_wall_cur (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 4097) (Hplo : 0x13000 ≤ bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) ≤ 0x16000)
    (H1 : reg_get regs 1 = (0x11208 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H9 : reg_get regs 9 = p) (H8 : reg_get regs 8 = nat_to_word rest.length)
    (H10 : reg_get regs 10 = nat_to_word n) (Hbg : bg_ok av ev rsp rrnd uid hw mem)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 (0x110d0 : word)))
    (Hread : rdn source_segs mem p rest.length = some rest) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x1126c mem rrom) (rest.drop n)
      (to_exit source_segs (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    have Hpn : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
      rw [word_add_nat]
      apply u_Z2bv <;> omega
    let ss0 := SS 70252 (sr_pins [(1, ELit 70152), (2, EVar 32), (9, EVar 33), (8, EVar 34), (10, EVar 35)] sr_id) [] 36
    let ss1 := SS 70152 ss0.s_regs [] 36
    let ss2 := SS 70156 (sr_upd ss1.s_regs 1 (ELit 69840)) [] 37
    let ss3 := SS 70160 (sr_upd ss2.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit 16))) [] 37
    let ss4 := SS 70164 ss3.s_regs [] 37
    let ss5 := SS 70168 (sr_upd ss4.s_regs 15 (ELit (-4096))) [] 37
    let ss6 := SS 70172 ss5.s_regs [] 37
    let ss7 := SS 69840 ss6.s_regs [] 37
    let ss8 := SS 69844 ss7.s_regs [] 37
    let ss9 := SS 69848 (sr_upd ss8.s_regs 8 (EAlu .ALU_SUB (EVar 34) (EVar 35))) [] 37
    let ss10 := SS 69852 (sr_upd ss9.s_regs 9 (EAlu .ALU_ADD (EVar 33) (EVar 35))) [] 37
    let c1 := [SCFlat (SA (SBVar 32) 8) 8, SCReadBase (SA (SBVar 32) 8) 8 (ELit 69840)]
    let c5 := [SCBr false .BC_LTU (ELit (-4096)) (EVar 35)]
    let c7 := [SCBr false .BC_GE (ELit 0) (EVar 35)]
    let scs := c7 ++ c5 ++ c1
    have Hexec (segs : List Segment)
        (F0 : fetch_word segs (Z_to_bv 64 70252) = some 0x00008067)
        (F1 : fetch_word segs (Z_to_bv 64 70152) = some 0x00813083)
        (F2 : fetch_word segs (Z_to_bv 64 70156) = some 0x01010113)
        (F3 : fetch_word segs (Z_to_bv 64 70160) = some 0x0040006f)
        (F4 : fetch_word segs (Z_to_bv 64 70164) = some 0xfffff7b7)
        (F5 : fetch_word segs (Z_to_bv 64 70168) = some 0x00a7e463)
        (F6 : fetch_word segs (Z_to_bv 64 70172) = some 0x00008067)
        (F7 : fetch_word segs (Z_to_bv 64 69840) = some 0x06a05663)
        (F8 : fetch_word segs (Z_to_bv 64 69844) = some 0x40a40433)
        (F9 : fetch_word segs (Z_to_bv 64 69848) = some 0x00a484b3) : sym_exec segs 10 [false, false] [ELit 69840] ss0 [] = (ss10, scs) := by
      rewrite [sym_exec, F0]
      dsimp only []
      rewrite [SD_1126c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 9 [false, false] [(ELit 69840)] ss1 ([]) = _
      rewrite [sym_exec, F1]
      dsimp only []
      rewrite [SD_11208]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 8 [false, false] [] ss2 (c1) = _
      rewrite [sym_exec, F2]
      dsimp only []
      rewrite [SD_1120c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 7 [false, false] [] ss3 (c1) = _
      rewrite [sym_exec, F3]
      dsimp only []
      rewrite [SD_11210]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0040006f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 6 [false, false] [] ss4 (c1) = _
      rewrite [sym_exec, F4]
      dsimp only []
      rewrite [SD_11214]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfffff7b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 5 [false, false] [] ss5 (c1) = _
      rewrite [sym_exec, F5]
      dsimp only []
      rewrite [SD_11218]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a7e463 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 4 [false] [] ss6 (c5 ++ c1) = _
      rewrite [sym_exec, F6]
      dsimp only []
      rewrite [SD_1121c]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 3 [false] [] ss7 (c5 ++ c1) = _
      rewrite [sym_exec, F7]
      dsimp only []
      rewrite [SD_110d0]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06a05663 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 2 [] [] ss8 (c7 ++ c5 ++ c1) = _
      rewrite [sym_exec, F8]
      dsimp only []
      rewrite [SD_110d4]
      simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x40a40433 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change sym_exec segs 1 [] [] ss9 (c7 ++ c5 ++ c1) = _
      rewrite [sym_exec, F9]
      dsimp only []
      rewrite [SD_110d8]
      rfl
    let E := Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 64), p, nat_to_word rest.length, nat_to_word n] ++ [])
    refine Exists.elim (sym_exec_ex source_segs 10 [false, false] [ELit 69840] ss0 [] ss10 scs E
      mem rrom (mkst regs (Z_to_bv 64 70252) mem rrom) (Hexec source_segs tail1_SF_1126c tail1_SF_11208 tail1_SF_1120c tail1_SF_11210 tail1_SF_11214 tail1_SF_11218 tail1_SF_1121c tail1_SF_110d0 tail1_SF_110d4 tail1_SF_110d8) ?sc1 ?st1) ?cont1
    case' cont1 =>
      intro RB HH
      obtain ⟨HRB, Hblock⟩ := HH
      dsimp only [ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRB Hblock
      sym_pc_Z
      chain_mst
      focus exact Hblock
      try sym_mem_norm
      norm_pc
      sym_pc_lit
    case' st1 =>
      refine ⟨regs, rfl, regs_ok_pins E [(1, ELit 70152), (2, EVar 32), (9, EVar 33), (8, EVar 34), (10, EVar 35)] sr_id regs
        (regs_ok_Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 64), p, nat_to_word rest.length, nat_to_word n] ++ [])) ?_, True.intro⟩
      simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      repeat' apply And.intro
      all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
    case' sc1 =>
      dsimp only [scs, c1, c5, c7, List.cons_append, List.nil_append]
      simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
      all_goals sym_norm
      all_goals try sym_sc_auto
    all_goals try first
      | scbr | sysret_ok
      | exact ⟨word_to_le_bytes 8 (0x110d0 : word), Hra, by decide +kernel⟩
      | (pin_lit (0x11208 : word); exact H1)
      | exact H2 | exact H9 | exact H8 | exact H10
    have Q2 : reg_get RB 2 = Z_to_bv 64 (bv_unsigned rsp - 48) := by
      sym_regs HRB
      congr 1
      change bv_unsigned rsp - 64 + 16 = bv_unsigned rsp - 48
      omega
    have Q9 : reg_get RB 9 = p + nat_to_word n := by sym_regs HRB; apply v_add_ntw
    have Q8 : reg_get RB 8 = nat_to_word (rest.length - n) := by
      sym_regs HRB
      apply v_sub_ntw <;> omega
    by_cases Hne : n = rest.length
    · subst n
      rw [List.drop_length]
      step_intro
      · rfl
      · apply step_bne_ft _ _ _ _ _ _ _ _ _ tail1_SF_110dc rfl SD_110dc
        getr_resolve
        rw [Q8]
        apply c_eq_0_of_u
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc
        apply to_wall_tail.twt_done
        exact epilogue_exit0 av ev rsp rrnd Hsp_lo Hsp_hi uid hw _ _ Q2 Hbg
    · step_intro
      · rfl
      · apply step_bne_tk _ _ _ _ _ _ _ _ _ tail1_SF_110dc rfl SD_110dc
        getr_resolve
        rw [Q8]
        apply c_eq_0_false
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc
        let ss0 := SS 69824 (sr_pins [(2, EVar 32), (9, EVar 33), (8, EVar 34)] sr_id) [] 35
        let ss1 := SS 69828 (sr_upd ss0.s_regs 12 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [] 35
        let ss2 := SS 69832 (sr_upd ss1.s_regs 11 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 35
        let ss3 := SS 69836 (sr_upd ss2.s_regs 10 (ELit 1)) [] 35
        let ss4 := SS 70112 (sr_upd ss3.s_regs 1 (ELit 69840)) [] 35
        let ss5 := SS 70116 (sr_upd ss4.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))) [] 35
        let ss6 := SS 70120 (sr_upd ss5.s_regs 13 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [] 35
        let ss7 := SS 70124 (sr_upd ss6.s_regs 16 (ELit 0)) [] 35
        let ss8 := SS 70128 (sr_upd ss7.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 35
        let ss9 := SS 70132 (sr_upd ss8.s_regs 15 (ELit 0)) [] 35
        let ss10 := SS 70136 (sr_upd ss9.s_regs 11 (ELit 1)) [] 35
        let ss11 := SS 70140 (sr_upd ss10.s_regs 14 (ELit 0)) [] 35
        let ss12 := SS 70144 (sr_upd ss11.s_regs 10 (ELit 64)) [] 35
        let ss13 := SS 70148 ss12.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss14 := SS 70256 (sr_upd ss13.s_regs 1 (ELit 70152)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss15 := SS 70220 ss14.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss16 := SS 70224 (sr_upd ss15.s_regs 17 (ELit 64)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss17 := SS 70228 (sr_upd ss16.s_regs 10 (ELit 1)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss18 := SS 70232 (sr_upd ss17.s_regs 11 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss19 := SS 70236 (sr_upd ss18.s_regs 12 (EAlu .ALU_ADD (EVar 34) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss20 := SS 70240 (sr_upd ss19.s_regs 13 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss21 := SS 70244 (sr_upd ss20.s_regs 14 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let ss22 := SS 70248 (sr_upd ss21.s_regs 15 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 35
        let c12 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
        let scs := c12
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69824) = some 0x00040613)
            (F1 : fetch_word segs (Z_to_bv 64 69828) = some 0x00048593)
            (F2 : fetch_word segs (Z_to_bv 64 69832) = some 0x00100513)
            (F3 : fetch_word segs (Z_to_bv 64 69836) = some 0x114000ef)
            (F4 : fetch_word segs (Z_to_bv 64 70112) = some 0xff010113)
            (F5 : fetch_word segs (Z_to_bv 64 70116) = some 0x00060693)
            (F6 : fetch_word segs (Z_to_bv 64 70120) = some 0x00000813)
            (F7 : fetch_word segs (Z_to_bv 64 70124) = some 0x00058613)
            (F8 : fetch_word segs (Z_to_bv 64 70128) = some 0x00000793)
            (F9 : fetch_word segs (Z_to_bv 64 70132) = some 0x00050593)
            (F10 : fetch_word segs (Z_to_bv 64 70136) = some 0x00000713)
            (F11 : fetch_word segs (Z_to_bv 64 70140) = some 0x04000513)
            (F12 : fetch_word segs (Z_to_bv 64 70144) = some 0x00113423)
            (F13 : fetch_word segs (Z_to_bv 64 70148) = some 0x06c000ef)
            (F14 : fetch_word segs (Z_to_bv 64 70256) = some 0xfddff06f)
            (F15 : fetch_word segs (Z_to_bv 64 70220) = some 0x00050893)
            (F16 : fetch_word segs (Z_to_bv 64 70224) = some 0x00058513)
            (F17 : fetch_word segs (Z_to_bv 64 70228) = some 0x00060593)
            (F18 : fetch_word segs (Z_to_bv 64 70232) = some 0x00068613)
            (F19 : fetch_word segs (Z_to_bv 64 70236) = some 0x00070693)
            (F20 : fetch_word segs (Z_to_bv 64 70240) = some 0x00078713)
            (F21 : fetch_word segs (Z_to_bv 64 70244) = some 0x00080793)
            (F22 : fetch_word segs (Z_to_bv 64 70248) = some 0x00000073) : sym_exec segs 40 [] [] ss0 [] = (ss22, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_110c0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00040613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 39 [] [] ss1 ([]) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_110c4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00048593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 38 [] [] ss2 ([]) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_110c8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00100513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 37 [] [] ss3 ([]) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_110cc]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x114000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 36 [] [] ss4 ([]) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_111e0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 35 [] [] ss5 ([]) = _
          rewrite [sym_exec, F5]
          dsimp only []
          rewrite [SD_111e4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 34 [] [] ss6 ([]) = _
          rewrite [sym_exec, F6]
          dsimp only []
          rewrite [SD_111e8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 33 [] [] ss7 ([]) = _
          rewrite [sym_exec, F7]
          dsimp only []
          rewrite [SD_111ec]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 32 [] [] ss8 ([]) = _
          rewrite [sym_exec, F8]
          dsimp only []
          rewrite [SD_111f0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 31 [] [] ss9 ([]) = _
          rewrite [sym_exec, F9]
          dsimp only []
          rewrite [SD_111f4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 30 [] [] ss10 ([]) = _
          rewrite [sym_exec, F10]
          dsimp only []
          rewrite [SD_111f8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 29 [] [] ss11 ([]) = _
          rewrite [sym_exec, F11]
          dsimp only []
          rewrite [SD_111fc]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 28 [] [] ss12 ([]) = _
          rewrite [sym_exec, F12]
          dsimp only []
          rewrite [SD_11200]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 27 [] [] ss13 (c12) = _
          rewrite [sym_exec, F13]
          dsimp only []
          rewrite [SD_11204]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06c000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 26 [] [] ss14 (c12) = _
          rewrite [sym_exec, F14]
          dsimp only []
          rewrite [SD_11270]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfddff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 25 [] [] ss15 (c12) = _
          rewrite [sym_exec, F15]
          dsimp only []
          rewrite [SD_1124c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 24 [] [] ss16 (c12) = _
          rewrite [sym_exec, F16]
          dsimp only []
          rewrite [SD_11250]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 23 [] [] ss17 (c12) = _
          rewrite [sym_exec, F17]
          dsimp only []
          rewrite [SD_11254]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 22 [] [] ss18 (c12) = _
          rewrite [sym_exec, F18]
          dsimp only []
          rewrite [SD_11258]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 21 [] [] ss19 (c12) = _
          rewrite [sym_exec, F19]
          dsimp only []
          rewrite [SD_1125c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00070693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 20 [] [] ss20 (c12) = _
          rewrite [sym_exec, F20]
          dsimp only []
          rewrite [SD_11260]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00078713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 19 [] [] ss21 (c12) = _
          rewrite [sym_exec, F21]
          dsimp only []
          rewrite [SD_11264]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 18 [] [] ss22 (c12) = _
          rewrite [sym_exec, F22]
          rfl
        let E := Eplus RB ([Z_to_bv 64 (bv_unsigned rsp - 48), p + nat_to_word n,
                    nat_to_word (rest.length - n)] ++ [])
        refine Exists.elim (sym_exec_ex source_segs 40 [] [] ss0 [] ss22 scs E
          mem rrom (mkst RB (Z_to_bv 64 69824) mem rrom) (Hexec source_segs tail1_SF_110c0 tail1_SF_110c4 tail1_SF_110c8 tail1_SF_110cc tail1_SF_111e0 tail1_SF_111e4 tail1_SF_111e8 tail1_SF_111ec tail1_SF_111f0 tail1_SF_111f4 tail1_SF_111f8 tail1_SF_111fc tail1_SF_11200 tail1_SF_11204 tail1_SF_11270 tail1_SF_1124c tail1_SF_11250 tail1_SF_11254 tail1_SF_11258 tail1_SF_1125c tail1_SF_11260 tail1_SF_11264 tail1_SF_11268) ?sc2 ?st2) ?cont2
        case' cont2 =>
          intro RC HH
          obtain ⟨HRC, Hblock⟩ := HH
          dsimp only [ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRC Hblock
          sym_pc_Z
          chain_mst
          focus exact Hblock
          try sym_mem_norm
          norm_pc
          sym_pc_lit
        case' st2 =>
          refine ⟨RB, rfl, regs_ok_pins E [(2, EVar 32), (9, EVar 33), (8, EVar 34)] sr_id RB
            (regs_ok_Eplus RB ([Z_to_bv 64 (bv_unsigned rsp - 48), p + nat_to_word n,
                    nat_to_word (rest.length - n)] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc2 =>
          dsimp only [scs, c12, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
        all_goals try first
          | (apply source_store_ok <;> imm_norm <;> u_norm <;> omega)
          | solve_store_ok_inv
          | exact Q2 | exact Q9 | exact Q8
        apply to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11268 rfl)
        apply to_wall_tail.twt_more
        · rw [List.length_drop]; omega
        · apply twl_write_rec source_segs (Z_to_bv 64 1)
          · sym_regs HRC; decide +kernel
          · sym_regs HRC; sym_close
          · have Q11 : reg_get RC 11 = p + nat_to_word n := by sym_regs HRC; exact u0_id _
            have Q12 : reg_get RC 12 = nat_to_word (rest.length - n) := by sym_regs HRC; exact u0_id _
            rw [Q11, Q12, ms_read_bytes_rdn source_segs _ _ _ rfl]
            dsimp only [machine_state.ms_mem]
            rw [word_to_nat_ntw _ (by omega)]
            rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega)
              (by rw [length_N_to_le_bytes]; u_norm; omega)]
            exact rdn_skipn source_segs mem rest.length p rest n Hread Hn2
          · rw [List.length_drop]; omega
          · intro m Hm1 Hm2
            norm_pc
            apply IH (rest.drop n) (p + nat_to_word n) m
            · rw [List.length_drop]; omega
            · exact Hm1
            · exact Hm2
            · rw [List.length_drop]; omega
            · omega
            · rw [List.length_drop]; omega
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC <;> sym_close
            · regupd_resolve; sym_regs HRC
              all_goals rw [List.length_drop]
              all_goals sym_close
            · regupd_resolve; exact len_word_firstn_nat _ _ Hm2
            · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
              u_norm; omega
            · apply rdn_wbytes_hit8
              u_norm; omega
            · rw [rdn_wbytes_below _ _ _ _ _ _ (by rw [List.length_drop]; u_norm; omega)
                (by rw [length_N_to_le_bytes]; u_norm; omega)]
              rw [List.length_drop]
              exact rdn_skipn source_segs mem rest.length p rest n Hread Hn2

include Hsp_lo Hsp_hi in
/-- EOF continuation: from the post-read state (a0 = 0, pc 0x1126c,
sp = rsp-64) run the return path, write the last line, exit 0. -/
theorem eof_to_out (R : bvmap 5 word) (mem : word → Option byte) (cur done : List byte)
    (H1 : reg_get R 1 = (0x111d4 : word))
    (H2 : reg_get R 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H10 : reg_get R 10 = Z_to_bv 64 0)
    (H8 : reg_get R 8 = nat_to_word cur.length) (H9 : reg_get R 9 = nat_to_word done.length)
    (Hbg : bg_ok av ev rsp rrnd uid hw mem)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 (0x11040 : word)))
    (Hcur : rdn source_segs mem cur_base cur.length = some cur)
    (Hdone : rdn source_segs mem done_base done.length = some done)
    (Hcurcap : (cur.length : Int) ≤ 4096) (Hdonecap : (done.length : Int) ≤ 4097) :
    to_out source_segs (out (cur, done)) (mkst R 0x1126c mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let ss0 := SS 70252 (sr_pins [(1, ELit 70100), (2, EVar 32), (10, ELit 0)] sr_id) [] 33
  let ss1 := SS 70100 ss0.s_regs [] 33
  let ss2 := SS 70104 (sr_upd ss1.s_regs 1 (ELit 69696)) [] 34
  let ss3 := SS 70108 (sr_upd ss2.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit 16))) [] 34
  let ss4 := SS 70164 ss3.s_regs [] 34
  let ss5 := SS 70168 (sr_upd ss4.s_regs 15 (ELit (-4096))) [] 34
  let ss6 := SS 70172 ss5.s_regs [] 34
  let ss7 := SS 69696 ss6.s_regs [] 34
  let ss8 := SS 69700 ss7.s_regs [] 34
  let ss9 := SS 69812 ss8.s_regs [] 34
  let c1 := [SCFlat (SA (SBVar 32) 8) 8, SCReadBase (SA (SBVar 32) 8) 8 (ELit 69696)]
  let c5 := [SCBr false .BC_LTU (ELit (-4096)) (ELit 0)]
  let c7 := [SCBr false .BC_LT (ELit 0) (ELit 0)]
  let c8 := [SCBr true .BC_EQ (ELit 0) (ELit 0)]
  let scs := c8 ++ c7 ++ c5 ++ c1
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 70252) = some 0x00008067)
      (F1 : fetch_word segs (Z_to_bv 64 70100) = some 0x00813083)
      (F2 : fetch_word segs (Z_to_bv 64 70104) = some 0x01010113)
      (F3 : fetch_word segs (Z_to_bv 64 70108) = some 0x0380006f)
      (F4 : fetch_word segs (Z_to_bv 64 70164) = some 0xfffff7b7)
      (F5 : fetch_word segs (Z_to_bv 64 70168) = some 0x00a7e463)
      (F6 : fetch_word segs (Z_to_bv 64 70172) = some 0x00008067)
      (F7 : fetch_word segs (Z_to_bv 64 69696) = some 0x10054263)
      (F8 : fetch_word segs (Z_to_bv 64 69700) = some 0x06050863) : sym_exec segs 9 [false, false, true] [ELit 69696] ss0 [] = (ss9, scs) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_1126c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 8 [false, false, true] [(ELit 69696)] ss1 ([]) = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_111d4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 7 [false, false, true] [] ss2 (c1) = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_111d8]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 6 [false, false, true] [] ss3 (c1) = _
    rewrite [sym_exec, F3]
    dsimp only []
    rewrite [SD_111dc]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0380006f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 5 [false, false, true] [] ss4 (c1) = _
    rewrite [sym_exec, F4]
    dsimp only []
    rewrite [SD_11214]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfffff7b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 4 [false, false, true] [] ss5 (c1) = _
    rewrite [sym_exec, F5]
    dsimp only []
    rewrite [SD_11218]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a7e463 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 3 [false, true] [] ss6 (c5 ++ c1) = _
    rewrite [sym_exec, F6]
    dsimp only []
    rewrite [SD_1121c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [false, true] [] ss7 (c5 ++ c1) = _
    rewrite [sym_exec, F7]
    dsimp only []
    rewrite [SD_11040]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x10054263 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [true] [] ss8 (c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F8]
    dsimp only []
    rewrite [SD_11044]
    rfl
  let E := Eplus R ([Z_to_bv 64 (bv_unsigned rsp - 64)] ++ [])
  refine Exists.elim (sym_exec_ex source_segs 9 [false, false, true] [ELit 69696] ss0 [] ss9 scs E
    mem rrom (mkst R (Z_to_bv 64 70252) mem rrom) (Hexec source_segs tail1_SF_1126c tail1_SF_111d4 tail1_SF_111d8 tail1_SF_111dc tail1_SF_11214 tail1_SF_11218 tail1_SF_1121c tail1_SF_11040 tail1_SF_11044) ?sc1 ?st1) ?cont1
  case' cont1 =>
    intro R0 HH
    obtain ⟨HR0, Hblock⟩ := HH
    dsimp only [ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR0 Hblock
    sym_pc_Z
    chain_mst
    focus exact Hblock
    try sym_mem_norm
    norm_pc
    sym_pc_lit
  case' st1 =>
    refine ⟨R, rfl, regs_ok_pins E [(1, ELit 70100), (2, EVar 32), (10, ELit 0)] sr_id R
      (regs_ok_Eplus R ([Z_to_bv 64 (bv_unsigned rsp - 64)] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
  case' sc1 =>
    dsimp only [scs, c1, c5, c7, c8, List.cons_append, List.nil_append]
    simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
    all_goals sym_norm
    all_goals try sym_sc_auto
    all_goals try rfl
  · exact ⟨word_to_le_bytes 8 (0x11040 : word), Hra, by decide +kernel⟩
  · pin_lit (0x111d4 : word)
    exact H1
  · exact H2
  · exact H10
  · have Q2 : reg_get R0 2 = Z_to_bv 64 (bv_unsigned rsp - 48) := by
      sym_regs HR0
      congr 1
      change bv_unsigned rsp - 64 + 16 = bv_unsigned rsp - 48
      omega
    cases cur with
    | nil =>
      cases done with
      | nil =>
        change to_out source_segs [] _
        apply to_out.tout_exit
        let ss0 := SS 69812 (sr_pins [(8, ELit 0), (9, ELit 0)] sr_id) [] 32
        let ss1 := SS 69896 ss0.s_regs [] 32
        let ss2 := SS 69900 (sr_upd ss1.s_regs 10 (ELit 0)) [] 32
        let ss3 := SS 69868 ss2.s_regs [] 32
        let c0 := [SCBr true .BC_EQ (ELit 0) (ELit 0)]
        let c2 := [SCBr true .BC_EQ (ELit 0) (ELit 0)]
        let scs := c2 ++ c0
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69812) = some 0x04040a63)
            (F1 : fetch_word segs (Z_to_bv 64 69896) = some 0x00000513)
            (F2 : fetch_word segs (Z_to_bv 64 69900) = some 0xfe0480e3) : sym_exec segs 3 [true, true] [] ss0 [] = (ss3, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_110b4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04040a63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 2 [true] [] ss1 (c0) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_11108]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 1 [true] [] ss2 (c0) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_1110c]
          rfl
        let E := Eplus R0 ([] ++ [])
        refine Exists.elim (sym_exec_ex source_segs 3 [true, true] [] ss0 [] ss3 scs E
          mem rrom (mkst R0 (Z_to_bv 64 69812) mem rrom) (Hexec source_segs tail1_SF_110b4 tail1_SF_11108 tail1_SF_1110c) ?sc2 ?st2) ?cont2
        case' cont2 =>
          intro R1 HH
          obtain ⟨HR1, Hblock⟩ := HH
          dsimp only [ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR1 Hblock
          sym_pc_Z
          chain_mst
          focus exact Hblock
          try sym_mem_norm
          norm_pc
          sym_pc_lit
        case' st2 =>
          refine ⟨R0, rfl, regs_ok_pins E [(8, ELit 0), (9, ELit 0)] sr_id R0
            (regs_ok_Eplus R0 ([] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc2 =>
          dsimp only [scs, c0, c2, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
          all_goals try rfl
        · sym_regs HR0; exact H8
        · sym_regs HR0; exact H9
        · apply epilogue_exit av ev rsp rrnd Hsp_lo Hsp_hi uid hw
          · sym_regs HR1; exact Q2
          · sym_regs HR1 <;> sym_close
          · exact Hbg
      | cons d done' =>
        change to_out source_segs (d :: done') _
        let ss0 := SS 69812 (sr_pins [(2, EVar 32), (8, ELit 0), (9, EVar 33)] sr_id) [] 34
        let ss1 := SS 69896 ss0.s_regs [] 34
        let ss2 := SS 69900 (sr_upd ss1.s_regs 10 (ELit 0)) [] 34
        let ss3 := SS 69904 ss2.s_regs [] 34
        let ss4 := SS 69908 (sr_upd ss3.s_regs 8 (ELit 77824)) [] 34
        let ss5 := SS 69912 (sr_upd ss4.s_regs 8 (ELit 78856)) [] 34
        let ss6 := SS 69916 (sr_upd ss5.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 34
        let ss7 := SS 69920 (sr_upd ss6.s_regs 11 (ELit 78856)) [] 34
        let ss8 := SS 69924 (sr_upd ss7.s_regs 10 (ELit 1)) [] 34
        let ss9 := SS 70112 (sr_upd ss8.s_regs 1 (ELit 69928)) [] 34
        let ss10 := SS 70116 (sr_upd ss9.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))) [] 34
        let ss11 := SS 70120 (sr_upd ss10.s_regs 13 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 34
        let ss12 := SS 70124 (sr_upd ss11.s_regs 16 (ELit 0)) [] 34
        let ss13 := SS 70128 (sr_upd ss12.s_regs 12 (ELit 78856)) [] 34
        let ss14 := SS 70132 (sr_upd ss13.s_regs 15 (ELit 0)) [] 34
        let ss15 := SS 70136 (sr_upd ss14.s_regs 11 (ELit 1)) [] 34
        let ss16 := SS 70140 (sr_upd ss15.s_regs 14 (ELit 0)) [] 34
        let ss17 := SS 70144 (sr_upd ss16.s_regs 10 (ELit 64)) [] 34
        let ss18 := SS 70148 ss17.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss19 := SS 70256 (sr_upd ss18.s_regs 1 (ELit 70152)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss20 := SS 70220 ss19.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss21 := SS 70224 (sr_upd ss20.s_regs 17 (ELit 64)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss22 := SS 70228 (sr_upd ss21.s_regs 10 (ELit 1)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss23 := SS 70232 (sr_upd ss22.s_regs 11 (ELit 78856)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss24 := SS 70236 (sr_upd ss23.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss25 := SS 70240 (sr_upd ss24.s_regs 13 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss26 := SS 70244 (sr_upd ss25.s_regs 14 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let ss27 := SS 70248 (sr_upd ss26.s_regs 15 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69928)] 34
        let c0 := [SCBr true .BC_EQ (ELit 0) (ELit 0)]
        let c2 := [SCBr false .BC_EQ (EVar 33) (ELit 0)]
        let c17 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
        let scs := c17 ++ c2 ++ c0
        have Hexec (segs : List Segment)
            (F0 : fetch_word segs (Z_to_bv 64 69812) = some 0x04040a63)
            (F1 : fetch_word segs (Z_to_bv 64 69896) = some 0x00000513)
            (F2 : fetch_word segs (Z_to_bv 64 69900) = some 0xfe0480e3)
            (F3 : fetch_word segs (Z_to_bv 64 69904) = some 0x00013437)
            (F4 : fetch_word segs (Z_to_bv 64 69908) = some 0x40840413)
            (F5 : fetch_word segs (Z_to_bv 64 69912) = some 0x00048613)
            (F6 : fetch_word segs (Z_to_bv 64 69916) = some 0x00040593)
            (F7 : fetch_word segs (Z_to_bv 64 69920) = some 0x00100513)
            (F8 : fetch_word segs (Z_to_bv 64 69924) = some 0x0bc000ef)
            (F9 : fetch_word segs (Z_to_bv 64 70112) = some 0xff010113)
            (F10 : fetch_word segs (Z_to_bv 64 70116) = some 0x00060693)
            (F11 : fetch_word segs (Z_to_bv 64 70120) = some 0x00000813)
            (F12 : fetch_word segs (Z_to_bv 64 70124) = some 0x00058613)
            (F13 : fetch_word segs (Z_to_bv 64 70128) = some 0x00000793)
            (F14 : fetch_word segs (Z_to_bv 64 70132) = some 0x00050593)
            (F15 : fetch_word segs (Z_to_bv 64 70136) = some 0x00000713)
            (F16 : fetch_word segs (Z_to_bv 64 70140) = some 0x04000513)
            (F17 : fetch_word segs (Z_to_bv 64 70144) = some 0x00113423)
            (F18 : fetch_word segs (Z_to_bv 64 70148) = some 0x06c000ef)
            (F19 : fetch_word segs (Z_to_bv 64 70256) = some 0xfddff06f)
            (F20 : fetch_word segs (Z_to_bv 64 70220) = some 0x00050893)
            (F21 : fetch_word segs (Z_to_bv 64 70224) = some 0x00058513)
            (F22 : fetch_word segs (Z_to_bv 64 70228) = some 0x00060593)
            (F23 : fetch_word segs (Z_to_bv 64 70232) = some 0x00068613)
            (F24 : fetch_word segs (Z_to_bv 64 70236) = some 0x00070693)
            (F25 : fetch_word segs (Z_to_bv 64 70240) = some 0x00078713)
            (F26 : fetch_word segs (Z_to_bv 64 70244) = some 0x00080793)
            (F27 : fetch_word segs (Z_to_bv 64 70248) = some 0x00000073) : sym_exec segs 28 [true, false] [] ss0 [] = (ss27, scs) := by
          rewrite [sym_exec, F0]
          dsimp only []
          rewrite [SD_110b4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04040a63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 27 [false] [] ss1 (c0) = _
          rewrite [sym_exec, F1]
          dsimp only []
          rewrite [SD_11108]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 26 [false] [] ss2 (c0) = _
          rewrite [sym_exec, F2]
          dsimp only []
          rewrite [SD_1110c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfe0480e3 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 25 [] [] ss3 (c2 ++ c0) = _
          rewrite [sym_exec, F3]
          dsimp only []
          rewrite [SD_11110]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00013437 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 24 [] [] ss4 (c2 ++ c0) = _
          rewrite [sym_exec, F4]
          dsimp only []
          rewrite [SD_11114]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x40840413 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 23 [] [] ss5 (c2 ++ c0) = _
          rewrite [sym_exec, F5]
          dsimp only []
          rewrite [SD_11118]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00048613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 22 [] [] ss6 (c2 ++ c0) = _
          rewrite [sym_exec, F6]
          dsimp only []
          rewrite [SD_1111c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00040593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 21 [] [] ss7 (c2 ++ c0) = _
          rewrite [sym_exec, F7]
          dsimp only []
          rewrite [SD_11120]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00100513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 20 [] [] ss8 (c2 ++ c0) = _
          rewrite [sym_exec, F8]
          dsimp only []
          rewrite [SD_11124]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0bc000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 19 [] [] ss9 (c2 ++ c0) = _
          rewrite [sym_exec, F9]
          dsimp only []
          rewrite [SD_111e0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 18 [] [] ss10 (c2 ++ c0) = _
          rewrite [sym_exec, F10]
          dsimp only []
          rewrite [SD_111e4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 17 [] [] ss11 (c2 ++ c0) = _
          rewrite [sym_exec, F11]
          dsimp only []
          rewrite [SD_111e8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 16 [] [] ss12 (c2 ++ c0) = _
          rewrite [sym_exec, F12]
          dsimp only []
          rewrite [SD_111ec]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 15 [] [] ss13 (c2 ++ c0) = _
          rewrite [sym_exec, F13]
          dsimp only []
          rewrite [SD_111f0]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 14 [] [] ss14 (c2 ++ c0) = _
          rewrite [sym_exec, F14]
          dsimp only []
          rewrite [SD_111f4]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 13 [] [] ss15 (c2 ++ c0) = _
          rewrite [sym_exec, F15]
          dsimp only []
          rewrite [SD_111f8]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 12 [] [] ss16 (c2 ++ c0) = _
          rewrite [sym_exec, F16]
          dsimp only []
          rewrite [SD_111fc]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 11 [] [] ss17 (c2 ++ c0) = _
          rewrite [sym_exec, F17]
          dsimp only []
          rewrite [SD_11200]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 10 [] [] ss18 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F18]
          dsimp only []
          rewrite [SD_11204]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06c000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 9 [] [] ss19 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F19]
          dsimp only []
          rewrite [SD_11270]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfddff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 8 [] [] ss20 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F20]
          dsimp only []
          rewrite [SD_1124c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 7 [] [] ss21 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F21]
          dsimp only []
          rewrite [SD_11250]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 6 [] [] ss22 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F22]
          dsimp only []
          rewrite [SD_11254]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 5 [] [] ss23 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F23]
          dsimp only []
          rewrite [SD_11258]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 4 [] [] ss24 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F24]
          dsimp only []
          rewrite [SD_1125c]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00070693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 3 [] [] ss25 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F25]
          dsimp only []
          rewrite [SD_11260]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00078713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 2 [] [] ss26 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F26]
          dsimp only []
          rewrite [SD_11264]
          simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
          change sym_exec segs 1 [] [] ss27 (c17 ++ c2 ++ c0) = _
          rewrite [sym_exec, F27]
          rfl
        let E := Eplus R0 ([Z_to_bv 64 (bv_unsigned rsp - 48), nat_to_word (d :: done').length] ++ [])
        refine Exists.elim (sym_exec_ex source_segs 28 [true, false] [] ss0 [] ss27 scs E
          mem rrom (mkst R0 (Z_to_bv 64 69812) mem rrom) (Hexec source_segs tail1_SF_110b4 tail1_SF_11108 tail1_SF_1110c tail1_SF_11110 tail1_SF_11114 tail1_SF_11118 tail1_SF_1111c tail1_SF_11120 tail1_SF_11124 tail1_SF_111e0 tail1_SF_111e4 tail1_SF_111e8 tail1_SF_111ec tail1_SF_111f0 tail1_SF_111f4 tail1_SF_111f8 tail1_SF_111fc tail1_SF_11200 tail1_SF_11204 tail1_SF_11270 tail1_SF_1124c tail1_SF_11250 tail1_SF_11254 tail1_SF_11258 tail1_SF_1125c tail1_SF_11260 tail1_SF_11264 tail1_SF_11268) ?sc3 ?st3) ?cont3
        case' cont3 =>
          intro R1 HH
          obtain ⟨HR1, Hblock⟩ := HH
          dsimp only [ss27, ss26, ss25, ss24, ss23, ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR1 Hblock
          sym_pc_Z
          chain_mst
          focus exact Hblock
          try sym_mem_norm
          norm_pc
          sym_pc_lit
        case' st3 =>
          refine ⟨R0, rfl, regs_ok_pins E [(2, EVar 32), (8, ELit 0), (9, EVar 33)] sr_id R0
            (regs_ok_Eplus R0 ([Z_to_bv 64 (bv_unsigned rsp - 48), nat_to_word (d :: done').length] ++ [])) ?_, True.intro⟩
          simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          repeat' apply And.intro
          all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
        case' sc3 =>
          dsimp only [scs, c0, c2, c17, List.cons_append, List.nil_append]
          simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
          all_goals sym_norm
          all_goals try sym_sc_auto
          all_goals try rfl
        · first | (apply source_store_ok <;> unorm <;> omega) | solve_store_ok_inv
        · scbr
        · exact Q2
        · sym_regs HR0; exact H8
        · sym_regs HR0; exact H9
        · apply to_out.tout_step _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11268 rfl)
          apply tout_wr_rec
          · sym_regs HR1; decide +kernel
          · sym_regs HR1 <;> sym_close
          · have Q11 : reg_get R1 11 = done_base := by sym_regs HR1; bveq
            have Q12 : reg_get R1 12 = nat_to_word (d :: done').length := by sym_regs HR1; exact u0_id _
            rw [Q11, Q12, ms_read_bytes_rdn source_segs _ _ _ rfl]
            dsimp only [machine_state.ms_mem]
            rw [word_to_nat_ntw _ (by lenlia)]
            rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
              (by rw [length_N_to_le_bytes]; unorm; omega)]
            exact Hdone
          · simp only [List.length_cons]; omega
          · intro n Hn1 Hn2
            norm_pc
            apply src_put_wall_done av ev rsp rrnd Hsp_lo Hsp_hi uid hw
              (d :: done').length (d :: done') done_base n
            · omega
            · exact Hn1
            · exact Hn2
            · lenlia
            · rw [u_done_base]; omega
            · rw [u_done_base]; lenlia
            · sym_regs HR1 <;> sym_close
            · sym_regs HR1 <;> sym_close
            · sym_regs HR1 <;> sym_close
            · sym_regs HR1 <;> sym_close
            · regupd_resolve; exact len_word_firstn_nat _ _ Hn2
            · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
              u_norm; omega
            · apply rdn_wbytes_hit8
              u_norm; omega
            · rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
                (by rw [length_N_to_le_bytes]; unorm; omega)]
              exact Hdone
    | cons c cur' =>
      change to_out source_segs (c :: cur') _
      let ss0 := SS 69812 (sr_pins [(2, EVar 32), (8, EVar 33)] sr_id) [] 34
      let ss1 := SS 69816 ss0.s_regs [] 34
      let ss2 := SS 69820 (sr_upd ss1.s_regs 9 (ELit 81920)) [] 34
      let ss3 := SS 69824 (sr_upd ss2.s_regs 9 (ELit 82960)) [] 34
      let ss4 := SS 69828 (sr_upd ss3.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 34
      let ss5 := SS 69832 (sr_upd ss4.s_regs 11 (ELit 82960)) [] 34
      let ss6 := SS 69836 (sr_upd ss5.s_regs 10 (ELit 1)) [] 34
      let ss7 := SS 70112 (sr_upd ss6.s_regs 1 (ELit 69840)) [] 34
      let ss8 := SS 70116 (sr_upd ss7.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))) [] 34
      let ss9 := SS 70120 (sr_upd ss8.s_regs 13 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [] 34
      let ss10 := SS 70124 (sr_upd ss9.s_regs 16 (ELit 0)) [] 34
      let ss11 := SS 70128 (sr_upd ss10.s_regs 12 (ELit 82960)) [] 34
      let ss12 := SS 70132 (sr_upd ss11.s_regs 15 (ELit 0)) [] 34
      let ss13 := SS 70136 (sr_upd ss12.s_regs 11 (ELit 1)) [] 34
      let ss14 := SS 70140 (sr_upd ss13.s_regs 14 (ELit 0)) [] 34
      let ss15 := SS 70144 (sr_upd ss14.s_regs 10 (ELit 64)) [] 34
      let ss16 := SS 70148 ss15.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss17 := SS 70256 (sr_upd ss16.s_regs 1 (ELit 70152)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss18 := SS 70220 ss17.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss19 := SS 70224 (sr_upd ss18.s_regs 17 (ELit 64)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss20 := SS 70228 (sr_upd ss19.s_regs 10 (ELit 1)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss21 := SS 70232 (sr_upd ss20.s_regs 11 (ELit 82960)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss22 := SS 70236 (sr_upd ss21.s_regs 12 (EAlu .ALU_ADD (EVar 33) (ELit 0))) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss23 := SS 70240 (sr_upd ss22.s_regs 13 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss24 := SS 70244 (sr_upd ss23.s_regs 14 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let ss25 := SS 70248 (sr_upd ss24.s_regs 15 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69840)] 34
      let c0 := [SCBr false .BC_EQ (EVar 33) (ELit 0)]
      let c15 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
      let scs := c15 ++ c0
      have Hexec (segs : List Segment)
          (F0 : fetch_word segs (Z_to_bv 64 69812) = some 0x04040a63)
          (F1 : fetch_word segs (Z_to_bv 64 69816) = some 0x000144b7)
          (F2 : fetch_word segs (Z_to_bv 64 69820) = some 0x41048493)
          (F3 : fetch_word segs (Z_to_bv 64 69824) = some 0x00040613)
          (F4 : fetch_word segs (Z_to_bv 64 69828) = some 0x00048593)
          (F5 : fetch_word segs (Z_to_bv 64 69832) = some 0x00100513)
          (F6 : fetch_word segs (Z_to_bv 64 69836) = some 0x114000ef)
          (F7 : fetch_word segs (Z_to_bv 64 70112) = some 0xff010113)
          (F8 : fetch_word segs (Z_to_bv 64 70116) = some 0x00060693)
          (F9 : fetch_word segs (Z_to_bv 64 70120) = some 0x00000813)
          (F10 : fetch_word segs (Z_to_bv 64 70124) = some 0x00058613)
          (F11 : fetch_word segs (Z_to_bv 64 70128) = some 0x00000793)
          (F12 : fetch_word segs (Z_to_bv 64 70132) = some 0x00050593)
          (F13 : fetch_word segs (Z_to_bv 64 70136) = some 0x00000713)
          (F14 : fetch_word segs (Z_to_bv 64 70140) = some 0x04000513)
          (F15 : fetch_word segs (Z_to_bv 64 70144) = some 0x00113423)
          (F16 : fetch_word segs (Z_to_bv 64 70148) = some 0x06c000ef)
          (F17 : fetch_word segs (Z_to_bv 64 70256) = some 0xfddff06f)
          (F18 : fetch_word segs (Z_to_bv 64 70220) = some 0x00050893)
          (F19 : fetch_word segs (Z_to_bv 64 70224) = some 0x00058513)
          (F20 : fetch_word segs (Z_to_bv 64 70228) = some 0x00060593)
          (F21 : fetch_word segs (Z_to_bv 64 70232) = some 0x00068613)
          (F22 : fetch_word segs (Z_to_bv 64 70236) = some 0x00070693)
          (F23 : fetch_word segs (Z_to_bv 64 70240) = some 0x00078713)
          (F24 : fetch_word segs (Z_to_bv 64 70244) = some 0x00080793)
          (F25 : fetch_word segs (Z_to_bv 64 70248) = some 0x00000073) : sym_exec segs 26 [false] [] ss0 [] = (ss25, scs) := by
        rewrite [sym_exec, F0]
        dsimp only []
        rewrite [SD_110b4]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04040a63 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 25 [] [] ss1 (c0) = _
        rewrite [sym_exec, F1]
        dsimp only []
        rewrite [SD_110b8]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x000144b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 24 [] [] ss2 (c0) = _
        rewrite [sym_exec, F2]
        dsimp only []
        rewrite [SD_110bc]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x41048493 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 23 [] [] ss3 (c0) = _
        rewrite [sym_exec, F3]
        dsimp only []
        rewrite [SD_110c0]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00040613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 22 [] [] ss4 (c0) = _
        rewrite [sym_exec, F4]
        dsimp only []
        rewrite [SD_110c4]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00048593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 21 [] [] ss5 (c0) = _
        rewrite [sym_exec, F5]
        dsimp only []
        rewrite [SD_110c8]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00100513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 20 [] [] ss6 (c0) = _
        rewrite [sym_exec, F6]
        dsimp only []
        rewrite [SD_110cc]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x114000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 19 [] [] ss7 (c0) = _
        rewrite [sym_exec, F7]
        dsimp only []
        rewrite [SD_111e0]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 18 [] [] ss8 (c0) = _
        rewrite [sym_exec, F8]
        dsimp only []
        rewrite [SD_111e4]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 17 [] [] ss9 (c0) = _
        rewrite [sym_exec, F9]
        dsimp only []
        rewrite [SD_111e8]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 16 [] [] ss10 (c0) = _
        rewrite [sym_exec, F10]
        dsimp only []
        rewrite [SD_111ec]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 15 [] [] ss11 (c0) = _
        rewrite [sym_exec, F11]
        dsimp only []
        rewrite [SD_111f0]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 14 [] [] ss12 (c0) = _
        rewrite [sym_exec, F12]
        dsimp only []
        rewrite [SD_111f4]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 13 [] [] ss13 (c0) = _
        rewrite [sym_exec, F13]
        dsimp only []
        rewrite [SD_111f8]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 12 [] [] ss14 (c0) = _
        rewrite [sym_exec, F14]
        dsimp only []
        rewrite [SD_111fc]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x04000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 11 [] [] ss15 (c0) = _
        rewrite [sym_exec, F15]
        dsimp only []
        rewrite [SD_11200]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 10 [] [] ss16 (c15 ++ c0) = _
        rewrite [sym_exec, F16]
        dsimp only []
        rewrite [SD_11204]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06c000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 9 [] [] ss17 (c15 ++ c0) = _
        rewrite [sym_exec, F17]
        dsimp only []
        rewrite [SD_11270]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfddff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 8 [] [] ss18 (c15 ++ c0) = _
        rewrite [sym_exec, F18]
        dsimp only []
        rewrite [SD_1124c]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 7 [] [] ss19 (c15 ++ c0) = _
        rewrite [sym_exec, F19]
        dsimp only []
        rewrite [SD_11250]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 6 [] [] ss20 (c15 ++ c0) = _
        rewrite [sym_exec, F20]
        dsimp only []
        rewrite [SD_11254]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 5 [] [] ss21 (c15 ++ c0) = _
        rewrite [sym_exec, F21]
        dsimp only []
        rewrite [SD_11258]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 4 [] [] ss22 (c15 ++ c0) = _
        rewrite [sym_exec, F22]
        dsimp only []
        rewrite [SD_1125c]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00070693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 3 [] [] ss23 (c15 ++ c0) = _
        rewrite [sym_exec, F23]
        dsimp only []
        rewrite [SD_11260]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00078713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 2 [] [] ss24 (c15 ++ c0) = _
        rewrite [sym_exec, F24]
        dsimp only []
        rewrite [SD_11264]
        simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        change sym_exec segs 1 [] [] ss25 (c15 ++ c0) = _
        rewrite [sym_exec, F25]
        rfl
      let E := Eplus R0 ([Z_to_bv 64 (bv_unsigned rsp - 48), nat_to_word (c :: cur').length] ++ [])
      refine Exists.elim (sym_exec_ex source_segs 26 [false] [] ss0 [] ss25 scs E
        mem rrom (mkst R0 (Z_to_bv 64 69812) mem rrom) (Hexec source_segs tail1_SF_110b4 tail1_SF_110b8 tail1_SF_110bc tail1_SF_110c0 tail1_SF_110c4 tail1_SF_110c8 tail1_SF_110cc tail1_SF_111e0 tail1_SF_111e4 tail1_SF_111e8 tail1_SF_111ec tail1_SF_111f0 tail1_SF_111f4 tail1_SF_111f8 tail1_SF_111fc tail1_SF_11200 tail1_SF_11204 tail1_SF_11270 tail1_SF_1124c tail1_SF_11250 tail1_SF_11254 tail1_SF_11258 tail1_SF_1125c tail1_SF_11260 tail1_SF_11264 tail1_SF_11268) ?sc4 ?st4) ?cont4
      case' cont4 =>
        intro R1 HH
        obtain ⟨HR1, Hblock⟩ := HH
        dsimp only [ss25, ss24, ss23, ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HR1 Hblock
        sym_pc_Z
        chain_mst
        focus exact Hblock
        try sym_mem_norm
        norm_pc
        sym_pc_lit
      case' st4 =>
        refine ⟨R0, rfl, regs_ok_pins E [(2, EVar 32), (8, EVar 33)] sr_id R0
          (regs_ok_Eplus R0 ([Z_to_bv 64 (bv_unsigned rsp - 48), nat_to_word (c :: cur').length] ++ [])) ?_, True.intro⟩
        simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
        repeat' apply And.intro
        all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
      case' sc4 =>
        dsimp only [scs, c0, c15, List.cons_append, List.nil_append]
        simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
        refine ⟨?_, ?_, ?_⟩
        all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
        all_goals sym_norm
        all_goals try sym_sc_auto
        all_goals try rfl
      · first | (apply source_store_ok <;> unorm <;> omega) | solve_store_ok_inv
      · scbr
      · exact Q2
      · sym_regs HR0; exact H8
      · apply to_out.tout_step _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11268 rfl)
        apply tout_wr_rec
        · sym_regs HR1; decide +kernel
        · sym_regs HR1 <;> sym_close
        · have Q11 : reg_get R1 11 = cur_base := by sym_regs HR1; bveq
          have Q12 : reg_get R1 12 = nat_to_word (c :: cur').length := by sym_regs HR1; exact u0_id _
          rw [Q11, Q12, ms_read_bytes_rdn source_segs _ _ _ rfl]
          dsimp only [machine_state.ms_mem]
          rw [word_to_nat_ntw _ (by lenlia)]
          rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
            (by rw [length_N_to_le_bytes]; unorm; omega)]
          exact Hcur
        · simp only [List.length_cons]; omega
        · intro n Hn1 Hn2
          norm_pc
          apply src_put_wall_cur av ev rsp rrnd Hsp_lo Hsp_hi uid hw
            (c :: cur').length (c :: cur') cur_base n
          · omega
          · exact Hn1
          · exact Hn2
          · lenlia
          · rw [u_cur_base]; omega
          · rw [u_cur_base]; lenlia
          · sym_regs HR1 <;> sym_close
          · sym_regs HR1 <;> sym_close
          · sym_regs HR1 <;> sym_close
          · sym_regs HR1 <;> sym_close
          · regupd_resolve; exact len_word_firstn_nat _ _ Hn2
          · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
            u_norm; omega
          · apply rdn_wbytes_hit8
            u_norm; omega
          · rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
              (by rw [length_N_to_le_bytes]; unorm; omega)]
            exact Hcur

include Hsp_lo Hsp_hi in
/-- Per-block continuation: from the post-read state (a0 = |bs|,
pc 0x1126c) fold the block and reach the loop head or exit 3. -/
theorem post_read_dispatch (R : bvmap 5 word) (mem : word → Option byte) (cur done bs : List byte)
    (H1 : reg_get R 1 = (0x111d4 : word))
    (H2 : reg_get R 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H3 : reg_get R 3 = (0x13800 : word))
    (H8 : reg_get R 8 = nat_to_word cur.length) (H9 : reg_get R 9 = nat_to_word done.length)
    (H18 : reg_get R 18 = cur_base) (H19 : reg_get R 19 = done_base)
    (H10 : reg_get R 10 = nat_to_word bs.length) (Hbg : bg_ok av ev rsp rrnd uid hw mem)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 (0x11040 : word)))
    (Hrb : rdn source_segs mem rb_base bs.length = some bs)
    (Hcur : rdn source_segs mem cur_base cur.length = some cur)
    (Hdone : rdn source_segs mem done_base done.length = some done)
    (Hcurcap : (cur.length : Int) ≤ 4096) (Hdonecap : (done.length : Int) ≤ 4097)
    (Hblo : 1 ≤ (bs.length : Int)) (Hbhi : (bs.length : Int) ≤ 1024) :
    match procs f (cur, done) bs with
    | some a' => lh_next source_segs (src_LH av ev rsp rrnd uid hw) a' (mkst R 0x1126c mem rrom)
    | none => to_exit source_segs ec (mkst R 0x1126c mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let ss0 := SS 70252 (sr_pins [(1, ELit 70100), (2, EVar 32), (3, ELit 79872), (10, EVar 33)] sr_id) [] 34
  let ss1 := SS 70100 ss0.s_regs [] 34
  let ss2 := SS 70104 (sr_upd ss1.s_regs 1 (ELit 69696)) [] 35
  let ss3 := SS 70108 (sr_upd ss2.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit 16))) [] 35
  let ss4 := SS 70164 ss3.s_regs [] 35
  let ss5 := SS 70168 (sr_upd ss4.s_regs 15 (ELit (-4096))) [] 35
  let ss6 := SS 70172 ss5.s_regs [] 35
  let ss7 := SS 69696 ss6.s_regs [] 35
  let ss8 := SS 69700 ss7.s_regs [] 35
  let ss9 := SS 69704 ss8.s_regs [] 35
  let ss10 := SS 69708 (sr_upd ss9.s_regs 14 (ELit 0)) [] 35
  let ss11 := SS 69712 (sr_upd ss10.s_regs 13 (ELit 10)) [] 35
  let ss12 := SS 69716 (sr_upd ss11.s_regs 12 (ELit 4096)) [] 35
  let ss13 := SS 69720 (sr_upd ss12.s_regs 11 (ELit 77832)) [] 35
  let c1 := [SCFlat (SA (SBVar 32) 8) 8, SCReadBase (SA (SBVar 32) 8) 8 (ELit 69696)]
  let c5 := [SCBr false .BC_LTU (ELit (-4096)) (EVar 33)]
  let c7 := [SCBr false .BC_LT (EVar 33) (ELit 0)]
  let c8 := [SCBr false .BC_EQ (EVar 33) (ELit 0)]
  let scs := c8 ++ c7 ++ c5 ++ c1
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 70252) = some 0x00008067)
      (F1 : fetch_word segs (Z_to_bv 64 70100) = some 0x00813083)
      (F2 : fetch_word segs (Z_to_bv 64 70104) = some 0x01010113)
      (F3 : fetch_word segs (Z_to_bv 64 70108) = some 0x0380006f)
      (F4 : fetch_word segs (Z_to_bv 64 70164) = some 0xfffff7b7)
      (F5 : fetch_word segs (Z_to_bv 64 70168) = some 0x00a7e463)
      (F6 : fetch_word segs (Z_to_bv 64 70172) = some 0x00008067)
      (F7 : fetch_word segs (Z_to_bv 64 69696) = some 0x10054263)
      (F8 : fetch_word segs (Z_to_bv 64 69700) = some 0x06050863)
      (F9 : fetch_word segs (Z_to_bv 64 69704) = some 0x00000713)
      (F10 : fetch_word segs (Z_to_bv 64 69708) = some 0x00a00693)
      (F11 : fetch_word segs (Z_to_bv 64 69712) = some 0x00001637)
      (F12 : fetch_word segs (Z_to_bv 64 69716) = some 0x80818593) : sym_exec segs 13 [false, false, false] [ELit 69696] ss0 [] = (ss13, scs) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_1126c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 12 [false, false, false] [(ELit 69696)] ss1 ([]) = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_111d4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00813083 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 11 [false, false, false] [] ss2 (c1) = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_111d8]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 10 [false, false, false] [] ss3 (c1) = _
    rewrite [sym_exec, F3]
    dsimp only []
    rewrite [SD_111dc]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0380006f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 9 [false, false, false] [] ss4 (c1) = _
    rewrite [sym_exec, F4]
    dsimp only []
    rewrite [SD_11214]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfffff7b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 8 [false, false, false] [] ss5 (c1) = _
    rewrite [sym_exec, F5]
    dsimp only []
    rewrite [SD_11218]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a7e463 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 7 [false, false] [] ss6 (c5 ++ c1) = _
    rewrite [sym_exec, F6]
    dsimp only []
    rewrite [SD_1121c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00008067 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 6 [false, false] [] ss7 (c5 ++ c1) = _
    rewrite [sym_exec, F7]
    dsimp only []
    rewrite [SD_11040]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x10054263 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 5 [false] [] ss8 (c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F8]
    dsimp only []
    rewrite [SD_11044]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x06050863 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 4 [] [] ss9 (c8 ++ c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F9]
    dsimp only []
    rewrite [SD_11048]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 3 [] [] ss10 (c8 ++ c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F10]
    dsimp only []
    rewrite [SD_1104c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00a00693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [] [] ss11 (c8 ++ c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F11]
    dsimp only []
    rewrite [SD_11050]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00001637 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [] [] ss12 (c8 ++ c7 ++ c5 ++ c1) = _
    rewrite [sym_exec, F12]
    dsimp only []
    rewrite [SD_11054]
    rfl
  let E := Eplus R ([Z_to_bv 64 (bv_unsigned rsp - 64), nat_to_word bs.length] ++ [])
  refine Exists.elim (sym_exec_ex source_segs 13 [false, false, false] [ELit 69696] ss0 [] ss13 scs E
    mem rrom (mkst R (Z_to_bv 64 70252) mem rrom) (Hexec source_segs tail1_SF_1126c tail1_SF_111d4 tail1_SF_111d8 tail1_SF_111dc tail1_SF_11214 tail1_SF_11218 tail1_SF_1121c tail1_SF_11040 tail1_SF_11044 tail1_SF_11048 tail1_SF_1104c tail1_SF_11050 tail1_SF_11054) ?sc1 ?st1) ?cont1
  case' cont1 =>
    intro RG HH
    obtain ⟨HRG, Hms⟩ := HH
    dsimp only [ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRG Hms
  case' st1 =>
    refine ⟨R, rfl, regs_ok_pins E [(1, ELit 70100), (2, EVar 32), (3, ELit 79872), (10, EVar 33)] sr_id R
      (regs_ok_Eplus R ([Z_to_bv 64 (bv_unsigned rsp - 64), nat_to_word bs.length] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
    all_goals try rfl
  case' sc1 =>
    dsimp only [scs, c1, c5, c7, c8, List.cons_append, List.nil_append]
    simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
    all_goals sym_norm
    all_goals try sym_sc_auto
    all_goals try rfl
  · scbr
  · scbr
  · sysret_ok
  · exact ⟨word_to_le_bytes 8 (0x11040 : word), Hra, by decide +kernel⟩
  · pin_lit (0x111d4 : word); exact H1
  · exact H2
  · pin_lit (0x13800 : word); exact H3
  · exact H10
  · have HBLH : BLH av ev rsp rrnd uid hw cur done bs 0 (mkst RG 0x11058 mem rrom) := by
      refine ⟨RG, mem, rfl, ?_⟩
      repeat' apply And.intro
      all_goals first | assumption | omega | (sym_regs HRG <;> first
        | assumption | sym_close
        | (congr 1; change bv_unsigned rsp - 64 + 16 = bv_unsigned rsp - 48; omega))
    have Hbl := byte_loop av ev rsp rrnd Hsp_lo Hsp_hi uid hw bs.length cur done bs 0
      (mkst RG 0x11058 mem rrom) (by omega) HBLH
    rw [List.drop_zero] at Hbl
    cases Ep : procs f (cur, done) bs with
    | some a' =>
      rw [Ep] at Hbl
      obtain ⟨msL, HmsL, HL⟩ := Hbl
      exact ⟨msL, msteps_trans _ _ _ _ Hms HmsL, HL⟩
    | none =>
      rw [Ep] at Hbl
      exact tail1_msteps_to_exit _ _ _ Hms Hbl

include Hsp_lo Hsp_hi in
/-- One loop iteration: the DrainSim per-binary obligation. -/
theorem src_LH_to_rd (a : A) (ms : machine_state)
    (HLH : src_LH av ev rsp rrnd uid hw a ms) :
    to_rd source_segs (Z_to_bv 64 1024) f out ec (src_LH av ev rsp rrnd uid hw) a ms := by
  rcases a with ⟨cur, done⟩
  obtain ⟨regs, mem, rfl, H2, H3, H8, H9, H18, H19, Hbg, Hcur, Hdone,
    Hcurcap, Hdonecap⟩ := HLH
  dsimp only [Prod.fst, Prod.snd] at *
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let ss0 := SS 69680 (sr_pins [(2, EVar 32), (3, ELit 79872)] sr_id) [] 33
  let ss1 := SS 69684 (sr_upd ss0.s_regs 11 (ELit 77832)) [] 33
  let ss2 := SS 69688 (sr_upd ss1.s_regs 12 (ELit 1024)) [] 33
  let ss3 := SS 69692 (sr_upd ss2.s_regs 10 (ELit 0)) [] 33
  let ss4 := SS 70060 (sr_upd ss3.s_regs 1 (ELit 69696)) [] 33
  let ss5 := SS 70064 (sr_upd ss4.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-16)))) [] 33
  let ss6 := SS 70068 (sr_upd ss5.s_regs 13 (ELit 1024)) [] 33
  let ss7 := SS 70072 (sr_upd ss6.s_regs 16 (ELit 0)) [] 33
  let ss8 := SS 70076 (sr_upd ss7.s_regs 12 (ELit 77832)) [] 33
  let ss9 := SS 70080 (sr_upd ss8.s_regs 15 (ELit 0)) [] 33
  let ss10 := SS 70084 (sr_upd ss9.s_regs 11 (ELit 0)) [] 33
  let ss11 := SS 70088 (sr_upd ss10.s_regs 14 (ELit 0)) [] 33
  let ss12 := SS 70092 (sr_upd ss11.s_regs 10 (ELit 63)) [] 33
  let ss13 := SS 70096 ss12.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss14 := SS 70256 (sr_upd ss13.s_regs 1 (ELit 70100)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss15 := SS 70220 ss14.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss16 := SS 70224 (sr_upd ss15.s_regs 17 (ELit 63)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss17 := SS 70228 (sr_upd ss16.s_regs 10 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss18 := SS 70232 (sr_upd ss17.s_regs 11 (ELit 77832)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss19 := SS 70236 (sr_upd ss18.s_regs 12 (ELit 1024)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss20 := SS 70240 (sr_upd ss19.s_regs 13 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss21 := SS 70244 (sr_upd ss20.s_regs 14 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let ss22 := SS 70248 (sr_upd ss21.s_regs 15 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 69696)] 33
  let c12 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
  let scs := c12
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 69680) = some 0x80818593)
      (F1 : fetch_word segs (Z_to_bv 64 69684) = some 0x40000613)
      (F2 : fetch_word segs (Z_to_bv 64 69688) = some 0x00000513)
      (F3 : fetch_word segs (Z_to_bv 64 69692) = some 0x170000ef)
      (F4 : fetch_word segs (Z_to_bv 64 70060) = some 0xff010113)
      (F5 : fetch_word segs (Z_to_bv 64 70064) = some 0x00060693)
      (F6 : fetch_word segs (Z_to_bv 64 70068) = some 0x00000813)
      (F7 : fetch_word segs (Z_to_bv 64 70072) = some 0x00058613)
      (F8 : fetch_word segs (Z_to_bv 64 70076) = some 0x00000793)
      (F9 : fetch_word segs (Z_to_bv 64 70080) = some 0x00050593)
      (F10 : fetch_word segs (Z_to_bv 64 70084) = some 0x00000713)
      (F11 : fetch_word segs (Z_to_bv 64 70088) = some 0x03f00513)
      (F12 : fetch_word segs (Z_to_bv 64 70092) = some 0x00113423)
      (F13 : fetch_word segs (Z_to_bv 64 70096) = some 0x0a0000ef)
      (F14 : fetch_word segs (Z_to_bv 64 70256) = some 0xfddff06f)
      (F15 : fetch_word segs (Z_to_bv 64 70220) = some 0x00050893)
      (F16 : fetch_word segs (Z_to_bv 64 70224) = some 0x00058513)
      (F17 : fetch_word segs (Z_to_bv 64 70228) = some 0x00060593)
      (F18 : fetch_word segs (Z_to_bv 64 70232) = some 0x00068613)
      (F19 : fetch_word segs (Z_to_bv 64 70236) = some 0x00070693)
      (F20 : fetch_word segs (Z_to_bv 64 70240) = some 0x00078713)
      (F21 : fetch_word segs (Z_to_bv 64 70244) = some 0x00080793)
      (F22 : fetch_word segs (Z_to_bv 64 70248) = some 0x00000073) : sym_exec segs 23 [] [] ss0 [] = (ss22, scs) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_11030]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x80818593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 22 [] [] ss1 ([]) = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_11034]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x40000613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 21 [] [] ss2 ([]) = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_11038]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 20 [] [] ss3 ([]) = _
    rewrite [sym_exec, F3]
    dsimp only []
    rewrite [SD_1103c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x170000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 19 [] [] ss4 ([]) = _
    rewrite [sym_exec, F4]
    dsimp only []
    rewrite [SD_111ac]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xff010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 18 [] [] ss5 ([]) = _
    rewrite [sym_exec, F5]
    dsimp only []
    rewrite [SD_111b0]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 17 [] [] ss6 ([]) = _
    rewrite [sym_exec, F6]
    dsimp only []
    rewrite [SD_111b4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000813 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 16 [] [] ss7 ([]) = _
    rewrite [sym_exec, F7]
    dsimp only []
    rewrite [SD_111b8]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 15 [] [] ss8 ([]) = _
    rewrite [sym_exec, F8]
    dsimp only []
    rewrite [SD_111bc]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 14 [] [] ss9 ([]) = _
    rewrite [sym_exec, F9]
    dsimp only []
    rewrite [SD_111c0]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 13 [] [] ss10 ([]) = _
    rewrite [sym_exec, F10]
    dsimp only []
    rewrite [SD_111c4]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 12 [] [] ss11 ([]) = _
    rewrite [sym_exec, F11]
    dsimp only []
    rewrite [SD_111c8]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x03f00513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 11 [] [] ss12 ([]) = _
    rewrite [sym_exec, F12]
    dsimp only []
    rewrite [SD_111cc]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 10 [] [] ss13 (c12) = _
    rewrite [sym_exec, F13]
    dsimp only []
    rewrite [SD_111d0]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x0a0000ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 9 [] [] ss14 (c12) = _
    rewrite [sym_exec, F14]
    dsimp only []
    rewrite [SD_11270]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfddff06f : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 8 [] [] ss15 (c12) = _
    rewrite [sym_exec, F15]
    dsimp only []
    rewrite [SD_1124c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00050893 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 7 [] [] ss16 (c12) = _
    rewrite [sym_exec, F16]
    dsimp only []
    rewrite [SD_11250]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00058513 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 6 [] [] ss17 (c12) = _
    rewrite [sym_exec, F17]
    dsimp only []
    rewrite [SD_11254]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00060593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 5 [] [] ss18 (c12) = _
    rewrite [sym_exec, F18]
    dsimp only []
    rewrite [SD_11258]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00068613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 4 [] [] ss19 (c12) = _
    rewrite [sym_exec, F19]
    dsimp only []
    rewrite [SD_1125c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00070693 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 3 [] [] ss20 (c12) = _
    rewrite [sym_exec, F20]
    dsimp only []
    rewrite [SD_11260]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00078713 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [] [] ss21 (c12) = _
    rewrite [sym_exec, F21]
    dsimp only []
    rewrite [SD_11264]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00080793 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [] [] ss22 (c12) = _
    rewrite [sym_exec, F22]
    rfl
  let E := Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 48)] ++ [])
  refine Exists.elim (sym_exec_ex source_segs 23 [] [] ss0 [] ss22 scs E
    mem rrom (mkst regs (Z_to_bv 64 69680) mem rrom) (Hexec source_segs tail1_SF_11030 tail1_SF_11034 tail1_SF_11038 tail1_SF_1103c tail1_SF_111ac tail1_SF_111b0 tail1_SF_111b4 tail1_SF_111b8 tail1_SF_111bc tail1_SF_111c0 tail1_SF_111c4 tail1_SF_111c8 tail1_SF_111cc tail1_SF_111d0 tail1_SF_11270 tail1_SF_1124c tail1_SF_11250 tail1_SF_11254 tail1_SF_11258 tail1_SF_1125c tail1_SF_11260 tail1_SF_11264 tail1_SF_11268) ?sc1 ?st1) ?cont1
  case' cont1 =>
    intro RG HH
    obtain ⟨HRG, Hblock⟩ := HH
    dsimp only [ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRG Hblock
    sym_pc_Z
    chain_mst
    focus exact Hblock
    try sym_mem_norm
    norm_pc
    sym_pc_lit
  case' st1 =>
    refine ⟨regs, rfl, regs_ok_pins E [(2, EVar 32), (3, ELit 79872)] sr_id regs
      (regs_ok_Eplus regs ([Z_to_bv 64 (bv_unsigned rsp - 48)] ++ [])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
    all_goals try rfl
  case' sc1 =>
    dsimp only [scs, c12, List.cons_append, List.nil_append]
    simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    refine ⟨?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
    all_goals sym_norm
    all_goals try sym_sc_auto
    all_goals try rfl
  · first | (apply source_store_ok <;> unorm <;> omega) | solve_store_ok_inv
  · exact H2
  · pin_lit (0x13800 : word); exact H3
  · apply to_rd.trd_step _ _ _ rfl (step_ecall _ _ _ _ _ _ tail1_SF_11268 rfl)
    apply trd_here_rec (buf := rb_base)
    · sym_regs HRG; decide +kernel
    · sym_regs HRG <;> sym_close
    · sym_regs HRG <;> sym_close
    · sym_regs HRG <;> sym_close
    · exact source_rb_wseg
    · apply access_okb_intro
      rw [u_rb_base]
      change (77832 : Int) + 1024 ≤ TASK_SIZE
      unfold TASK_SIZE
      omega
    · norm_pc
      apply eof_to_out av ev rsp rrnd Hsp_lo Hsp_hi uid hw
      · sym_regs HRG <;> sym_close
      · sym_regs HRG <;> sym_close
      · sym_regs HRG <;> sym_close
      · sym_regs HRG; exact H8
      · sym_regs HRG; exact H9
      · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
        u_norm; omega
      · apply rdn_wbytes_hit8
        u_norm; omega
      · rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
          (by rw [length_N_to_le_bytes]; unorm; omega)]
        exact Hcur
      · rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
          (by rw [length_N_to_le_bytes]; unorm; omega)]
        exact Hdone
      · exact Hcurcap
      · exact Hdonecap
    · exact out_modeled _ _ Hcurcap Hdonecap
    · intro bs Hblo Hbhi
      wlits
      have Hdispatch := post_read_dispatch av ev rsp rrnd Hsp_lo Hsp_hi uid hw
        (regupd RG 10 (len_word bs))
        (write_to_mem (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
          (word_to_le_bytes 8 (0x11040 : word))) rb_base bs) cur done bs
        (by sym_regs HRG <;> sym_close)
        (by sym_regs HRG <;> sym_close)
        (by sym_regs HRG <;> sym_close)
        (by sym_regs HRG; exact H8)
        (by sym_regs HRG; exact H9)
        (by sym_regs HRG; exact H18)
        (by sym_regs HRG; exact H19)
        (by regupd_resolve; exact len_word_nat bs)
        (by
          apply bg_ok_wtm_below av ev rsp rrnd uid hw
          · apply bg_ok_scr8 av ev rsp rrnd uid hw _ _ _ Hbg
            u_norm; omega
          · unorm; omega)
        (by
          rw [rdn_wtm_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega) (by unorm; omega)]
          apply rdn_wbytes_hit8
          u_norm; omega)
        (by apply rdn_write_to_mem; unorm; omega)
        (by
          rw [rdn_wtm_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega) (by unorm; omega)]
          rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
            (by rw [length_N_to_le_bytes]; unorm; omega)]
          exact Hcur)
        (by
          rw [rdn_wtm_out _ _ _ _ _ _ (by unorm; omega) (by unorm; omega) (by unorm; omega)]
          rw [rdn_wbytes_below _ _ _ _ _ _ (by unorm; omega)
            (by rw [length_N_to_le_bytes]; unorm; omega)]
          exact Hdone)
        Hcurcap Hdonecap Hblo Hbhi
      cases Ep : procs f (cur, done) bs <;>
        simp only [Ep] at Hdispatch ⊢ <;> exact Hdispatch

include Hva Hve Hsp_lo Hsp_hi in
/-- From the initial state to the loop head. -/
theorem src_init_to_rd :
    to_rd source_segs (Z_to_bv 64 1024) f out ec (src_LH av ev rsp rrnd uid hw) a0
      (init_machine_state source_segs 0x11154 source_phdrs rsp rrnd av ev uid hw) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hargc := valid_argv_len av Hva
  have Hargc_rd : rdn source_segs (tail1_wmem av ev rsp rrnd uid hw) rsp 8 = some (word_le8 (tail1_argcN av)) := by
    unfold tail1_wmem
    rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    apply read_argc
    exact source_bsb_nw av ev Hva Hve rsp rrnd Hsp_hi uid hw
  rw [init_mkst]
  norm_pc
  let ss0 := SS 69972 (sr_pins [(2, EVar 32), (8, ELit 0), (9, ELit 0), (18, ELit 0), (19, ELit 0)] sr_id) [] 33
  let ss1 := SS 69976 (sr_upd ss0.s_regs 3 (ELit 78164)) [] 33
  let ss2 := SS 69980 (sr_upd ss1.s_regs 3 (ELit 79872)) [] 33
  let ss3 := SS 69984 (sr_upd ss2.s_regs 10 (EVar 33)) [] 34
  let ss4 := SS 69988 (sr_upd ss3.s_regs 11 (EAlu .ALU_ADD (EVar 32) (ELit 8))) [] 34
  let ss5 := SS 69992 (sr_upd ss4.s_regs 5 (EAlu .ALU_SLL (EVar 33) (ELit 3))) [] 34
  let ss6 := SS 69996 (sr_upd ss5.s_regs 12 (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3)))) [] 34
  let ss7 := SS 70000 (sr_upd ss6.s_regs 12 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))) [] 34
  let ss8 := SS 70004 (sr_upd ss7.s_regs 6 (ELit 78192)) [] 34
  let ss9 := SS 70008 (sr_upd ss8.s_regs 6 (ELit 77824)) [] 34
  let ss10 := SS 70012 ss9.s_regs [SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss11 := SS 69632 (sr_upd ss10.s_regs 1 (ELit 70016)) [SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss12 := SS 69636 (sr_upd ss11.s_regs 2 (EAlu .ALU_ADD (EVar 32) (ELit (-48)))) [SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss13 := SS 69640 ss12.s_regs [SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss14 := SS 69644 ss13.s_regs [SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss15 := SS 69648 (sr_upd ss14.s_regs 18 (ELit 81920)) [SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss16 := SS 69652 (sr_upd ss15.s_regs 19 (ELit 77824)) [SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss17 := SS 69656 ss16.s_regs [SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss18 := SS 69660 ss17.s_regs [SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss19 := SS 69664 ss18.s_regs [SE (SA (SBVar 32) (-8)) 8 (ELit 70016), SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss20 := SS 69668 (sr_upd ss19.s_regs 9 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 70016), SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss21 := SS 69672 (sr_upd ss20.s_regs 8 (ELit 0)) [SE (SA (SBVar 32) (-8)) 8 (ELit 70016), SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss22 := SS 69676 (sr_upd ss21.s_regs 18 (ELit 82960)) [SE (SA (SBVar 32) (-8)) 8 (ELit 70016), SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let ss23 := SS 69680 (sr_upd ss22.s_regs 19 (ELit 78856)) [SE (SA (SBVar 32) (-8)) 8 (ELit 70016), SE (SA (SBVar 32) (-24)) 8 (ELit 0), SE (SA (SBVar 32) (-16)) 8 (ELit 0), SE (SA (SBVar 32) (-40)) 8 (ELit 0), SE (SA (SBVar 32) (-32)) 8 (ELit 0), SE (SA SBLit 77824) 8 (EAlu .ALU_ADD (EAlu .ALU_ADD (EAlu .ALU_ADD (EVar 32) (ELit 8)) (EAlu .ALU_SLL (EVar 33) (ELit 3))) (ELit 8))] 34
  let c2 := [SCFlat (SA (SBVar 32) 0) 8, SCReadBase (SA (SBVar 32) 0) 8 (EVar 33)]
  let c9 := [SCFlat (SA SBLit 77824) 8, SCStoreOk (SA SBLit 77824) 8]
  let c12 := [SCFlat (SA (SBVar 32) (-32)) 8, SCStoreOk (SA (SBVar 32) (-32)) 8]
  let c13 := [SCFlat (SA (SBVar 32) (-40)) 8, SCStoreOk (SA (SBVar 32) (-40)) 8]
  let c16 := [SCFlat (SA (SBVar 32) (-16)) 8, SCStoreOk (SA (SBVar 32) (-16)) 8]
  let c17 := [SCFlat (SA (SBVar 32) (-24)) 8, SCStoreOk (SA (SBVar 32) (-24)) 8]
  let c18 := [SCFlat (SA (SBVar 32) (-8)) 8, SCStoreOk (SA (SBVar 32) (-8)) 8]
  let scs := c18 ++ c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2
  have Hexec (segs : List Segment)
      (F0 : fetch_word segs (Z_to_bv 64 69972) = some 0x00002197)
      (F1 : fetch_word segs (Z_to_bv 64 69976) = some 0x6ac18193)
      (F2 : fetch_word segs (Z_to_bv 64 69980) = some 0x00013503)
      (F3 : fetch_word segs (Z_to_bv 64 69984) = some 0x00810593)
      (F4 : fetch_word segs (Z_to_bv 64 69988) = some 0x00351293)
      (F5 : fetch_word segs (Z_to_bv 64 69992) = some 0x00558633)
      (F6 : fetch_word segs (Z_to_bv 64 69996) = some 0x00860613)
      (F7 : fetch_word segs (Z_to_bv 64 70000) = some 0x00002317)
      (F8 : fetch_word segs (Z_to_bv 64 70004) = some 0xe9030313)
      (F9 : fetch_word segs (Z_to_bv 64 70008) = some 0x00c33023)
      (F10 : fetch_word segs (Z_to_bv 64 70012) = some 0xe85ff0ef)
      (F11 : fetch_word segs (Z_to_bv 64 69632) = some 0xfd010113)
      (F12 : fetch_word segs (Z_to_bv 64 69636) = some 0x01213823)
      (F13 : fetch_word segs (Z_to_bv 64 69640) = some 0x01313423)
      (F14 : fetch_word segs (Z_to_bv 64 69644) = some 0x00014937)
      (F15 : fetch_word segs (Z_to_bv 64 69648) = some 0x000139b7)
      (F16 : fetch_word segs (Z_to_bv 64 69652) = some 0x02813023)
      (F17 : fetch_word segs (Z_to_bv 64 69656) = some 0x00913c23)
      (F18 : fetch_word segs (Z_to_bv 64 69660) = some 0x02113423)
      (F19 : fetch_word segs (Z_to_bv 64 69664) = some 0x00000493)
      (F20 : fetch_word segs (Z_to_bv 64 69668) = some 0x00000413)
      (F21 : fetch_word segs (Z_to_bv 64 69672) = some 0x41090913)
      (F22 : fetch_word segs (Z_to_bv 64 69676) = some 0x40898993) : sym_exec segs 23 [] [EVar 33] ss0 [] = (ss23, scs) := by
    rewrite [sym_exec, F0]
    dsimp only []
    rewrite [SD_11154]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00002197 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 22 [] [(EVar 33)] ss1 ([]) = _
    rewrite [sym_exec, F1]
    dsimp only []
    rewrite [SD_11158]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x6ac18193 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 21 [] [(EVar 33)] ss2 ([]) = _
    rewrite [sym_exec, F2]
    dsimp only []
    rewrite [SD_1115c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00013503 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 20 [] [] ss3 (c2) = _
    rewrite [sym_exec, F3]
    dsimp only []
    rewrite [SD_11160]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00810593 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 19 [] [] ss4 (c2) = _
    rewrite [sym_exec, F4]
    dsimp only []
    rewrite [SD_11164]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00351293 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 18 [] [] ss5 (c2) = _
    rewrite [sym_exec, F5]
    dsimp only []
    rewrite [SD_11168]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00558633 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 17 [] [] ss6 (c2) = _
    rewrite [sym_exec, F6]
    dsimp only []
    rewrite [SD_1116c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00860613 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 16 [] [] ss7 (c2) = _
    rewrite [sym_exec, F7]
    dsimp only []
    rewrite [SD_11170]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00002317 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 15 [] [] ss8 (c2) = _
    rewrite [sym_exec, F8]
    dsimp only []
    rewrite [SD_11174]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xe9030313 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 14 [] [] ss9 (c2) = _
    rewrite [sym_exec, F9]
    dsimp only []
    rewrite [SD_11178]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00c33023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 13 [] [] ss10 (c9 ++ c2) = _
    rewrite [sym_exec, F10]
    dsimp only []
    rewrite [SD_1117c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xe85ff0ef : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 12 [] [] ss11 (c9 ++ c2) = _
    rewrite [sym_exec, F11]
    dsimp only []
    rewrite [SD_11000]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0xfd010113 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 11 [] [] ss12 (c9 ++ c2) = _
    rewrite [sym_exec, F12]
    dsimp only []
    rewrite [SD_11004]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01213823 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 10 [] [] ss13 (c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F13]
    dsimp only []
    rewrite [SD_11008]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x01313423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 9 [] [] ss14 (c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F14]
    dsimp only []
    rewrite [SD_1100c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00014937 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 8 [] [] ss15 (c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F15]
    dsimp only []
    rewrite [SD_11010]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x000139b7 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 7 [] [] ss16 (c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F16]
    dsimp only []
    rewrite [SD_11014]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x02813023 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 6 [] [] ss17 (c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F17]
    dsimp only []
    rewrite [SD_11018]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00913c23 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 5 [] [] ss18 (c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F18]
    dsimp only []
    rewrite [SD_1101c]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x02113423 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 4 [] [] ss19 (c18 ++ c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F19]
    dsimp only []
    rewrite [SD_11020]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000493 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 3 [] [] ss20 (c18 ++ c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F20]
    dsimp only []
    rewrite [SD_11024]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x00000413 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 2 [] [] ss21 (c18 ++ c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F21]
    dsimp only []
    rewrite [SD_11028]
    simp (config := { implicitDefEqProofs := false }) only [show is_ecall (0x41090913 : BitVec 32) = false from by decide, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change sym_exec segs 1 [] [] ss22 (c18 ++ c17 ++ c16 ++ c13 ++ c12 ++ c9 ++ c2) = _
    rewrite [sym_exec, F22]
    dsimp only []
    rewrite [SD_1102c]
    rfl
  let E := Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp) ([rsp] ++ [tail1_argcN av])
  refine Exists.elim (sym_exec_ex source_segs 23 [] [EVar 33] ss0 [] ss23 scs E
    (wrap_mem source_phdrs rsp av ev uid hw rrnd) rrom (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp) (Z_to_bv 64 69972) (wrap_mem source_phdrs rsp av ev uid hw rrnd) rrom) (Hexec source_segs tail1_SF_11154 tail1_SF_11158 tail1_SF_1115c tail1_SF_11160 tail1_SF_11164 tail1_SF_11168 tail1_SF_1116c tail1_SF_11170 tail1_SF_11174 tail1_SF_11178 tail1_SF_1117c tail1_SF_11000 tail1_SF_11004 tail1_SF_11008 tail1_SF_1100c tail1_SF_11010 tail1_SF_11014 tail1_SF_11018 tail1_SF_1101c tail1_SF_11020 tail1_SF_11024 tail1_SF_11028 tail1_SF_1102c) ?sc1 ?st1) ?cont1
  case' cont1 =>
    intro RG HH
    obtain ⟨HRG, Hblock⟩ := HH
    dsimp only [ss23, ss22, ss21, ss20, ss19, ss18, ss17, ss16, ss15, ss14, ss13, ss12, ss11, ss10, ss9, ss8, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, E, sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at HRG Hblock
    sym_pc_Z
    chain_mst
    focus exact Hblock
    try sym_mem_norm
    norm_pc
    sym_pc_lit
  case' st1 =>
    refine ⟨(regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp), rfl, regs_ok_pins E [(2, EVar 32), (8, ELit 0), (9, ELit 0), (18, ELit 0), (19, ELit 0)] sr_id (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (regs_ok_Eplus (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp) ([rsp] ++ [tail1_argcN av])) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (dsimp only [E]; sym_env_norm; try sym_pin_auto)
    all_goals (getr_resolve <;> rfl)
  case' sc1 =>
    dsimp only [scs, c2, c9, c12, c13, c16, c17, c18, List.cons_append, List.nil_append]
    simp only [scs_denot, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off, E]
    all_goals sym_norm
    all_goals try sym_sc_auto
    all_goals try rfl
  · solve_store_ok_inv
  · solve_store_ok_inv
  · solve_store_ok_inv
  · solve_store_ok_inv
  · solve_store_ok_inv
  · apply source_store_ok <;> unorm <;> omega
  · rw [u0_id]
    exact ⟨word_le8 (tail1_argcN av), Hargc_rd, bytes_le_n_to_le_8 _⟩
  · have Hep := tail1_envp_ptr_eq av Hva rsp Hsp_lo Hsp_hi
    rw [alu_add] at Hep
    rw [Hep]
    apply src_LH_to_rd av ev rsp rrnd Hsp_lo Hsp_hi uid hw
    refine ⟨RG, src_bg av ev rsp rrnd uid hw, rfl, ?_⟩
    dsimp only [a0, Prod.fst, Prod.snd, List.length_nil]
    repeat' apply And.intro
    all_goals first
      | (sym_regs HRG <;> first | rfl | sym_close)
      | exact bg_ok_bg av ev rsp rrnd uid hw
      | rfl
      | omega

end SourceProof

end LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_source
