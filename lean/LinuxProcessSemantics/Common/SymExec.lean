import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StoreOk

/-!
# Common.SymExec — a reflective certified symbolic executor

Ports `theories/Common/SymExec.v` at
`2cde689f94c086b868999970834b76a25616b94a`: the constants the cat1024_ns
example's `strong_universal` reaches, and `sym_exec_msteps` and `sym_exec_ex`,
which `Common.SymTac`'s `sym_block_ex` applies.

In Rocq this file is an alternative to the per-instruction tactic route of
`PropExec`/`StepTac`: a straight line of instructions is discharged by one
application of a soundness theorem whose hypothesis is a computed equation
over deep syntax.

- `expr` is a deep-embedded symbolic value language whose constructors mirror
  the ISA's own value primitives (`Sem.alu64`, `Sem.alu32`, `Sem.mul_div`), so
  the generic step lemmas (`PropExec.step_opimm_gen` and the rest) are already
  stated in exactly those terms.  Literals are plain `Int`, never a bitvector.
- `sym_state` is a literal pc, a list of `expr` for the 32 registers, and a
  symbolic memory: a store log over an opaque base memory, which `st_ok`
  denotes as a fold of `CatExec.wbytes`.
- `sym_exec` fetches, decodes and steps from the symbolic pc, accumulating
  side conditions, and stops at anything it does not model;
  `sym_exec_sound` turns a successful run into `CatSim.msteps`.

The memory model.  An address is kept as `saddr` = symbolic base + literal
offset, where a base is the literal 0 (`SBLit`: globals, `.data`, image
constants) or an ambient symbolic value (`SBVar n`: the ASLR `sp`, a heap or
argv-derived pointer).  A load walks the log (`sm_lookup`): with the SAME base
the offsets decide hit / free skip / stuck by integer arithmetic; with
DIFFERENT bases it emits an `SCDisjoint` obligation and carries on.  A load
that falls through the whole log emits `SCReadBase`, the hook for the
per-image `rdn` facts a proof already has, and its result is a fresh `EVar`.
A store emits `SCStoreOk` against the ORIGINAL memory; `mem_denot_grows` and
`StoreOk.store_ok_mono` lift it through the chain.

`sym_step` has no arm for `Branch` or `ecall`, which `sym_exec` handles
before it would call `sym_step` (below).  It returns `none`, stopping
`sym_exec` there, on every other instruction kind it has no arm for (the
fences, `ebreak`, the atomics, the CSR accesses and the F/D instructions),
and on these shapes of the kinds it has: loads `lb`/`lh`, and the unsigned
8-byte load RV64 lacks (`Load .SZ8 false`); stores `sh`; a `jalr` whose base
register does not hold a literal; an address `to_saddr` cannot read as a
base plus a literal offset (a data-dependent offset among them); and a load
with a deciding log entry other than an 8-byte entry at exactly the load's
address, read back by an `ld`.  The deciding entry is the newest one with
the load's base whose bytes overlap the load (`sm_lookup`, below), and no
entry older than it is looked at: a narrower read of an 8-byte slot stops,
and a read spanning several entries stops unless the newest of them is such
a slot.  An entry with another base never stops a load; `sm_lookup` records
an `SCDisjoint` obligation for it instead.  A load with no deciding entry
falls through to the base memory.  `sym_exec` itself stops, before calling
`sym_step`, at a pc it cannot fetch, an `ecall`, an undecodable word, a
compressed encoding and a `Branch` once `dirs` is used up, and when its fuel
runs out.  The Lean decoder does not yet decode a compressed or an F/D
encoding (`decode_any`, `Riscv/DecodeC.lean`; `decode`,
`Riscv/Decode.lean`), so here both stop `sym_exec` as undecodable words, and
no F/D instruction reaches `sym_step`; nor does `Load .SZ8 false`, which the
decoder never produces.

Left unported (cat1024_ns does not reach them): `E0`, `regs_ok_id`,
`sc_flat_of_region`, `sc_disjoint_of_regions`, `sc_disjoint_same_region`,
the `sym_val_norm` Ltac, and the
eliminators Rocq generates for `expr`, `sbase` and `sidecond` (the `_rect`,
`_ind`, `_rec` and `_sind` of each).  Rocq also imports `Footprint`,
`State`, `Run` and `Decode`, which the ported part does not use.

Representation spellings:
- Rocq `nth i l d` is `l.getD i d`; `Nat.eqb`/`Nat.ltb` are
  `Nat.beq`/`Nat.blt`; `Z.eqb a b`/`Z.leb a b` are `decide (a = b)` /
  `decide (a ≤ b)`; stdpp's `bv_wrap` is `PropExec.bv_wrap`.
- Rocq `Forall P l` is `∀ x ∈ l, P x` (`scs_denot`).
- `Z.land`, `Z.shiftl`, `bv_swrap` and `Z.pow` at a free `Z` exponent are
  the proof-side twins `PropExec.Z_land`, `PropExec.Z_shiftl`,
  `PropExec.bv_swrap` and `PropExec.Z_pow`; a literal exponent (`2 ^ 64`)
  stays Lean's `^`, and `2 ^ (8 * Z.of_nat n)` is `2 ^ (8 * n)` at a `Nat`
  exponent.
- `msize_bytes` here is Rocq `SymExec.msize_bytes` (a `Nat`); the
  `Instr.msize_bytes` of the same name is hidden from the `open`.
- The records `saddr`, `sentry`, `sym_state` keep Rocq's constructor names
  (`SA`, `SE`, `SS`) and field names; constructors of the inductives are
  exported so Rocq's spellings transcribe unqualified.
- Section `WithSegs`'s `segs` is an explicit leading argument.
-/

namespace LinuxProcessSemantics.Common.SymExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr hiding msize_bytes
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StoreOk

/-! ## 1. The symbolic value language -/

/-- A symbolic 64-bit value.  `ELit z` denotes `Z_to_bv 64 z` (so the
literal is an ordinary `Int` and folding is `Int` arithmetic — no bitvector
ever enters a computed term).  `EVar n` denotes `E n` for the ambient
valuation; this is how the quantified initial `sp`, `argc` and any
input-dependent value get in.

The remaining four constructors are the ISA's own value primitives, so that
`edenot` of a symbolic register is SYNTACTICALLY the value the generic
`step_*_gen` lemmas write back. -/
inductive expr : Type
  | ELit (z : Int)
  | EVar (n : Nat)
  /-- `alu64 op a b` -/
  | EAlu (op : aluop) (a b : expr)
  /-- `sext 64 (alu32 op (low32 a) (low32 b))` -/
  | EAluw (op : aluop) (a b : expr)
  /-- `mul_div op a b` -/
  | EMd (op : mulop) (a b : expr)
  /-- `sext 64 (mul_div op (low32 a) (low32 b))` -/
  | EMdw (op : mulop) (a b : expr)

export expr (ELit EVar EAlu EAluw EMd EMdw)

abbrev env := Nat → word

def edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))

/-! ### Int-level plumbing for literals -/

theorem Z_to_bv64_wrap_l (a b : Int) : Z_to_bv 64 (bv_wrap 64 a + b) = Z_to_bv 64 (a + b) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod]
  exact Int.emod_add_emod a _ b

theorem Z_to_bv64_wrap_r (a b : Int) : Z_to_bv 64 (a + bv_wrap 64 b) = Z_to_bv 64 (a + b) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod]
  exact Int.add_emod_emod a b _

theorem Z_to_bv64_wrap_sub (a b : Int) :
    Z_to_bv 64 (bv_wrap 64 a - bv_wrap 64 b) = Z_to_bv 64 (a - b) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod,
    bv_wrap64_mod]
  omega

/-- The pc of a symbolic state is an `Int`; every straight-line instruction
advances it by 4 through `v_addi`, which this lemma keeps a literal;
`btgt_lit` and `jalr_tgt_lit` do the same for branch and `jalr` targets. -/
theorem v_addi_lit (p i : Int) : v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i) := by
  unfold v_addi
  rw [Z_to_bv_unsigned]
  exact Z_to_bv64_wrap_l p i

theorem btgt_lit (p i : Int) : btgt (Z_to_bv 64 p) i = Z_to_bv 64 (p + i) :=
  v_addi_lit p i

theorem v_auipc_lit (p i : Int) : v_auipc (Z_to_bv 64 p) i = Z_to_bv 64 (i + p) := by
  unfold v_auipc
  rw [Z_to_bv_unsigned]
  exact Z_to_bv64_wrap_r i p

theorem jalr_tgt_lit (z i : Int) :
    jalr_tgt (Z_to_bv 64 z) i = Z_to_bv 64 (Z_land (bv_wrap 64 z + i) (-2)) := by
  unfold jalr_tgt jalr_tgtZ
  rw [Z_to_bv_unsigned]

/-- `sext`/`zext` on a literal.  Both are `Z_to_bv` of the signed/unsigned
value, which is what lets the immediates of the decoded AST become `ELit`s. -/
theorem sext64_lit {n : Nat} (b : BitVec n) : sext 64 b = Z_to_bv 64 (bv_signed b) := rfl

theorem zext64_lit {n : Nat} (b : BitVec n) : zext 64 b = Z_to_bv 64 (bv_unsigned b) := by
  apply BitVec.eq_of_toNat_eq
  unfold zext bv_zero_extend Z_to_bv bv_unsigned
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

theorem bv_wrap_32_64 (z : Int) : bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z := by
  unfold bv_wrap
  omega

theorem low32_lit (z : Int) : low32 (Z_to_bv 64 z) = Z_to_bv 32 z := by
  apply BitVec.eq_of_toNat_eq
  unfold low32 bv_extract Z_to_bv
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofInt, Nat.shiftRight_zero]
  omega

theorem sext32_low32 {n : Nat} (b : BitVec n) : sext 32 b = low32 (Z_to_bv 64 (bv_signed b)) := by
  rw [low32_lit]
  rfl

theorem zext32_low32 {n : Nat} (b : BitVec n) :
    zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)) := by
  rw [low32_lit]
  apply BitVec.eq_of_toNat_eq
  unfold zext bv_zero_extend Z_to_bv bv_unsigned
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

/-! ### Smart constructors: constant folding -/

/-- Folding `ALU_ADD`/`ALU_SUB` on literals is what keeps a real compiled
prologue's `li`/`mv`/`addi` chain collapsed to one `ELit` per register
instead of a growing tree.  The nested cases (`(base + x) + y ~> base +
(x+y)`) are what keeps a SYMBOLIC base — `sp` after two `addi sp,sp,-16`s,
or a heap pointer that has been bumped twice — in the `EVar n + literal`
normal form that `to_saddr` below recognises as an address.  (The other
eight `aluop`s and the `mulop`s fold the same way; each costs one more
three-line lemma of the shape below.) -/
def mkAlu (op : aluop) (a b : expr) : expr :=
  match op with
  | .ALU_ADD =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x + y)
          | EAlu .ALU_ADD a' (ELit x) => EAlu .ALU_ADD a' (ELit (x + y))
          | _ => EAlu .ALU_ADD a b
      | _ => EAlu .ALU_ADD a b
  | .ALU_SUB =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x - y)
          | EAlu .ALU_ADD a' (ELit x) => EAlu .ALU_ADD a' (ELit (x - y))
          | _ => EAlu .ALU_SUB a b
      | _ => EAlu .ALU_SUB a b
  | _ => EAlu op a b

theorem alu64_add_lit (x y : Int) :
    alu64 .ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y) :=
  (BitVec.ofInt_add x y).symm

theorem alu64_sub_lit (x y : Int) :
    alu64 .ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  show bv_unsigned (Z_to_bv 64 x - Z_to_bv 64 y) = _
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

/-- `(u + x) + y = u + (x+y)` on the ALU, with `x`,`y` literals. -/
theorem Z_to_bv64_wrap_sub_l (a b : Int) :
    Z_to_bv 64 (bv_wrap 64 a - b) = Z_to_bv 64 (a - b) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod]
  omega

theorem Z_to_bv64_wrap_sub_r (a b : Int) :
    Z_to_bv 64 (a - bv_wrap 64 b) = Z_to_bv 64 (a - b) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod]
  omega

/-- The two "register plus literal" normal forms, as `Int` arithmetic on
`bv_unsigned`.  Everything below rewrites through these. -/
theorem v_add_lit (u : word) (x : Int) :
    v_add u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u + x) := by
  unfold v_add
  rw [Z_to_bv_unsigned]
  exact Z_to_bv64_wrap_r _ x

theorem v_add_comm (x y : word) : v_add x y = v_add y x := by
  unfold v_add
  rw [Int.add_comm]

theorem v_sub_lit (u : word) (x : Int) :
    v_sub u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u - x) := by
  unfold v_sub
  rw [Z_to_bv_unsigned]
  exact Z_to_bv64_wrap_sub_r _ x

theorem alu64_add_add_lit (u : word) (x y : Int) :
    alu64 .ALU_ADD (alu64 .ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
      = alu64 .ALU_ADD u (Z_to_bv 64 (x + y)) := by
  show u + Z_to_bv 64 x + Z_to_bv 64 y = u + Z_to_bv 64 (x + y)
  rw [BitVec.add_assoc]
  exact congrArg (u + ·) (BitVec.ofInt_add x y).symm

theorem alu64_add_sub_lit (u : word) (x y : Int) :
    alu64 .ALU_SUB (alu64 .ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
      = alu64 .ALU_ADD u (Z_to_bv 64 (x - y)) := by
  show u + Z_to_bv 64 x - Z_to_bv 64 y = u + Z_to_bv 64 (x - y)
  rw [Int.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  unfold Z_to_bv
  rw [BitVec.ofInt_add, BitVec.ofInt_neg]

theorem mkAlu_denot (E : env) (op : aluop) (a b : expr) :
    edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b) := by
  cases op <;> try rfl
  all_goals cases b <;> try rfl
  all_goals cases a <;> try rfl
  case ALU_ADD.ELit.ELit y x => exact (alu64_add_lit x y).symm
  case ALU_SUB.ELit.ELit y x => exact (alu64_sub_lit x y).symm
  all_goals rename_i y op' a1 a2
  all_goals cases op' <;> try rfl
  all_goals cases a2 <;> try rfl
  case ALU_ADD.ELit.EAlu.ALU_ADD.ELit z => exact (alu64_add_add_lit (edenot E a1) z y).symm
  case ALU_SUB.ELit.EAlu.ALU_ADD.ELit z => exact (alu64_add_sub_lit (edenot E a1) z y).symm

/-! ## 2. The symbolic register file and state -/

def ridx (r : reg) : Nat := (bv_unsigned r).toNat

theorem ridx_inj (r r' : reg) (h : ridx r = ridx r') : r = r' := by
  apply BitVec.eq_of_toNat_eq
  unfold ridx bv_unsigned at h
  omega

/-- Register 0 is not stored: `sr_get` answers `ELit 0` for it, matching
`getr`'s hard-wired x0. -/
def sr_get (sr : List expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else sr.getD (ridx r) (ELit 0)

/-- A total update: extends the list with `ELit 0` padding rather than
carrying a `length sr = 32` invariant. -/
def sr_upd (sr : List expr) (n : Nat) (e : expr) : List expr :=
  match n with
  | 0 => match sr with
    | [] => [e]
    | _ :: t => e :: t
  | n' + 1 => match sr with
    | [] => ELit 0 :: sr_upd [] n' e
    | h :: t => h :: sr_upd t n' e

theorem nth_sr_upd (n : Nat) (sr : List expr) (e : expr) (i : Nat) :
    (sr_upd sr n e).getD i (ELit 0) = if Nat.beq i n then e else sr.getD i (ELit 0) := by
  induction n generalizing sr i with
  | zero =>
    cases sr <;> cases i <;> rfl
  | succ n ih =>
    cases sr with
    | nil =>
      cases i with
      | zero => rfl
      | succ i =>
        simp only [sr_upd, List.getD_cons_succ]
        rw [ih]
        rfl
    | cons h t =>
      cases i with
      | zero => rfl
      | succ i =>
        simp only [sr_upd, List.getD_cons_succ]
        exact ih t i

/-! ## 2b. Symbolic addresses and the store log -/

/-- An address is kept in the NORMAL FORM "symbolic base + literal offset".
A base is either the literal 0 (`SBLit` — absolute addresses: globals,
.data, an image constant) or one of the ambient symbolic values (`SBVar n` —
the ASLR `sp`, a heap pointer returned by mmap/brk, an argv-derived
pointer).  Nothing else: this is what makes the load resolver's offset
arithmetic plain `Int` arithmetic, which evaluation decides.

Cross-base reasoning is FIRST CLASS: two different bases are never assumed
disjoint, they emit an `SCDisjoint` obligation. -/
inductive sbase : Type
  | SBLit
  | SBVar (n : Nat)

export sbase (SBLit SBVar)

def sbase_eqb (b1 b2 : sbase) : Bool :=
  match b1, b2 with
  | SBLit, SBLit => true
  | SBVar n, SBVar m => Nat.beq n m
  | _, _ => false

theorem sbase_eqb_eq (b1 b2 : sbase) (h : sbase_eqb b1 b2 = true) : b1 = b2 := by
  cases b1 <;> cases b2
  · rfl
  · cases h
  · cases h
  · rename_i n m
    have hnm : n = m := Nat.eq_of_beq_eq_true h
    rw [hnm]

structure saddr : Type where
  SA ::
  a_base : sbase
  a_off : Int

export saddr (SA a_base a_off)

/-- A store log entry: address, width in bytes, stored value. -/
structure sentry : Type where
  SE ::
  e_addr : saddr
  e_width : Nat
  e_val : expr

export sentry (SE e_addr e_width e_val)

def bdenot (E : env) (b : sbase) : word :=
  match b with
  | SBLit => Z_to_bv 64 0
  | SBVar n => E n

/-- Written with `v_addi` — exactly the shape the machine's addressing mode
produces — so that the address side of every load/store lemma matches by
`rw`, not by bitvector normalisation. -/
def adenot (E : env) (a : saddr) : word :=
  v_addi (bdenot E (a_base a)) (a_off a)

/-- Recognise "`expr` used as a base register, plus a displacement" as a
symbolic address.  Anything else stops the executor. -/
def to_saddr (e : expr) (i : Int) : Option saddr :=
  match e with
  | ELit z => some (SA SBLit (z + i))
  | EVar n => some (SA (SBVar n) i)
  | EAlu .ALU_ADD (EVar n) (ELit z) => some (SA (SBVar n) (z + i))
  | EAlu .ALU_ADD (ELit z) (EVar n) => some (SA (SBVar n) (z + i))
  | _ => none

theorem u_Z_to_bv64_0 : bv_unsigned (Z_to_bv 64 0) = 0 :=
  PropExec.u_zero64

/-- Lean-only helper: `PropExec.alu_add` at the machine's `+`, which
`alu64 .ALU_ADD` unfolds to. -/
private theorem add_v_add (a b : word) : a + b = v_add a b := alu_add a b

theorem to_saddr_denot (E : env) (e : expr) (i : Int) (a : saddr)
    (h : to_saddr e i = some a) : adenot E a = v_addi (edenot E e) i := by
  unfold adenot
  cases e with
  | ELit z =>
    cases h
    show v_addi (Z_to_bv 64 0) (z + i) = v_addi (Z_to_bv 64 z) i
    unfold v_addi
    rw [u_Z_to_bv64_0, Z_to_bv_unsigned, Z_to_bv64_wrap_l, Int.zero_add]
  | EVar n =>
    cases h
    rfl
  | EAlu op e1 e2 =>
    cases op <;> try cases h
    cases e1 <;> cases e2 <;> try cases h
    · -- `ELit z + EVar n`: commute the literal to the right first
      rename_i z n
      show v_addi (E n) (z + i) = v_addi (Z_to_bv 64 z + E n) i
      rw [add_v_add, v_add_comm, v_add_lit]
      unfold v_addi
      rw [Z_to_bv_unsigned, Z_to_bv64_wrap_l, Int.add_assoc]
    · -- `EVar n + ELit z`
      rename_i n z
      show v_addi (E n) (z + i) = v_addi (E n + Z_to_bv 64 z) i
      rw [add_v_add, v_add_lit]
      unfold v_addi
      rw [Z_to_bv_unsigned, Z_to_bv64_wrap_l, Int.add_assoc]
  | EAluw _ _ _ => cases h
  | EMd _ _ _ => cases h
  | EMdw _ _ _ => cases h

/-! ### The state -/

/-- `s_log` is the store log, MOST RECENT FIRST; `s_next` is the next free
valuation index (fresh symbolic values for bytes read out of the base memory
are `EVar` at these indices, starting at 32 — indices below 32 are the entry
register values, see `sr_id`). -/
structure sym_state : Type where
  SS ::
  s_pc : Int
  s_regs : List expr
  s_log : List sentry
  s_next : Nat

export sym_state (SS s_pc s_regs s_log s_next)

/-- Write `e` to `rd` (x0 discarded) and set the pc. -/
def sset (ss : sym_state) (rd : reg) (e : expr) (npc : Int) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_next ss)

def sjump (ss : sym_state) (npc : Int) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_next ss)

/-! ### Denotation into the concrete machine state -/

def regs_ok (E : env) (sr : List expr) (regs : bvmap 5 word) : Prop :=
  ∀ r : reg, getr regs r = edenot E (sr_get sr r)

/-- The log denotes a fold of `wbytes` over the base memory: the oldest entry
is applied first, so the head of the list is the outermost — exactly the
layering the tactic route builds by hand. -/
def mem_denot (E : env) (base : word → Option byte) (log : List sentry) :
    word → Option byte :=
  match log with
  | [] => base
  | SE a w v :: rest =>
      wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v))

/-- Everything the log does to memory only ADDS defined bytes, which is what
lets a `store_ok` obligation be stated against the ORIGINAL memory and lifted
through the whole chain (see `SCStoreOk`). -/
theorem mem_denot_grows (E : env) (base : word → Option byte) (log : List sentry) :
    mem_grows base (mem_denot E base log) := by
  induction log with
  | nil => exact mem_grows_refl base
  | cons ent rest ih =>
    obtain ⟨a, w, v⟩ := ent
    exact mem_grows_trans _ _ _ ih (wbytes_grows _ _ _)

/-- Every logged store address is flat (no wraparound).  Established one
entry at a time from the `SCFlat` the store emits; consumed by every later
load, which is why a same-base overlap test costs no side condition at
all. -/
def log_flat (E : env) (log : List sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      0 ≤ bv_unsigned (bdenot E (a_base a)) + a_off a
      ∧ bv_unsigned (bdenot E (a_base a)) + a_off a < 2 ^ 64
      ∧ bv_unsigned (bdenot E (a_base a)) + a_off a + (w : Int) ≤ 2 ^ 64
      ∧ log_flat E rest

/-- `ms` is described by `ss` under valuation `E`: same registers, same pc,
and a memory that is the base memory with the log's writes layered on
top. -/
def st_ok (E : env) (base rom : word → Option byte) (ss : sym_state)
    (ms : machine_state) : Prop :=
  ∃ regs, ms = mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
    ∧ regs_ok E (s_regs ss) regs
    ∧ log_flat E (s_log ss)

/-- Lean-only helper: the x0 case every register-file lemma below opens
with. -/
private theorem getr_x0 (regs : bvmap 5 word) (r : reg) (h : bv_eqb r 0 = true) :
    getr regs r = Z_to_bv 64 0 := by
  unfold getr
  rw [h]
  simp only [↓reduceIte]
  decide

theorem regs_ok_upd (E : env) (sr : List expr) (regs : bvmap 5 word) (rd : reg) (v : word)
    (e : expr) (hr : regs_ok E sr regs) (hv : edenot E e = v) :
    regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
      (if bv_eqb rd 0 then regs else regupd regs rd v) := by
  cases hrd : bv_eqb rd 0 with
  | true => exact hr
  | false =>
    have hne : rd ≠ 0 := by
      intro hc
      rw [hc, PropExec.bv_eqb_refl] at hrd
      cases hrd
    intro r
    unfold sr_get
    cases hr0 : bv_eqb r 0 with
    | true =>
      rw [getr_x0 _ r hr0]
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [nth_sr_upd]
      cases hi : Nat.beq (ridx r) (ridx rd) with
      | true =>
        have hrr : r = rd := ridx_inj r rd (Nat.eq_of_beq_eq_true hi)
        rw [hrr, getr_same regs rd v hne]
        exact hv.symm
      | false =>
        have hrr : r ≠ rd := by
          intro hc
          rw [hc, Nat.beq_refl] at hi
          cases hi
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [getr_other regs rd v r hrr]
        have h1 := hr r
        unfold sr_get at h1
        rw [hr0] at h1
        exact h1

/-- Pin one register to a symbolic expression, given that the concrete file
already agrees.  This is how a block's ENTRY state is built: start from
`sr_id` (nothing known) and pin the registers the caller has facts for. -/
theorem regs_ok_pin (E : env) (sr : List expr) (regs : bvmap 5 word) (r : reg) (e : expr)
    (hr : regs_ok E sr regs) (hv : getr regs r = edenot E e) :
    regs_ok E (sr_upd sr (ridx r) e) regs := by
  intro r'
  unfold sr_get
  cases hr0 : bv_eqb r' 0 with
  | true =>
    rw [getr_x0 _ r' hr0]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nth_sr_upd]
    cases hi : Nat.beq (ridx r') (ridx r) with
    | true =>
      have hrr : r' = r := ridx_inj r' r (Nat.eq_of_beq_eq_true hi)
      rw [hrr]
      exact hv
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 := hr r'
      unfold sr_get at h1
      rw [hr0] at h1
      exact h1

/-- The "nothing known" symbolic register file: every register is its own
variable. -/
def sr_id : List expr :=
  [EVar 0, EVar 1, EVar 2, EVar 3, EVar 4, EVar 5, EVar 6, EVar 7,
   EVar 8, EVar 9, EVar 10, EVar 11, EVar 12, EVar 13, EVar 14, EVar 15,
   EVar 16, EVar 17, EVar 18, EVar 19, EVar 20, EVar 21, EVar 22, EVar 23,
   EVar 24, EVar 25, EVar 26, EVar 27, EVar 28, EVar 29, EVar 30, EVar 31]

theorem ridx_range (r : reg) : ridx r < 32 := by
  unfold ridx bv_unsigned
  have := r.isLt
  omega

theorem ridx_roundtrip (r : reg) : Z_to_bv 5 ((ridx r : Nat) : Int) = r := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned]
  unfold ridx bv_wrap bv_unsigned
  have := r.isLt
  omega

/-- The register environment (Rocq's `E0`, unported; below index 32 this
is its body inline) extended with the values of the bytes the block reads
OUT OF the base memory, in the order the executor meets them: index `32 + k` is the
`k`-th such read.  This is the only place the caller has to say anything
about the contents of memory it did not itself write — `argc` at `sp`, an
image word, a syscall's read buffer. -/
def Eplus (regs : bvmap 5 word) (vals : List word) : env :=
  fun n => if Nat.blt n 32
           then getr regs (Z_to_bv 5 (n : Int))
           else vals.getD (n - 32) (Z_to_bv 64 0)

/-- Lean-only helper: `sr_id`'s `k`-th entry is `EVar k`. -/
private theorem sr_id_getD (k : Nat) (hk : k < 32) : sr_id.getD k (ELit 0) = EVar k := by
  have hmap : sr_id = List.map EVar (List.range 32) := rfl
  rw [hmap, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem regs_ok_Eplus (regs : bvmap 5 word) (vals : List word) :
    regs_ok (Eplus regs vals) sr_id regs := by
  intro r
  unfold sr_get
  cases hr0 : bv_eqb r 0 with
  | true =>
    rw [getr_x0 _ r hr0]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sr_id_getD (ridx r) (ridx_range r)]
    show getr regs r = Eplus regs vals (ridx r)
    unfold Eplus
    have hlt : Nat.blt (ridx r) 32 = true := by
      rw [Nat.blt_eq]
      exact ridx_range r
    simp only [hlt, ↓reduceIte]
    rw [ridx_roundtrip]

/-! ## 3. The symbolic stepper -/

/-- Deep side conditions.  The executor NEVER guesses and never fails on a
semantic question: whenever it needs a fact it cannot decide by closed
arithmetic, it records the fact and carries on.  The caller discharges a
*batch* of them at the end.

- `SCBr` — a branch decision (the caller's branch script says which way;
  the path condition is recorded).
- `SCFlat` — "this address is `base + offset` with no wraparound, and the
  `n` bytes after it stay inside the address space".  Emitted at every
  memory access; the ones a STORE emits enter the state invariant
  (`log_flat`), which is what lets a later load decide same-base overlap by
  `Int` arithmetic alone.
- `SCDisjoint` — "these two byte ranges do not overlap" (and neither wraps).
  Emitted for every DIFFERENT-base log entry a load has to look past; a
  same-base entry is decided by offset arithmetic instead.
- `SCStoreOk` — "this range is writable".  Stated against the ORIGINAL
  memory: `mem_denot_grows` + `StoreOk.store_ok_mono` lift it through the
  whole store chain, without any peeling.
- `SCReadBase` — "the load fell through the entire log; here is what the
  base memory holds there".  This is the hook for the per-image `rdn` facts.
  The loaded word is normally the fresh variable `EVar i`, but the caller's
  READ SCRIPT can NAME it instead (see `sym_step`'s `rds` argument): naming a
  reloaded return address `ELit 0x11020` is what lets the `ret` two
  instructions later resolve to a concrete pc, so a musl wrapper's whole
  epilogue stays inside one block. -/
inductive sidecond : Type
  | SCBr (taken : Bool) (c : branch_cond) (a b : expr)
  | SCFlat (a : saddr) (n : Nat)
  | SCDisjoint (a1 : saddr) (n1 : Nat) (a2 : saddr) (n2 : Nat)
  | SCStoreOk (a : saddr) (n : Nat)
  | SCReadBase (a : saddr) (n : Nat) (e : expr)

export sidecond (SCBr SCFlat SCDisjoint SCStoreOk SCReadBase)

/-- "`a` is `base + offset` literally, and `n` bytes fit above it." -/
def sc_flat (E : env) (a : saddr) (n : Nat) : Prop :=
  0 ≤ bv_unsigned (bdenot E (a_base a)) + a_off a
  ∧ bv_unsigned (bdenot E (a_base a)) + a_off a < 2 ^ 64
  ∧ bv_unsigned (bdenot E (a_base a)) + a_off a + (n : Int) ≤ 2 ^ 64

theorem flat_u (E : env) (a : saddr) (n : Nat) (h : sc_flat E a n) :
    bv_unsigned (adenot E a) = bv_unsigned (bdenot E (a_base a)) + a_off a := by
  obtain ⟨h1, h2, _⟩ := h
  unfold adenot v_addi
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt h1 h2

def sc_denot (segs : List Segment) (base : word → Option byte) (E : env) (s : sidecond) :
    Prop :=
  match s with
  | SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | SCFlat a n => sc_flat E a n
  | SCDisjoint a1 n1 a2 n2 =>
      bv_unsigned (adenot E a1) + (n1 : Int) ≤ 2 ^ 64
      ∧ bv_unsigned (adenot E a2) + (n2 : Int) ≤ 2 ^ 64
      ∧ (bv_unsigned (adenot E a1) + (n1 : Int) ≤ bv_unsigned (adenot E a2)
          ∨ bv_unsigned (adenot E a2) + (n2 : Int) ≤ bv_unsigned (adenot E a1))
  | SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
  | SCReadBase a n e =>
      ∃ bs, rdn segs base (adenot E a) n = some bs
        ∧ bytes_le_to_Z bs = bv_unsigned (edenot E e)

def scs_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (l : List sidecond) : Prop :=
  ∀ s ∈ l, sc_denot segs base E s

/-! ### Load resolution against the log -/

/-- Walk the log (most recent first) looking for the `n` bytes at `SA b k`.

- SAME base: the offsets decide.  Exact same address and width 8 (the only
  width whose stored bytes read back as the stored word with no masking) is
  a HIT.  Provably-disjoint is a skip, decided by `Int` arithmetic with NO
  side condition — this is the case that makes a spill/reload frame free.
  Anything else (an inexact overlap, a narrower read of a wider slot) STOPS the
  executor.
- DIFFERENT base: an `SCDisjoint` obligation and carry on.  Two argv-derived
  pointers, or a heap pointer versus `sp`, land here.

Result: `none` = stuck; `some (some e, scs)` = hit, value `e`;
`some (none, scs)` = fell through to the base memory. -/
def sm_lookup (log : List sentry) (b : sbase) (k : Int) (n : Nat) :
    Option (Option expr × List sidecond) :=
  match log with
  | [] => some (none, [])
  | SE (SA b' k') w v :: rest =>
      if sbase_eqb b b' then
        (if (decide (k = k') && Nat.beq n 8 && Nat.beq w 8)
         then some (some v, [])
         else if (decide (k + (n : Int) ≤ k') || decide (k' + (w : Int) ≤ k))
              then sm_lookup rest b k n
              else none)
      else
        match sm_lookup rest b k n with
        | some (r, scs) => some (r, SCDisjoint (SA b k) n (SA b' k') w :: scs)
        | none => none

def msize_bytes (sz : msize) : Nat :=
  match sz with
  | .SZ1 => 1
  | .SZ2 => 2
  | .SZ4 => 4
  | .SZ8 => 8

/-- Sign-extend a 32-bit value using the ALU primitives the executor already
denotes: `sext 64 (alu32 ADD (low32 x) 0)` IS `v_lw x`. -/
def mkSext32 (e : expr) : expr := EAluw .ALU_ADD e (ELit 0)

/-- One instruction.  `none` = "not modelled, stop the block here";
otherwise the new state, the side conditions it assumed, and the unconsumed
tail of the READ SCRIPT.

`rds` is to loads what `dirs` is to branches: an optional caller-supplied
name for each value the block reads out of the BASE memory.  An empty script
keeps the old behaviour (a fresh `EVar`); a supplied `expr` is used instead,
and the `SCReadBase` obligation is stated against it, so the caller pays
exactly the same `rdn` fact and gets a value the executor can go on
computing with. -/
def sym_step (i : instr) (ss : sym_state) (rds : List expr) :
    Option (sym_state × List sidecond × List expr) :=
  let g r := sr_get (s_regs ss) r
  let p := s_pc ss
  match i with
  | .OpImm op rd rs imm =>
      some (sset ss rd (mkAlu op (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | .ShiftImm op rd rs sh =>
      some (sset ss rd (mkAlu op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | .Op op rd rs1 rs2 =>
      some (sset ss rd (mkAlu op (g rs1) (g rs2)) (p + 4), [], rds)
  | .OpImm32 rd rs imm =>
      some (sset ss rd (EAluw .ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | .ShiftImm32 op rd rs sh =>
      some (sset ss rd (EAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | .Op32 op rd rs1 rs2 =>
      some (sset ss rd (EAluw op (g rs1) (g rs2)) (p + 4), [], rds)
  | .Mul op rd rs1 rs2 =>
      some (sset ss rd (EMd op (g rs1) (g rs2)) (p + 4), [], rds)
  | .Mul32 op rd rs1 rs2 =>
      some (sset ss rd (EMdw op (g rs1) (g rs2)) (p + 4), [], rds)
  | .Lui rd imm =>
      some (sset ss rd (ELit (Z_shiftl (bv_signed imm) 12)) (p + 4), [], rds)
  | .Auipc rd imm =>
      some (sset ss rd (ELit (Z_shiftl (bv_signed imm) 12 + p)) (p + 4), [], rds)
  | .Jal rd imm =>
      some (sset ss rd (ELit (p + 4)) (p + bv_signed imm), [], rds)
  | .Jalr rd rs1 imm =>
      -- the jump target must be a literal for the pc to stay concrete
      match g rs1 with
      | ELit z => some (sset ss rd (ELit (p + 4))
                          (Z_land (bv_wrap 64 z + bv_signed imm) (-2)), [], rds)
      | _ => none
  -- loads: ld, lwu, lw, lhu, lbu (lh/lb are not modelled)
  | .Load sz sgn rd rs imm =>
      let n := msize_bytes sz
      match to_saddr (g rs) (bv_signed imm) with
      | none => none
      | some a =>
          match sm_lookup (s_log ss) (a_base a) (a_off a) n with
          | none => none
          | some (some v, scs) =>
              -- a hit is only ever an 8-byte slot read back whole
              match sz, sgn with
              | .SZ8, true => some (sset ss rd v (p + 4), SCFlat a 8 :: scs, rds)
              | _, _ => none
          | some (none, scs) =>
              let i := s_next ss
              let rv := match rds with
                | [] => EVar i
                | e :: _ => e
              let rds' := match rds with
                | [] => []
                | _ :: t => t
              let scs' := SCFlat a n :: SCReadBase a n rv :: scs
              let mk e := some (SS (p + 4)
                                   (if bv_eqb rd 0 then s_regs ss
                                    else sr_upd (s_regs ss) (ridx rd) e)
                                   (s_log ss) (i + 1), scs', rds')
              match sz, sgn with
              | .SZ8, true => mk rv
              | .SZ4, false => mk rv
              | .SZ2, false => mk rv
              | .SZ1, false => mk rv
              | .SZ4, true => mk (mkSext32 rv)
              | _, _ => none
  -- stores: sb, sw and sd (sh has no step lemma yet)
  | .Store sz rs1 rs2 imm =>
      match sz with
      | .SZ1 | .SZ4 | .SZ8 =>
          let n := msize_bytes sz
          match to_saddr (g rs1) (bv_signed imm) with
          | none => none
          | some a =>
              some (SS (p + 4) (s_regs ss)
                       (SE a n (g rs2) :: s_log ss) (s_next ss),
                    [SCFlat a n, SCStoreOk a n], rds)
      | _ => none
  | _ => none

/-! ### Extra machine-level step lemmas the executor needs -/

/-- Signed 32-bit load, value exposed. -/
theorem b_lw_val (v : word) : sext 64 (bv_extract 0 32 v) = v_lw v := by
  have h : bv_signed (bv_extract 0 32 v) = bv_swrap 32 (bv_unsigned v) := by
    unfold bv_signed bv_extract bv_swrap bv_half_modulus bv_modulus bv_wrap bv_unsigned
    rw [BitVec.toInt_eq_toNat_cond, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    split <;> omega
  unfold v_lw
  show Z_to_bv 64 (bv_signed (bv_extract 0 32 v)) = _
  rw [h]

theorem step_lw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Load .SZ4 true rd rs imm, 4))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 = some bs)
    (hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  refine interp_load segs 32 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 4
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact hread
  · show eff.EDone (rset rd (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v hv, b_lw_val, npc4, rset_mk]

theorem alu32_add_0 (x : BitVec 32) : alu32 .ALU_ADD x (Z_to_bv 32 0) = x := by
  show x + Z_to_bv 32 0 = x
  have h0 : Z_to_bv 32 0 = 0#32 := by decide
  rw [h0, BitVec.add_zero]

theorem mkSext32_denot (E : env) (e : expr) : edenot E (mkSext32 e) = v_lw (edenot E e) := by
  show sext 64 (alu32 .ALU_ADD (low32 (edenot E e)) (low32 (Z_to_bv 64 0))) = _
  rw [low32_lit, alu32_add_0]
  exact b_lw_val _

theorem bytes_le_to_Z_1 (b : byte) : bytes_le_to_Z [b] = bv_unsigned b := by
  unfold bytes_le_to_Z bytes_le_to_nat bytes_le_to_nat bv_unsigned
  rw [Nat.zero_shiftLeft, Nat.or_zero]

/-! ### Word store (`sw`): the SZ4 twin of `SeqExec.step_sb`/`step_sd_val`

The interpreter narrows the stored value for every width below 64:
`Sem.store_val` hands `EStore` the low 8, 16 or 32 bits (`bv_extract 0 8`,
`bv_extract 0 16`, `low32`), and only `sd` stores the full register.  A
little-endian byte list of length `n` only ever looks at the low `8n` bits,
so the narrowed value and the full register store the same bytes; that is
`Z_to_le_bytes_mod` below for `sw`, and `SeqExec.step_sb` carries the same
bridge for `sb`. -/

/-- Lean-only helper: `Z_pow 2 k` at a non-negative exponent is Lean's
power at `k.toNat`. -/
private theorem Z_pow_two_nonneg (k : Int) (hk : 0 ≤ k) : Z_pow 2 k = 2 ^ k.toNat := by
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rfl

theorem shiftr8_mod_pow2 (k z : Int) (hk : 0 ≤ k) :
    (z % Z_pow 2 (k + 8)) >>> 8 = (z >>> 8) % Z_pow 2 k := by
  rw [Z_pow_two_nonneg (k + 8) (by omega), Z_pow_two_nonneg k hk]
  rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow]
  have hK : (k + 8).toNat = k.toNat + 8 := by omega
  rw [hK, Int.pow_add]
  have h256 : (((2 ^ 8 : Nat)) : Int) = 256 := rfl
  have h28 : (2 : Int) ^ 8 = 256 := rfl
  rw [h256, h28]
  have hPpos : 0 < (2 : Int) ^ k.toNat := Int.pow_pos (by decide)
  generalize (2 : Int) ^ k.toNat = P at hPpos ⊢
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
    · have : t + 1 ≤ P := ht1
      have hm : (t + 1) * 256 ≤ P * 256 := Int.mul_le_mul_of_nonneg_right this (by decide)
      omega
  rw [hmod]
  omega

theorem mod_pow2_low (z k m : Int) (h : 0 ≤ m ∧ m ≤ k) :
    (z % Z_pow 2 k) % Z_pow 2 m = z % Z_pow 2 m := by
  rw [Z_pow_two_nonneg k (by omega), Z_pow_two_nonneg m h.1]
  apply Int.emod_emod_of_dvd
  refine ⟨2 ^ (k.toNat - m.toNat), ?_⟩
  rw [← Int.pow_add]
  congr 1
  omega

theorem Z_to_le_bytes_mod (n : Nat) (z : Int) :
    Z_to_le_bytes n (z % 2 ^ (8 * n)) = Z_to_le_bytes n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Z_to_le_bytes]
    congr 1
    · apply bv_eq_of_unsigned
      rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap, bv_wrap]
      exact mod_pow2_low z ((8 * (n + 1) : Nat) : Int) 8 ⟨by decide, by omega⟩
    · have h := shiftr8_mod_pow2 ((8 * n : Nat) : Int) z (by omega)
      have hk : ((8 * n : Nat) : Int) + 8 = ((8 * (n + 1) : Nat) : Int) := by omega
      rw [hk] at h
      rw [show (2 : Int) ^ (8 * (n + 1)) = Z_pow 2 ((8 * (n + 1) : Nat) : Int) from rfl, h]
      exact ih (z >>> 8)

/-- Lean-only helper: the unsigned view of `low32`. -/
private theorem bv_unsigned_low32 (v : word) : bv_unsigned (low32 v) = bv_unsigned v % 2 ^ 32 := by
  unfold low32 bv_extract bv_unsigned
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

theorem low32_le_bytes (v : word) :
    Z_to_le_bytes 4 (bv_unsigned (low32 v)) = word_to_le_bytes 4 v := by
  unfold word_to_le_bytes
  rw [bv_unsigned_low32]
  exact Z_to_le_bytes_mod 4 (bv_unsigned v)

/-- Store word, stored VALUE exposed — the `sw` analogue of
`SeqExec.step_sd_val`. -/
theorem step_sw_val (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ4 rs1 rs2 imm, 4))
    (hok : RiscvSemantics.store_ok segs mem
      (v_addi (getr regs rs1) (bv_signed imm)) 4 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          (word_to_le_bytes 4 (getr regs rs2))) rom) := by
  rw [step_of_fetch segs (mkst regs pc mem rom) w hf]
  apply decode_exec_of_interp segs regs regs pc (v_addi pc 4) mem _ rom w _ he hd
  change interp_eff segs (.EStore 32
      (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (.EDone (core.Core regs bvmap_empty (pc + 4) 0 none))) mem = _
  rw [rget_mk, rget_mk, b_addsext, interp_store segs 32 _ _ _ mem hok,
    write_to_mem_wbytes]
  have hw : width_bytes 32 = 4 := rfl
  have hpc : pc + 4 = v_addi pc 4 := b_npc4 pc
  rw [hw, low32_le_bytes, hpc]

/-! ### Log lookup soundness -/

theorem scs_denot_cons (segs : List Segment) (base : word → Option byte) (E : env)
    (s : sidecond) (l : List sidecond) (h : scs_denot segs base E (s :: l)) :
    sc_denot segs base E s ∧ scs_denot segs base E l :=
  ⟨h s (List.mem_cons.2 (Or.inl rfl)), fun x hx => h x (List.mem_cons.2 (Or.inr hx))⟩

/-- The heart of the memory model: a log lookup that the executor resolved
really does describe the layered memory. -/
theorem sm_lookup_sound (segs : List Segment) (base : word → Option byte) (E : env)
    (log : List sentry) (b : sbase) (k : Int) (n : Nat) (r : Option expr)
    (scs : List sidecond)
    (hl : sm_lookup log b k n = some (r, scs))
    (hsc : scs_denot segs base E scs)
    (hlf : log_flat E log)
    (hfl : sc_flat E (SA b k) n) :
    match r with
    | none => rdn segs (mem_denot E base log) (adenot E (SA b k)) n
                = rdn segs base (adenot E (SA b k)) n
    | some v =>
        n = 8 ∧
        rdn segs (mem_denot E base log) (adenot E (SA b k)) n
          = some (word_to_le_bytes 8 (edenot E v)) := by
  have hua := flat_u E (SA b k) n hfl
  obtain ⟨hk1, hk2, hk3⟩ := hfl
  -- a read of `SA b k` skips any store it provably does not overlap
  have hskip : ∀ (a' : saddr) (w : Nat) (v : expr) (m : word → Option byte),
      (bv_unsigned (adenot E (SA b k)) + (n : Int) ≤ bv_unsigned (adenot E a')
        ∨ bv_unsigned (adenot E a') + (w : Int) ≤ bv_unsigned (adenot E (SA b k))) →
      bv_unsigned (adenot E a') + (w : Int) ≤ 2 ^ 64 →
      rdn segs (wbytes m (adenot E a') (word_to_le_bytes w (edenot E v)))
          (adenot E (SA b k)) n
        = rdn segs m (adenot E (SA b k)) n := by
    intro a' w v m hd hnw
    rcases hd with hd | hd
    · exact rdn_wbytes_below segs _ m _ _ n hd (by rw [length_N_to_le_bytes]; exact hnw)
    · exact rdn_wbytes_disjoint segs _ m _ _ n (by rw [length_N_to_le_bytes]; exact hd)
        (by rw [hua]; exact hk3)
  induction log generalizing r scs with
  | nil =>
    simp only [sm_lookup, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rfl
  | cons ent rest ih =>
    obtain ⟨⟨b', k'⟩, w, v'⟩ := ent
    obtain ⟨hf1, hf2, hf3, hlf'⟩ := hlf
    dsimp only at hf1 hf2 hf3
    simp only [sm_lookup] at hl
    cases hb : sbase_eqb b b' with
    | true =>
      have hbb : b = b' := sbase_eqb_eq b b' hb
      subst hbb
      have hua' : bv_unsigned (adenot E (SA b k')) = bv_unsigned (bdenot E b) + k' :=
        flat_u E (SA b k') w ⟨hf1, hf2, hf3⟩
      dsimp only at hua hua'
      rw [hb] at hl
      simp only [↓reduceIte] at hl
      cases hhit : (decide (k = k') && Nat.beq n 8 && Nat.beq w 8) with
      | true =>
        rw [hhit] at hl
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hhit
        obtain ⟨⟨hkk, hn8⟩, hw8⟩ := hhit
        have hn : n = 8 := Nat.eq_of_beq_eq_true hn8
        have hw : w = 8 := Nat.eq_of_beq_eq_true hw8
        subst hkk hn hw
        exact ⟨rfl, rdn_wbytes_hit8 segs _ _ _ (by rw [hua]; exact hk3)⟩
      | false =>
        rw [hhit] at hl
        simp only [Bool.false_eq_true, ↓reduceIte] at hl
        cases hdis : (decide (k + (n : Int) ≤ k') || decide (k' + (w : Int) ≤ k)) with
        | false =>
          rw [hdis] at hl
          simp only [Bool.false_eq_true, ↓reduceIte] at hl
          cases hl
        | true =>
          rw [hdis] at hl
          simp only [↓reduceIte] at hl
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hdis
          have hs := hskip (SA b k') w v' (mem_denot E base rest)
            (by rw [hua, hua']; omega) (by rw [hua']; exact hf3)
          have ih' := ih r scs hl hsc hlf'
          cases r with
          | none =>
            simp only [mem_denot]
            rw [hs]
            exact ih'
          | some v =>
            obtain ⟨hn8, ih2⟩ := ih'
            refine ⟨hn8, ?_⟩
            simp only [mem_denot]
            rw [hs]
            exact ih2
    | false =>
      rw [hb] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      cases hrec : sm_lookup rest b k n with
      | none =>
        rw [hrec] at hl
        cases hl
      | some p =>
        obtain ⟨r0, scs0⟩ := p
        rw [hrec] at hl
        simp only [Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        obtain ⟨hhd, htl⟩ := scs_denot_cons segs base E _ _ hsc
        obtain ⟨_, hnw2, hd⟩ := hhd
        have hs := hskip (SA b' k') w v' (mem_denot E base rest) hd hnw2
        have ih' := ih r0 scs0 hrec htl hlf'
        cases r0 with
        | none =>
          simp only [mem_denot]
          rw [hs]
          exact ih'
        | some v =>
          obtain ⟨hn8, ih2⟩ := ih'
          refine ⟨hn8, ?_⟩
          simp only [mem_denot]
          rw [hs]
          exact ih2

/-! ### One instruction -/

/-- Lean-only helper: the state `sset` builds describes the machine state a
register-writing step produces. -/
private theorem sset_ok (E : env) (base rom : word → Option byte) (ss : sym_state)
    (regs : bvmap 5 word) (rd : reg) (e : expr) (v : word) (npc : Int)
    (hregs : regs_ok E (s_regs ss) regs) (hlf : log_flat E (s_log ss))
    (hv : edenot E e = v) :
    st_ok E base rom (sset ss rd e npc)
      (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (Z_to_bv 64 npc)
        (mem_denot E base (s_log ss)) rom) :=
  ⟨_, rfl, regs_ok_upd E (s_regs ss) regs rd v e hregs hv, hlf⟩

/-- Lean-only helper: the base-memory read a load miss assumed
(`SCReadBase`), moved onto the layered memory by `sm_lookup_sound`. -/
private theorem load_miss_read (segs : List Segment) (base : word → Option byte) (E : env)
    (log : List sentry) (ab : sbase) (ak : Int) (n : Nat) (scs0 : List sidecond)
    (rv : expr) (x : word)
    (hlk : sm_lookup log ab ak n = some (none, scs0))
    (hsc : scs_denot segs base E (SCFlat (SA ab ak) n :: SCReadBase (SA ab ak) n rv :: scs0))
    (hlf : log_flat E log)
    (hadr : adenot E (SA ab ak) = x) :
    ∃ bs, rdn segs (mem_denot E base log) x n = some bs
      ∧ bytes_le_to_Z bs = bv_unsigned (edenot E rv) := by
  obtain ⟨hfit, hsc1⟩ := scs_denot_cons segs base E _ _ hsc
  obtain ⟨hrb, hsc0⟩ := scs_denot_cons segs base E _ _ hsc1
  obtain ⟨bs, hrdn, hbs⟩ := hrb
  have hmiss : rdn segs (mem_denot E base log) (adenot E (SA ab ak)) n
      = rdn segs base (adenot E (SA ab ak)) n :=
    sm_lookup_sound segs base E log ab ak n none scs0 hlk hsc0 hlf hfit
  rw [← hadr]
  exact ⟨bs, hmiss.trans hrdn, hbs⟩

theorem sym_step_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (i : instr) (ss' : sym_state)
    (scs : List sidecond) (w : BitVec 32) (rds rds' : List expr)
    (hf : fetch_word segs (Z_to_bv 64 (s_pc ss)) = some w)
    (he : is_ecall w = false)
    (hd : decode_any w = some (i, 4))
    (hs : sym_step i ss rds = some (ss', scs, rds'))
    (hsc : scs_denot segs base E scs)
    (hst : st_ok E base rom ss ms) :
    ∃ ms', RiscvSemantics.step segs ms = MachineOk ms' ∧ st_ok E base rom ss' ms' := by
  obtain ⟨regs, rfl, hregs, hlf⟩ := hst
  cases i
  case Lui rd imm =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_lui segs regs _ _ rom w rd imm hf he hd, ?_⟩
    rw [v_addi_lit]
    exact sset_ok E base rom ss regs rd _ _ _ hregs hlf rfl
  case Auipc rd imm =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_auipc segs regs _ _ rom w rd imm hf he hd, ?_⟩
    rw [v_addi_lit]
    exact sset_ok E base rom ss regs rd _ _ _ hregs hlf (v_auipc_lit _ _).symm
  case Jal rd imm =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_jal_link segs regs _ _ rom w rd imm hf he hd, ?_⟩
    rw [btgt_lit, v_addi_lit]
    exact sset_ok E base rom ss regs rd _ _ _ hregs hlf rfl
  case Jalr rd rs1 imm =>
    simp only [sym_step] at hs
    split at hs
    · rename_i z hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      have hg1 : getr regs rs1 = Z_to_bv 64 z := by
        rw [hregs rs1, hg]
        rfl
      have hpc : v_jalr (getr regs rs1) (bv_signed imm)
          = Z_to_bv 64 (Z_land (bv_wrap 64 z + bv_signed imm) (-2)) := by
        rw [hg1]
        exact jalr_tgt_lit z (bv_signed imm)
      refine ⟨_, step_jalr segs regs _ _ rom w rd rs1 imm hf he hd, ?_⟩
      rw [hpc, v_addi_lit]
      exact sset_ok E base rom ss regs rd _ _ _ hregs hlf rfl
    · cases hs
  case Load sz sgn rd rs imm =>
    cases ha : to_saddr (sr_get (s_regs ss) rs) (bv_signed imm) with
    | none => simp only [sym_step, ha, reduceCtorEq] at hs
    | some a =>
      obtain ⟨ab, ak⟩ := a
      have hadr : adenot E (SA ab ak) = v_addi (getr regs rs) (bv_signed imm) := by
        rw [to_saddr_denot E _ _ _ ha, hregs rs]
      cases hlk : sm_lookup (s_log ss) ab ak (msize_bytes sz) with
      | none => simp only [sym_step, ha, hlk, reduceCtorEq] at hs
      | some p =>
        obtain ⟨r, scs0⟩ := p
        cases r with
        | some v =>
          -- a hit: only `ld` reads a logged slot back
          cases sz <;> cases sgn <;>
            simp only [sym_step, ha, hlk, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          obtain ⟨hfit, hsc0⟩ := scs_denot_cons segs base E _ _ hsc
          obtain ⟨_, hread⟩ :=
            sm_lookup_sound segs base E (s_log ss) ab ak 8 (some v) scs0 hlk hsc0 hlf hfit
          rw [hadr] at hread
          refine ⟨_, step_ld segs regs _ _ rom w rd rs imm _ (edenot E v) hf he hd hread
            (bytes_le_to_Z_8 _), ?_⟩
          rw [v_addi_lit]
          exact sset_ok E base rom ss regs rd _ _ _ hregs hlf rfl
        | none =>
          -- a miss: the value is read out of the base memory
          cases sz <;> cases sgn <;>
            simp only [sym_step, ha, hlk, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
          · -- lbu
            obtain ⟨rfl, rfl, rfl⟩ := hs
            obtain ⟨bs, hrdn, hbs⟩ :=
              load_miss_read segs base E (s_log ss) ab ak _ scs0 _ _ hlk hsc hlf hadr
            have hlen := rdn_length segs _ 1 _ bs hrdn
            match bs, hlen, hrdn, hbs with
            | [b0], _, hrdn, hbs =>
              rw [bytes_le_to_Z_1] at hbs
              refine ⟨_, step_lbu segs regs _ _ rom w rd rs imm b0 hf he hd hrdn, ?_⟩
              rw [v_addi_lit]
              refine ⟨_, rfl, regs_ok_upd E _ regs rd _ _ hregs ?_, hlf⟩
              rw [hbs, Z_to_bv_bv_unsigned64]
          · -- lhu
            obtain ⟨rfl, rfl, rfl⟩ := hs
            obtain ⟨bs, hrdn, hbs⟩ :=
              load_miss_read segs base E (s_log ss) ab ak _ scs0 _ _ hlk hsc hlf hadr
            refine ⟨_, step_lhu segs regs _ _ rom w rd rs imm bs _ hf he hd hrdn hbs, ?_⟩
            rw [v_addi_lit]
            exact ⟨_, rfl, regs_ok_upd E _ regs rd _ _ hregs rfl, hlf⟩
          · -- lwu
            obtain ⟨rfl, rfl, rfl⟩ := hs
            obtain ⟨bs, hrdn, hbs⟩ :=
              load_miss_read segs base E (s_log ss) ab ak _ scs0 _ _ hlk hsc hlf hadr
            refine ⟨_, step_lwu segs regs _ _ rom w rd rs imm bs _ hf he hd hrdn hbs, ?_⟩
            rw [v_addi_lit]
            exact ⟨_, rfl, regs_ok_upd E _ regs rd _ _ hregs rfl, hlf⟩
          · -- lw
            obtain ⟨rfl, rfl, rfl⟩ := hs
            obtain ⟨bs, hrdn, hbs⟩ :=
              load_miss_read segs base E (s_log ss) ab ak _ scs0 _ _ hlk hsc hlf hadr
            refine ⟨_, step_lw segs regs _ _ rom w rd rs imm bs _ hf he hd hrdn hbs, ?_⟩
            rw [v_addi_lit]
            exact ⟨_, rfl, regs_ok_upd E _ regs rd _ _ hregs (mkSext32_denot E _), hlf⟩
          · -- ld
            obtain ⟨rfl, rfl, rfl⟩ := hs
            obtain ⟨bs, hrdn, hbs⟩ :=
              load_miss_read segs base E (s_log ss) ab ak _ scs0 _ _ hlk hsc hlf hadr
            refine ⟨_, step_ld segs regs _ _ rom w rd rs imm bs _ hf he hd hrdn hbs, ?_⟩
            rw [v_addi_lit]
            exact ⟨_, rfl, regs_ok_upd E _ regs rd _ _ hregs rfl, hlf⟩
  case Store sz rs1 rs2 imm =>
    cases ha : to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm) with
    | none => cases sz <;> simp only [sym_step, ha, reduceCtorEq] at hs
    | some a =>
      have hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm) := by
        rw [to_saddr_denot E _ _ _ ha, hregs rs1]
      cases sz <;> simp only [sym_step, ha, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
      all_goals
        obtain ⟨rfl, rfl, rfl⟩ := hs
        obtain ⟨hfl, hsc1⟩ := scs_denot_cons segs base E _ _ hsc
        obtain ⟨hok, _⟩ := scs_denot_cons segs base E _ _ hsc1
        have hok' := store_ok_mono segs _ base _ _ (mem_denot_grows E base (s_log ss)) hok
        rw [hadr] at hok'
      · -- sb
        refine ⟨_, step_sb segs regs _ _ rom w rs1 rs2 imm hf he hd hok', regs, ?_, hregs,
          hfl.1, hfl.2.1, hfl.2.2, hlf⟩
        show mkst regs (v_addi (Z_to_bv 64 (s_pc ss)) 4)
            (wbytes (mem_denot E base (s_log ss)) (v_addi (getr regs rs1) (bv_signed imm))
              (word_to_le_bytes 1 (getr regs rs2))) rom
          = mkst regs (Z_to_bv 64 (s_pc ss + 4))
            (wbytes (mem_denot E base (s_log ss)) (adenot E a)
              (word_to_le_bytes 1 (edenot E (sr_get (s_regs ss) rs2)))) rom
        rw [v_addi_lit, hadr, hregs rs2]
      · -- sw
        refine ⟨_, step_sw_val segs regs _ _ rom w rs1 rs2 imm hf he hd hok', regs, ?_, hregs,
          hfl.1, hfl.2.1, hfl.2.2, hlf⟩
        show mkst regs (v_addi (Z_to_bv 64 (s_pc ss)) 4)
            (wbytes (mem_denot E base (s_log ss)) (v_addi (getr regs rs1) (bv_signed imm))
              (word_to_le_bytes 4 (getr regs rs2))) rom
          = mkst regs (Z_to_bv 64 (s_pc ss + 4))
            (wbytes (mem_denot E base (s_log ss)) (adenot E a)
              (word_to_le_bytes 4 (edenot E (sr_get (s_regs ss) rs2)))) rom
        rw [v_addi_lit, hadr, hregs rs2]
      · -- sd
        refine ⟨_, step_sd_val segs regs _ _ rom w rs1 rs2 imm hf he hd hok', regs, ?_, hregs,
          hfl.1, hfl.2.1, hfl.2.2, hlf⟩
        show mkst regs (v_addi (Z_to_bv 64 (s_pc ss)) 4)
            (wbytes (mem_denot E base (s_log ss)) (v_addi (getr regs rs1) (bv_signed imm))
              (word_to_le_bytes 8 (getr regs rs2))) rom
          = mkst regs (Z_to_bv 64 (s_pc ss + 4))
            (wbytes (mem_denot E base (s_log ss)) (adenot E a)
              (word_to_le_bytes 8 (edenot E (sr_get (s_regs ss) rs2)))) rom
        rw [v_addi_lit, hadr, hregs rs2]
  case OpImm op rd rs imm =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_opimm_gen segs regs _ _ rom w op rd rs imm hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    rw [mkAlu_denot, hregs rs]
    rfl
  case ShiftImm op rd rs sh =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_shiftimm_gen segs regs _ _ rom w op rd rs sh hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    rw [mkAlu_denot, hregs rs, zext64_lit]
    rfl
  case Op op rd rs1 rs2 =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_op_gen segs regs _ _ rom w op rd rs1 rs2 hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    rw [mkAlu_denot, hregs rs1, hregs rs2]
  case OpImm32 rd rs imm =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_opimm32_gen segs regs _ _ rom w rd rs imm hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    simp only [edenot]
    rw [hregs rs, sext32_low32 imm]
  case ShiftImm32 op rd rs sh =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_shiftimm32_gen segs regs _ _ rom w op rd rs sh hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    simp only [edenot]
    rw [hregs rs, zext32_low32 sh]
  case Op32 op rd rs1 rs2 =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_op32_gen segs regs _ _ rom w op rd rs1 rs2 hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    simp only [edenot]
    rw [hregs rs1, hregs rs2]
  case Mul op rd rs1 rs2 =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_mul_gen segs regs _ _ rom w op rd rs1 rs2 hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    simp only [edenot]
    rw [hregs rs1, hregs rs2]
  case Mul32 op rd rs1 rs2 =>
    simp only [sym_step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    refine ⟨_, step_mul32_gen segs regs _ _ rom w op rd rs1 rs2 hf he hd, ?_⟩
    rw [v_addi_lit]
    apply sset_ok E base rom ss regs rd _ _ _ hregs hlf
    simp only [edenot]
    rw [hregs rs1, hregs rs2]
  all_goals simp only [sym_step, reduceCtorEq] at hs

/-! ## 4. The executor -/

/-- Run from `ss`'s pc for at most `fuel` instructions.  `dirs` is the
caller's branch script: one boolean per `Branch` encountered, saying which
way to go; the assumed path condition is recorded in the side-condition
list.  A pc it cannot fetch, an `ecall`, an undecodable word, a compressed
encoding or a `Branch` once `dirs` is used up stops the run here, before
`sym_step` is called; so does anything `sym_step` declines (the module
header lists each case).  Either way the run returns the state AT that
instruction. -/
def sym_exec (segs : List Segment) (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) : sym_state × List sidecond :=
  match fuel with
  | 0 => (ss, acc)
  | f + 1 =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | none => (ss, acc)
      | some w =>
          if is_ecall w then (ss, acc) else
          match decode_any w with
          | none => (ss, acc)
          | some (i, sz) =>
              if !(decide (sz = 4)) then (ss, acc) else
              match i with
              | .Branch c rs1 rs2 imm =>
                  match dirs with
                  | [] => (ss, acc)
                  | t :: dirs' =>
                      sym_exec segs f dirs' rds
                        (sjump ss (if t then s_pc ss + bv_signed imm else s_pc ss + 4))
                        (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc)
              | _ =>
                  match sym_step i ss rds with
                  | some (ss', scs, rds') => sym_exec segs f dirs rds' ss' (scs ++ acc)
                  | none => (ss, acc)

/-- The accumulator only grows, so side conditions proved for the RESULT
list cover every assumption made along the way. -/
theorem sym_exec_acc (segs : List Segment) (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) :
    ∃ pre, (sym_exec segs fuel dirs rds ss acc).2 = pre ++ acc := by
  induction fuel generalizing dirs rds ss acc with
  | zero => exact ⟨[], rfl⟩
  | succ f ih =>
    simp only [sym_exec]
    split
    · exact ⟨[], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · split
        · exact ⟨[], rfl⟩
        · split
          · exact ⟨[], rfl⟩
          · split
            · rename_i c rs1 rs2 imm _
              split
              · exact ⟨[], rfl⟩
              · rename_i t dirs'
                obtain ⟨pre, hpre⟩ := ih dirs' rds
                  (sjump ss (if t then s_pc ss + bv_signed imm else s_pc ss + 4))
                  (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc)
                refine ⟨pre ++ [SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)], ?_⟩
                rw [hpre, List.append_assoc]
                rfl
            · split
              · rename_i ss2 scs2 rds2 _
                obtain ⟨pre, hpre⟩ := ih dirs rds2 ss2 (scs2 ++ acc)
                refine ⟨pre ++ scs2, ?_⟩
                rw [hpre, List.append_assoc]
              · exact ⟨[], rfl⟩

theorem scs_denot_app (segs : List Segment) (base : word → Option byte) (E : env)
    (l1 l2 : List sidecond) (h : scs_denot segs base E (l1 ++ l2)) :
    scs_denot segs base E l1 ∧ scs_denot segs base E l2 :=
  ⟨fun x hx => h x (List.mem_append.2 (Or.inl hx)),
   fun x hx => h x (List.mem_append.2 (Or.inr hx))⟩

/-- If the executor reaches `ss'` from `ss` and every side condition it
assumed holds under the valuation `E`, then the concrete machine really does
reach a state described by `ss'` — INCLUDING its memory, which is the base
memory with the symbolic store log layered on. -/
theorem sym_exec_sound (segs : List Segment) (fuel : Nat) (dirs : List Bool)
    (rds : List expr) (ss : sym_state) (acc : List sidecond) (ss' : sym_state)
    (scs : List sidecond) (E : env) (base rom : word → Option byte) (ms : machine_state)
    (hex : sym_exec segs fuel dirs rds ss acc = (ss', scs))
    (hsc : scs_denot segs base E scs)
    (hst : st_ok E base rom ss ms) :
    ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' := by
  induction fuel generalizing dirs rds ss acc ms with
  | zero =>
    simp only [sym_exec, Prod.mk.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    exact ⟨ms, .mst_refl ms, hst⟩
  | succ f ih =>
    have hstop : (ss, acc) = (ss', scs) →
        ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' := by
      intro hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨ms, .mst_refl ms, hst⟩
    simp only [sym_exec] at hex
    split at hex
    · exact hstop hex
    · rename_i w hf
      split at hex
      · exact hstop hex
      · rename_i he'
        have he : is_ecall w = false := Bool.of_not_eq_true he'
        split at hex
        · exact hstop hex
        · rename_i i sz hd
          split at hex
          · exact hstop hex
          · rename_i hsz
            have hsz4 : sz = 4 := by
              cases h : decide (sz = 4) with
              | true => exact of_decide_eq_true h
              | false =>
                rw [h] at hsz
                exact absurd rfl hsz
            subst hsz4
            split at hex
            · -- Branch: the executor consumed one caller-supplied direction
              rename_i c rs1 rs2 imm
              split at hex
              · exact hstop hex
              · rename_i t dirs'
                obtain ⟨regs, rfl, hregs, hlf⟩ := hst
                obtain ⟨pre, hpre⟩ := sym_exec_acc segs f dirs' rds
                  (sjump ss (if t then s_pc ss + bv_signed imm else s_pc ss + 4))
                  (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc)
                rw [hex] at hpre
                have hpre' : scs = pre ++ (SCBr t c (sr_get (s_regs ss) rs1)
                    (sr_get (s_regs ss) rs2) :: acc) := hpre
                subst hpre'
                have hhd : sc_denot segs base E
                    (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) :=
                  (scs_denot_app segs base E _ _ hsc).2 _ (List.mem_cons_self ..)
                have hc : branch_taken c (getr regs rs1) (getr regs rs2) = t := by
                  rw [hregs rs1, hregs rs2]
                  exact hhd
                have hstA : st_ok E base rom
                    (sjump ss (if t then s_pc ss + bv_signed imm else s_pc ss + 4))
                    (mkst regs (if t then btgt (Z_to_bv 64 (s_pc ss)) (bv_signed imm)
                                else v_addi (Z_to_bv 64 (s_pc ss)) 4)
                      (mem_denot E base (s_log ss)) rom) := by
                  refine ⟨regs, ?_, hregs, hlf⟩
                  cases t
                  · show mkst regs (v_addi (Z_to_bv 64 (s_pc ss)) 4) (mem_denot E base (s_log ss)) rom
                      = mkst regs (Z_to_bv 64 (s_pc ss + 4)) (mem_denot E base (s_log ss)) rom
                    rw [v_addi_lit]
                  · show mkst regs (btgt (Z_to_bv 64 (s_pc ss)) (bv_signed imm))
                        (mem_denot E base (s_log ss)) rom
                      = mkst regs (Z_to_bv 64 (s_pc ss + bv_signed imm))
                        (mem_denot E base (s_log ss)) rom
                    rw [btgt_lit]
                obtain ⟨msB, hmsB, hstB⟩ := ih dirs' rds _ _ _ hex hstA
                refine ⟨msB, .mst_step _ _ _ rfl ?_ hmsB, hstB⟩
                cases t
                · exact step_branch_ft_gen segs regs _ _ rom w c rs1 rs2 imm hf he hd hc
                · exact step_branch_tk_gen segs regs _ _ rom w c rs1 rs2 imm hf he hd hc
            · split at hex
              · rename_i ss2 scs2 rds2 hstep
                obtain ⟨pre, hpre⟩ := sym_exec_acc segs f dirs rds2 ss2 (scs2 ++ acc)
                rw [hex] at hpre
                have hpre' : scs = pre ++ (scs2 ++ acc) := hpre
                subst hpre'
                have hsc2 : scs_denot segs base E scs2 :=
                  (scs_denot_app segs base E _ _ (scs_denot_app segs base E _ _ hsc).2).1
                obtain ⟨msA, hstepA, hstA⟩ :=
                  sym_step_sound segs E base rom ss ms i ss2 scs2 w rds rds2 hf he hd hstep
                    hsc2 hst
                obtain ⟨msB, hmsB, hstB⟩ := ih dirs rds2 ss2 (scs2 ++ acc) msA hex hstA
                obtain ⟨regs, hms, _, _⟩ := hst
                refine ⟨msB, .mst_step _ _ _ ?_ hstepA hmsB, hstB⟩
                rw [hms]
                rfl
              · exact hstop hex

/-- Rocq's `sym_exec_msteps`: `sym_exec_sound` from an empty accumulator. -/
theorem sym_exec_msteps (segs : List Segment) (fuel : Nat) (dirs : List Bool)
    (rds : List expr) (ss ss' : sym_state) (scs : List sidecond) (E : env)
    (base rom : word → Option byte) (ms : machine_state)
    (hex : sym_exec segs fuel dirs rds ss [] = (ss', scs))
    (hsc : scs_denot segs base E scs)
    (hst : st_ok E base rom ss ms) :
    ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' := by
  exact sym_exec_sound segs fuel dirs rds ss [] ss' scs E base rom ms hex hsc hst

/-- Rocq's `sym_exec_ex`: `sym_exec_sound` with `st_ok` unfolded once, so the
exit register file is the existential's witness and the exit machine state is
spelled out.  `log_flat` is not exported. -/
theorem sym_exec_ex (segs : List Segment) (fuel : Nat) (dirs : List Bool)
    (rds : List expr) (ss : sym_state) (acc : List sidecond) (ss' : sym_state)
    (scs : List sidecond) (E : env) (base rom : word → Option byte) (ms : machine_state)
    (hex : sym_exec segs fuel dirs rds ss acc = (ss', scs))
    (hsc : scs_denot segs base E scs)
    (hst : st_ok E base rom ss ms) :
    ∃ R, regs_ok E (s_regs ss') R ∧
      msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom) := by
  obtain ⟨ms', hms, R, heq, hregs, _⟩ :=
    sym_exec_sound segs fuel dirs rds ss acc ss' scs E base rom ms hex hsc hst
  exact ⟨R, hregs, heq ▸ hms⟩

end LinuxProcessSemantics.Common.SymExec
