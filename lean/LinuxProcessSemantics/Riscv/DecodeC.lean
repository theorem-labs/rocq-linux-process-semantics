-- Ports rocq-linux-process-semantics f1006fe8:theories/Riscv/DecodeC.v
import LinuxProcessSemantics.Riscv.Decode

/-! # DecodeC: the RV64C compressed (16-bit) decoder

Mirrors `theories/Riscv/DecodeC.v`, arm for arm.

Compressed instructions get their own AST `cinstr` (one constructor per
instruction, fields at encoded width) and are expanded into the base
`instr` AST by `expand_c`, so the execution semantics is written once.
Immediate fields of `cinstr` are stored *scaled* (as byte offsets / actual
values, sign bit included) since the RVC scaling is a pure encoding
artifact.

Policy notes for a comparison with objdump (all confirmed against
binutils objdump on rv64):
- HINT encodings decode, matching binutils: c.addi with imm=0
  (c.nop prints as "c.addi zero,0" under -M no-aliases), c.li /
  c.lui / c.mv / c.add with rd=0, c.slli with rd=0.
- Shifts with shamt=0 decode here as shamt-0 CSlli/CSrli/CSrai,
  but binutils prints them with the RV128 mnemonics c.slli64 /
  c.srli64 / c.srai64 — a comparison must special-case them.
- The all-zero halfword 0x0000 returns None here, but binutils
  prints it as "c.unimp" — a comparison must special-case it.
- Reserved encodings return None, matching binutils: c.addi4spn
  nzuimm=0, c.addiw rd=0, c.lui nzimm=0, c.lwsp/c.ldsp
  rd=0, c.jr rs1=0, the bit12=1 subw-group funct2 2/3.
  EXCEPTION: c.addi16sp nzimm=0 is reserved by the spec but
  binutils 2.40 accepts it, so we decode it (see below).

Two shape differences from the Rocq text, both computing the same result:
Rocq's `bv_concat m hi lo` names the result width `m`, which Lean derives
from the operand widths, so this file writes the concatenations with `++`
(as `Decode.lean` does); and Rocq's single `| 1, 6 | 1, 7` arm, which
builds the branch immediate once and then selects the constructor with
`decide (f3 = 6)`, is written here as two arms over the branch immediate
`imm_b9`, lifted into the `let` preamble. -/


namespace LinuxProcessSemantics.Riscv.DecodeC

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Decode

/-- Map a 3-bit compressed register field to x8..x15. -/
def creg (r : BitVec 3) : reg := (1 : BitVec 2) ++ r

inductive cinstr : Type
  -- Quadrant 0
  | CAddi4spn (rd' : BitVec 3) (nzuimm : BitVec 10)   -- addi rd', x2, nzuimm
  | CFld (rd' rs1' : BitVec 3) (uimm : BitVec 8)
  | CLw  (rd' rs1' : BitVec 3) (uimm : BitVec 7)
  | CLd  (rd' rs1' : BitVec 3) (uimm : BitVec 8)
  | CFsd (rs1' rs2' : BitVec 3) (uimm : BitVec 8)
  | CSw  (rs1' rs2' : BitVec 3) (uimm : BitVec 7)
  | CSd  (rs1' rs2' : BitVec 3) (uimm : BitVec 8)
  -- Quadrant 1
  | CAddi (rd : reg) (imm : BitVec 6)                 -- c.nop = CAddi x0 0
  | CAddiw (rd : reg) (imm : BitVec 6)
  | CLi (rd : reg) (imm : BitVec 6)
  | CAddi16sp (imm : BitVec 10)                       -- addi x2, x2, imm (×16)
  | CLui (rd : reg) (imm : BitVec 6)
  | CSrli (rd' : BitVec 3) (shamt : BitVec 6)
  | CSrai (rd' : BitVec 3) (shamt : BitVec 6)
  | CAndi (rd' : BitVec 3) (imm : BitVec 6)
  | CSub (rd' rs2' : BitVec 3) | CXor (rd' rs2' : BitVec 3)
  | COr  (rd' rs2' : BitVec 3) | CAnd (rd' rs2' : BitVec 3)
  | CSubw (rd' rs2' : BitVec 3) | CAddw (rd' rs2' : BitVec 3)
  | CJ (imm : BitVec 12)
  | CBeqz (rs1' : BitVec 3) (imm : BitVec 9)
  | CBnez (rs1' : BitVec 3) (imm : BitVec 9)
  -- Quadrant 2
  | CSlli (rd : reg) (shamt : BitVec 6)
  | CFldsp (rd : reg) (uimm : BitVec 9)
  | CLwsp (rd : reg) (uimm : BitVec 8)
  | CLdsp (rd : reg) (uimm : BitVec 9)
  | CJr (rs1 : reg)
  | CMv (rd rs2 : reg)
  | CEbreak
  | CJalr (rs1 : reg)
  | CAdd (rd rs2 : reg)
  | CFsdsp (rs2 : reg) (uimm : BitVec 9)
  | CSwsp (rs2 : reg) (uimm : BitVec 8)
  | CSdsp (rs2 : reg) (uimm : BitVec 9)
  deriving DecidableEq, Repr

/-- Rocq's `cinstr_eq_dec : EqDecision cinstr`, which `solve_decision`
builds; here the `deriving DecidableEq` clause above supplies it.  It is
named but not re-registered as an instance: the derived one is already
global, and a second registration would only add a redundant candidate. -/
def cinstr_eq_dec : DecidableEq cinstr := inferInstance

def decode16 (h : BitVec 16) : Option cinstr :=
  let f3 := (bits 13 3 h).toNat
  let r1c := bits 7 3 h   -- rs1'/rd'
  let r2c := bits 2 3 h   -- rs2'/rd'
  let rd  := bits 7 5 h   -- full-width rd/rs1
  let rs2 := bits 2 5 h   -- full-width rs2
  -- Common immediates
  let imm6 : BitVec 6 := (bits 12 1 h) ++ (bits 2 5 h)
  let uimm_d : BitVec 8 :=  -- c.fld/c.ld/c.fsd/c.sd: ×8
    (bits 5 2 h) ++ ((bits 10 3 h) ++ (0 : BitVec 3))
  let uimm_w : BitVec 7 :=  -- c.lw/c.sw: ×4
    (bits 5 1 h) ++ ((bits 10 3 h) ++ ((bits 6 1 h) ++ (0 : BitVec 2)))
  -- c.beqz/c.bnez: imm[8|4:3|7:6|2:1|5] at h[12|11:10|6:5|4:3|2]
  let imm_b9 : BitVec 9 :=
    (bits 12 1 h) ++ ((bits 5 2 h) ++ ((bits 2 1 h) ++
      ((bits 10 2 h) ++ ((bits 3 2 h) ++ (0 : BitVec 1)))))
  match (bits 0 2 h).toNat, f3 with
  -- ---- Quadrant 0 ----
  | 0, 0 =>
      -- c.addi4spn; nzuimm = 0 is reserved (covers the all-zero
      -- halfword 0x0000, which must be illegal)
      let nzuimm : BitVec 10 :=
        (bits 7 4 h) ++ ((bits 11 2 h) ++ ((bits 5 1 h) ++
          ((bits 6 1 h) ++ (0 : BitVec 2))))
      if nzuimm.toNat = 0 then none
      else some (.CAddi4spn r2c nzuimm)
  | 0, 1 => some (.CFld r2c r1c uimm_d)
  | 0, 2 => some (.CLw r2c r1c uimm_w)
  | 0, 3 => some (.CLd r2c r1c uimm_d)   -- RV64: c.ld, not c.flw
  | 0, 5 => some (.CFsd r1c r2c uimm_d)
  | 0, 6 => some (.CSw r1c r2c uimm_w)
  | 0, 7 => some (.CSd r1c r2c uimm_d)
  -- ---- Quadrant 1 ----
  | 1, 0 => some (.CAddi rd imm6)        -- incl. c.nop and hints
  | 1, 1 => -- RV64: c.addiw (RV32's c.jal); rd = 0 reserved
      if rd.toNat = 0 then none else some (.CAddiw rd imm6)
  | 1, 2 => some (.CLi rd imm6)          -- rd = 0 is a hint; decode it
  | 1, 3 =>
      if rd.toNat = 2 then
        -- c.addi16sp: nzimm[9|8:7|6|5|4] at h[12|4:3|5|2|6], ×16.
        -- nzimm = 0 is reserved by the ISA spec, but binutils 2.40
        -- ACCEPTS it (0x6101 prints "c.addi16sp sp,0"), so we decode
        -- it too, to match objdump.
        let imm : BitVec 10 :=
          (bits 12 1 h) ++ ((bits 3 2 h) ++ ((bits 5 1 h) ++
            ((bits 2 1 h) ++ ((bits 6 1 h) ++ (0 : BitVec 4)))))
        some (.CAddi16sp imm)
      else
        -- c.lui; imm = 0 reserved.  rd = 0 is a hint — we decode it
        -- (POLICY: check binutils' printing of the rd=0 hint form).
        if imm6.toNat = 0 then none else some (.CLui rd imm6)
  | 1, 4 =>
      match (bits 10 2 h).toNat with
      | 0 => some (.CSrli r1c imm6)  -- shamt = 0 is a hint; decode it
      | 1 => some (.CSrai r1c imm6)
      | 2 => some (.CAndi r1c imm6)
      | _ => -- 3: register-register group
          match bit 12 h, (bits 5 2 h).toNat with
          | false, 0 => some (.CSub r1c r2c)
          | false, 1 => some (.CXor r1c r2c)
          | false, 2 => some (.COr r1c r2c)
          | false, _ => some (.CAnd r1c r2c)
          | true, 0 => some (.CSubw r1c r2c)
          | true, 1 => some (.CAddw r1c r2c)
          | true, _ => none  -- reserved
  | 1, 5 => -- c.j: imm[11|4|9:8|10|6|7|3:1|5] at h[12|11|10:9|8|7|6|5:3|2]
      some (.CJ ((bits 12 1 h) ++ ((bits 8 1 h) ++ ((bits 9 2 h) ++
        ((bits 6 1 h) ++ ((bits 7 1 h) ++ ((bits 2 1 h) ++
          ((bits 11 1 h) ++ ((bits 3 3 h) ++ (0 : BitVec 1))))))))))
  | 1, 6 => some (.CBeqz r1c imm_b9)
  | 1, 7 => some (.CBnez r1c imm_b9)
  -- ---- Quadrant 2 ----
  | 2, 0 => some (.CSlli rd imm6)        -- rd = 0 / shamt = 0: hints
  | 2, 1 => -- c.fldsp: uimm[5|4:3|8:6] at h[12|6:5|4:2], ×8
      some (.CFldsp rd ((bits 2 3 h) ++
        ((bits 12 1 h) ++ ((bits 5 2 h) ++ (0 : BitVec 3)))))
  | 2, 2 => -- c.lwsp: uimm[5|4:2|7:6] at h[12|6:4|3:2], ×4; rd = 0 reserved
      if rd.toNat = 0 then none
      else some (.CLwsp rd ((bits 2 2 h) ++
        ((bits 12 1 h) ++ ((bits 4 3 h) ++ (0 : BitVec 2)))))
  | 2, 3 => -- c.ldsp; rd = 0 reserved
      if rd.toNat = 0 then none
      else some (.CLdsp rd ((bits 2 3 h) ++
        ((bits 12 1 h) ++ ((bits 5 2 h) ++ (0 : BitVec 3)))))
  | 2, 4 =>
      match bit 12 h, rs2.toNat with
      | false, 0 => -- c.jr; rs1 = 0 reserved
          if rd.toNat = 0 then none else some (.CJr rd)
      | false, _ => some (.CMv rd rs2)   -- rd = 0 hint; decode
      | true, 0 =>
          if rd.toNat = 0 then some .CEbreak
          else some (.CJalr rd)
      | true, _ => some (.CAdd rd rs2)   -- rd = 0 hint; decode
  | 2, 5 => -- c.fsdsp: uimm[5:3|8:6] at h[12:10|9:7], ×8
      some (.CFsdsp rs2 ((bits 7 3 h) ++ ((bits 10 3 h) ++ (0 : BitVec 3))))
  | 2, 6 => -- c.swsp: uimm[5:2|7:6] at h[12:9|8:7], ×4
      some (.CSwsp rs2 ((bits 7 2 h) ++ ((bits 9 4 h) ++ (0 : BitVec 2))))
  | 2, 7 => -- c.sdsp
      some (.CSdsp rs2 ((bits 7 3 h) ++ ((bits 10 3 h) ++ (0 : BitVec 3))))
  -- Quadrant 3 = low bits 11: a 32-bit instruction, not compressed.
  | _, _ => none

/-! ## Expansion into the base AST (total). -/

def x0 : reg := 0
def x1 : reg := 1
def x2 : reg := 2

/-- The expansion is total.  The four `FMT_D` arms (`c.fld`, `c.fsd`,
`c.fldsp`, `c.fsdsp`) produce `FLoad`/`FStore`, whose execution semantics
arrives with the FPU port; decoding them is complete regardless. -/
def expand_c (c : cinstr) : instr :=
  match c with
  | .CAddi4spn rd' nzuimm => .OpImm .ALU_ADD (creg rd') x2 (zext 12 nzuimm)
  | .CFld rd' rs1' uimm => .FLoad .FMT_D (creg rd') (creg rs1') (zext 12 uimm)
  | .CLw rd' rs1' uimm => .Load .SZ4 true (creg rd') (creg rs1') (zext 12 uimm)
  | .CLd rd' rs1' uimm => .Load .SZ8 true (creg rd') (creg rs1') (zext 12 uimm)
  | .CFsd rs1' rs2' uimm => .FStore .FMT_D (creg rs1') (creg rs2') (zext 12 uimm)
  | .CSw rs1' rs2' uimm => .Store .SZ4 (creg rs1') (creg rs2') (zext 12 uimm)
  | .CSd rs1' rs2' uimm => .Store .SZ8 (creg rs1') (creg rs2') (zext 12 uimm)
  | .CAddi rd imm => .OpImm .ALU_ADD rd rd (sext 12 imm)
  | .CAddiw rd imm => .OpImm32 rd rd (sext 12 imm)
  | .CLi rd imm => .OpImm .ALU_ADD rd x0 (sext 12 imm)
  | .CAddi16sp imm => .OpImm .ALU_ADD x2 x2 (sext 12 imm)  -- imm is ×16 already
  | .CLui rd imm => .Lui rd (sext 20 imm)   -- 6-bit nzimm sexts into U-imm
  | .CSrli rd' sh => .ShiftImm .ALU_SRL (creg rd') (creg rd') sh
  | .CSrai rd' sh => .ShiftImm .ALU_SRA (creg rd') (creg rd') sh
  | .CAndi rd' imm => .OpImm .ALU_AND (creg rd') (creg rd') (sext 12 imm)
  | .CSub rd' rs2' => .Op .ALU_SUB (creg rd') (creg rd') (creg rs2')
  | .CXor rd' rs2' => .Op .ALU_XOR (creg rd') (creg rd') (creg rs2')
  | .COr rd' rs2' => .Op .ALU_OR (creg rd') (creg rd') (creg rs2')
  | .CAnd rd' rs2' => .Op .ALU_AND (creg rd') (creg rd') (creg rs2')
  | .CSubw rd' rs2' => .Op32 .ALU_SUB (creg rd') (creg rd') (creg rs2')
  | .CAddw rd' rs2' => .Op32 .ALU_ADD (creg rd') (creg rd') (creg rs2')
  | .CJ imm => .Jal x0 (sext 21 imm)
  | .CBeqz rs1' imm => .Branch .BC_EQ (creg rs1') x0 (sext 13 imm)
  | .CBnez rs1' imm => .Branch .BC_NE (creg rs1') x0 (sext 13 imm)
  | .CSlli rd sh => .ShiftImm .ALU_SLL rd rd sh
  | .CFldsp rd uimm => .FLoad .FMT_D rd x2 (zext 12 uimm)
  | .CLwsp rd uimm => .Load .SZ4 true rd x2 (zext 12 uimm)
  | .CLdsp rd uimm => .Load .SZ8 true rd x2 (zext 12 uimm)
  | .CJr rs1 => .Jalr x0 rs1 0
  | .CMv rd rs2 => .Op .ALU_ADD rd x0 rs2
  | .CEbreak => .Ebreak
  | .CJalr rs1 => .Jalr x1 rs1 0
  | .CAdd rd rs2 => .Op .ALU_ADD rd rd rs2
  | .CFsdsp rs2 uimm => .FStore .FMT_D x2 rs2 (zext 12 uimm)
  | .CSwsp rs2 uimm => .Store .SZ4 x2 rs2 (zext 12 uimm)
  | .CSdsp rs2 uimm => .Store .SZ8 x2 rs2 (zext 12 uimm)

/-- Driver convenience: decode either width from a 32-bit fetch.
Returns the instruction and its length in bytes (2 or 4). -/
def decode_any (w : BitVec 32) : Option (instr × Int) :=
  if (bits 0 2 w).toNat = 3 then
    match decode w with
    | some i => some (i, 4)
    | none => none
  else
    match decode16 (bits 0 16 w) with
    | some c => some (expand_c c, 2)
    | none => none

/-! ## Architecturally defined-illegal encodings

`decode_any` returning `none` covers two different kinds of word: bit
patterns this decoder does not model (reserved or unallocated encoding
space, which a future extension may claim), and the one pattern the
unprivileged ISA DEFINES to be an illegal instruction in every
implementation, under every extension: an instruction whose bits [15:0]
are all zeros ("Encodings with bits [15:0] all zeros are defined as
illegal instructions" -- RISC-V unprivileged spec, Expanded
Instruction-Length Encoding).  Fetching such a parcel raises an
illegal-instruction trap on real hardware; under Linux the process takes
SIGILL.

`is_defined_illegal` recognizes exactly that pattern, and is deliberately
conservative about everything else: reserved opcode space, prefixes
announcing encodings longer than 32 bits (including the all-ones parcel
-- the spec makes all-ones illegal only across all ILEN bits, which a
32-bit window cannot see), and HINT-adjacent code points are all NOT
defined-illegal.  Only the upper halfword of `w` is ignored: an all-zero
low parcel is a complete 16-bit illegal instruction on its own, whatever
follows it. -/
def is_defined_illegal (w : BitVec 32) : Bool :=
  (bits 0 16 w).toNat = 0

/-! ## Sanity checks (see the note in `Decode.lean`). -/

-- The all-zero halfword is illegal
example : decode16 0x0000 = none := by decide
example : decode16 0x4108 /- c.lw a0,0(a0) -/ = some (.CLw 2 2 0) := by decide
example : expand_c (.CLw 2 2 0) = .Load .SZ4 true 10 10 0 := by decide
example : decode16 0x0001 /- c.nop = c.addi x0,0 -/ = some (.CAddi 0 0) := by decide
example : decode16 0x852a /- c.mv a0,a0 -/ = some (.CMv 10 10) := by decide
example : decode16 0x8082 /- c.jr ra = ret -/ = some (.CJr 1) := by decide
example : expand_c (.CJr 1) = .Jalr 0 1 0 := by decide
example : decode16 0x9002 = some .CEbreak := by decide
example : decode16 0x1141 /- c.addi sp,-16 -/
    = some (.CAddi 2 (Z_to_bv 6 (-16))) := by decide
example : decode16 0xe022 /- c.sdsp s0,0(sp) -/ = some (.CSdsp 8 0) := by decide
example : decode16 0x6505 /- c.lui a0,0x1 -/ = some (.CLui 10 1) := by decide
example : expand_c (.CLui 10 1) = .Lui 10 1 := by decide
example : decode16 0x7139 /- c.addi16sp sp,-64 -/
    = some (.CAddi16sp (Z_to_bv 10 (-64))) := by decide
-- Low bits 11: not a compressed instruction
example : decode16 0x0013 = none := by decide
-- decode_any picks the right width
example : decode_any 0x00000013 = some (.OpImm .ALU_ADD 0 0 0, 4) := by decide
example : decode_any 0x00008082 = some (.Jalr 0 1 0, 2) := by decide

-- Defined-illegal: exactly the all-zero low parcel, upper bits ignored
example : is_defined_illegal 0x00000000 = true := by decide
example : is_defined_illegal 0xffff0000 = true := by decide
-- ...and nothing decode_any accepts, nor merely-reserved space
example : is_defined_illegal 0x00000013 = false := by decide
example : is_defined_illegal 0x00000001 = false := by decide
example : is_defined_illegal 0xffffffff = false := by decide
-- A defined-illegal word is (a fortiori) undecodable
example : decode_any 0x00000000 = none := by decide
example : decode_any 0xffff0000 = none := by decide

end LinuxProcessSemantics.Riscv.DecodeC
