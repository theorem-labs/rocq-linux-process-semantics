import LinuxProcessSemantics.Riscv.Instr

/-! # Decode: the 32-bit RV64IMA_Zicsr_Zifencei decoder

Mirrors `theories/Riscv/Decode.v`, arm for arm, with the F/D opcodes NOT
YET PORTED: LOAD-FP (0x07), STORE-FP (0x27), the FMA group and OP-FP (0x53)
decode to `none` here where Rocq decodes them, so a floating-point
instruction is `MachineUnmodeled` on the Lean side (fail closed; see
`lean/README.md`, "What is not yet ported").

`decode w = none` means "not a valid 32-bit instruction"; the intent is to
match binutils objdump byte-for-byte (an objdump differential validates
the Rocq decoder; the Lean one is pinned to it by the examples at the end
and, later, by the isa-check backend).

Immediates are kept at their encoded width, sign bit included (see
`Instr`); no sign extension happens here. -/


namespace LinuxProcessSemantics.Riscv.Decode

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr

section fields
variable (w : BitVec 32)

/-- Register fields. -/
def f_rd  : reg := bits 7 5 w
def f_rs1 : reg := bits 15 5 w
def f_rs2 : reg := bits 20 5 w
def f_rs3 : reg := bits 27 5 w

/-- Immediates, reassembled at encoded width. -/
def imm_i : BitVec 12 := bits 20 12 w
def imm_s : BitVec 12 := bits 25 7 w ++ bits 7 5 w
def imm_b : BitVec 13 :=
  bits 31 1 w ++ (bits 7 1 w ++ (bits 25 6 w ++ (bits 8 4 w ++ (0 : BitVec 1))))
def imm_u : BitVec 20 := bits 12 20 w
def imm_j : BitVec 21 :=
  bits 31 1 w ++ (bits 12 8 w ++ (bits 20 1 w ++ (bits 21 10 w ++ (0 : BitVec 1))))
end fields

def decode (w : BitVec 32) : Option instr :=
  let opc := (bits 0 7 w).toNat
  let rd  := f_rd w
  let f3  := (bits 12 3 w).toNat
  let rs1 := f_rs1 w
  let rs2 := f_rs2 w
  let f7  := (bits 25 7 w).toNat
  match opc with
  -- Words whose low two bits are not 11 fall through to `none` below, as
  -- do the 48-bit-and-up prefixes (bits[4:2] = 111).
  | 0x37 => some (.Lui rd (imm_u w))
  | 0x17 => some (.Auipc rd (imm_u w))
  | 0x6F => some (.Jal rd (imm_j w))
  | 0x67 => if f3 = 0 then some (.Jalr rd rs1 (imm_i w)) else none
  | 0x63 => -- BRANCH
      let br (c : branch_cond) := some (instr.Branch c rs1 rs2 (imm_b w))
      match f3 with
      | 0 => br .BC_EQ  | 1 => br .BC_NE
      | 4 => br .BC_LT  | 5 => br .BC_GE
      | 6 => br .BC_LTU | 7 => br .BC_GEU
      | _ => none
  | 0x03 => -- LOAD; funct3 = 7 (an "ldu") does not exist
      let ld (sz : msize) (sg : Bool) := some (instr.Load sz sg rd rs1 (imm_i w))
      match f3 with
      | 0 => ld .SZ1 true  | 1 => ld .SZ2 true
      | 2 => ld .SZ4 true  | 3 => ld .SZ8 true
      | 4 => ld .SZ1 false | 5 => ld .SZ2 false | 6 => ld .SZ4 false
      | _ => none
  | 0x23 => -- STORE
      let st (sz : msize) := some (instr.Store sz rs1 rs2 (imm_s w))
      match f3 with
      | 0 => st .SZ1 | 1 => st .SZ2 | 2 => st .SZ4 | 3 => st .SZ8
      | _ => none
  | 0x13 => -- OP-IMM; RV64 shifts have 6-bit shamt (bit 25 may be set)
      let oi (op : aluop) := some (instr.OpImm op rd rs1 (imm_i w))
      let sh := bits 20 6 w
      match f3 with
      | 0 => oi .ALU_ADD | 2 => oi .ALU_SLT | 3 => oi .ALU_SLTU
      | 4 => oi .ALU_XOR | 6 => oi .ALU_OR  | 7 => oi .ALU_AND
      | 1 => -- slli: bits[31:26] must be 000000
          if (bits 26 6 w).toNat = 0
          then some (.ShiftImm .ALU_SLL rd rs1 sh) else none
      | 5 =>
          match (bits 26 6 w).toNat with
          | 0x00 => some (.ShiftImm .ALU_SRL rd rs1 sh)
          | 0x10 => some (.ShiftImm .ALU_SRA rd rs1 sh)
          | _ => none
      | _ => none
  | 0x1B => -- OP-IMM-32; 5-bit shamt, bit 25 must be 0 (checked via funct7)
      let sh5 := bits 20 5 w
      match f3 with
      | 0 => some (.OpImm32 rd rs1 (imm_i w))
      | 1 => if f7 = 0 then some (.ShiftImm32 .ALU_SLL rd rs1 sh5) else none
      | 5 =>
          match f7 with
          | 0x00 => some (.ShiftImm32 .ALU_SRL rd rs1 sh5)
          | 0x20 => some (.ShiftImm32 .ALU_SRA rd rs1 sh5)
          | _ => none
      | _ => none
  | 0x33 => -- OP: funct7 checked exactly (0x00 / 0x20 / 0x01 = M)
      let op (o : aluop) := some (instr.Op o rd rs1 rs2)
      let ml (o : mulop) := some (instr.Mul o rd rs1 rs2)
      match f7, f3 with
      | 0x00, 0 => op .ALU_ADD | 0x20, 0 => op .ALU_SUB
      | 0x00, 1 => op .ALU_SLL
      | 0x00, 2 => op .ALU_SLT | 0x00, 3 => op .ALU_SLTU
      | 0x00, 4 => op .ALU_XOR
      | 0x00, 5 => op .ALU_SRL | 0x20, 5 => op .ALU_SRA
      | 0x00, 6 => op .ALU_OR  | 0x00, 7 => op .ALU_AND
      | 0x01, 0 => ml .M_MUL    | 0x01, 1 => ml .M_MULH
      | 0x01, 2 => ml .M_MULHSU | 0x01, 3 => ml .M_MULHU
      | 0x01, 4 => ml .M_DIV    | 0x01, 5 => ml .M_DIVU
      | 0x01, 6 => ml .M_REM    | 0x01, 7 => ml .M_REMU
      | _, _ => none
  | 0x3B => -- OP-32; the M subset here is only mulw/divw/divuw/remw/remuw
      let op (o : aluop) := some (instr.Op32 o rd rs1 rs2)
      let ml (o : mulop) := some (instr.Mul32 o rd rs1 rs2)
      match f7, f3 with
      | 0x00, 0 => op .ALU_ADD | 0x20, 0 => op .ALU_SUB
      | 0x00, 1 => op .ALU_SLL
      | 0x00, 5 => op .ALU_SRL | 0x20, 5 => op .ALU_SRA
      | 0x01, 0 => ml .M_MUL
      | 0x01, 4 => ml .M_DIV   | 0x01, 5 => ml .M_DIVU
      | 0x01, 6 => ml .M_REM   | 0x01, 7 => ml .M_REMU
      | _, _ => none
  | 0x0F => -- MISC-MEM.  Empirically (binutils 2.4x objdump, rv64):
            -- fence requires rd = rs1 = 0, and either fm = 0 (any pred/succ)
            -- or the exact fm=8, pred=succ=rw combination (fence.tso); all
            -- other fm/field combinations are rejected.  fence.i decodes
            -- only as the exact word 0x0000100f.
      match f3 with
      | 0 =>
          if rd.toNat = 0 && rs1.toNat = 0
             && ((bits 28 4 w).toNat = 0 || (bits 20 12 w).toNat = 0x833)
          then some (.Fence (bits 28 4 w) (bits 24 4 w) (bits 20 4 w) rd rs1)
          else none
      | 1 =>
          if w.toNat = 0x0000100F then some (.FenceI rd rs1 (imm_i w)) else none
      | _ => none
  | 0x73 => -- SYSTEM
      match f3 with
      | 0 => -- Only ecall/ebreak; privileged instructions are out of scope.
          match w.toNat with
          | 0x00000073 => some .Ecall
          | 0x00100073 => some .Ebreak
          | _ => none
      | 1 => some (.Csr .CSR_RW rd rs1 (bits 20 12 w))
      | 2 => some (.Csr .CSR_RS rd rs1 (bits 20 12 w))
      | 3 => some (.Csr .CSR_RC rd rs1 (bits 20 12 w))
      | 5 => some (.CsrI .CSR_RW rd rs1 (bits 20 12 w))
      | 6 => some (.CsrI .CSR_RS rd rs1 (bits 20 12 w))
      | 7 => some (.CsrI .CSR_RC rd rs1 (bits 20 12 w))
      | _ => none  -- funct3 = 4
  | 0x2F => -- AMO
      let aq := bit 26 w
      let rl := bit 25 w
      let go (aw : awidth) :=
        let am (o : amoop) := some (instr.Amo o aw aq rl rd rs1 rs2)
        match (bits 27 5 w).toNat with
        | 0x00 => am .AMO_ADD
        | 0x01 => am .AMO_SWAP
        | 0x02 => -- lr: rs2 must be 0 (binutils rejects rs2 <> 0)
            if rs2.toNat = 0 then some (.Lr aw aq rl rd rs1) else none
        | 0x03 => some (.Sc aw aq rl rd rs1 rs2)
        | 0x04 => am .AMO_XOR
        | 0x08 => am .AMO_OR
        | 0x0C => am .AMO_AND
        | 0x10 => am .AMO_MIN
        | 0x14 => am .AMO_MAX
        | 0x18 => am .AMO_MINU
        | 0x1C => am .AMO_MAXU
        | _ => none
      match f3 with | 2 => go .AW | 3 => go .AD | _ => none
  -- NOT YET PORTED (fail closed): 0x07 LOAD-FP, 0x27 STORE-FP,
  -- 0x43/0x47/0x4B/0x4F the FMA group, 0x53 OP-FP.  Rocq decodes them;
  -- here they are `none`, so `RiscvSemantics.step` answers
  -- `MachineUnmodeled` for every F/D instruction.
  | _ => none

/-! ## Sanity checks against known encodings

The same encodings `Decode.v` pins with `vm_compute`. -/

example : decode 0x00000013 = some (.OpImm .ALU_ADD 0 0 0) := by decide  -- addi x0,x0,0 = nop
example : decode 0x00c58533 = some (.Op .ALU_ADD 10 11 12) := by decide   -- add a0,a1,a2
example : decode 0xfe0796e3 = some (.Branch .BC_NE 15 0 (Z_to_bv 13 (-20))) := by decide -- bnez a5, .-20
example : decode 0x00153513 = some (.OpImm .ALU_SLTU 10 10 1) := by decide -- sltiu a0,a0,1 = seqz
example : decode 0x02b4d53b = some (.Mul32 .M_DIVU 10 9 11) := by decide  -- divuw a0,s1,a1
example : decode 0x140536af = some (.Lr .AD true false 13 10) := by decide -- lr.d.aq a3,(a0)
-- SYSTEM: ecall/ebreak decode; uret (privileged) does not
example : decode 0x00000073 = some .Ecall := by decide
example : decode 0x00100073 = some .Ebreak := by decide
example : decode 0x00200073 = none := by decide
example : decode 0x0ff0000f = some (.Fence 0 15 15 0 0) := by decide  -- fence iorw,iorw
example : decode 0x8330000f = some (.Fence 8 3 3 0 0) := by decide    -- fence.tso
example : decode 0x0000100f = some (.FenceI 0 0 0) := by decide       -- fence.i
-- binutils rejects fence/fence.i with nonzero reserved fields
example : decode 0x00a0100f = none := by decide
example : decode 0x0ff0080f = none := by decide
example : decode 0x8120000f = none := by decide
example : decode 0x341022f3 = some (.Csr .CSR_RS 5 0 0x341) := by decide -- csrrs t0,mepc,zero
-- fcvt.s.s / fcvt.d.d are illegal (in Rocq by the OP-FP arm; here the whole opcode is `none`)
example : decode 0x40058553 = none := by decide
example : decode 0x42158553 = none := by decide
-- One pin per immediate/format the exit demo does not reach.
example : decode 0x12345537 = some (.Lui 10 0x12345) := by decide            -- lui a0,0x12345
example : decode 0x00000517 = some (.Auipc 10 0) := by decide                -- auipc a0,0
example : decode 0x008000ef = some (.Jal 1 8) := by decide                   -- jal ra,+8
example : decode 0x000500e7 = some (.Jalr 1 10 0) := by decide               -- jalr ra,0(a0)
example : decode 0x00412503 = some (.Load .SZ4 true 10 2 4) := by decide     -- lw a0,4(sp)
example : decode 0x0005c503 = some (.Load .SZ1 false 10 11 0) := by decide   -- lbu a0,0(a1)
example : decode 0x00013503 = some (.Load .SZ8 true 10 2 0) := by decide     -- ld a0,0(sp)
example : decode 0xfea12e23 = some (.Store .SZ4 2 10 (Z_to_bv 12 (-4))) := by decide -- sw a0,-4(sp)
example : decode 0x00351513 = some (.ShiftImm .ALU_SLL 10 10 3) := by decide  -- slli a0,a0,3
example : decode 0x43f55513 = some (.ShiftImm .ALU_SRA 10 10 63) := by decide -- srai a0,a0,63
example : decode 0x0015051b = some (.OpImm32 10 10 1) := by decide           -- addiw a0,a0,1
example : decode 0x4015551b = some (.ShiftImm32 .ALU_SRA 10 10 1) := by decide -- sraiw a0,a0,1
example : decode 0x00c5853b = some (.Op32 .ALU_ADD 10 11 12) := by decide    -- addw a0,a1,a2
example : decode 0x02c58533 = some (.Mul .M_MUL 10 11 12) := by decide       -- mul a0,a1,a2
example : decode 0x18c5a52f = some (.Sc .AW false false 10 11 12) := by decide -- sc.w a0,a2,(a1)
example : decode 0x00c5b52f = some (.Amo .AMO_ADD .AD false false 10 11 12) := by decide -- amoadd.d a0,a2,(a1)
example : decode 0x0032d573 = some (.CsrI .CSR_RW 10 5 3) := by decide       -- csrrwi a0,fcsr,5
-- The rejections the arms above make: bad funct7, bad load funct3, a
-- set reserved shamt bit, a bad OP-IMM-32 funct7, jalr with funct3 <> 0,
-- lr with rs2 <> 0.
example : decode 0x40c59533 = none := by decide   -- funct7 = 0x20 with funct3 = 1
example : decode 0x00007003 = none := by decide   -- load funct3 = 7
example : decode 0x04051513 = none := by decide   -- slli with bit 26 set
example : decode 0x43f5551b = none := by decide   -- sraiw with bit 25 set (funct7 = 0x21)
example : decode 0x00051067 = none := by decide   -- jalr funct3 = 1
example : decode 0x10c5a52f = none := by decide   -- lr.w with rs2 = a2
-- Low 2 bits <> 11: never a valid 32-bit instruction
example : decode 0x00000001 = none := by decide
example : decode 0x0000852a = none := by decide
-- The exit-0 demo's three words (Checks/Examples): addi a7,x0,93; addi a0,x0,0; ecall
example : decode 0x05d00893 = some (.OpImm .ALU_ADD 17 0 93) := by decide
example : decode 0x00000513 = some (.OpImm .ALU_ADD 10 0 0) := by decide
-- NOT YET PORTED: an F instruction Rocq decodes (fadd.s fa0,fa1,fa2,rne) is
-- `none` here.  This pin is what a port of the F/D arms must flip.
example : decode 0x00c58553 = none := by decide

end LinuxProcessSemantics.Riscv.Decode
