-- Ports rocq-linux-process-semantics f1006fe8:theories/Riscv/Instr.v
import LinuxProcessSemantics.Riscv.Prelude

/-! # Instr: the RV64GC base instruction AST

Mirrors `theories/Riscv/Instr.v`, constructor for constructor.

Immediates are kept at their *encoded* width with the sign bit included
(I/S: 12 bits, B: 13, U: 20, J: 21); interpretation is deferred to `Sem`.
Compressed instructions have their own AST in `DecodeC` and are expanded
into this one, so the execution semantics is written once. -/


namespace LinuxProcessSemantics.Riscv.Instr

open LinuxProcessSemantics.Riscv.Prelude

/-- Integer register-register ops (OP / OP-32 major opcodes). -/
inductive aluop : Type
  | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SLT | ALU_SLTU
  | ALU_XOR | ALU_SRL | ALU_SRA | ALU_OR | ALU_AND
  deriving DecidableEq, Repr

/-- M extension ops. -/
inductive mulop : Type
  | M_MUL | M_MULH | M_MULHSU | M_MULHU
  | M_DIV | M_DIVU | M_REM | M_REMU
  deriving DecidableEq, Repr

inductive branch_cond : Type
  | BC_EQ | BC_NE | BC_LT | BC_GE | BC_LTU | BC_GEU
  deriving DecidableEq, Repr

/-- Memory access sizes, in bytes. -/
inductive msize : Type
  | SZ1 | SZ2 | SZ4 | SZ8
  deriving DecidableEq, Repr

/-- A extension. -/
inductive amoop : Type
  | AMO_SWAP | AMO_ADD | AMO_XOR | AMO_AND | AMO_OR
  | AMO_MIN | AMO_MAX | AMO_MINU | AMO_MAXU
  deriving DecidableEq, Repr

/-- `.w` / `.d` -/
inductive awidth : Type
  | AW | AD
  deriving DecidableEq, Repr

/-- Zicsr. -/
inductive csrop : Type
  | CSR_RW | CSR_RS | CSR_RC
  deriving DecidableEq, Repr

/-- F/D formats and op groups. -/
inductive ffmt : Type
  | FMT_S | FMT_D
  deriving DecidableEq, Repr

inductive fariop : Type
  | F_ADD | F_SUB | F_MUL | F_DIV
  deriving DecidableEq, Repr
inductive fmaop : Type
  | F_MADD | F_MSUB | F_NMSUB | F_NMADD
  deriving DecidableEq, Repr
inductive fsgnop : Type
  | F_SGNJ | F_SGNJN | F_SGNJX
  deriving DecidableEq, Repr
inductive fminmaxop : Type
  | F_MIN | F_MAX
  deriving DecidableEq, Repr
inductive fcmpop : Type
  | F_EQ | F_LT | F_LE
  deriving DecidableEq, Repr

/-- Operand kind of an `Fcvt`: integer (32/64, signed/unsigned) or FP
format.  Decoding only produces the architecturally valid pairs. -/
inductive fcvt_ty : Type
  | FC_W | FC_WU | FC_L | FC_LU  -- integer targets/sources
  | FC_S | FC_D                  -- FP formats
  deriving DecidableEq, Repr

/-- fmv.x.w / fmv.w.x / fmv.x.d / fmv.d.x: direction of the raw move. -/
inductive fmvdir : Type
  | FMV_X_F | FMV_F_X
  deriving DecidableEq, Repr

inductive instr : Type
  -- RV32I / RV64I
  | Lui (rd : reg) (imm : BitVec 20)
  | Auipc (rd : reg) (imm : BitVec 20)
  | Jal (rd : reg) (imm : BitVec 21)               -- bit 0 of imm is always 0
  | Jalr (rd rs1 : reg) (imm : BitVec 12)
  | Branch (c : branch_cond) (rs1 rs2 : reg) (imm : BitVec 13)  -- bit 0 always 0
  | Load (sz : msize) (signed : Bool) (rd rs1 : reg) (imm : BitVec 12)
  | Store (sz : msize) (rs1 rs2 : reg) (imm : BitVec 12)  -- mem[rs1+imm] <- rs2
  | OpImm (op : aluop) (rd rs1 : reg) (imm : BitVec 12)
      -- addi/slti/sltiu/xori/ori/andi; never SUB/shift
  | ShiftImm (op : aluop) (rd rs1 : reg) (shamt : BitVec 6)   -- slli/srli/srai
  | Op (op : aluop) (rd rs1 rs2 : reg)
  | OpImm32 (rd rs1 : reg) (imm : BitVec 12)                  -- addiw
  | ShiftImm32 (op : aluop) (rd rs1 : reg) (shamt : BitVec 5) -- slliw/srliw/sraiw
  | Op32 (op : aluop) (rd rs1 rs2 : reg)  -- addw/subw/sllw/srlw/sraw
  | Fence (fm : BitVec 4) (pred succ : BitVec 4) (rd rs1 : reg)
  | FenceI (rd rs1 : reg) (imm : BitVec 12)
  | Ecall
  | Ebreak
  -- M
  | Mul (op : mulop) (rd rs1 rs2 : reg)
  | Mul32 (op : mulop) (rd rs1 rs2 : reg)  -- mulw/divw/divuw/remw/remuw
  -- A
  | Lr (w : awidth) (aq rl : Bool) (rd rs1 : reg)
  | Sc (w : awidth) (aq rl : Bool) (rd rs1 rs2 : reg)
  | Amo (op : amoop) (w : awidth) (aq rl : Bool) (rd rs1 rs2 : reg)
  -- Zicsr
  | Csr (op : csrop) (rd rs1 : reg) (csr : BitVec 12)
  | CsrI (op : csrop) (rd : reg) (uimm : BitVec 5) (csr : BitVec 12)
  -- F/D loads/stores (rd/rs2 name FP registers)
  | FLoad (fmt : ffmt) (rd rs1 : reg) (imm : BitVec 12)
  | FStore (fmt : ffmt) (rs1 rs2 : reg) (imm : BitVec 12)
  -- F/D computation
  | Fma (op : fmaop) (fmt : ffmt) (rd rs1 rs2 rs3 : reg) (rm : BitVec 3)
  | Fari (op : fariop) (fmt : ffmt) (rd rs1 rs2 : reg) (rm : BitVec 3)
  | Fsqrt (fmt : ffmt) (rd rs1 : reg) (rm : BitVec 3)
  | Fsgnj (op : fsgnop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fminmax (op : fminmaxop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fcmp (op : fcmpop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fcvt (dst src : fcvt_ty) (rd rs1 : reg) (rm : BitVec 3)
  | Fmv (dir : fmvdir) (fmt : ffmt) (rd rs1 : reg)
  | Fclass (fmt : ffmt) (rd rs1 : reg)
  deriving DecidableEq, Repr

def msize_bytes (sz : msize) : Int :=
  match sz with
  | .SZ1 => 1 | .SZ2 => 2 | .SZ4 => 4 | .SZ8 => 8

end LinuxProcessSemantics.Riscv.Instr
