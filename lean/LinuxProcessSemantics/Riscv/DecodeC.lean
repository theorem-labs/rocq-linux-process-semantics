import LinuxProcessSemantics.Riscv.Decode

/-! # DecodeC: compressed (RVC) decoding and the any-width entry point

Mirrors `theories/Riscv/DecodeC.v`.  Only the two entry points the machine
layer consumes are here; the 16-bit decoder (`decode16`, `expand_c`, the
`cinstr` AST) is NOT YET PORTED, so `decode_any` answers `none` for every
compressed parcel and `RiscvSemantics.step` treats it as `MachineUnmodeled`
(fail closed).  `is_defined_illegal` is ported in full: it decides which
undecodable words are a FAULT rather than a gap, and that classification
must agree with Rocq's exactly. -/


namespace LinuxProcessSemantics.Riscv.DecodeC

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Decode

/-- Decode a fetched 32-bit word at either width: a 32-bit instruction when
the low two bits are `11`, else a compressed one (NOT YET PORTED: `none`).
Returns the instruction with its size in bytes — always 4 until the
compressed half lands, 2 for an expanded compressed instruction then. -/
def decode_any (w : BitVec 32) : Option (instr × Int) :=
  if (bits 0 2 w).toNat = 3 then
    match decode w with
    | some i => some (i, 4)
    | none => none
  else
    none  -- NOT YET PORTED: decode16 (bits 0 16 w) >>= expand_c, size 2

/-- The one undecodable pattern the ISA pins as illegal in EVERY
implementation: an all-zero low parcel.  Real hardware traps and Linux
delivers SIGILL, so `RiscvSemantics.decode_exec` classifies it as
`MachineFault` rather than `MachineUnmodeled`. -/
def is_defined_illegal (w : BitVec 32) : Bool :=
  (bits 0 16 w).toNat = 0

-- decode_any picks the right width (the 32-bit half).
example : decode_any 0x00000013 = some (.OpImm .ALU_ADD 0 0 0, 4) := by decide
-- NOT YET PORTED: `c.ret` (0x8082), which Rocq decodes as
-- `Some (Jalr 0 1 0, 2)`, is `none` here.  This pin is what the DecodeC
-- port must flip.
example : decode_any 0x00008082 = none := by decide
example : is_defined_illegal 0x00000000 = true := by decide
example : is_defined_illegal 0xffff0000 = true := by decide
-- ...and nothing decode_any accepts, nor merely-reserved space
example : is_defined_illegal 0x00000013 = false := by decide
example : is_defined_illegal 0x00000001 = false := by decide
example : is_defined_illegal 0xffffffff = false := by decide
example : decode_any 0x00000000 = none := by decide
example : decode_any 0xffff0000 = none := by decide

end LinuxProcessSemantics.Riscv.DecodeC
