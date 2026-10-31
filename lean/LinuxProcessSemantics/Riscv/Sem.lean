import LinuxProcessSemantics.Riscv.Instr

/-! # Sem: the abstract RV64 semantics, as a first-order effect tree

Mirrors `theories/Riscv/Sem.v`.  The semantics is a plain function

    exec : word → instr → core → eff

from a decoded instruction and the CORE state (registers, FP registers,
pc, fcsr, LR/SC reservation) to a finite, first-order tree of residual
effects.  Only the operations this semantics deliberately does NOT
interpret appear as tree nodes: the memory boundary (`ELoad`/`EStore`),
the process/hardware split (`EEcall`/`EEbreak`), the model declining
(`EIllegal`), the architecture defining a trap (`EFault`,
`EDefinedIllegal`), and retirement (`EDone`).  See the Rocq header for
the full contract; what matters for an interpreter is the PC-ADVANCE
CONTRACT: `exec sz i` reads pc once, and every non-control-flow
instruction's resulting core carries `pc := pc + sz`; `EFault` and
`EDefinedIllegal` carry the PRE-state (nothing retires); `EIllegal` from
`step` on an undecodable fetch carries pc NOT advanced.

NOT YET PORTED (each answers `EIllegal cn`, the model declining, which
`RiscvSemantics.interp_eff` turns into `MachineUnmodeled` — fail closed):
the F/D arms (`FLoad`, `FStore`, `Fma`, `Fari`, `Fsqrt`, `Fsgnj`,
`Fminmax`, `Fcmp`, `Fcvt`, `Fmv`, `Fclass`), because `Fpu.v` rests on
Flocq and floating point stays unmodeled in Lean for now.  The decoder
does not produce them either (`Decode.decode`), so the arm is
unreachable today; it is written so that porting the decoder alone does
not silently change the answer. -/


namespace LinuxProcessSemantics.Riscv.Sem

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr

/-! ## Pure helpers -/

def w0 : word := Z_to_bv 64 0
def w1 : word := Z_to_bv 64 1
def low32 (v : word) : BitVec 32 := bv_extract 0 32 v
def is_x0 (r : reg) : Bool := r.toNat = 0

/-- Integer ALU at any width.  Shift amounts are masked to the low
`log2 n` bits (6 for n=64, 5 for n=32), per the ISA; `shmask` is that
mask. -/
def alu {n : Nat} (shmask : Int) (op : aluop) (a b : BitVec n) : BitVec n :=
  match op with
  | .ALU_ADD => a + b
  | .ALU_SUB => a - b
  | .ALU_SLL => a <<< (bv_and b (Z_to_bv n shmask)).toNat
  | .ALU_SLT => if bv_lts a b then Z_to_bv n 1 else Z_to_bv n 0
  | .ALU_SLTU => if bv_ltu a b then Z_to_bv n 1 else Z_to_bv n 0
  | .ALU_XOR => bv_xor a b
  | .ALU_SRL => a >>> (bv_and b (Z_to_bv n shmask)).toNat
  | .ALU_SRA => bv_ashiftr a (bv_and b (Z_to_bv n shmask))
  | .ALU_OR => bv_or a b
  | .ALU_AND => bv_and a b

def alu64 : aluop → word → word → word := alu 63
def alu32 : aluop → BitVec 32 → BitVec 32 → BitVec 32 := alu 31

def branch_taken (c : branch_cond) (a b : word) : Bool :=
  match c with
  | .BC_EQ => bv_eqb a b
  | .BC_NE => !(bv_eqb a b)
  | .BC_LT => bv_lts a b
  | .BC_GE => !(bv_lts a b)
  | .BC_LTU => bv_ltu a b
  | .BC_GEU => !(bv_ltu a b)

/-- M extension at any width; MULH* shift the exact product right by the
width.  RISC-V division is TRUNCATING (`bv_quots`/`bv_rems`).  Division by
zero: div/divu = all ones, rem/remu = the dividend.  Signed overflow
(min / -1) needs no special case: the quotient wraps back to min and the
remainder is 0. -/
def mul_div {n : Nat} (op : mulop) (a b : BitVec n) : BitVec n :=
  let div0 := b.toNat = 0
  match op with
  | .M_MUL => a * b
  | .M_MULH => bv_mulhss a b
  | .M_MULHSU => bv_mulhsu a b
  | .M_MULHU => bv_mulhuu a b
  | .M_DIV => if div0 then Z_to_bv n (-1) else bv_quots a b
  | .M_DIVU => if div0 then Z_to_bv n (-1) else bv_divu a b
  | .M_REM => if div0 then a else bv_rems a b
  | .M_REMU => if div0 then a else bv_modu a b

/-- Natural alignment for the A extension: lr/sc/amo at an address that is
not naturally aligned to the operand width (4 for .w, 8 for .d) traps
(`EFault`, the SIGBUS analogue).  The check runs FIRST, before sc consults
its reservation; see the Rocq note and
`bugs/riscv-misaligned-sc-nonmatching.md`. -/
def amo_bytes (wd : awidth) : Int :=
  match wd with | .AW => 4 | .AD => 8

def amo_aligned (wd : awidth) (a : word) : Bool :=
  bv_unsigned a % amo_bytes wd = 0

/-- AMO combine function (`old` is the memory value). -/
def amo_val {n : Nat} (op : amoop) (old src : BitVec n) : BitVec n :=
  match op with
  | .AMO_SWAP => src
  | .AMO_ADD => old + src
  | .AMO_XOR => bv_xor old src
  | .AMO_AND => bv_and old src
  | .AMO_OR => bv_or old src
  | .AMO_MIN => if bv_lts old src then old else src
  | .AMO_MAX => if bv_lts old src then src else old
  | .AMO_MINU => if bv_ltu old src then old else src
  | .AMO_MAXU => if bv_ltu old src then src else old

/-! ## Read-only CSR addresses

The CSR address encodes its own writability: csr[11:10] = 11 is read-only,
and a write to such an address raises an illegal-instruction exception in
every conforming implementation (RISC-V unprivileged spec, CSR Address
Mapping Conventions).  That is a property of the ADDRESS alone, so it is
defined-illegal in the same sense `DecodeC.is_defined_illegal` uses on the
decode side, and not a gap in this model's CSR map.  GNU as's `unimp`
(0xc0001073 = csrrw x0, cycle, x0) is a death rather than a decline for
exactly this reason.  The privilege-level rule (csr[9:8]) is deliberately
NOT taken: it is a fact about the executing hart. -/
def csr_read_only (csr : BitVec 12) : Bool :=
  (csr.toNat >>> 10) &&& 3 = 3

/-- The write side of a CSR instruction is architecturally illegal exactly
when it happens at all and the address is read-only. -/
def csr_write_illegal (writes : Bool) (csr : BitVec 12) : Bool :=
  writes && csr_read_only csr

/-- CSR address map: only the fcsr aliases exist; each is a (lo, len)
slice of the stored 32-bit fcsr.  0x001 = fflags = fcsr[4:0],
0x002 = frm = fcsr[7:5], 0x003 = fcsr itself (low 8 bits). -/
def csr_slice (csr : BitVec 12) : Option (Nat × Nat) :=
  let c := csr.toNat
  if c = 1 then some (0, 5)
  else if c = 2 then some (5, 3)
  else if c = 3 then some (0, 8)
  else none

/-- The new fault arm cannot swallow an instruction this model used to
answer: every address `csr_slice` resolves is read/write. -/
theorem csr_read_only_unimplemented (csr : BitVec 12) :
    csr_read_only csr = true → csr_slice csr = none := by
  intro h
  unfold csr_slice
  unfold csr_read_only at h
  by_cases h1 : csr.toNat = 1
  · rw [h1] at h; simp at h
  by_cases h2 : csr.toNat = 2
  · rw [h2] at h; simp at h
  by_cases h3 : csr.toNat = 3
  · rw [h3] at h; simp at h
  simp [h1, h2, h3]

/-- Rocq: `Z_to_bv 64 (Z.land (Z.shiftr f lo) (Z.ones len))`, written with
`Nat` bit operations (the value is non-negative). -/
def slice_get (f : BitVec 32) (lo len : Nat) : word :=
  BitVec.ofNat 64 ((f.toNat >>> lo) &&& (2 ^ len - 1))

/-- Rocq: `Z_to_bv 32 (Z.lor (Z.land f (Z.lnot mask)) (Z.land (Z.shiftl v lo) mask))`
with `mask = Z.shiftl (Z.ones len) lo`; the complement is taken inside 32
bits, which is all `Z_to_bv 32` keeps. -/
def slice_set (f : BitVec 32) (lo len : Nat) (v : word) : BitVec 32 :=
  let mask := (2 ^ len - 1) <<< lo
  BitVec.ofNat 32 ((f.toNat &&& ((2 ^ 32 - 1) ^^^ mask)) ||| ((v.toNat <<< lo) &&& mask))

/-! ## Core state: what the ISA owns -/

structure core where
  Core ::
  c_regs : bvmap 5 word
  c_fregs : bvmap 5 word
  c_pc : word
  c_fcsr : BitVec 32
  c_resv : Option word

-- Hand-written field updaters (extraction-friendly in Rocq; kept for the
-- names).
def with_regs (f : bvmap 5 word → bvmap 5 word) (c : core) : core :=
  core.Core (f c.c_regs) c.c_fregs c.c_pc c.c_fcsr c.c_resv
def with_fregs (f : bvmap 5 word → bvmap 5 word) (c : core) : core :=
  core.Core c.c_regs (f c.c_fregs) c.c_pc c.c_fcsr c.c_resv
def with_pc (v : word) (c : core) : core :=
  core.Core c.c_regs c.c_fregs v c.c_fcsr c.c_resv
def with_fcsr (v : BitVec 32) (c : core) : core :=
  core.Core c.c_regs c.c_fregs c.c_pc v c.c_resv
def with_resv (v : Option word) (c : core) : core :=
  core.Core c.c_regs c.c_fregs c.c_pc c.c_fcsr v

/-- Register stores are dumb `bvmap`s; missing keys read as 0. -/
def reg_get (rm : bvmap 5 word) (r : reg) : word :=
  match bvmap_get r rm with | some v => v | none => w0

/-- x0 hardwiring: reads 0, writes discarded. -/
def rget (c : core) (r : reg) : word :=
  if is_x0 r then w0 else reg_get c.c_regs r
def rset (r : reg) (v : word) (c : core) : core :=
  if is_x0 r then c else with_regs (bvmap_set r v) c

def fget (c : core) (r : reg) : word := reg_get c.c_fregs r
def fset (r : reg) (v : word) (c : core) : core :=
  with_fregs (bvmap_set r v) c

/-- fcsr[7:5] is frm, the DYNAMIC rounding mode. -/
def frm_of (c : core) : Nat := (c.c_fcsr.toNat >>> 5) &&& 7

/-- A store or AMO from this hart to the reserved address invalidates the
LR/SC reservation.  The access base address is compared exactly. -/
def inval_resv (a : word) (c : core) : core :=
  match c.c_resv with
  | some r => if r.toNat = a.toNat then with_resv none c else c
  | none => c

/-! ## The effect tree -/

inductive eff : Type
  | EDone (c : core)
  | EIllegal (c : core)
  | EDefinedIllegal (c : core)
  | EEcall (c : core)
  | EEbreak (c : core)
  | EFault (c : core)
  | ELoad (n : Nat) (a : word) (k : BitVec n → eff)
  | EStore (n : Nat) (a : word) (v : BitVec n) (k : eff)

open eff

/-- Load a value of size `sz`: the interpreter answers with the `n` bits at
`a` assembled little-endian; signed loads sign-extend, unsigned
zero-extend (for SZ8 both are the identity). -/
def load_val (sz : msize) (sgn : Bool) (a : word) (k : word → eff) : eff :=
  match sz with
  | .SZ1 => ELoad 8 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ2 => ELoad 16 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ4 => ELoad 32 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ8 => ELoad 64 a k

def store_val (sz : msize) (a : word) (v : word) (k : eff) : eff :=
  match sz with
  | .SZ1 => EStore 8 a (bv_extract 0 8 v) k
  | .SZ2 => EStore 16 a (bv_extract 0 16 v) k
  | .SZ4 => EStore 32 a (low32 v) k
  | .SZ8 => EStore 64 a v k

/-- CSR access.  `writes` says whether the write side happens.  The read
ALWAYS happens.  Unknown CSR addresses are `EIllegal` (with pc already
advanced).  A write to a read-only address never reaches here: `exec`
rejects it first, with `EDefinedIllegal` and the un-advanced core. -/
def exec_csr (op : csrop) (rd : reg) (operand : word)
    (writes : Bool) (csr : BitVec 12) (c : core) : eff :=
  match csr_slice csr with
  | none => EIllegal c
  | some (lo, len) =>
      let f := c.c_fcsr
      let old := slice_get f lo len
      let newv :=
        match op with
        | .CSR_RW => operand
        | .CSR_RS => bv_or old operand
        | .CSR_RC => bv_and old (bv_not operand)
      EDone (rset rd old
               (if writes then with_fcsr (slice_set f lo len newv) c else c))

/-! ## The semantics

Execute one already-decoded instruction, including the pc update.  `sz` is
the encoded size (2 for expanded compressed instructions, else 4): it
determines both the pc advance and the jal/jalr link value.  A direct
transcription of `Sem.v`'s `exec`, arm for arm and in the same order up
to `CsrI`; the eleven F/D arms that follow in Rocq are folded into one
`EIllegal` arm here. -/
def exec (sz : word) (i : instr) (c : core) : eff :=
  let pc := c.c_pc
  let npc := pc + sz
  let cn := with_pc npc c   -- pc advanced past the instruction
  match i with
  -- RV64I
  | .Lui rd imm =>
      EDone (rset rd (sext 64 (imm ++ (Z_to_bv 12 0))) cn)
  | .Auipc rd imm =>
      EDone (rset rd (pc + sext 64 (imm ++ (Z_to_bv 12 0))) cn)
  | .Jal rd imm =>
      EDone (rset rd npc (with_pc (pc + sext 64 imm) c))
  | .Jalr rd rs1 imm =>
      -- Target computed before the link write: rd may equal rs1.
      let a := rget c rs1
      EDone (rset rd npc (with_pc (bv_and (a + sext 64 imm) (bv_not w1)) c))
  | .Branch bc rs1 rs2 imm =>
      EDone (with_pc (if branch_taken bc (rget c rs1) (rget c rs2)
                      then pc + sext 64 imm else npc) c)
  | .Load msz sgn rd rs1 imm =>
      load_val msz sgn (rget c rs1 + sext 64 imm)
        (fun v => EDone (rset rd v cn))
  | .Store msz rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm
      store_val msz a (rget c rs2) (EDone (inval_resv a cn))
  | .OpImm op rd rs1 imm =>
      EDone (rset rd (alu64 op (rget c rs1) (sext 64 imm)) cn)
  | .ShiftImm op rd rs1 shamt =>
      EDone (rset rd (alu64 op (rget c rs1) (zext 64 shamt)) cn)
  | .Op op rd rs1 rs2 =>
      EDone (rset rd (alu64 op (rget c rs1) (rget c rs2)) cn)
  | .OpImm32 rd rs1 imm =>
      EDone (rset rd (sext 64 (alu32 .ALU_ADD (low32 (rget c rs1)) (sext 32 imm))) cn)
  | .ShiftImm32 op rd rs1 shamt =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (zext 32 shamt))) cn)
  | .Op32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | .Fence _ _ _ _ _ | .FenceI _ _ _ =>
      EDone cn   -- single hart: fences are no-ops
  | .Ecall => EEcall cn
  | .Ebreak => EEbreak cn
  -- M
  | .Mul op rd rs1 rs2 =>
      EDone (rset rd (mul_div op (rget c rs1) (rget c rs2)) cn)
  -- Operands are truncated to 32 bits BEFORE the divide, per the ISA.
  | .Mul32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (mul_div op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  -- A: sequential single-hart model, composed from plain memory ops.
  | .Lr wd _ _ rd rs1 =>
      let a := rget c rs1
      if !(amo_aligned wd a) then EFault c
      else match wd with
      | .AW => ELoad 32 a (fun v =>
                EDone (with_resv (some a) (rset rd (sext 64 v) cn)))
      | .AD => ELoad 64 a (fun v =>
                EDone (with_resv (some a) (rset rd v cn)))
  | .Sc wd _ _ rd rs1 rs2 =>
      let a := rget c rs1
      -- Alignment first, before the reservation.
      if !(amo_aligned wd a) then EFault c
      else
      let ok : Bool := match c.c_resv with
                | some r => decide (r.toNat = a.toNat)
                | none => false
      let c1 := with_resv none cn
      if ok then
        (match wd with
         | .AW => EStore 32 a (low32 (rget c rs2))
         | .AD => EStore 64 a (rget c rs2)) (EDone (rset rd w0 c1))
      else EDone (rset rd w1 c1)
  | .Amo op wd _ _ rd rs1 rs2 =>
      let a := rget c rs1
      if !(amo_aligned wd a) then EFault c
      else
      let src := rget c rs2
      let c1 := inval_resv a cn
      match wd with
      | .AW => ELoad 32 a (fun old =>
                EStore 32 a (amo_val op old (low32 src))
                  (EDone (rset rd (sext 64 old) c1)))
      | .AD => ELoad 64 a (fun old =>
                EStore 64 a (amo_val op old src)
                  (EDone (rset rd old c1)))
  -- Zicsr.  The architectural read-only check runs on the PRE-state core
  -- `c`: nothing retires when it fires.
  | .Csr op rd rs1 csr =>
      let writes := match op with | .CSR_RW => true | _ => !(is_x0 rs1)
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (rget c rs1) writes csr cn
  | .CsrI op rd uimm csr =>
      let writes :=
        match op with
        | .CSR_RW => true
        | _ => !(uimm.toNat = 0)
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (zext 64 uimm) writes csr cn
  -- F/D: NOT YET PORTED (floating point stays unmodeled in Lean).  The
  -- model declines, with pc advanced as the in-`exec` `EIllegal`s do.
  | .FLoad _ _ _ _ | .FStore _ _ _ _ | .Fmv _ _ _ _ | .Fsgnj _ _ _ _ _
  | .Fari _ _ _ _ _ _ | .Fsqrt _ _ _ _ | .Fma _ _ _ _ _ _ _
  | .Fminmax _ _ _ _ _ | .Fcmp _ _ _ _ _ | .Fclass _ _ _ | .Fcvt _ _ _ _ _ =>
      EIllegal cn

/-- Fetch, decode, dispatch.  `decode_any` is supplied by the driver and
returns the decoded instruction with its size in bytes.  On an undecodable
word we issue `EIllegal` with pc NOT advanced. -/
def step (decode_any : BitVec 32 → Option (instr × Int)) (c : core) : eff :=
  ELoad 32 c.c_pc (fun w32 =>
    match decode_any w32 with
    | some (i, isz) => exec (Z_to_bv 64 isz) i c
    | none => EIllegal c)

/-! ## Pins for the CSR classification

Stated as booleans because `eff` and `core` carry functions and have no
decidable equality; a `true` here is the kernel evaluating `exec`. -/

/-- A core with every register 0 and pc 0. -/
def core0 : core := core.Core bvmap_empty bvmap_empty (Z_to_bv 64 0) (Z_to_bv 32 0) none

def eff_is_defined_illegal : eff → Bool
  | .EDefinedIllegal _ => true
  | _ => false
def eff_is_illegal : eff → Bool
  | .EIllegal _ => true
  | _ => false
def eff_is_done : eff → Bool
  | .EDone _ => true
  | _ => false

-- `unimp` = csrrw x0, cycle, x0 (0xc0001073): a write to a read-only
-- address is the architecture's death, not the model's decline.
example : eff_is_defined_illegal (exec (Z_to_bv 64 4) (.Csr .CSR_RW 0 0 0xc00) core0) = true := by decide
-- `csrr t0, cycle` (csrrs t0, cycle, x0): the read side alone is legal
-- and the model declines it — cycle is not in its CSR map.
example : eff_is_illegal (exec (Z_to_bv 64 4) (.Csr .CSR_RS 5 0 0xc00) core0) = true := by decide
example : eff_is_defined_illegal (exec (Z_to_bv 64 4) (.Csr .CSR_RS 5 0 0xc00) core0) = false := by decide
-- fcsr (0x003) is read/write: csrrw retires.
example : eff_is_done (exec (Z_to_bv 64 4) (.Csr .CSR_RW 5 6 0x003) core0) = true := by decide
-- csrrwi always writes, so a read-only address dies even with uimm = 0.
example : eff_is_defined_illegal (exec (Z_to_bv 64 4) (.CsrI .CSR_RW 0 0 0xc00) core0) = true := by decide
-- csrrsi with uimm = 0 does not write: the read-only address is a decline.
example : eff_is_illegal (exec (Z_to_bv 64 4) (.CsrI .CSR_RS 5 0 0xc00) core0) = true := by decide

end LinuxProcessSemantics.Riscv.Sem
