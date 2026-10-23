(** * DecodeC: the RV64C compressed (16-bit) decoder.

    Compressed instructions get their own AST [cinstr] (one constructor
    per instruction, fields at encoded width) and are expanded into the
    base [instr] AST by [expand_c], so the execution semantics is written
    once.  Immediate fields of [cinstr] are stored *scaled* (as byte
    offsets / actual values, sign bit included) since the RVC scaling is
    a pure encoding artifact.

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
    - Reserved encodings return None: c.addi4spn nzuimm=0, c.addiw
      rd=0, c.addi16sp nzimm=0, c.lui nzimm=0, c.lwsp/c.ldsp rd=0,
      c.jr rs1=0, the bit12=1 subw-group funct2 2/3.  binutils 2.40
      prints c.addi16sp nzimm=0 (0x6101) as "c.addi16sp sp,0", so a
      comparison with that objdump must special-case it. *)

From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.

(** Map a 3-bit compressed register field to x8..x15. *)
Definition creg (r : bv 3) : reg := bv_concat 5 (1 : bv 2) r.

Inductive cinstr : Type :=
(* Quadrant 0 *)
| CAddi4spn (rd' : bv 3) (nzuimm : bv 10)     (* addi rd', x2, nzuimm *)
| CFld (rd' rs1' : bv 3) (uimm : bv 8)
| CLw  (rd' rs1' : bv 3) (uimm : bv 7)
| CLd  (rd' rs1' : bv 3) (uimm : bv 8)
| CFsd (rs1' rs2' : bv 3) (uimm : bv 8)
| CSw  (rs1' rs2' : bv 3) (uimm : bv 7)
| CSd  (rs1' rs2' : bv 3) (uimm : bv 8)
(* Quadrant 1 *)
| CAddi (rd : reg) (imm : bv 6)               (* c.nop = CAddi x0 0 *)
| CAddiw (rd : reg) (imm : bv 6)
| CLi (rd : reg) (imm : bv 6)
| CAddi16sp (imm : bv 10)                     (* addi x2, x2, imm (×16) *)
| CLui (rd : reg) (imm : bv 6)
| CSrli (rd' : bv 3) (shamt : bv 6)
| CSrai (rd' : bv 3) (shamt : bv 6)
| CAndi (rd' : bv 3) (imm : bv 6)
| CSub (rd' rs2' : bv 3) | CXor (rd' rs2' : bv 3)
| COr  (rd' rs2' : bv 3) | CAnd (rd' rs2' : bv 3)
| CSubw (rd' rs2' : bv 3) | CAddw (rd' rs2' : bv 3)
| CJ (imm : bv 12)
| CBeqz (rs1' : bv 3) (imm : bv 9)
| CBnez (rs1' : bv 3) (imm : bv 9)
(* Quadrant 2 *)
| CSlli (rd : reg) (shamt : bv 6)
| CFldsp (rd : reg) (uimm : bv 9)
| CLwsp (rd : reg) (uimm : bv 8)
| CLdsp (rd : reg) (uimm : bv 9)
| CJr (rs1 : reg)
| CMv (rd rs2 : reg)
| CEbreak
| CJalr (rs1 : reg)
| CAdd (rd rs2 : reg)
| CFsdsp (rs2 : reg) (uimm : bv 9)
| CSwsp (rs2 : reg) (uimm : bv 8)
| CSdsp (rs2 : reg) (uimm : bv 9).

#[global] Instance cinstr_eq_dec : EqDecision cinstr.
Proof. solve_decision. Defined.

Definition decode16 (h : bv 16) : option cinstr :=
  let f3 := bv_unsigned (bits 13 3 h) in
  let r1c := bits 7 3 h in   (* rs1'/rd' *)
  let r2c := bits 2 3 h in   (* rs2'/rd' *)
  let rd  := bits 7 5 h in   (* full-width rd/rs1 *)
  let rs2 := bits 2 5 h in   (* full-width rs2 *)
  (* Common immediates *)
  let imm6 : bv 6 := bv_concat 6 (bits 12 1 h) (bits 2 5 h) in
  let uimm_d : bv 8 :=  (* c.fld/c.ld/c.fsd/c.sd: ×8 *)
    bv_concat 8 (bits 5 2 h) (bv_concat 6 (bits 10 3 h) (0 : bv 3)) in
  let uimm_w : bv 7 :=  (* c.lw/c.sw: ×4 *)
    bv_concat 7 (bits 5 1 h)
      (bv_concat 6 (bits 10 3 h) (bv_concat 3 (bits 6 1 h) (0 : bv 2))) in
  match bv_unsigned (bits 0 2 h), f3 with
  (* ---- Quadrant 0 ---- *)
  | 0, 0 =>
      (* c.addi4spn; nzuimm = 0 is reserved (covers the all-zero
         halfword 0x0000, which must be illegal) *)
      let nzuimm : bv 10 :=
        bv_concat 10 (bits 7 4 h)
          (bv_concat 6 (bits 11 2 h)
            (bv_concat 4 (bits 5 1 h)
              (bv_concat 3 (bits 6 1 h) (0 : bv 2)))) in
      if decide (bv_unsigned nzuimm = 0%Z) then None
      else Some (CAddi4spn r2c nzuimm)
  | 0, 1 => Some (CFld r2c r1c uimm_d)
  | 0, 2 => Some (CLw r2c r1c uimm_w)
  | 0, 3 => Some (CLd r2c r1c uimm_d)   (* RV64: c.ld, not c.flw *)
  | 0, 5 => Some (CFsd r1c r2c uimm_d)
  | 0, 6 => Some (CSw r1c r2c uimm_w)
  | 0, 7 => Some (CSd r1c r2c uimm_d)
  (* ---- Quadrant 1 ---- *)
  | 1, 0 => Some (CAddi rd imm6)        (* incl. c.nop and hints *)
  | 1, 1 => (* RV64: c.addiw (RV32's c.jal); rd = 0 reserved *)
      if decide (bv_unsigned rd = 0%Z) then None else Some (CAddiw rd imm6)
  | 1, 2 => Some (CLi rd imm6)          (* rd = 0 is a hint; decode it *)
  | 1, 3 =>
      if decide (bv_unsigned rd = 2%Z) then
        (* c.addi16sp: nzimm[9|8:7|6|5|4] at h[12|4:3|5|2|6], ×16.
           nzimm = 0 is reserved by the ISA spec, and QEMU user mode
           raises an illegal-instruction exception for it
           (target/riscv/insn16.decode: "c.addi16sp and c.lui, RES
           nzimm=0").  Decline it, like every other reserved encoding
           here, rather than run it as addi sp, sp, 0. *)
        let imm : bv 10 :=
          bv_concat 10 (bits 12 1 h)
            (bv_concat 9 (bits 3 2 h)
              (bv_concat 7 (bits 5 1 h)
                (bv_concat 6 (bits 2 1 h)
                  (bv_concat 5 (bits 6 1 h) (0 : bv 4))))) in
        if decide (bv_unsigned imm = 0%Z) then None else Some (CAddi16sp imm)
      else
        (* c.lui; imm = 0 reserved.  rd = 0 is a hint — we decode it
           (POLICY: check binutils' printing of the rd=0 hint form). *)
        if decide (bv_unsigned imm6 = 0%Z) then None else Some (CLui rd imm6)
  | 1, 4 =>
      match bv_unsigned (bits 10 2 h) with
      | 0 => Some (CSrli r1c imm6)  (* shamt = 0 is a hint; decode it *)
      | 1 => Some (CSrai r1c imm6)
      | 2 => Some (CAndi r1c imm6)
      | _ => (* 3: register-register group *)
          match bit 12 h, bv_unsigned (bits 5 2 h) with
          | false, 0 => Some (CSub r1c r2c)
          | false, 1 => Some (CXor r1c r2c)
          | false, 2 => Some (COr r1c r2c)
          | false, _ => Some (CAnd r1c r2c)
          | true, 0 => Some (CSubw r1c r2c)
          | true, 1 => Some (CAddw r1c r2c)
          | true, _ => None  (* reserved *)
          end
      end
  | 1, 5 => (* c.j: imm[11|4|9:8|10|6|7|3:1|5] at h[12|11|10:9|8|7|6|5:3|2] *)
      Some (CJ (bv_concat 12 (bits 12 1 h)
        (bv_concat 11 (bits 8 1 h)
          (bv_concat 10 (bits 9 2 h)
            (bv_concat 8 (bits 6 1 h)
              (bv_concat 7 (bits 7 1 h)
                (bv_concat 6 (bits 2 1 h)
                  (bv_concat 5 (bits 11 1 h)
                    (bv_concat 4 (bits 3 3 h) (0 : bv 1))))))))))
  | 1, 6 | 1, 7 => (* c.beqz/c.bnez: imm[8|4:3|7:6|2:1|5] at h[12|11:10|6:5|4:3|2] *)
      let imm : bv 9 :=
        bv_concat 9 (bits 12 1 h)
          (bv_concat 8 (bits 5 2 h)
            (bv_concat 6 (bits 2 1 h)
              (bv_concat 5 (bits 10 2 h)
                (bv_concat 3 (bits 3 2 h) (0 : bv 1))))) in
      if decide (f3 = 6%Z) then Some (CBeqz r1c imm) else Some (CBnez r1c imm)
  (* ---- Quadrant 2 ---- *)
  | 2, 0 => Some (CSlli rd imm6)        (* rd = 0 / shamt = 0: hints *)
  | 2, 1 => (* c.fldsp: uimm[5|4:3|8:6] at h[12|6:5|4:2], ×8 *)
      Some (CFldsp rd (bv_concat 9 (bits 2 3 h)
        (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 5 2 h) (0 : bv 3)))))
  | 2, 2 => (* c.lwsp: uimm[5|4:2|7:6] at h[12|6:4|3:2], ×4; rd = 0 reserved *)
      if decide (bv_unsigned rd = 0%Z) then None
      else Some (CLwsp rd (bv_concat 8 (bits 2 2 h)
        (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 4 3 h) (0 : bv 2)))))
  | 2, 3 => (* c.ldsp; rd = 0 reserved *)
      if decide (bv_unsigned rd = 0%Z) then None
      else Some (CLdsp rd (bv_concat 9 (bits 2 3 h)
        (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 5 2 h) (0 : bv 3)))))
  | 2, 4 =>
      match bit 12 h, decide (bv_unsigned rs2 = 0%Z) with
      | false, left _ => (* c.jr; rs1 = 0 reserved *)
          if decide (bv_unsigned rd = 0%Z) then None else Some (CJr rd)
      | false, right _ => Some (CMv rd rs2)   (* rd = 0 hint; decode *)
      | true, left _ =>
          if decide (bv_unsigned rd = 0%Z) then Some CEbreak
          else Some (CJalr rd)
      | true, right _ => Some (CAdd rd rs2)   (* rd = 0 hint; decode *)
      end
  | 2, 5 => (* c.fsdsp: uimm[5:3|8:6] at h[12:10|9:7], ×8 *)
      Some (CFsdsp rs2 (bv_concat 9 (bits 7 3 h)
        (bv_concat 6 (bits 10 3 h) (0 : bv 3))))
  | 2, 6 => (* c.swsp: uimm[5:2|7:6] at h[12:9|8:7], ×4 *)
      Some (CSwsp rs2 (bv_concat 8 (bits 7 2 h)
        (bv_concat 6 (bits 9 4 h) (0 : bv 2))))
  | 2, 7 => (* c.sdsp *)
      Some (CSdsp rs2 (bv_concat 9 (bits 7 3 h)
        (bv_concat 6 (bits 10 3 h) (0 : bv 3))))
  (* Quadrant 3 = low bits 11: a 32-bit instruction, not compressed. *)
  | _, _ => None
  end%Z.

(** ** Expansion into the base AST (total). *)

Definition x0 : reg := 0.
Definition x1 : reg := 1.
Definition x2 : reg := 2.

Definition expand_c (c : cinstr) : instr :=
  match c with
  | CAddi4spn rd' nzuimm => OpImm ALU_ADD (creg rd') x2 (zext 12 nzuimm)
  | CFld rd' rs1' uimm => FLoad FMT_D (creg rd') (creg rs1') (zext 12 uimm)
  | CLw rd' rs1' uimm => Load SZ4 true (creg rd') (creg rs1') (zext 12 uimm)
  | CLd rd' rs1' uimm => Load SZ8 true (creg rd') (creg rs1') (zext 12 uimm)
  | CFsd rs1' rs2' uimm => FStore FMT_D (creg rs1') (creg rs2') (zext 12 uimm)
  | CSw rs1' rs2' uimm => Store SZ4 (creg rs1') (creg rs2') (zext 12 uimm)
  | CSd rs1' rs2' uimm => Store SZ8 (creg rs1') (creg rs2') (zext 12 uimm)
  | CAddi rd imm => OpImm ALU_ADD rd rd (sext 12 imm)
  | CAddiw rd imm => OpImm32 rd rd (sext 12 imm)
  | CLi rd imm => OpImm ALU_ADD rd x0 (sext 12 imm)
  | CAddi16sp imm => OpImm ALU_ADD x2 x2 (sext 12 imm)  (* imm is ×16 already *)
  | CLui rd imm => Lui rd (sext 20 imm)   (* 6-bit nzimm sexts into U-imm *)
  | CSrli rd' sh => ShiftImm ALU_SRL (creg rd') (creg rd') sh
  | CSrai rd' sh => ShiftImm ALU_SRA (creg rd') (creg rd') sh
  | CAndi rd' imm => OpImm ALU_AND (creg rd') (creg rd') (sext 12 imm)
  | CSub rd' rs2' => Op ALU_SUB (creg rd') (creg rd') (creg rs2')
  | CXor rd' rs2' => Op ALU_XOR (creg rd') (creg rd') (creg rs2')
  | COr rd' rs2' => Op ALU_OR (creg rd') (creg rd') (creg rs2')
  | CAnd rd' rs2' => Op ALU_AND (creg rd') (creg rd') (creg rs2')
  | CSubw rd' rs2' => Op32 ALU_SUB (creg rd') (creg rd') (creg rs2')
  | CAddw rd' rs2' => Op32 ALU_ADD (creg rd') (creg rd') (creg rs2')
  | CJ imm => Jal x0 (sext 21 imm)
  | CBeqz rs1' imm => Branch BC_EQ (creg rs1') x0 (sext 13 imm)
  | CBnez rs1' imm => Branch BC_NE (creg rs1') x0 (sext 13 imm)
  | CSlli rd sh => ShiftImm ALU_SLL rd rd sh
  | CFldsp rd uimm => FLoad FMT_D rd x2 (zext 12 uimm)
  | CLwsp rd uimm => Load SZ4 true rd x2 (zext 12 uimm)
  | CLdsp rd uimm => Load SZ8 true rd x2 (zext 12 uimm)
  | CJr rs1 => Jalr x0 rs1 0
  | CMv rd rs2 => Op ALU_ADD rd x0 rs2
  | CEbreak => Ebreak
  | CJalr rs1 => Jalr x1 rs1 0
  | CAdd rd rs2 => Op ALU_ADD rd rd rs2
  | CFsdsp rs2 uimm => FStore FMT_D x2 rs2 (zext 12 uimm)
  | CSwsp rs2 uimm => Store SZ4 x2 rs2 (zext 12 uimm)
  | CSdsp rs2 uimm => Store SZ8 x2 rs2 (zext 12 uimm)
  end.

(** Driver convenience: decode either width from a 32-bit fetch.
    Returns the instruction and its length in bytes (2 or 4). *)
Definition decode_any (w : bv 32) : option (instr * Z) :=
  if decide (bv_unsigned (bits 0 2 w) = 3%Z) then
    match decode w with
    | Some i => Some (i, 4%Z)
    | None => None
    end
  else
    match decode16 (bits 0 16 w) with
    | Some c => Some (expand_c c, 2%Z)
    | None => None
    end.

(** ** Architecturally defined-illegal encodings

    [decode_any] returning [None] covers two different kinds of word:
    bit patterns this decoder does not model (reserved or unallocated
    encoding space, which a future extension may claim), and the one
    pattern the unprivileged ISA DEFINES to be an illegal instruction in
    every implementation, under every extension: an instruction whose
    bits [15:0] are all zeros ("Encodings with bits [15:0] all zeros are
    defined as illegal instructions" -- RISC-V unprivileged spec,
    Expanded Instruction-Length Encoding).  Fetching such a parcel
    raises an illegal-instruction trap on real hardware; under Linux the
    process takes SIGILL.

    [is_defined_illegal] recognizes exactly that pattern, and is
    deliberately conservative about everything else: reserved opcode
    space, prefixes announcing encodings longer than 32 bits (including
    the all-ones parcel -- the spec makes all-ones illegal only across
    all ILEN bits, which a 32-bit window cannot see), and HINT-adjacent
    code points are all NOT defined-illegal.  Only the upper halfword of
    [w] is ignored: an all-zero low parcel is a complete 16-bit illegal
    instruction on its own, whatever follows it. *)
Definition is_defined_illegal (w : bv 32) : bool :=
  bool_decide (bv_unsigned (bits 0 16 w) = 0%Z).

(** ** Sanity checks (via [bool_decide]; see the note in Decode.v). *)

(* The all-zero halfword is illegal *)
Goal decode16 0x0000 = None. Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x4108 (* c.lw a0,0(a0) *)
  = Some (CLw 2 2 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (expand_c (CLw 2 2 0) = Load SZ4 true 10 10 0) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x0001 (* c.nop = c.addi x0,0 *)
  = Some (CAddi 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x852a (* c.mv a0,a0 *)
  = Some (CMv 10 10)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x8082 (* c.jr ra = ret *)
  = Some (CJr 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (expand_c (CJr 1) = Jalr 0 1 0) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x9002 = Some CEbreak) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x1141 (* c.addi sp,-16 *)
  = Some (CAddi 2 (Z_to_bv 6 (-16)))) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0xe022 (* c.sdsp s0,0(sp) *)
  = Some (CSdsp 8 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x6505 (* c.lui a0,0x1 *)
  = Some (CLui 10 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (expand_c (CLui 10 1) = Lui 10 1) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode16 0x7139 (* c.addi16sp sp,-64 *)
  = Some (CAddi16sp (Z_to_bv 10 (-64)))) = true.
Proof. vm_compute. reflexivity. Qed.
(* c.addi16sp with nzimm = 0 is reserved *)
Goal decode16 0x6101 = None. Proof. vm_compute. reflexivity. Qed.
(* Low bits 11: not a compressed instruction *)
Goal decode16 0x0013 = None. Proof. vm_compute. reflexivity. Qed.
(* decode_any picks the right width *)
Goal bool_decide (decode_any 0x00000013
  = Some (OpImm ALU_ADD 0 0 0, 4%Z)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode_any 0x00008082 = Some (Jalr 0 1 0, 2%Z)) = true.
Proof. vm_compute. reflexivity. Qed.

(* Defined-illegal: exactly the all-zero low parcel, upper bits ignored *)
Goal is_defined_illegal 0x00000000 = true. Proof. vm_compute. reflexivity. Qed.
Goal is_defined_illegal 0xffff0000 = true. Proof. vm_compute. reflexivity. Qed.
(* ...and nothing decode_any accepts, nor merely-reserved space *)
Goal is_defined_illegal 0x00000013 = false. Proof. vm_compute. reflexivity. Qed.
Goal is_defined_illegal 0x00000001 = false. Proof. vm_compute. reflexivity. Qed.
Goal is_defined_illegal 0xffffffff = false. Proof. vm_compute. reflexivity. Qed.
(* A defined-illegal word is (a fortiori) undecodable *)
Goal decode_any 0x00000000 = None. Proof. vm_compute. reflexivity. Qed.
Goal decode_any 0xffff0000 = None. Proof. vm_compute. reflexivity. Qed.
