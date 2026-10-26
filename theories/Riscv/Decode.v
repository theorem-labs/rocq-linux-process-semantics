(** * Decode: the 32-bit RV64IMAFD_Zicsr_Zifencei decoder.

    [decode w = None] means "not a valid 32-bit instruction".  What counts
    as valid is the RISC-V specification (RV64GC) and QEMU user mode, the
    references SCOPE.md names for instructions.  binutils objdump is
    narrower in places; those cases are flagged inline as policy notes for
    a comparison with objdump.

    Immediates are kept at their encoded width, sign bit included
    (see Instr.v); no sign extension happens here. *)

From LinuxProcessSemantics.Riscv Require Import Prelude Instr.

Section fields.
  Context (w : bv 32).

  (** Register fields. *)
  Definition f_rd  : reg := bits 7 5 w.
  Definition f_rs1 : reg := bits 15 5 w.
  Definition f_rs2 : reg := bits 20 5 w.
  Definition f_rs3 : reg := bits 27 5 w.

  (** Immediates, reassembled at encoded width. *)
  Definition imm_i : bv 12 := bits 20 12 w.
  Definition imm_s : bv 12 := bv_concat 12 (bits 25 7 w) (bits 7 5 w).
  Definition imm_b : bv 13 :=
    bv_concat 13 (bits 31 1 w)
      (bv_concat 12 (bits 7 1 w)
        (bv_concat 11 (bits 25 6 w)
          (bv_concat 5 (bits 8 4 w) (0 : bv 1)))).
  Definition imm_u : bv 20 := bits 12 20 w.
  Definition imm_j : bv 21 :=
    bv_concat 21 (bits 31 1 w)
      (bv_concat 20 (bits 12 8 w)
        (bv_concat 12 (bits 20 1 w)
          (bv_concat 11 (bits 21 10 w) (0 : bv 1)))).
End fields.

Definition decode (w : bv 32) : option instr :=
  let opc := bv_unsigned (bits 0 7 w) in
  let rd  := f_rd w in
  let f3  := bv_unsigned (bits 12 3 w) in
  let rs1 := f_rs1 w in
  let rs2 := f_rs2 w in
  let f7  := bv_unsigned (bits 25 7 w) in
  let rm  : bv 3 := bits 12 3 w in
  match opc with
  (* Words whose low two bits are not 11 fall through to [None] below,
     as do the 48-bit-and-up prefixes (bits[4:2] = 111). *)
  | 0x37 => Some (Lui rd (imm_u w))
  | 0x17 => Some (Auipc rd (imm_u w))
  | 0x6F => Some (Jal rd (imm_j w))
  | 0x67 => if decide (f3 = 0%Z) then Some (Jalr rd rs1 (imm_i w)) else None
  | 0x63 => (* BRANCH *)
      let br c := Some (Branch c rs1 rs2 (imm_b w)) in
      match f3 with
      | 0 => br BC_EQ  | 1 => br BC_NE
      | 4 => br BC_LT  | 5 => br BC_GE
      | 6 => br BC_LTU | 7 => br BC_GEU
      | _ => None
      end
  | 0x03 => (* LOAD; funct3 = 7 (an "ldu") does not exist *)
      let ld sz sg := Some (Load sz sg rd rs1 (imm_i w)) in
      match f3 with
      | 0 => ld SZ1 true  | 1 => ld SZ2 true
      | 2 => ld SZ4 true  | 3 => ld SZ8 true
      | 4 => ld SZ1 false | 5 => ld SZ2 false | 6 => ld SZ4 false
      | _ => None
      end
  | 0x23 => (* STORE *)
      let st sz := Some (Store sz rs1 rs2 (imm_s w)) in
      match f3 with
      | 0 => st SZ1 | 1 => st SZ2 | 2 => st SZ4 | 3 => st SZ8
      | _ => None
      end
  | 0x13 => (* OP-IMM; RV64 shifts have 6-bit shamt (bit 25 may be set) *)
      let oi op := Some (OpImm op rd rs1 (imm_i w)) in
      let sh := bits 20 6 w in
      match f3 with
      | 0 => oi ALU_ADD | 2 => oi ALU_SLT | 3 => oi ALU_SLTU
      | 4 => oi ALU_XOR | 6 => oi ALU_OR  | 7 => oi ALU_AND
      | 1 => (* slli: bits[31:26] must be 000000 *)
          if decide (bv_unsigned (bits 26 6 w) = 0%Z)
          then Some (ShiftImm ALU_SLL rd rs1 sh) else None
      | 5 =>
          match bv_unsigned (bits 26 6 w) with
          | 0x00 => Some (ShiftImm ALU_SRL rd rs1 sh)
          | 0x10 => Some (ShiftImm ALU_SRA rd rs1 sh)
          | _ => None
          end
      | _ => None
      end
  | 0x1B => (* OP-IMM-32; 5-bit shamt, bit 25 must be 0 (checked via funct7) *)
      let sh5 := bits 20 5 w in
      match f3 with
      | 0 => Some (OpImm32 rd rs1 (imm_i w))
      | 1 => if decide (f7 = 0%Z)
             then Some (ShiftImm32 ALU_SLL rd rs1 sh5) else None
      | 5 =>
          match f7 with
          | 0x00 => Some (ShiftImm32 ALU_SRL rd rs1 sh5)
          | 0x20 => Some (ShiftImm32 ALU_SRA rd rs1 sh5)
          | _ => None
          end
      | _ => None
      end
  | 0x33 => (* OP: funct7 checked exactly (0x00 / 0x20 / 0x01 = M) *)
      let op o := Some (Op o rd rs1 rs2) in
      let ml o := Some (Mul o rd rs1 rs2) in
      match f7, f3 with
      | 0x00, 0 => op ALU_ADD | 0x20, 0 => op ALU_SUB
      | 0x00, 1 => op ALU_SLL
      | 0x00, 2 => op ALU_SLT | 0x00, 3 => op ALU_SLTU
      | 0x00, 4 => op ALU_XOR
      | 0x00, 5 => op ALU_SRL | 0x20, 5 => op ALU_SRA
      | 0x00, 6 => op ALU_OR  | 0x00, 7 => op ALU_AND
      | 0x01, 0 => ml M_MUL    | 0x01, 1 => ml M_MULH
      | 0x01, 2 => ml M_MULHSU | 0x01, 3 => ml M_MULHU
      | 0x01, 4 => ml M_DIV    | 0x01, 5 => ml M_DIVU
      | 0x01, 6 => ml M_REM    | 0x01, 7 => ml M_REMU
      | _, _ => None
      end
  | 0x3B => (* OP-32; the M subset here is only mulw/divw/divuw/remw/remuw *)
      let op o := Some (Op32 o rd rs1 rs2) in
      let ml o := Some (Mul32 o rd rs1 rs2) in
      match f7, f3 with
      | 0x00, 0 => op ALU_ADD | 0x20, 0 => op ALU_SUB
      | 0x00, 1 => op ALU_SLL
      | 0x00, 5 => op ALU_SRL | 0x20, 5 => op ALU_SRA
      | 0x01, 0 => ml M_MUL
      | 0x01, 4 => ml M_DIV   | 0x01, 5 => ml M_DIVU
      | 0x01, 6 => ml M_REM   | 0x01, 7 => ml M_REMU
      | _, _ => None
      end
  | 0x0F => (* MISC-MEM.  The unprivileged spec reserves fence's rd and
               rs1 fields and says base implementations SHALL IGNORE
               them, and that reserved fm and predecessor/successor
               settings are to be treated as a fence with fm = 0000
               (src/unpriv/rv32.adoc, norm:fence_unused_flds_rsv);
               Zifencei says the same of fence.i's funct12, rs1 and rd
               (src/unpriv/zifencei.adoc, norm:fence-i_rsv).  QEMU user
               mode decodes both that way (target/riscv/insn32.decode:
               "fence  ---- pred:4 succ:4 ----- 000 ----- 0001111" and
               "fence_i  ---- ---- ---- ----- 001 ----- 0001111").  The
               fields are kept raw; [Sem.exec] runs every fence as a
               no-op (one hart), which is what "treat as fm = 0000"
               gives here.
               POLICY: binutils 2.4x objdump is narrower — it wants
               rd = rs1 = 0 and either fm = 0 (any pred/succ, 0 printing
               as "unknown") or the exact fm=8, pred=succ=rw word
               (fence.tso), and it takes fence.i only as 0x0000100f.  A
               comparison with objdump must special-case the words it
               rejects. *)
      match f3 with
      | 0 => Some (Fence (bits 28 4 w) (bits 24 4 w) (bits 20 4 w) rd rs1)
      | 1 => Some (FenceI rd rs1 (imm_i w))
      | _ => None  (* funct3 = 2 (Zicbom/Zicboz) is out of scope *)
      end
  | 0x73 => (* SYSTEM *)
      match f3 with
      | 0 => (* Only ecall/ebreak; privileged instructions are out of scope
                and return None.  POLICY (confirmed): binutils objdump for
                plain rv64 DOES print mret/wfi/sfence.vma etc. — a
                comparison with objdump must expect them, or this
                decoder must be extended. *)
          match bv_unsigned w with
          | 0x00000073 => Some Ecall
          | 0x00100073 => Some Ebreak
          | _ => None
          end
      | 1 => Some (Csr CSR_RW rd rs1 (bits 20 12 w))
      | 2 => Some (Csr CSR_RS rd rs1 (bits 20 12 w))
      | 3 => Some (Csr CSR_RC rd rs1 (bits 20 12 w))
      | 5 => Some (CsrI CSR_RW rd rs1 (bits 20 12 w))
      | 6 => Some (CsrI CSR_RS rd rs1 (bits 20 12 w))
      | 7 => Some (CsrI CSR_RC rd rs1 (bits 20 12 w))
      | _ => None  (* funct3 = 4 *)
      end
  | 0x2F => (* AMO *)
      let aq := bit 26 w in
      let rl := bit 25 w in
      let go aw :=
        let am o := Some (Amo o aw aq rl rd rs1 rs2) in
        match bv_unsigned (bits 27 5 w) with
        | 0x00 => am AMO_ADD
        | 0x01 => am AMO_SWAP
        | 0x02 => (* lr: rs2 must be 0 (binutils rejects rs2 <> 0) *)
            if decide (bv_unsigned rs2 = 0%Z)
            then Some (Lr aw aq rl rd rs1) else None
        | 0x03 => Some (Sc aw aq rl rd rs1 rs2)
        | 0x04 => am AMO_XOR
        | 0x08 => am AMO_OR
        | 0x0C => am AMO_AND
        | 0x10 => am AMO_MIN
        | 0x14 => am AMO_MAX
        | 0x18 => am AMO_MINU
        | 0x1C => am AMO_MAXU
        | _ => None
        end in
      match f3 with 2 => go AW | 3 => go AD | _ => None end
  | 0x07 => (* LOAD-FP: flw/fld only *)
      match f3 with
      | 2 => Some (FLoad FMT_S rd rs1 (imm_i w))
      | 3 => Some (FLoad FMT_D rd rs1 (imm_i w))
      | _ => None
      end
  | 0x27 => (* STORE-FP *)
      match f3 with
      | 2 => Some (FStore FMT_S rs1 rs2 (imm_s w))
      | 3 => Some (FStore FMT_D rs1 rs2 (imm_s w))
      | _ => None
      end
  | 0x43 | 0x47 | 0x4B | 0x4F => (* FMA group; fmt = bits[26:25] *)
      let mo := match opc with
                | 0x43 => F_MADD  | 0x47 => F_MSUB
                | 0x4B => F_NMSUB | _    => F_NMADD
                end in
      (* POLICY: rm kept raw; the reserved rm values 5/6 still decode here —
         check binutils' policy and align in the differ. *)
      match bv_unsigned (bits 25 2 w) with
      | 0 => Some (Fma mo FMT_S rd rs1 rs2 (f_rs3 w) rm)
      | 1 => Some (Fma mo FMT_D rd rs1 rs2 (f_rs3 w) rm)
      | _ => None  (* fmt 10/11 illegal (no Q/H) *)
      end
  | 0x53 => (* OP-FP: funct7 dispatch.  rm kept raw for arith/sqrt/cvt
               (POLICY: reserved rm values 5/6 accepted — differ to align). *)
      let cvt_int :=  (* integer fcvt_ty selected by the rs2 field *)
        match bv_unsigned rs2 with
        | 0 => Some FC_W | 1 => Some FC_WU
        | 2 => Some FC_L | 3 => Some FC_LU
        | _ => None
        end in
      match f7 with
      | 0x00 => Some (Fari F_ADD FMT_S rd rs1 rs2 rm)
      | 0x01 => Some (Fari F_ADD FMT_D rd rs1 rs2 rm)
      | 0x04 => Some (Fari F_SUB FMT_S rd rs1 rs2 rm)
      | 0x05 => Some (Fari F_SUB FMT_D rd rs1 rs2 rm)
      | 0x08 => Some (Fari F_MUL FMT_S rd rs1 rs2 rm)
      | 0x09 => Some (Fari F_MUL FMT_D rd rs1 rs2 rm)
      | 0x0C => Some (Fari F_DIV FMT_S rd rs1 rs2 rm)
      | 0x0D => Some (Fari F_DIV FMT_D rd rs1 rs2 rm)
      | 0x2C => if decide (bv_unsigned rs2 = 0%Z)
                then Some (Fsqrt FMT_S rd rs1 rm) else None
      | 0x2D => if decide (bv_unsigned rs2 = 0%Z)
                then Some (Fsqrt FMT_D rd rs1 rm) else None
      | 0x10 | 0x11 =>
          let fmt := if decide (f7 = 0x10%Z) then FMT_S else FMT_D in
          match f3 with
          | 0 => Some (Fsgnj F_SGNJ fmt rd rs1 rs2)
          | 1 => Some (Fsgnj F_SGNJN fmt rd rs1 rs2)
          | 2 => Some (Fsgnj F_SGNJX fmt rd rs1 rs2)
          | _ => None
          end
      | 0x14 | 0x15 =>
          let fmt := if decide (f7 = 0x14%Z) then FMT_S else FMT_D in
          match f3 with
          | 0 => Some (Fminmax F_MIN fmt rd rs1 rs2)
          | 1 => Some (Fminmax F_MAX fmt rd rs1 rs2)
          | _ => None
          end
      | 0x50 | 0x51 => (* fcmp: feq/flt/fle = funct3 2/1/0 *)
          let fmt := if decide (f7 = 0x50%Z) then FMT_S else FMT_D in
          match f3 with
          | 2 => Some (Fcmp F_EQ fmt rd rs1 rs2)
          | 1 => Some (Fcmp F_LT fmt rd rs1 rs2)
          | 0 => Some (Fcmp F_LE fmt rd rs1 rs2)
          | _ => None
          end
      | 0x60 => (* fcvt.{w,wu,l,lu}.s *)
          match cvt_int with
          | Some dst => Some (Fcvt dst FC_S rd rs1 rm) | None => None
          end
      | 0x61 => (* fcvt.{w,wu,l,lu}.d *)
          match cvt_int with
          | Some dst => Some (Fcvt dst FC_D rd rs1 rm) | None => None
          end
      | 0x68 => (* fcvt.s.{w,wu,l,lu} *)
          match cvt_int with
          | Some src => Some (Fcvt FC_S src rd rs1 rm) | None => None
          end
      | 0x69 => (* fcvt.d.{w,wu,l,lu}.  fcvt.d.w/fcvt.d.wu are exact, but
                   the spec still decodes rm as usual: "Some instructions,
                   including widening conversions, have the rm field but
                   are nevertheless mathematically unaffected by the
                   rounding mode; software should set their rm field to
                   RNE (000) but implementations must treat the rm field
                   as usual (in particular, with regard to decoding legal
                   vs. reserved encodings)" (src/unpriv/f-st-ext.adoc,
                   norm:roundingmode_unaffected_rm_decode).  QEMU decodes
                   all four with a free rm (insn32.decode @r2_rm).  The
                   reserved modes 5/6 are rejected by [Sem.exec], not
                   here.
                   POLICY: binutils objdump is narrower — it rejects
                   rm <> 0 on fcvt.d.w/fcvt.d.wu (0xd205c553 is invalid
                   to objdump); a comparison must special-case it. *)
          match cvt_int with
          | Some src => Some (Fcvt FC_D src rd rs1 rm)
          | None => None
          end
      | 0x20 => (* fcvt.s.d (rs2 = 1); rs2 = 0 would be fcvt.s.s: illegal *)
          if decide (bv_unsigned rs2 = 1%Z)
          then Some (Fcvt FC_S FC_D rd rs1 rm) else None
      | 0x21 => (* fcvt.d.s (rs2 = 0); rs2 = 1 would be fcvt.d.d: illegal.
                   The conversion is exact, and rm is decoded as usual for
                   a widening conversion (same spec rule as 0x69 above);
                   QEMU: @r2_rm.
                   POLICY: binutils objdump rejects rm <> 0 here
                   (0x4205c553 invalid) — special-case it in a
                   comparison. *)
          if decide (bv_unsigned rs2 = 0%Z)
          then Some (Fcvt FC_D FC_S rd rs1 rm) else None
      | 0x70 => (* fmv.x.w (f3 = 0) / fclass.s (f3 = 1); rs2 must be 0 *)
          if decide (bv_unsigned rs2 = 0%Z) then
            match f3 with
            | 0 => Some (Fmv FMV_X_F FMT_S rd rs1)
            | 1 => Some (Fclass FMT_S rd rs1)
            | _ => None
            end
          else None
      | 0x71 => (* fmv.x.d / fclass.d *)
          if decide (bv_unsigned rs2 = 0%Z) then
            match f3 with
            | 0 => Some (Fmv FMV_X_F FMT_D rd rs1)
            | 1 => Some (Fclass FMT_D rd rs1)
            | _ => None
            end
          else None
      | 0x78 => (* fmv.w.x *)
          if bool_decide (bv_unsigned rs2 = 0%Z) && bool_decide (f3 = 0%Z)
          then Some (Fmv FMV_F_X FMT_S rd rs1) else None
      | 0x79 => (* fmv.d.x *)
          if bool_decide (bv_unsigned rs2 = 0%Z) && bool_decide (f3 = 0%Z)
          then Some (Fmv FMV_F_X FMT_D rd rs1) else None
      | _ => None
      end
  | _ => None
  end%Z.

(** ** Sanity checks against known encodings.

    Stated via [bool_decide] because the [BvWf] proofs inside [bv]
    literals are opaque, so plain [reflexivity] on [bv] equalities gets
    stuck; the boolean equality test only inspects [bv_unsigned]. *)

Goal bool_decide (decode 0x00000013 (* addi x0,x0,0 = nop *)
  = Some (OpImm ALU_ADD 0 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x00c58533 (* add a0,a1,a2 *)
  = Some (Op ALU_ADD 10 11 12)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0xfe0796e3 (* bnez a5, .-20 *)
  = Some (Branch BC_NE 15 0 (Z_to_bv 13 (-20)))) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x00153513 (* sltiu a0,a0,1 = seqz *)
  = Some (OpImm ALU_SLTU 10 10 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x02b4d53b (* divuw a0,s1,a1 *)
  = Some (Mul32 M_DIVU 10 9 11)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x140536af (* lr.d.aq a3,(a0) *)
  = Some (Lr AD true false 13 10)) = true.
Proof. vm_compute. reflexivity. Qed.
(* SYSTEM: ecall/ebreak decode; uret (privileged) does not *)
Goal bool_decide (decode 0x00000073 = Some Ecall) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x00100073 = Some Ebreak) = true.
Proof. vm_compute. reflexivity. Qed.
Goal decode 0x00200073 = None.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x0ff0000f (* fence iorw,iorw *)
  = Some (Fence 0 15 15 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x8330000f (* fence.tso *)
  = Some (Fence 8 3 3 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x0000100f (* fence.i *)
  = Some (FenceI 0 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
(* The fields the spec tells an implementation to ignore: fence, fence.i
   and the exact fcvt forms decode whatever those fields hold.  binutils
   objdump rejects all seven words below; QEMU executes them (issue #9). *)
Goal bool_decide (decode 0x0ff0008f (* fence iorw,iorw with rd = ra *)
  = Some (Fence 0 15 15 1 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x0ff0080f (* ... with rd = a6 *)
  = Some (Fence 0 15 15 16 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x8120000f (* reserved fm = 8 with pred/succ <> rw *)
  = Some (Fence 8 1 2 0 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x0010100f (* fence.i, funct12 = 1 *)
  = Some (FenceI 0 0 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x00a0100f (* fence.i, funct12 = 10 *)
  = Some (FenceI 0 0 10)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0xd2001053 (* fcvt.d.w ft0,zero,rtz *)
  = Some (Fcvt FC_D FC_W 0 0 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x4201f553 (* fcvt.d.s fa0,ft3,dyn *)
  = Some (Fcvt FC_D FC_S 10 3 7)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x341022f3 (* csrrs t0,mepc,zero *)
  = Some (Csr CSR_RS 5 0 0x341)) = true.
Proof. vm_compute. reflexivity. Qed.
Goal bool_decide (decode 0x00c58553 (* fadd.s fa0,fa1,fa2,rne *)
  = Some (Fari F_ADD FMT_S 10 11 12 0)) = true.
Proof. vm_compute. reflexivity. Qed.
(* fcvt.s.s / fcvt.d.d are illegal *)
Goal decode 0x40058553 = None. Proof. vm_compute. reflexivity. Qed.
Goal decode 0x42158553 = None. Proof. vm_compute. reflexivity. Qed.
(* Low 2 bits <> 11: never a valid 32-bit instruction *)
Goal decode 0x00000001 = None. Proof. vm_compute. reflexivity. Qed.
Goal decode 0x0000852a = None. Proof. vm_compute. reflexivity. Qed.
