(** * Sem: the abstract RV64GC semantics, as a first-order effect tree.

    The semantics is a plain function

        exec : word -> instr -> core -> eff

    from a decoded instruction and the CORE state (registers, FP
    registers, pc, fcsr, LR/SC reservation) to a finite, first-order
    tree of residual effects.  There is no monad parameter and no
    typeclass: core state is threaded concretely through the
    continuations (register/pc/CSR/reservation accesses are ordinary
    record operations), and only the operations this semantics
    deliberately does NOT interpret appear as tree nodes:

    - [ELoad n a k] / [EStore n a v k]: the MEMORY boundary.  Memory
      belongs to the interpreter (in this library,
      [RiscvSemantics]); the semantics only issues
      sized little-endian accesses.  [n] is the access width in bits
      (8/16/32/64).
    - [EEcall c] / [EEbreak c]: the process/hardware split.  The
      semantics never interprets syscalls; these nodes surface them to
      an external driver.  They carry the core state with pc ALREADY
      ADVANCED (see the pc-advance contract below) and no
      continuation: the instruction is over, and the driver's resume
      protocol is: mutate the stopped state, step again.
    - [EIllegal c]: an undecodable fetch or a CSR address this model
      does not implement.  The MODEL declining, not the architecture:
      an interpreter must not read it as a crash.
    - [EDefinedIllegal c]: the ARCHITECTURE defines this instruction to
      raise an illegal-instruction exception, in every conforming
      implementation and at every privilege level — today exactly a CSR
      instruction whose write side happens on a read-only CSR address
      (see [csr_write_illegal]).  Distinct from [EIllegal] in the same
      way [EFault] is: an interpreter must treat it as the process
      crashing (SIGILL under Linux), never as a hole in the model.  The
      carried core is the PRE-state: nothing retires.
    - [EFault c]: the instruction TRAPS by the ISA's own rules — today
      exactly the misaligned atomics (lr/sc/amo at an address that is
      not naturally aligned; see [amo_aligned]).  Distinct from
      [EIllegal]: this is not the model declining an instruction, it is
      the architecture defining the execution to fault, so an
      interpreter must treat it as the process crashing (SIGBUS), never
      as a hole in the model.  The carried core is the PRE-state (pc
      still at the faulting instruction): nothing retires.
    - [EDone c]: the instruction retired with core state [c].

    Every instruction terminates, so [eff] is a plain inductive (the
    continuations under [ELoad] are functions, but every tree is
    finite) and an interpreter is a structural [Fixpoint] — no fuel,
    no coinduction, no typeclass instance.

    Design decisions:
    - x0 hardwiring lives HERE, in the [rget]/[rset] wrappers over a
      dumb [bvmap] register store.
    - fcsr is the ONLY stored FP CSR; fflags (0x001) and frm (0x002)
      are read and written as slices of it.
    - AMOs compose from plain sized loads/stores: a deliberately
      sequential, single-hart memory model.
    - FP: F and D execute HERE, in full — arithmetic included.  The
      IEEE side (rounding, exception flags, the special cases) lives
      in [Fpu] as a computation over raw bit patterns; this file owns
      the ISA side: which register file each operand comes from, NaN
      boxing of single-precision values, resolving the instruction's
      rounding-mode field against fcsr's frm, and accruing the flags
      into fcsr[4:0].  A reserved rounding mode is [EIllegal], not a
      default.

    PC-advance contract: [exec sz i] reads pc once, and for every
    non-control-flow instruction the resulting core carries
    pc := pc + sz.  Branches/jumps instead carry their target (a
    not-taken branch carries pc + sz); the link value of jal/jalr is
    pc + sz.  Consequently, the cores carried by [EEcall]/[EEbreak]
    (and the in-[exec] [EIllegal] for a bad CSR or a reserved
    rounding mode) have pc already past the instruction, so a driver
    that stops there can resume directly.  The [EIllegal] issued by [step] on an
    undecodable fetch carries pc NOT advanced (still pointing at the
    bad instruction), and so do [EFault] and [EDefinedIllegal]: neither
    retires. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.

(** ** Pure helpers *)

Definition w0 : word := Z_to_bv 64 0.
Definition w1 : word := Z_to_bv 64 1.
Definition low32 (v : word) : bv 32 := bv_extract 0 32 v.
Definition is_x0 (r : reg) : bool := Z.eqb (bv_unsigned r) 0.

(** Integer ALU at any width.  Shift amounts are masked to the low
    [log2 n] bits (6 for n=64, 5 for n=32), per the ISA; [shmask] is
    that mask. *)
Definition alu {n : N} (shmask : Z) (op : aluop) (a b : bv n) : bv n :=
  match op with
  | ALU_ADD => a + b
  | ALU_SUB => a - b
  | ALU_SLL => a ≪ bv_and b (Z_to_bv n shmask)
  | ALU_SLT => if bv_lts a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_SLTU => if bv_ltu a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_XOR => bv_xor a b
  | ALU_SRL => a ≫ bv_and b (Z_to_bv n shmask)
  | ALU_SRA => bv_ashiftr a (bv_and b (Z_to_bv n shmask))
  | ALU_OR => bv_or a b
  | ALU_AND => bv_and a b
  end.

Definition alu64 : aluop → word → word → word := alu 63.
Definition alu32 : aluop → bv 32 → bv 32 → bv 32 := alu 31.

Definition branch_taken (c : branch_cond) (a b : word) : bool :=
  match c with
  | BC_EQ => bv_eqb a b
  | BC_NE => negb (bv_eqb a b)
  | BC_LT => bv_lts a b
  | BC_GE => negb (bv_lts a b)
  | BC_LTU => bv_ltu a b
  | BC_GEU => negb (bv_ltu a b)
  end.

(** M extension at any width; MULH* shift the exact product right by
    the width.  RISC-V division is TRUNCATING ([Z.quot]/[Z.rem] via
    [bv_quots]/[bv_rems], not floor division).  Division by zero:
    div/divu = all ones, rem/remu = the dividend.  Signed overflow
    (min / -1) needs no special case: [Z.quot min (-1) = -min] wraps
    back to min under [Z_to_bv], and [Z.rem min (-1) = 0]. *)
Definition mul_div {n : N} (op : mulop) (a b : bv n) : bv n :=
  let div0 := Z.eqb (bv_unsigned b) 0 in
  match op with
  | M_MUL => a * b
  | M_MULH => bv_mulhss a b
  | M_MULHSU => bv_mulhsu a b
  | M_MULHU => bv_mulhuu a b
  | M_DIV => if div0 then Z_to_bv n (-1) else bv_quots a b
  | M_DIVU => if div0 then Z_to_bv n (-1) else bv_divu a b
  | M_REM => if div0 then a else bv_rems a b
  | M_REMU => if div0 then a else bv_modu a b
  end.

(** Natural alignment for the A extension.  The ISA requires lr/sc/amo
    addresses to be naturally aligned to the operand width (4 for .w, 8
    for .d) and defines a misaligned one to raise an
    address-misaligned/access-fault exception — unlike plain loads and
    stores, whose misaligned forms this model permits (qemu-user and
    Linux-on-real-hardware both make them work).  A misaligned atomic
    is SIGBUS under qemu-user, so [exec] gates all three on this check
    and emits [EFault].  The check runs FIRST, before sc consults its
    reservation: the spec raises the exception whether or not the sc
    would succeed, and Sail agrees.  One known divergence: QEMU 8.2.2's
    FAILING-sc path (reservation mismatch, [gen_sc] in
    target/riscv/insn_trans/trans_rva.c.inc) skips the memory access
    entirely and retires with rd = 1, so it retires a misaligned sc the
    model faults, and a failing sc on memory the process may not write,
    which the model also faults (see the [Sc] arm of [exec]).  QEMU
    fixed both in commit d107b748072c ("Generate access fault if sc
    comparison fails", 2026-04-29; in 10.0.10, 10.2.3 and 11.0.1).  We
    follow the spec/Sail. *)
Definition amo_bytes (wd : awidth) : Z :=
  match wd with AW => 4 | AD => 8 end.

Definition amo_aligned (wd : awidth) (a : word) : bool :=
  Z.eqb (bv_unsigned a mod amo_bytes wd) 0.

(** AMO combine function ([old] is the memory value). *)
Definition amo_val {n : N} (op : amoop) (old src : bv n) : bv n :=
  match op with
  | AMO_SWAP => src
  | AMO_ADD => old + src
  | AMO_XOR => bv_xor old src
  | AMO_AND => bv_and old src
  | AMO_OR => bv_or old src
  | AMO_MIN => if bv_lts old src then old else src
  | AMO_MAX => if bv_lts old src then src else old
  | AMO_MINU => if bv_ltu old src then old else src
  | AMO_MAXU => if bv_ltu old src then src else old
  end.

(** ** Read-only CSR addresses

    The CSR address encodes its own writability: "The top two bits
    (csr[11:10]) indicate whether the register is read/write (00, 01, or
    10) or read-only (11)", and "attempts to access a CSR without
    appropriate privilege level or to write a read-only register also
    raise illegal-instruction exceptions" -- RISC-V unprivileged spec,
    CSR Address Mapping Conventions.  That rule is a property of the
    ADDRESS alone: it holds in every conforming implementation, at every
    privilege level, and whether or not the address names a CSR the
    implementation has.  So an instruction whose write side happens on
    such an address is defined-illegal in the same sense DecodeC's
    [is_defined_illegal] uses on the decode side, and not a gap in this
    model's CSR map.

    This is what makes GNU as's [unimp] (0xc0001073 = csrrw x0, cycle,
    x0) a death rather than a decline: [cycle] is 0xc00, csr[11:10] = 11,
    and csrrw always writes.  Trap-mode sanitizers emit that word for a
    fired check.

    The neighbouring rule -- an access from below the CSR's own privilege
    level, csr[9:8] -- is deliberately NOT taken here.  It is illegal
    only for a process running at a lower privilege than the address
    names, so it is a fact about the executing hart rather than about the
    instruction, and a reference ISA model that runs in machine mode
    finds the same access legal.  Such
    an address stays [EIllegal]: fail closed. *)
Definition csr_read_only (csr : bv 12) : bool :=
  Z.eqb (Z.land (Z.shiftr (bv_unsigned csr) 10) 3) 3.

(** The write side of a CSR instruction is architecturally illegal
    exactly when it happens at all and the address is read-only.
    [writes] is the instruction's own write predicate: csrrw/csrrwi
    always write, csrrs/csrrc skip the write when rs1 = x0 and
    csrrsi/csrrci when uimm = 0, so `csrr rd, cycle` reads a read-only
    counter legally and must NOT come here. *)
Definition csr_write_illegal (writes : bool) (csr : bv 12) : bool :=
  (writes && csr_read_only csr)%bool.

(** CSR address map: only the fcsr aliases exist; each is a (lo, len)
    slice of the stored 32-bit fcsr.  0x001 = fflags = fcsr[4:0],
    0x002 = frm = fcsr[7:5], 0x003 = fcsr itself (low 8 bits). *)
Definition csr_slice (csr : bv 12) : option (Z * Z) :=
  let c := bv_unsigned csr in
  if Z.eqb c 1 then Some (0%Z, 5%Z)
  else if Z.eqb c 2 then Some (5%Z, 3%Z)
  else if Z.eqb c 3 then Some (0%Z, 8%Z)
  else None.

(** The read-only fault arm cannot swallow an instruction this model
    answers: every address [csr_slice] resolves is read/write, so a CSR
    access to such an address still reaches [exec_csr].  Stated
    over ALL addresses rather than checked on the three that exist, so
    that growing [csr_slice] into read-only space has to confront this
    lemma instead of silently turning a modeled instruction into a
    death. *)
Lemma csr_read_only_unimplemented : forall csr : bv 12,
  csr_read_only csr = true -> csr_slice csr = None.
Proof.
  intros csr H. unfold csr_slice. cbv zeta.
  unfold csr_read_only in H.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  reflexivity.
Qed.

Definition slice_get (f : bv 32) (lo len : Z) : word :=
  Z_to_bv 64 (Z.land (Z.shiftr (bv_unsigned f) lo) (Z.ones len)).

Definition slice_set (f : bv 32) (lo len : Z) (v : word) : bv 32 :=
  let mask := Z.shiftl (Z.ones len) lo in
  Z_to_bv 32 (Z.lor (Z.land (bv_unsigned f) (Z.lnot mask))
                    (Z.land (Z.shiftl (bv_unsigned v) lo) mask)).

(** NaN boxing for single-precision values in 64-bit FP registers. *)
Definition nan_box (v : bv 32) : word := bv_concat 64 (Z_to_bv 32 (-1)) v.

(** An S-format input that is not properly NaN-boxed is treated as the
    canonical NaN. *)
Definition unbox_s (v : word) : bv 32 :=
  if Z.eqb (bv_unsigned (bv_extract 32 32 v)) (Z.ones 32)
  then low32 v
  else Z_to_bv 32 0x7fc00000.

(** Sign injection at any width (n = 32 after unboxing, or 64). *)
Definition sgnj_val {n : N} (op : fsgnop) (a b : bv n) : bv n :=
  let sa := bit (n - 1) a in
  let sb := bit (n - 1) b in
  let s := match op with
           | F_SGNJ => sb
           | F_SGNJN => negb sb
           | F_SGNJX => xorb sa sb
           end in
  bv_concat n (Z_to_bv 1 (if s then 1 else 0)) (bv_extract 0 (n - 1) a).

(** ** Core state: what the ISA owns

    Everything the semantics reads and writes by itself: registers,
    FP registers, pc, fcsr, and the LR/SC reservation.  Memory is NOT
    here — it belongs to the interpreter (in this library,
    [RiscvSemantics]).  The core
    state is total and every access to it succeeds, which is exactly
    why it is threaded concretely instead of appearing as effects. *)

Record core := Core {
  c_regs : bvmap 5 word;
  c_fregs : bvmap 5 word;
  c_pc : word;
  c_fcsr : bv 32;
  c_resv : option word;
}.

(* Hand-written field updaters (extraction-friendly). *)
Definition with_regs f (c : core) :=
  Core (f (c_regs c)) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c).
Definition with_fregs f (c : core) :=
  Core (c_regs c) (f (c_fregs c)) (c_pc c) (c_fcsr c) (c_resv c).
Definition with_pc (v : word) (c : core) :=
  Core (c_regs c) (c_fregs c) v (c_fcsr c) (c_resv c).
Definition with_fcsr (v : bv 32) (c : core) :=
  Core (c_regs c) (c_fregs c) (c_pc c) v (c_resv c).
Definition with_resv (v : option word) (c : core) :=
  Core (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) v.

(** Register stores are dumb [bvmap]s; missing keys read as 0. *)
Definition reg_get (rm : bvmap 5 word) (r : reg) : word :=
  match bvmap_get r rm with Some v => v | None => w0 end.

(** x0 hardwiring: reads 0, writes discarded. *)
Definition rget (c : core) (r : reg) : word :=
  if is_x0 r then w0 else reg_get (c_regs c) r.
Definition rset (r : reg) (v : word) (c : core) : core :=
  if is_x0 r then c else with_regs (bvmap_set r v) c.

Definition fget (c : core) (r : reg) : word := reg_get (c_fregs c) r.
Definition fset (r : reg) (v : word) (c : core) : core :=
  with_fregs (bvmap_set r v) c.

(** ** The FP register file's ISA-side plumbing

    [Fpu] speaks raw bit patterns of the FORMAT's width; the register
    file is 64 bits wide whatever the format.  These functions are the
    whole translation, and NaN boxing is why they are not the
    identity: a single-precision datum occupies the low 32 bits with
    the high 32 all ones, an input that is not boxed that way reads as
    the canonical NaN ([unbox_s]), and every single-precision result
    is re-boxed on the way out.  Skipping the box would leave a
    silently valid-looking double in the register. *)

Definition fp_format (fmt : ffmt) : format :=
  match fmt with FMT_S => fmt_single | FMT_D => fmt_double end.

Definition fread (c : core) (fmt : ffmt) (r : reg) : Z :=
  match fmt with
  | FMT_S => bv_unsigned (unbox_s (fget c r))
  | FMT_D => bv_unsigned (fget c r)
  end.

Definition fwrite (fmt : ffmt) (r : reg) (v : Z) (c : core) : core :=
  match fmt with
  | FMT_S => fset r (nan_box (Z_to_bv 32 v)) c
  | FMT_D => fset r (Z_to_bv 64 v) c
  end.

(** fcsr[7:5] is frm, the DYNAMIC rounding mode.  An instruction whose
    rm field is 7 uses it, so compiled FP code that sets the rounding
    mode with [fsrm] and then issues plain [fadd.d] depends on fcsr
    being real state — which is why fcsr cannot be a dummy and why
    Zicsr has to be executed rather than declined. *)
Definition frm_of (c : core) : Z :=
  Z.land (Z.shiftr (bv_unsigned (c_fcsr c)) 5) 7.

Definition resolve_rm (rm : bv 3) (c : core) : option rmode :=
  rmode_of_field (bv_unsigned rm) (frm_of c).

(** Flags ACCRUE: fcsr[4:0] is sticky, so new exceptions are OR-ed in
    and nothing is ever cleared by an arithmetic instruction. *)
Definition accrue (fl : fflags) (c : core) : core :=
  with_fcsr (Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl))) c.

(** A store or AMO from this hart to the reserved address invalidates
    the LR/SC reservation, so a subsequent SC fails.  This matches
    qemu-user, whose SC does a cmpxchg against the value
    loaded by LR: overwriting the reserved cell makes the SC fail.
    We compare the
    access base address exactly — a same-address same-value rewrite
    (ABA) or a partially overlapping store would diverge from qemu's
    value comparison, a documented model boundary. *)
Definition inval_resv (a : word) (c : core) : core :=
  match c_resv c with
  | Some r =>
      if Z.eqb (bv_unsigned r) (bv_unsigned a) then with_resv None c else c
  | None => c
  end.

(** ** The effect tree *)

Inductive eff : Type :=
| EDone (c : core)
| EIllegal (c : core)
| EDefinedIllegal (c : core)
| EEcall (c : core)
| EEbreak (c : core)
| EFault (c : core)
| ELoad (n : N) (a : word) (k : bv n → eff)
| EStore (n : N) (a : word) (v : bv n) (k : eff).

(** Load a value of size [sz]: the interpreter answers with the [n]
    bits at [a] assembled little-endian; signed loads sign-extend,
    unsigned zero-extend (for SZ8 both are the identity). *)
Definition load_val (sz : msize) (sgn : bool) (a : word) (k : word → eff) : eff :=
  match sz with
  | SZ1 => ELoad 8 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ2 => ELoad 16 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ4 => ELoad 32 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ8 => ELoad 64 a k
  end.

Definition store_val (sz : msize) (a : word) (v : word) (k : eff) : eff :=
  match sz with
  | SZ1 => EStore 8 a (bv_extract 0 8 v) k
  | SZ2 => EStore 16 a (bv_extract 0 16 v) k
  | SZ4 => EStore 32 a (low32 v) k
  | SZ8 => EStore 64 a v k
  end.

(** CSR access.  [writes] says whether the write side happens:
    csrrw/csrrwi always write; csrrs/csrrc skip the write when
    rs1 = x0, csrrsi/csrrci when uimm = 0.  The read ALWAYS happens
    (even csrrw with rd = x0 — a stated model boundary; harmless
    here since reading fcsr has no side effect).  Unknown CSR
    addresses are [EIllegal] (with pc already advanced, per the
    pc-advance contract).

    A write to a read-only address never reaches here: [exec] rejects it
    first, with [EDefinedIllegal] and the un-advanced core.  Order
    matters — the architectural rule is about the address, so it fires
    ahead of this model's own CSR map and independently of it. *)
Definition exec_csr (op : csrop) (rd : reg) (operand : word)
    (writes : bool) (csr : bv 12) (c : core) : eff :=
  match csr_slice csr with
  | None => EIllegal c
  | Some (lo, len) =>
      let f := c_fcsr c in
      let old := slice_get f lo len in
      let newv :=
        match op with
        | CSR_RW => operand
        | CSR_RS => bv_or old operand
        | CSR_RC => bv_and old (bv_not operand)
        end in
      EDone (rset rd old
               (if writes then with_fcsr (slice_set f lo len newv) c else c))
  end.

(** ** The semantics

    Execute one already-decoded instruction, including the pc update.
    [sz] is the encoded size (2 for expanded compressed instructions,
    else 4): it determines both the pc advance and the jal/jalr link
    value (c.jalr links pc+2). *)
Definition exec (sz : word) (i : instr) (c : core) : eff :=
  let pc := c_pc c in
  let npc := pc + sz in
  let cn := with_pc npc c in   (* pc advanced past the instruction *)
  match i with
  (* RV64I *)
  | Lui rd imm =>
      EDone (rset rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Auipc rd imm =>
      EDone (rset rd (pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Jal rd imm =>
      EDone (rset rd npc (with_pc (pc + sext 64 imm) c))
  | Jalr rd rs1 imm =>
      (* Target computed before the link write: rd may equal rs1. *)
      let a := rget c rs1 in
      EDone (rset rd npc (with_pc (bv_and (a + sext 64 imm) (bv_not w1)) c))
  | Branch bc rs1 rs2 imm =>
      EDone (with_pc (if branch_taken bc (rget c rs1) (rget c rs2)
                      then pc + sext 64 imm else npc) c)
  | Load msz sgn rd rs1 imm =>
      load_val msz sgn (rget c rs1 + sext 64 imm)
        (λ v, EDone (rset rd v cn))
  | Store msz rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm in
      store_val msz a (rget c rs2) (EDone (inval_resv a cn))
  | OpImm op rd rs1 imm =>
      EDone (rset rd (alu64 op (rget c rs1) (sext 64 imm)) cn)
  | ShiftImm op rd rs1 shamt =>
      EDone (rset rd (alu64 op (rget c rs1) (zext 64 shamt)) cn)
  | Op op rd rs1 rs2 =>
      EDone (rset rd (alu64 op (rget c rs1) (rget c rs2)) cn)
  | OpImm32 rd rs1 imm =>
      EDone (rset rd (sext 64 (alu32 ALU_ADD (low32 (rget c rs1)) (sext 32 imm))) cn)
  | ShiftImm32 op rd rs1 shamt =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (zext 32 shamt))) cn)
  | Op32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | Fence _ _ _ _ _ | FenceI _ _ _ =>
      EDone cn   (* single hart: fences are no-ops *)
  | Ecall => EEcall cn
  | Ebreak => EEbreak cn
  (* M *)
  | Mul op rd rs1 rs2 =>
      EDone (rset rd (mul_div op (rget c rs1) (rget c rs2)) cn)
  (* Operands are truncated to 32 bits BEFORE the divide, per the ISA
     ("divide the lower 32 bits of rs1 by the lower 32 bits of rs2").
     mit-plv/riscv-coq gets this wrong (its module
     riscv.Spec.ExecuteM64, generated from riscv-semantics; master
     as of 2026-08): Divw, Divuw, Remw and Remuw bind both operands
     from getRegister at full width and apply s32 only to the
     result, so DIVW of 0x0000000100000002 by 2 gives
     0xffffffff80000001 where the ISA gives 1.  MULW is unaffected:
     truncation commutes with multiplication. *)
  | Mul32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (mul_div op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  (* A: sequential single-hart model, composed from plain memory ops. *)
  | Lr wd _ _ rd rs1 =>
      let a := rget c rs1 in
      if negb (amo_aligned wd a) then EFault c
      else match wd with
      | AW => ELoad 32 a (λ v,
                EDone (with_resv (Some a) (rset rd (sext 64 v) cn)))
      | AD => ELoad 64 a (λ v,
                EDone (with_resv (Some a) (rset rd v cn)))
      end
  | Sc wd _ _ rd rs1 rs2 =>
      let a := rget c rs1 in
      (* Alignment first, before the reservation: a misaligned sc traps
         whether or not it would succeed (see [amo_aligned]). *)
      if negb (amo_aligned wd a) then EFault c
      else
      let ok := match c_resv c with
                | Some r => Z.eqb (bv_unsigned r) (bv_unsigned a)
                | None => false
                end in
      let c1 := with_resv None cn in
      if ok then
        (match wd with
         | AW => EStore 32 a (low32 (rget c rs2))
         | AD => EStore 64 a (rget c rs2)
         end) (EDone (rset rd w0 c1))
      (* A FAILING sc still passes the store permission check: "No SC.W
         instruction shall retire unless it passes memory permission
         checks" (RISC-V unprivileged ISA v20260120, Zalrsc), and the
         check is a store's: "Attempting to execute a store,
         store-conditional, AMO ... whose effective address lies within
         a page without write permissions raises a store page-fault
         exception" (privileged ISA v20260120, 11.1.3.1).  Sail's
         STORECON reaches [vmem_write_addr] (model/sys/vmem_utils.sail),
         which translates the address for a write before it matches the
         reservation.  The check is written as a load and a store back
         of the same bytes: every read returns the same values afterwards,
         a range the process may not write faults as a store there does,
         and the access is reported, so a first touch of a lazy anonymous
         page is charged, as the store page fault that Linux takes for it
         is.  The load adds one condition the store check lacks: the
         bytes must be readable.  Linux on riscv maps every writable page
         readable, and the model already refuses a load from a writable
         segment without 'r' ([RiscvSemantics.memory_read]), so a failing
         sc there faults in the model and retires on Linux; SCOPE.md
         names it. *)
      else
        match wd with
        | AW => ELoad 32 a (λ v, EStore 32 a v (EDone (rset rd w1 c1)))
        | AD => ELoad 64 a (λ v, EStore 64 a v (EDone (rset rd w1 c1)))
        end
  | Amo op wd _ _ rd rs1 rs2 =>
      let a := rget c rs1 in
      if negb (amo_aligned wd a) then EFault c
      else
      let src := rget c rs2 in
      let c1 := inval_resv a cn in
      match wd with
      | AW => ELoad 32 a (λ old,
                EStore 32 a (amo_val op old (low32 src))
                  (EDone (rset rd (sext 64 old) c1)))
      | AD => ELoad 64 a (λ old,
                EStore 64 a (amo_val op old src)
                  (EDone (rset rd old c1)))
      end
  (* Zicsr.  The architectural read-only check runs on the PRE-state
     core [c]: nothing retires when it fires. *)
  | Csr op rd rs1 csr =>
      let writes := match op with CSR_RW => true | _ => negb (is_x0 rs1) end in
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (rget c rs1) writes csr cn
  | CsrI op rd uimm csr =>
      let writes :=
        match op with
        | CSR_RW => true
        | _ => negb (Z.eqb (bv_unsigned uimm) 0)
        end in
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (zext 64 uimm) writes csr cn
  (* F/D data movement executes concretely. *)
  | FLoad fmt rd rs1 imm =>
      let a := rget c rs1 + sext 64 imm in
      match fmt with
      | FMT_S => ELoad 32 a (λ v, EDone (fset rd (nan_box v) cn))
      | FMT_D => ELoad 64 a (λ v, EDone (fset rd v cn))
      end
  | FStore fmt rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm in
      let v := fget c rs2 in
      (match fmt with
       | FMT_S => EStore 32 a (low32 v)
       | FMT_D => EStore 64 a v
       end) (EDone (inval_resv a cn))
  | Fmv dir fmt rd rs1 =>
      EDone match dir, fmt with
            | FMV_X_F, FMT_S => rset rd (sext 64 (low32 (fget c rs1))) cn
            | FMV_X_F, FMT_D => rset rd (fget c rs1) cn
            | FMV_F_X, FMT_S => fset rd (nan_box (low32 (rget c rs1))) cn
            | FMV_F_X, FMT_D => fset rd (rget c rs1) cn
            end
  | Fsgnj op fmt rd rs1 rs2 =>
      let a := fget c rs1 in
      let b := fget c rs2 in
      EDone match fmt with
            | FMT_S => fset rd (nan_box (sgnj_val op (unbox_s a) (unbox_s b))) cn
            | FMT_D => fset rd (sgnj_val op a b) cn
            end
  (* F/D arithmetic.  Every arm has the same shape: resolve the
     rounding mode (a reserved one is EIllegal, with pc advanced),
     read the operands out of the FP file at the format's width, call
     [Fpu], write the result back and OR the flags into fcsr.  The
     operations with no rounding-mode field (fmin/fmax, the compares,
     fclass) skip the first step; their funct3 is a sub-opcode, not an
     rm, and the decoder has already consumed it. *)
  | Fari op fmt rd rs1 rs2 rm =>
      match resolve_rm rm cn with
      | None => EIllegal cn
      | Some md =>
        let f := fp_format fmt in
        let a := fread c fmt rs1 in
        let b := fread c fmt rs2 in
        let '(v, fl) :=
          match op with
          | F_ADD => fp_add f md a b
          | F_SUB => fp_sub f md a b
          | F_MUL => fp_mul f md a b
          | F_DIV => fp_div f md a b
          end in
        EDone (fwrite fmt rd v (accrue fl cn))
      end
  | Fsqrt fmt rd rs1 rm =>
      match resolve_rm rm cn with
      | None => EIllegal cn
      | Some md =>
        let '(v, fl) := fp_sqrt (fp_format fmt) md (fread c fmt rs1) in
        EDone (fwrite fmt rd v (accrue fl cn))
      end
  (* The four fused forms differ only by which of the product and the
     addend is negated, and negation is a SIGN-BIT FLIP applied to an
     operand — not a rounded subtraction — so all four share one fused
     kernel.  Negating rs1 negates the product. *)
  | Fma op fmt rd rs1 rs2 rs3 rm =>
      match resolve_rm rm cn with
      | None => EIllegal cn
      | Some md =>
        let f := fp_format fmt in
        let a := fread c fmt rs1 in
        let b := fread c fmt rs2 in
        let z := fread c fmt rs3 in
        let '(a', z') :=
          match op with
          | F_MADD => (a, z)
          | F_MSUB => (a, fp_neg f z)
          | F_NMSUB => (fp_neg f a, z)
          | F_NMADD => (fp_neg f a, fp_neg f z)
          end in
        let '(v, fl) := fp_fma f md a' b z' in
        EDone (fwrite fmt rd v (accrue fl cn))
      end
  | Fminmax op fmt rd rs1 rs2 =>
      let '(v, fl) :=
        fp_minmax (fp_format fmt) (match op with F_MIN => false | F_MAX => true end)
                  (fread c fmt rs1) (fread c fmt rs2) in
      EDone (fwrite fmt rd v (accrue fl cn))
  (* The compares and fclass write an INTEGER register. *)
  | Fcmp op fmt rd rs1 rs2 =>
      let f := fp_format fmt in
      let a := fread c fmt rs1 in
      let b := fread c fmt rs2 in
      let '(v, fl) :=
        match op with
        | F_EQ => fp_eq f a b
        | F_LT => fp_lt f a b
        | F_LE => fp_le f a b
        end in
      EDone (rset rd (if v then w1 else w0) (accrue fl cn))
  | Fclass fmt rd rs1 =>
      EDone (rset rd (Z_to_bv 64 (fp_class (fp_format fmt) (fread c fmt rs1))) cn)
  (* fcvt.  The pair (dst, src) says which of the four directions this
     is; the decoder only ever produces the architecturally valid
     pairs, so the leftover combinations are dead and answer
     [EIllegal] rather than inventing a meaning.  An integer result is
     SIGN-extended into the 64-bit destination even when the
     conversion is unsigned (fcvt.wu.s writes a sign-extended 32-bit
     value), which is why the width is threaded rather than assumed. *)
  | Fcvt dst src rd rs1 rm =>
      match resolve_rm rm cn with
      | None => EIllegal cn
      | Some md =>
        let ity (t : fcvt_ty) : option (bool * Z) :=
          match t with
          | FC_W => Some (true, 32%Z) | FC_WU => Some (false, 32%Z)
          | FC_L => Some (true, 64%Z) | FC_LU => Some (false, 64%Z)
          | _ => None
          end in
        let fty (t : fcvt_ty) : option ffmt :=
          match t with FC_S => Some FMT_S | FC_D => Some FMT_D | _ => None end in
        match fty dst, fty src with
        | Some df, Some sf =>            (* float -> float *)
            let '(v, fl) :=
              fp_convert (fp_format sf) (fp_format df) md (fread c sf rs1) in
            EDone (fwrite df rd v (accrue fl cn))
        | None, Some sf =>               (* float -> integer *)
            match ity dst with
            | None => EIllegal cn
            | Some (sgn, bits) =>
              let '(v, fl) := fp_to_int (fp_format sf) md sgn bits (fread c sf rs1) in
              EDone (rset rd (if Z.eqb bits 32%Z then sext 64 (Z_to_bv 32 v)
                              else Z_to_bv 64 v)
                          (accrue fl cn))
            end
        | Some df, None =>               (* integer -> float *)
            match ity src with
            | None => EIllegal cn
            | Some (sgn, bits) =>
              let '(v, fl) :=
                fp_of_int (fp_format df) md sgn bits (bv_unsigned (rget c rs1)) in
              EDone (fwrite df rd v (accrue fl cn))
            end
        | None, None => EIllegal cn
        end
      end
  end.

(** Fetch, decode, dispatch.  [decode_any] is supplied by the driver
    (32-bit decoder + compressed expansion) and returns the decoded
    instruction with its size in bytes (2 or 4).  For a 16-bit
    instruction the high half of the fetched word may be garbage or
    unmapped (unmapped reads return 0 in the concrete instance) —
    the decoder must ignore it.  On an undecodable word we issue
    [EIllegal] with pc NOT advanced. *)
Definition step (decode_any : bv 32 → option (instr * Z)) (c : core) : eff :=
  ELoad 32 (c_pc c) (λ w32,
    match decode_any w32 with
    | Some (i, isz) => exec (Z_to_bv 64 isz) i c
    | None => EIllegal c
    end).
