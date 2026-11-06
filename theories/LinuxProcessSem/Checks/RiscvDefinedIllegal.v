(** * LinuxProcessSem.Checks.RiscvDefinedIllegal — defined-illegal encodings fault

    Classification checks for [DecodeC.is_defined_illegal]: a word
    [decode_any] rejects is normally [MachineUnmodeled] (the MODEL gave
    up — it may be a decoder hole), but the all-zero 16-bit parcel is
    defined illegal by the ISA in every implementation, so real hardware
    traps and the process takes SIGILL — a failure the real process also
    suffers, hence [MachineFault] (see the [machine_result] taxonomy in
    [RiscvSemantics]).

    The fixtures pin both sides of the split on the same shape: the same
    segment layout holding all-zero bytes (defined illegal → fault)
    versus all-ones bytes (merely unallocated/reserved space →
    unmodeled).

    The second half of the file is the same split one layer up, where
    the word DECODES.  [is_defined_illegal] is consulted only when
    [decode_any] fails, so it cannot see an architecturally illegal
    instruction that decodes fine — the standing example being GNU as's
    [unimp] (0xc0001073 = csrrw x0, cycle, x0), which is what a
    -fsanitize-trap binary executes when a check fires.  That decision
    belongs to [Sem.exec], which answers [Sem.EDefinedIllegal] and gets
    the same [MachineFault]; the contrast fixtures are the CSR
    instructions on the SAME read-only address that do not write, which
    stay this model's own decline. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Instr Decode DecodeC.
(* NOT [Import]ed: [Sem.step] would shadow [RiscvSemantics.step], which is
   the function every check below is about. *)
From LinuxProcessSemantics.Riscv Require Sem.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

Definition st0 (segs : list Segment) (pc : word) : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := pc;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None;
  ms_rom := fun _ => None
|}.

(** A 4-byte executable segment of zeroed memory — the shape a wild jump
    into a zero-filled page lands on, which is exactly why the ISA
    defines the all-zero parcel illegal. *)
Definition zero_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x";
  seg_bytes := ["00000000"%pstring];
  seg_kind  := SegLoader
|}.
Definition zero_segments : list Segment := [zero_segment].

(** The fetch itself succeeds — the bytes are mapped and executable —
    so the classification below is [decode_exec]'s, not the fetch
    layer's. *)
Example zero_fetch_ok :
  fetch_word zero_segments (Z_to_bv 64 0x100) = Some (Z_to_bv 32 0).
Proof. vm_compute. reflexivity. Qed.

Example zero_word_undecodable :
  decode_any (Z_to_bv 32 0) = None.
Proof. vm_compute. reflexivity. Qed.

Example zero_word_defined_illegal :
  is_defined_illegal (Z_to_bv 32 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** THE CHECK: stepping onto the all-zero word is a fault the real
    process suffers too (SIGILL), not the model giving up. *)
Example zero_step_fault :
  step zero_segments (st0 zero_segments (Z_to_bv 64 0x100)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** A 2-byte segment holding only the zero parcel: the all-zero halfword
    is a complete 16-bit illegal instruction on its own, so it faults
    even when no further bytes are mapped (the length-correct
    [fetch_tail] path). *)
Definition zero2_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 2;
  seg_perms := "r-x";
  seg_bytes := ["0000"%pstring];
  seg_kind  := SegLoader
|}.
Definition zero2_segments : list Segment := [zero2_segment].

Example zero2_step_fault :
  step zero2_segments (st0 zero2_segments (Z_to_bv 64 0x100)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** An all-zero LOW parcel under a nonzero upper halfword is still the
    defined-illegal instruction — the parcel is 16 bits long, and the
    following bytes are simply the next (never-reached) parcel. *)
Definition zerolow_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x";
  seg_bytes := ["00001300"%pstring];
  seg_kind  := SegLoader
|}.
Definition zerolow_segments : list Segment := [zerolow_segment].

Example zerolow_step_fault :
  step zerolow_segments (st0 zerolow_segments (Z_to_bv 64 0x100)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** CONTRAST: the all-ones word is also undecodable, but the ISA does
    NOT define it illegal from a 32-bit window (all-ones is illegal only
    across all ILEN bits, and the low bits announce a longer encoding a
    future extension could give meaning to) — so it stays the model's
    own limit. *)
Definition ones_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x";
  seg_bytes := ["ffffffff"%pstring];
  seg_kind  := SegLoader
|}.
Definition ones_segments : list Segment := [ones_segment].

Example ones_word_not_defined_illegal :
  is_defined_illegal (Z_to_bv 32 0xffffffff) = false.
Proof. vm_compute. reflexivity. Qed.

Example ones_step_unmodeled :
  step ones_segments (st0 ones_segments (Z_to_bv 64 0x100)) = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** * Defined-illegal instructions that DECODE

    csr[11:10] = 11 marks a read-only CSR address, and writing one raises
    an illegal-instruction exception in every conforming implementation
    at every privilege level (RISC-V unprivileged spec, CSR Address
    Mapping Conventions; the argument is on [Sem.csr_write_illegal]).
    The address alone settles it, so the rule reaches addresses this
    model does not implement — which is the whole point, since the
    instruction the toolchain picked for "always illegal" names one. *)

(** The predicate reads the two top bits and nothing else, so the cases
    that matter are the boundary and the addresses a reader would expect
    it to claim and it does not. *)
Example csr_ro_cycle : Sem.csr_read_only (Z_to_bv 12 0xc00) = true.
Proof. vm_compute. reflexivity. Qed.
Example csr_ro_top : Sem.csr_read_only (Z_to_bv 12 0xfff) = true.
Proof. vm_compute. reflexivity. Qed.
Example csr_ro_fcsr : Sem.csr_read_only (Z_to_bv 12 0x003) = false.
Proof. vm_compute. reflexivity. Qed.
(** 0xbff is the last read/WRITE address; 0xc00 the first read-only one. *)
Example csr_ro_just_below : Sem.csr_read_only (Z_to_bv 12 0xbff) = false.
Proof. vm_compute. reflexivity. Qed.
(** mstatus is read/write.  Writing it from user mode is illegal too, but
    for a reason about the HART rather than about the instruction, so
    this predicate does not claim it — see [Sem.csr_read_only]. *)
Example csr_ro_mstatus : Sem.csr_read_only (Z_to_bv 12 0x300) = false.
Proof. vm_compute. reflexivity. Qed.

(** [unimp] is a well-formed Zicsr instruction: the decoder accepts it,
    and [is_defined_illegal] — which only ever sees words the decoder
    REJECTED — says nothing about it.  These two are why the fault has to
    be issued by [exec]. *)
Example unimp_decodes :
  match decode_any (Z_to_bv 32 0xc0001073) with
  | Some _ => true | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example unimp_not_flagged_by_decode_hook :
  is_defined_illegal (Z_to_bv 32 0xc0001073) = false.
Proof. vm_compute. reflexivity. Qed.

(** A 4-byte executable segment holding one instruction word, given in
    memory (little-endian) byte order. *)
Definition word_segment (hex : PrimString.string) : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x";
  seg_bytes := [hex];
  seg_kind  := SegLoader
|}.
Definition word_segments (hex : PrimString.string) : list Segment :=
  [word_segment hex].

Definition step_word (hex : PrimString.string) : machine_result machine_state :=
  step (word_segments hex) (st0 (word_segments hex) (Z_to_bv 64 0x100)).

(** THE CHECK, in the shape the sanitizer emits it: `unimp`, the word a
    -fsanitize-trap check executes when it fires, is the process dying of
    SIGILL — not the model giving up. *)
Example unimp_step_fault : step_word "731000c0"%pstring = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** The rule is about the write side, not about that one encoding.
    `csrs cycle, x1` (0xc000a073) writes because rs1 /= x0... *)
Example csrs_readonly_step_fault : step_word "73a000c0"%pstring = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** ...and `csrwi cycle, 1` (0xc000d073) writes because csrrwi always
    does, whatever the immediate. *)
Example csrwi_readonly_step_fault : step_word "73d000c0"%pstring = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** CONTRAST 1: `rdcycle x1` (0xc00020f3 = csrrs x1, cycle, x0) reads the
    SAME read-only address and rs1 = x0, so it does not write and the
    architecture does not define it illegal.  This model has no [cycle]
    counter, so it declines — and the decline must stay a decline.  A
    rule keyed on the address instead of on the write would fault here,
    claiming a death for an instruction a real process survives. *)
Example rdcycle_step_unmodeled : step_word "f32000c0"%pstring = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** CONTRAST 2: the immediate form, `csrrsi x1, cycle, 0` (0xc00060f3).
    uimm = 0 suppresses the write for csrrsi/csrrci exactly as rs1 = x0
    does for csrrs/csrrc, so this is a legal read too. *)
Example csrrsi_zero_step_unmodeled :
  step_word "f36000c0"%pstring = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** CONTRAST 3: a write to a read/WRITE address the model does implement
    still retires.  `fscsr x1, x2` (0x003110f3 = csrrw x1, fcsr, x2)
    would be the casualty of a gate that fired on the write alone. *)
Example fscsr_step_retires :
  match step_word "f3103100"%pstring with
  | MachineOk _ => true | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
