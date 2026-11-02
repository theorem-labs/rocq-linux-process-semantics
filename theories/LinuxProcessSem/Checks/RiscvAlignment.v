(** * LinuxProcessSem.Checks.RiscvAlignment — instruction-fetch alignment checks

    Regression checks for the IALIGN=32 gate in [fetch_word].  The
    misaligned addresses below are deliberately mapped, executable, and
    backed by enough bytes: they would all be readable through [code_read],
    so only the PC-alignment rule can make the fetch and step fail.

    [fetch_word] gates on [addr mod 2], not [addr mod 4]: with compressed
    instructions modeled, [pc ≡ 2 (mod 4)] is a legal (halfword-aligned)
    fetch address, so only the odd residues below are actually rejected. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

(** Two aligned instructions: ECALL at [0x100], then ADDI x0,x0,0 at
    [0x104].  Eight bytes also make every four-byte read starting at
    [0x101], [0x102], or [0x103] stay within the executable segment. *)
Definition alignment_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 8;
  seg_perms := "r-x";
  seg_bytes := ["7300000013000000"%pstring];
  seg_kind  := SegLoader
|}.

Definition alignment_segments : list Segment := [alignment_segment].

Definition alignment_state (pc : word) : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := pc;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None;
  ms_rom := fun _ => None
|}.

(** Each misaligned range is otherwise a successful instruction-memory
    read.  These checks keep the tests from passing because of a fixture
    boundary or permission mistake instead of the alignment gate. *)
Example code_read_misaligned_mod_1_is_mapped :
  code_read alignment_segments (Z_to_bv 64 0x101) 4
    = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0x13].
Proof. vm_compute. reflexivity. Qed.

Example code_read_misaligned_mod_2_is_mapped :
  code_read alignment_segments (Z_to_bv 64 0x102) 4
    = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0x13; Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Example code_read_misaligned_mod_3_is_mapped :
  code_read alignment_segments (Z_to_bv 64 0x103) 4
    = Some [Z_to_bv 8 0; Z_to_bv 8 0x13; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

(** Aligned fetches remain unchanged at both instruction boundaries. *)
Example fetch_aligned_ecall :
  fetch_word alignment_segments (Z_to_bv 64 0x100) = Some (Z_to_bv 32 0x73).
Proof. vm_compute. reflexivity. Qed.

Example fetch_aligned_addi :
  fetch_word alignment_segments (Z_to_bv 64 0x104) = Some (Z_to_bv 32 0x13).
Proof. vm_compute. reflexivity. Qed.

(** Odd addresses fault even though the underlying four-byte range is
    executable and mapped; [pc ≡ 2 (mod 4)] is halfword-aligned and
    therefore a legal (compressed-instruction) fetch address, so it
    reads the four-byte word straddling the two instructions instead
    of faulting. *)
Example fetch_misaligned_mod_1 :
  fetch_word alignment_segments (Z_to_bv 64 0x101) = None.
Proof. vm_compute. reflexivity. Qed.

Example fetch_halfword_aligned_mod_2 :
  fetch_word alignment_segments (Z_to_bv 64 0x102) = Some (Z_to_bv 32 0x130000).
Proof. vm_compute. reflexivity. Qed.

Example fetch_misaligned_mod_3 :
  fetch_word alignment_segments (Z_to_bv 64 0x103) = None.
Proof. vm_compute. reflexivity. Qed.

(** Pin the externally visible machine-step behavior, not just the helper:
    a valid aligned instruction steps, while each misaligned initial PC is
    [MachineFault]. *)
Example step_aligned_succeeds :
  match step alignment_segments (alignment_state (Z_to_bv 64 0x100)) with
  | MachineOk _ => True
  | _ => False
  end.
Proof. vm_compute. exact I. Qed.

Example step_misaligned_mod_1 :
  step alignment_segments (alignment_state (Z_to_bv 64 0x101)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** The word fetched at this halfword-aligned PC is [0x130000], whose
    LOW parcel is the all-zero halfword the ISA defines illegal
    ([DecodeC.is_defined_illegal]), so the step faults through the
    defined-illegal path rather than the alignment gate: real hardware
    traps on this parcel too (SIGILL), so it is a [MachineFault] like
    the misaligned fetches around it — not [MachineUnmodeled].  (See
    [Checks.RiscvDefinedIllegal] for the classification checks proper.) *)
Example step_halfword_aligned_mod_2 :
  step alignment_segments (alignment_state (Z_to_bv 64 0x102)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example step_misaligned_mod_3 :
  step alignment_segments (alignment_state (Z_to_bv 64 0x103)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.
