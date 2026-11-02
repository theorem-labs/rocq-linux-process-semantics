(** * Segment payload chunks are invisible to memory semantics

    [elf-snapshot] divides a large logical ELF segment into bounded primitive
    strings.  These checks pin the load and fetch behavior at the join: the
    join is not a mapping or permission boundary. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

Definition chunked_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 5;
  seg_perms := "r-x";
  seg_bytes := ["1122"%pstring; "334455"%pstring];
  seg_kind  := SegLoader
|}.

Definition chunked_segments : list Segment := [chunked_segment].

Example chunk_join_byte_before :
  segment_byte_at (seg_bytes chunked_segment) 1 = Some (Z_to_bv 8 0x22).
Proof. vm_compute. reflexivity. Qed.

Example chunk_join_byte_after :
  segment_byte_at (seg_bytes chunked_segment) 2 = Some (Z_to_bv 8 0x33).
Proof. vm_compute. reflexivity. Qed.

Example data_read_crosses_chunk_join :
  memory_read chunked_segments (Z_to_bv 64 0x101) 4 =
    Some [Z_to_bv 8 0x22; Z_to_bv 8 0x33;
          Z_to_bv 8 0x44; Z_to_bv 8 0x55].
Proof. vm_compute. reflexivity. Qed.

Example instruction_fetch_crosses_chunk_join :
  fetch_word chunked_segments (Z_to_bv 64 0x100) =
    Some (Z_to_bv 32 0x44332211).
Proof. vm_compute. reflexivity. Qed.
