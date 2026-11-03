(** * Tests: the extracted ISA model refuses an input the Rocq type does not hold

    The companion of tests/CheckedInputWitness.v, for the second
    extracted artifact.  [Riscv/Extraction.v] used to tell its OCaml
    caller that it "must therefore mask values itself when constructing
    inputs"; these are the cases that hold the boundary to doing it
    instead.

    Each refusal has its in-range control beside it, so the tests cannot
    pass by refusing everything, and the two kinds of "no" stay apart: a
    word this model does not decode is [CkAnswer None], and a value that
    is not a word at all is [CkRefused]. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Prelude CheckedBv Instr Sem CheckedIsa.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The decoders                                                        *)
(* ------------------------------------------------------------------ *)

Example decode_refuses_2_32 : decode_checked 4294967296 = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example decode_refuses_negative : decode_checked (-1) = CkRefused.
Proof. vm_compute. reflexivity. Qed.

(** 0x00000013 is [addi x0, x0, 0] — the canonical nop — so this is both
    the in-range control and a check that the answer is the model's. *)
Example decode_takes_a_real_encoding :
  decode_checked 19 = CkAnswer (Some (OpImm ALU_ADD (Z_to_bv 5 0)
                                        (Z_to_bv 5 0) (Z_to_bv 12 0))).
Proof. vm_compute. reflexivity. Qed.

(** The top 32-bit word is a word: refusing it would be a narrowing. *)
Example decode_takes_the_top_word :
  decode_checked 4294967295 <> CkRefused.
Proof. vm_compute. discriminate. Qed.

Example decode16_refuses_2_16 : decode16_checked 65536 = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example decode16_takes_the_top_halfword :
  decode16_checked 65535 <> CkRefused.
Proof. vm_compute. discriminate. Qed.

Example expand_c_refuses_2_16 : expand_c_checked 65536 = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example expand_c_takes_a_halfword : expand_c_checked 1 <> CkRefused.
Proof. vm_compute. discriminate. Qed.

Example decode_any_refuses_2_32 : decode_any_checked 4294967296 = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example decode_any_takes_a_real_encoding :
  decode_any_checked 19 <> CkRefused.
Proof. vm_compute. discriminate. Qed.

(** A refusal is not the model declining an encoding: an undecodable
    word is an ANSWER, and the two must not be confused. *)
Example an_undecodable_word_is_answered_not_refused :
  decode_any_checked 4294967295 = CkAnswer None.
Proof. vm_compute. reflexivity. Qed.

Example is_defined_illegal_refuses_2_32 :
  is_defined_illegal_checked 4294967296 = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example is_defined_illegal_takes_the_zero_parcel :
  is_defined_illegal_checked 0 = CkAnswer true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The core state                                                      *)
(* ------------------------------------------------------------------ *)

Definition zeros32 : list Z := repeat 0 32.

Definition zero_core : RawCore := mkRawCore zeros32 zeros32 0 0 None.

Example zero_core_is_accepted : exists c, core_of_raw zero_core = Some c.
Proof. eexists. vm_compute. reflexivity. Qed.

(* word: the program counter *)
Example core_refuses_wide_pc :
  core_of_raw (mkRawCore zeros32 zeros32 18446744073709551616 0 None) = None.
Proof. vm_compute. reflexivity. Qed.

(* word: an integer register *)
Example core_refuses_wide_register :
  core_of_raw (mkRawCore (18446744073709551616 :: repeat 0 31) zeros32 0 0 None)
  = None.
Proof. vm_compute. reflexivity. Qed.

(* word: a floating-point register *)
Example core_refuses_wide_fregister :
  core_of_raw (mkRawCore zeros32 (18446744073709551616 :: repeat 0 31) 0 0 None)
  = None.
Proof. vm_compute. reflexivity. Qed.

(* word: a negative register value, the other side of the type *)
Example core_refuses_negative_register :
  core_of_raw (mkRawCore ((-1) :: repeat 0 31) zeros32 0 0 None) = None.
Proof. vm_compute. reflexivity. Qed.

(* bv 32: fcsr *)
Example core_refuses_wide_fcsr :
  core_of_raw (mkRawCore zeros32 zeros32 0 4294967296 None) = None.
Proof. vm_compute. reflexivity. Qed.

(* word: the LR/SC reservation address *)
Example core_refuses_wide_reservation :
  core_of_raw (mkRawCore zeros32 zeros32 0 0 (Some 18446744073709551616))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example core_takes_a_live_reservation :
  core_of_raw (mkRawCore zeros32 zeros32 0 0 (Some 4096)) <> None.
Proof. vm_compute. discriminate. Qed.

(** A register file of any other length is refused rather than padded:
    a caller that gives thirty-one values has not said what x31 is. *)
Example core_refuses_a_short_register_file :
  core_of_raw (mkRawCore (repeat 0 31) zeros32 0 0 None) = None.
Proof. vm_compute. reflexivity. Qed.

Example core_refuses_a_long_register_file :
  core_of_raw (mkRawCore (repeat 0 33) zeros32 0 0 None) = None.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Running one instruction                                             *)
(* ------------------------------------------------------------------ *)

Example exec_refuses_a_wide_encoding :
  exec_encoded_checked 4294967296 zero_core = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example exec_refuses_a_bad_core :
  exec_encoded_checked 19 (mkRawCore (repeat 0 31) zeros32 0 0 None)
  = CkRefused.
Proof. vm_compute. reflexivity. Qed.

Example exec_runs_a_real_encoding :
  exec_encoded_checked 19 zero_core <> CkRefused.
Proof. vm_compute. discriminate. Qed.

Example step_refuses_a_bad_core :
  step_checked (mkRawCore zeros32 zeros32 18446744073709551616 0 None)
  = CkRefused.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The value that arrives mid-execution                                *)
(* ------------------------------------------------------------------ *)

(** [step] opens with the instruction fetch, so the first thing the
    interpreter is asked for is a 32-bit load.  Answering it with an
    integer no 32-bit word holds is refused, not executed. *)
Example fetch_refuses_a_wide_answer :
  match step_checked zero_core with
  | CkAnswer e => eff_feed_load e 4294967296 = LsRefused
  | CkRefused => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example fetch_refuses_a_negative_answer :
  match step_checked zero_core with
  | CkAnswer e => eff_feed_load e (-1) = LsRefused
  | CkRefused => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The control: the nop encoding is a 32-bit word, so the fetch is
    answered and the step proceeds. *)
Example fetch_takes_a_real_answer :
  match step_checked zero_core with
  | CkAnswer e => eff_feed_load e 19 <> LsRefused
  | CkRefused => False
  end.
Proof. vm_compute. discriminate. Qed.

(** An effect that is not waiting for a load says so, and that is not a
    refusal either. *)
Example a_retired_effect_is_not_pending :
  forall c, eff_feed_load (EDone c) 0 = LsNotPending.
Proof. intro c. reflexivity. Qed.

Example a_retired_effect_has_no_pending_load :
  forall c, eff_pending_load (EDone c) = None.
Proof. intro c. reflexivity. Qed.
