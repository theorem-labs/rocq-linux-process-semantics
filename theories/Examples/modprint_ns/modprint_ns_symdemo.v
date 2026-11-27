(** * modprint_ns — REFLECTIVE vs TACTIC symbolic execution, side by side.

    EXPLORATION / PROTOTYPE (see [Common/SymExec.v]).

    Both halves of this file prove the SAME lemma about the same real block
    of the modprint_ns source binary: the 7-instruction musl-[write]
    argument shuffle at 0x1109c..0x110b4, entered from the [write] prologue
    (a0 = fd = 1, a1 = buf = 0x13000, a2 = len = 2, ra = 0x11034, sp
    symbolic) and stopping at the [sd ra,8(sp)] at 0x110b8.

      - [block_tactic]    — the existing route: one [stepiv]/[step_*] block
                            per instruction, with a hand-supplied normalized
                            value and a register-resolution script.
                            This is a faithful transcription of
                            [modprint_ns_source.v:269-311].
      - [block_reflective] — one application of [SymExec.sym_exec_sound]
                            whose hypothesis is discharged by [vm_compute].

    Both are [Time]d so the build log carries the comparison. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac SymExec.
From LinuxProcessSemantics.Examples.modprint_ns Require Import
  modprint_ns_code SourceMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The block's states carry the FP state of process entry; no
    instruction here touches it. *)
#[local] Instance modprint_ns_symdemo_fx : FPState := fx0.

(** The post-state the block is supposed to establish (musl's raw-syscall
    register layout: a0 = SYS_write = 64, a1 = fd, a2 = buf, a3 = len,
    a4/a5/a6 = 0), plus the two callee registers it must not have touched. *)
Definition block_post (rsp : word) (regs' : bvmap 5 word) : Prop :=
     getr regs' 10 = Z_to_bv 64 64
  /\ getr regs' 11 = Z_to_bv 64 1
  /\ getr regs' 12 = Z_to_bv 64 0x13000
  /\ getr regs' 13 = Z_to_bv 64 2
  /\ getr regs' 14 = Z_to_bv 64 0
  /\ getr regs' 15 = Z_to_bv 64 0
  /\ getr regs' 16 = Z_to_bv 64 0
  /\ getr regs' 1  = Z_to_bv 64 0x11034
  /\ getr regs' 2  = rsp.

Definition block_spec (mem rom : word -> option byte)
                      (rsp : word) (regs : bvmap 5 word) : Prop :=
  exists regs' pc',
    msteps source_segs (mkst regs (Z_to_bv 64 0x1109c) mem rom)
                       (mkst regs' pc' mem rom)
    /\ pc' = Z_to_bv 64 0x110b8
    /\ block_post rsp regs'.

Section Demo.

Variables mem rom : word -> option byte.
Variable rsp : word.
Variable regs : bvmap 5 word.

Hypothesis Hra  : getr regs 1  = Z_to_bv 64 0x11034.
Hypothesis Hsp  : getr regs 2  = rsp.
Hypothesis Ha0  : getr regs 10 = Z_to_bv 64 1.
Hypothesis Ha1  : getr regs 11 = Z_to_bv 64 0x13000.
Hypothesis Ha2  : getr regs 12 = Z_to_bv 64 2.

(** [getr_resolve] leaves a base lookup as [reg_get]; restate the entry
    facts in that form once, so neither route below is charged for it. *)
Lemma Rra : reg_get regs 1  = Z_to_bv 64 0x11034.
Proof. rewrite <- getr_nz by reg_neq_tac. exact Hra. Qed.
Lemma Rsp : reg_get regs 2  = rsp.
Proof. rewrite <- getr_nz by reg_neq_tac. exact Hsp. Qed.
Lemma Ra0 : reg_get regs 10 = Z_to_bv 64 1.
Proof. rewrite <- getr_nz by reg_neq_tac. exact Ha0. Qed.
Lemma Ra1 : reg_get regs 11 = Z_to_bv 64 0x13000.
Proof. rewrite <- getr_nz by reg_neq_tac. exact Ha1. Qed.
Lemma Ra2 : reg_get regs 12 = Z_to_bv 64 2.
Proof. rewrite <- getr_nz by reg_neq_tac. exact Ha2. Qed.

(* ========================================================================= *)
(* A. The existing route: one tactic block per instruction.                  *)
(* ========================================================================= *)

Lemma block_tactic : block_spec mem rom rsp regs.
Proof.
  Time (
  unfold block_spec; do 2 eexists; split;
  [ (* 0x1109c: mv a3,a2 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 2);
        [ exact SF_1109c | reflexivity | exact SD_1109c | reflexivity
        | getr_resolve; rewrite Ra2, v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110a0: li a6,0 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0);
        [ exact SF_110a0 | reflexivity | exact SD_110a0 | reflexivity
        | getr_resolve; rewrite v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110a4: mv a2,a1 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0x13000);
        [ exact SF_110a4 | reflexivity | exact SD_110a4 | reflexivity
        | getr_resolve; rewrite Ra1, v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110a8: li a5,0 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0);
        [ exact SF_110a8 | reflexivity | exact SD_110a8 | reflexivity
        | getr_resolve; rewrite v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110ac: mv a1,a0 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact SF_110ac | reflexivity | exact SD_110ac | reflexivity
        | getr_resolve; rewrite Ra0, v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110b0: li a4,0 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0);
        [ exact SF_110b0 | reflexivity | exact SD_110b0 | reflexivity
        | getr_resolve; rewrite v_addi_0; reflexivity ]
      | norm_pc ];
    (* 0x110b4: li a0,64 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 64);
        [ exact SF_110b4 | reflexivity | exact SD_110b4 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ];
    apply mst_refl
  | split; [ bveq | unfold block_post; repeat split;
             getr_resolve;
             first [ exact Rra | exact Rsp | bveq ] ] ]).
Qed.

(* ========================================================================= *)
(* B. The reflective route.                                                  *)
(* ========================================================================= *)

(** The block's entry state, as deep syntax: start from "nothing known"
    ([sr_id], every register its own variable) and pin the four registers
    the caller has facts about.  sp stays [EVar 2] — the reflective route
    never needs to know what the ASLR stack pointer is. *)
Definition ss_entry : sym_state :=
  SS 0x1109c
     (sr_upd (sr_upd (sr_upd (sr_upd sr_id (ridx 1) (ELit 0x11034))
                             (ridx 10) (ELit 1))
                     (ridx 11) (ELit 0x13000))
             (ridx 12) (ELit 2))
     [] 32.

(** The block's exit state — COMPUTED, not written by hand. *)
Definition ss_exit : sym_state :=
  Eval vm_compute in fst (sym_exec source_segs 7 [] [] ss_entry []).

Lemma block_reflective : block_spec mem rom rsp regs.
Proof.
  Time (
  (* 1. the entry state denotes the concrete one *)
  assert (Hst : st_ok (E0 regs) mem rom ss_entry (mkst regs (Z_to_bv 64 0x1109c) mem rom))
    by (eexists; split; [reflexivity|]; split; [| exact I];
        cbn [ss_entry s_regs];
        repeat (apply regs_ok_pin;
                [| cbn [edenot]; first [exact Hra|exact Ha0|exact Ha1|exact Ha2]]);
        apply regs_ok_id);
  (* 2. ONE reflective step over the whole block *)
  destruct (sym_exec_sound source_segs 7 [] [] ss_entry [] ss_exit []
              (E0 regs) mem rom _ ltac:(vm_compute; reflexivity)
              (Forall_nil _) Hst)
    as (ms' & Hms & (regs' & -> & Hr' & _));
  (* 3. read the post-condition off the symbolic exit state *)
  unfold block_spec; exists regs', (Z_to_bv 64 (s_pc ss_exit));
  split; [exact Hms | split; [vm_compute; reflexivity|]];
  unfold block_post; repeat split; rewrite (Hr' _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end;
  cbn [edenot E0];
  first [ reflexivity
        | rewrite <- Hsp; f_equal; apply bv_eq; vm_compute; reflexivity ]).
Qed.

End Demo.
