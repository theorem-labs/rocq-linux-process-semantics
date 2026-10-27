(** * LinuxProcessSem.Checks.MmStepFrame — what a successful mmap, mremap or brk leaves alone

    Not part of the trusted specification: three facts about every [Ok]
    outcome [Specs.syscall_spec] admits for mmap (222), mremap (216) and
    brk (214), stated for a consumer that steps a run across one of them.

    - [mm_ok_keeps_halted]: the call does not change [m_halted].  Every
      post-model these arms build is [with_vmmaps], [with_vm_backing] or
      one of the wrappers over them ([with_brk_next], [with_mmap_backing],
      [with_mmap_replacement], [with_mmap_destroyed],
      [mremap_model_next]), and none of them rebuilds [ProcState].
    - [mm_ok_no_accesses]: the effect names no user-memory access
      ([State.syscall_effect_accesses] is [[]]).  No arm records a
      copy-in or a byte write: mmap is anonymous-only, the bytes a grow
      exposes are [eff_zeros], and a move is an [eff_copies] entry —
      neither of which [syscall_effect_accesses] counts.
    - [mm_ok_step]: the two together, for a consumer of the run rule
      [Run.sstep_syscall]: from a live model the post-model is live and
      not killed, the effect names no access, and materializing no
      access is the identity on the post-model.

    Each arm is walked through its checker ([check_syscall_complete_ok]
    and the [DispatchCompute] rewrite for its number), which is a function
    of the effect, so the walk is a case split and nothing else. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
Import ListNotations.

(* -------------------------------------------------------------------------
   The post-model wrappers keep [m_halted]
   ------------------------------------------------------------------------- *)

Lemma m_halted_forget_vm_ranges : forall rs m,
  m_halted (forget_vm_ranges rs m) = m_halted m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma m_halted_with_brk_next : forall m req r,
  m_halted (with_brk_next m req r) = m_halted m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite m_halted_forget_vm_ranges. reflexivity.
Qed.

Lemma m_halted_with_mmap_backing : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma m_halted_with_mmap_replacement : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite m_halted_with_mmap_backing. reflexivity.
Qed.

Lemma m_halted_with_mmap_destroyed : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_halted_mremap_model_next : forall m old old_n dst new_n,
  m_halted (mremap_model_next m old old_n dst new_n) = m_halted m.
Proof. reflexivity. Qed.

(** Materializing no access is the identity on any model. *)
Lemma materialize_model_accesses_none : forall m,
  materialize_model_accesses m [] = Some m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* -------------------------------------------------------------------------
   The three checkers
   ------------------------------------------------------------------------- *)

(** Split [H] on every [if] and [match] until it is a leaf: a
    [CheckOk _ _ = CheckOk _ _] for the caller, or a refusal that
    [discriminate] closes. *)
Local Ltac walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 end
          end);
  try discriminate H.

Local Ltac leaf H :=
  injection H as <- <-; split;
  [ rewrite ?m_halted_with_mmap_backing, ?m_halted_with_mmap_replacement,
            ?m_halted_with_brk_next, ?m_halted_with_mmap_destroyed,
            ?m_halted_mremap_model_next;
    reflexivity
  | reflexivity ].

Lemma check_brk_mm_frame : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  m_halted m' = m_halted m /\ syscall_effect_accesses eff = [].
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. walk H. all: leaf H.
Qed.

Lemma check_mmap_mm_frame : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  m_halted m' = m_halted m /\ syscall_effect_accesses eff = [].
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap, check_ret_only in H. walk H. all: leaf H.
Qed.

Lemma check_mremap_mm_frame : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  m_halted m' = m_halted m /\ syscall_effect_accesses eff = [].
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. walk H. all: leaf H.
Qed.

(* -------------------------------------------------------------------------
   Through the dispatcher
   ------------------------------------------------------------------------- *)

Lemma mm_ok_frame : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [222; 216; 214]%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  m_halted m' = m_halted m /\ syscall_effect_accesses eff = [].
Proof.
  intros i m eff m' evs Hin Hspec.
  apply check_syscall_complete_ok in Hspec.
  destruct Hin as [E | [E | [E | []]]]; symmetry in E.
  - rewrite (check_syscall_mmap i eff m E) in Hspec.
    exact (check_mmap_mm_frame _ _ _ _ _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_mremap i eff m E) in Hspec.
    exact (check_mremap_mm_frame _ _ _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_brk i eff m E) in Hspec.
    exact (check_brk_mm_frame _ _ _ _ _ Hspec).
Qed.

Theorem mm_ok_keeps_halted : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [222; 216; 214]%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  m_halted m' = m_halted m.
Proof. intros i m eff m' evs Hin Hspec. exact (proj1 (mm_ok_frame i m eff m' evs Hin Hspec)). Qed.

Theorem mm_ok_no_accesses : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [222; 216; 214]%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  syscall_effect_accesses eff = [].
Proof. intros i m eff m' evs Hin Hspec. exact (proj2 (mm_ok_frame i m eff m' evs Hin Hspec)). Qed.

Theorem mm_ok_step : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [222; 216; 214]%Z ->
  m_halted m = None ->
  syscall_spec i m (Ok eff m' evs) ->
  m_halted m' = None /\ m_killed m' = None /\
  syscall_effect_accesses eff = [] /\ materialize_model_accesses m' [] = Some m'.
Proof.
  intros i m eff m' evs Hin Hh Hspec.
  destruct (mm_ok_frame i m eff m' evs Hin Hspec) as [Hh' Hacc].
  rewrite Hh in Hh'.
  split; [exact Hh'|].
  split; [exact (m_killed_of_m_halted_none m' Hh')|].
  split; [exact Hacc|].
  apply materialize_model_accesses_none.
Qed.
