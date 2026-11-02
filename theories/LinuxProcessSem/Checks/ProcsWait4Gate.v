(** * LinuxProcessSem.Checks.ProcsWait4Gate — the [wait4] gate, pinned

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header.  It earns its
    place under that file's FIRST reason: every statement here is
    UNIVERSALLY QUANTIFIED over configurations, entries and argument
    words, which no finite set of runs can establish.

    ** What this pins, and why it is not decoration

    [Exit.wait4_spec] is the one-process answer to [wait4]: correct only
    for a caller with nothing to reap.  In [Procs] a child is an entry of
    the process table, so a caller with one must never reach that spec,
    and nothing in the type of [Procs.pstep_at] says so: the gate is a
    premise ([Procs.wait4_owned_b] = false) on two arms among eight, and
    deleting it from either leaves every proof of [Procs] closing.  These
    statements are what stop closing.

    - [owned_wait4_never_released] and its extension twin
      [owned_wait4_never_released_x]: every step of a caller with a child
      in the table, at a pending 260, is one of the core's own outcomes --
      a reap, the WNOHANG zero, or the refusal -- and the statement of
      that outcome mentions neither [Run.sstep_cfg] nor the extension.
      No released step, and no claimed answer, can be what justified it.
    - [owned_nonblocking_wait4_steps] and its twin: such a caller's
      [wait4] in any shape but the blocking one ALWAYS has a step.  In
      [Procs] no arm means blocked, so a non-blocking call left without an
      arm would be modeled as a sleep; this is what rules that out.

    ** What it does NOT claim

    Nothing here says the WNOHANG answers are Linux's in every detail: the
    usage record a reap writes into a non-NULL [ru] is the environment's
    choice ([Procs]'s design note at the gate), and a killed child is a
    refusal rather than an answer until its status word is modeled. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** The outcomes the gate's arms give a caller with a child in the table:
    a reap of a halted child, the WNOHANG zero, or the refusal.  Stated
    without [Run.sstep_cfg] on purpose. *)
Definition wait4_core_outcome (segs : list Segment) (P : pconfig) (e : ProcessEntry)
    (evs : list event) (r : pstep_to) : Prop :=
  evs = []
  /\ ( (exists q ez eff model'',
          look P q = Some ez /\ q <> pe_pid e /\ pe_parent ez = Some (pe_pid e)
          /\ pe_zombie ez <> None /\ eff_ret eff = q
          /\ r = PNext (wait4_reap_result P e q eff model''))
     \/ (List.existsb pe_zombie_b (children_of P (pe_pid e)) = false
         /\ r = PNext (wait4_zero_result P e))
     \/ (wait4_refused_b segs P e = true /\ r = PError) ).

(** A child the reap arms take is a zombie: [pe_status] answers only for
    a halted entry. *)
Lemma pe_status_zombie : forall dumped ez status,
  pe_status dumped ez = Some status -> pe_zombie ez <> None.
Proof.
  intros dumped ez status H Hz. unfold pe_zombie in Hz. unfold pe_status in H.
  rewrite Hz in H. discriminate H.
Qed.

(** The surface guard of the extension is open wherever the gate is. *)
Lemma multiproc_ok_owned : forall ext segs P e,
  wait4_owned_b P e = true -> multiproc_ok ext segs P e = true.
Proof.
  intros ext segs P e H. unfold multiproc_ok. cbv zeta.
  rewrite (wait4_owned_allowed P e H). reflexivity.
Qed.

(** THE RELEASED STEP NEVER ANSWERS A [wait4] OF A CALLER WITH A CHILD. *)
Theorem owned_wait4_never_released : forall segs cfg p P e evs r,
  look P p = Some e ->
  wait4_owned_b P e = true ->
  pstep_at segs cfg p P evs r ->
  wait4_core_outcome segs P e evs r.
Proof.
  intros segs cfg p P e evs r Hl Hwo Hp. revert Hl Hwo.
  destruct Hp as
    [ Q e0 ev c' Hl0 Hs Hsucc Hwt Hma Hwo0
    | Q e0 ev c' q Hl0 Hs Hsucc Hq Hfree Hma
    | Q e0 q ez x8 stat_addr status eff model'' dumped
        Hl0 Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
    | Q e0 ev Hl0 Hs Hwt Hwo0
    | Q e0 Hl0 Hh Hma
    | Q e0 q ez x8 stat_addr ru ru_bytes status eff model'' dumped
        Hl0 Hh Hx8 Hwo0 Hna Hru Hq Hne Hpar Hk Hst Hrd Hlen Heff Hmat
    | Q e0 x8 stat_addr ru Hl0 Hh Hx8 Hwo0 Hna Hru Hz
    | Q e0 Hl0 Hh Hrf ]; intros Hl Hwo;
    rewrite Hl0 in Hl; injection Hl as Hl; subst e0.
  - (* pstep_other: behind the gate *)
    rewrite Hwo0 in Hwo. discriminate Hwo.
  - (* pstep_clone: a clone is not a [wait4] *)
    rewrite (clone_pending_not_owned Q e (clone_success_pending _ _ Hsucc)) in Hwo.
    discriminate Hwo.
  - (* pstep_wait_reap *)
    split; [reflexivity|]. left. exists q, ez, eff, model''.
    split; [exact Hq|]. split; [exact Hne|]. split; [exact Hpar|].
    split; [exact (pe_status_zombie _ _ _ Hst)|].
    split; [subst eff; reflexivity | reflexivity].
  - (* pstep_error: behind the gate *)
    rewrite Hwo0 in Hwo. discriminate Hwo.
  - (* pstep_outside: 260 is on the surface *)
    rewrite (wait4_owned_allowed Q e Hwo) in Hma. discriminate Hma.
  - (* pstep_wait_nohang_reap *)
    split; [reflexivity|]. left. exists q, ez, eff, model''.
    split; [exact Hq|]. split; [exact Hne|]. split; [exact Hpar|].
    split; [exact (pe_status_zombie _ _ _ Hst)|].
    split; [subst eff; reflexivity | reflexivity].
  - (* pstep_wait_nohang_zero *)
    split; [reflexivity|]. right; left. split; [exact Hz | reflexivity].
  - (* pstep_wait_refuse *)
    split; [reflexivity|]. right; right. split; [exact Hrf | reflexivity].
Qed.

(** NOR DOES THE EXTENSION, claimed or not. *)
Theorem owned_wait4_never_released_x : forall ext cenv segs cfg p P e evs r,
  look P p = Some e ->
  wait4_owned_b P e = true ->
  pstep_x_at ext cenv segs cfg p P evs r ->
  wait4_core_outcome segs P e evs r.
Proof.
  intros ext cenv segs cfg p P e evs r Hl Hwo Hp. revert Hl Hwo.
  destruct Hp as
    [ Q e0 ev c' ctx' st' Hl0 Hx Hcp Hwt Hwo0 Hmp
    | Q e0 ev c' q child ret st' Hl0 Hcl Hs Hsucc Hq Hfree Hma Hec
    | Q e0 ev c' en hq st' Hl0 Hcl Hs Hcp Hsucc Hret Hma Hec Hnr
    | Q e0 ev c' hq Hl0 Hcl Hs Hcp Hma Hec
    | Q e0 Hl0 Hh Hcp Hcl
    | Q e0 q ez x8 stat_addr status eff model'' dumped
        Hl0 Hcl Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
    | Q e0 ev ctx' st' Hl0 Hx Hwt Hwo0
    | Q e0 Hl0 Hh Hmp
    | Q e0 q ez x8 stat_addr ru ru_bytes status eff model'' dumped
        Hl0 Hh Hx8 Hwo0 Hna Hru Hq Hne Hpar Hk Hst Hrd Hlen Heff Hmat
    | Q e0 x8 stat_addr ru Hl0 Hh Hx8 Hwo0 Hna Hru Hz
    | Q e0 Hl0 Hh Hrf ]; intros Hl Hwo;
    rewrite Hl0 in Hl; injection Hl as Hl; subst e0.
  - (* px_other: behind the gate *)
    rewrite Hwo0 in Hwo. discriminate Hwo.
  - (* px_clone *)
    rewrite (clone_pending_not_owned Q e (clone_success_pending _ _ Hsucc)) in Hwo.
    discriminate Hwo.
  - (* px_clone_fail *)
    rewrite (clone_pending_not_owned Q e Hcp) in Hwo. discriminate Hwo.
  - (* px_clone_unmodeled *)
    rewrite (clone_pending_not_owned Q e Hcp) in Hwo. discriminate Hwo.
  - (* px_clone_claimed *)
    rewrite (clone_pending_not_owned Q e Hcp) in Hwo. discriminate Hwo.
  - (* px_wait_reap *)
    split; [reflexivity|]. left. exists q, ez, eff, model''.
    split; [exact Hq|]. split; [exact Hne|]. split; [exact Hpar|].
    split; [exact (pe_status_zombie _ _ _ Hst)|].
    split; [subst eff; reflexivity | reflexivity].
  - (* px_error: behind the gate *)
    rewrite Hwo0 in Hwo. discriminate Hwo.
  - (* px_outside: 260 is on the surface *)
    rewrite (multiproc_ok_owned ext segs Q e Hwo) in Hmp. discriminate Hmp.
  - (* px_wait_nohang_reap *)
    split; [reflexivity|]. left. exists q, ez, eff, model''.
    split; [exact Hq|]. split; [exact Hne|]. split; [exact Hpar|].
    split; [exact (pe_status_zombie _ _ _ Hst)|].
    split; [subst eff; reflexivity | reflexivity].
  - (* px_wait_nohang_zero *)
    split; [reflexivity|]. right; left. split; [exact Hz | reflexivity].
  - (* px_wait_refuse *)
    split; [reflexivity|]. right; right. split; [exact Hrf | reflexivity].
Qed.

(** What the two "never blocks" theorems share: a non-blocking [wait4] of
    a caller with a child is refused, or has no zombie child under the
    answered WNOHANG shape, or has a child the WNOHANG reap can take, with
    everything that reap needs. *)
Lemma owned_nonblocking_cases : forall segs P e,
  wait4_owned_b P e = true ->
  wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
  wait4_refused_b segs P e = true
  \/ (exists x8 sa ru,
        ms_svc_pending (pe_ms e) = Some x8
        /\ wait4_nohang_args (pe_ms e) = Some (sa, ru)
        /\ wait4_rusage_ok_b segs (pe_ms e) x8 ru = true
        /\ ( List.existsb pe_zombie_b (children_of P (pe_pid e)) = false
           \/ exists q ez code model'',
                look P q = Some ez /\ q <> pe_pid e
                /\ pe_parent ez = Some (pe_pid e)
                /\ m_halted (pe_model ez) = Some code
                /\ m_killed (pe_model ez) = None
                /\ read_bytes_map (in_wmem (sys_input segs (pe_ms e) x8)) sa
                     (Z_to_bv 64 4) <> None
                /\ materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
                     (wait4_nohang_accesses sa ru) = Some model'')).
Proof.
  intros segs P e Hwo Hwi.
  destruct (wait4_refused_b segs P e) eqn:Hrf; [left; reflexivity|]. right.
  unfold wait4_refused_b in Hrf. rewrite Hwo, Hwi in Hrf. cbn [negb andb] in Hrf.
  apply orb_false_iff in Hrf as [Hshape Hz].
  apply negb_false_iff in Hshape. unfold wait4_nohang_shape_b in Hshape.
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hsv; [|discriminate Hshape].
  destruct (wait4_nohang_args (pe_ms e)) as [[sa ru]|] eqn:Hna; [|discriminate Hshape].
  exists x8, sa, ru. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hshape|].
  destruct (List.existsb pe_zombie_b (children_of P (pe_pid e))) eqn:Hex;
    [|left; reflexivity].
  right. cbn [andb] in Hz. apply negb_false_iff in Hz.
  unfold wait4_nohang_reap_ok_b in Hz. rewrite Hsv, Hna in Hz.
  apply andb_true_iff in Hz as [Hz Hmat]. apply andb_true_iff in Hz as [Hwr Hre].
  destruct (materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
              (wait4_nohang_accesses sa ru)) as [model''|] eqn:Hm; [|discriminate Hmat].
  apply List.existsb_exists in Hre as ([q ez0] & _ & Hra). cbn [fst] in Hra.
  unfold wait4_reapable_at in Hra.
  destruct (look P q) as [ez|] eqn:Hlq; [|discriminate Hra].
  apply andb_true_iff in Hra as [Hra Hhk]. apply andb_true_iff in Hra as [Hpar Hne].
  destruct (pe_parent ez) as [r0|] eqn:Hpe; [|discriminate Hpar].
  apply bv_eqb_true_eq in Hpar. subst r0.
  destruct (m_halted (pe_model ez)) as [code|] eqn:Hhz; [|discriminate Hhk].
  destruct (m_killed (pe_model ez)) as [k|] eqn:Hkz; [discriminate Hhk|].
  exists q, ez, code, model''.
  split; [exact Hlq|].
  split; [intros Heq; rewrite Heq, bv_eqb_same in Hne; discriminate Hne|].
  split; [exact Hpe|]. split; [exact Hhz|]. split; [exact Hkz|].
  split; [|reflexivity].
  unfold user_writable_b in Hwr. intros Hc. rewrite Hc in Hwr. discriminate Hwr.
Qed.

(** The usage record the reap writes when [ru] is not NULL: any record of
    the right length will do for an existence statement. *)
Definition some_rusage : list byte := List.repeat (Z_to_bv 8 0) (Z.to_nat RUSAGE_BYTES).

(** The copy-out a WNOHANG reap materializes is [wait4_nohang_accesses],
    whatever child, status or usage bytes it carries. *)
Lemma wait4_nohang_effect_accesses : forall q sa status ru,
  syscall_effect_accesses (mkEffect q (wait4_nohang_writes sa status ru some_rusage) [])
  = wait4_nohang_accesses sa ru.
Proof.
  intros q sa status ru.
  unfold syscall_effect_accesses, wait4_nohang_writes, wait4_nohang_accesses.
  cbn [eff_copyins eff_writes app write_accesses].
  rewrite length_Z_to_le_bytes.
  destruct (w_is0 ru); cbn [write_accesses]; [reflexivity|].
  unfold some_rusage. rewrite repeat_length. reflexivity.
Qed.

(** THE GATE NEVER LEAVES A NON-BLOCKING [wait4] WITHOUT AN ARM.  In this
    core no arm means blocked, so this is the statement that WNOHANG, and
    every shape the gate refuses, is never modeled as a sleep. *)
Theorem owned_nonblocking_wait4_steps : forall segs cfg P e,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  wait4_owned_b P e = true ->
  wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
  exists r, pstep_at segs cfg (pe_pid e) P [] r.
Proof.
  intros segs cfg P e Hl Hh Hwo Hwi.
  destruct (owned_nonblocking_cases segs P e Hwo Hwi)
    as [Hrf | (x8 & sa & ru & Hsv & Hna & Hru & [Hz | (q & ez & code & model'' &
            Hlq & Hne & Hpe & Hhz & Hkz & Hrd & Hm)])].
  - exists PError. apply pstep_wait_refuse; assumption.
  - exists (PNext (wait4_zero_result P e)).
    eapply pstep_wait_nohang_zero; eassumption.
  - set (status := bv_mul (bv_and code (Z_to_bv 64 255)) (Z_to_bv 64 256)).
    set (eff := mkEffect q (wait4_nohang_writes sa status ru some_rusage) []).
    exists (PNext (wait4_reap_result P e q eff model'')).
    apply (pstep_wait_nohang_reap segs cfg P e q ez x8 sa ru some_rusage status eff
             model'' false);
      try assumption.
    + unfold pe_status. rewrite Hhz, Hkz. reflexivity.
    + unfold some_rusage. apply repeat_length.
    + reflexivity.
    + unfold eff. rewrite wait4_nohang_effect_accesses. exact Hm.
Qed.

Theorem owned_nonblocking_wait4_steps_x : forall ext cenv segs cfg P e,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  wait4_owned_b P e = true ->
  wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
  exists r, pstep_x_at ext cenv segs cfg (pe_pid e) P [] r.
Proof.
  intros ext cenv segs cfg P e Hl Hh Hwo Hwi.
  destruct (owned_nonblocking_cases segs P e Hwo Hwi)
    as [Hrf | (x8 & sa & ru & Hsv & Hna & Hru & [Hz | (q & ez & code & model'' &
            Hlq & Hne & Hpe & Hhz & Hkz & Hrd & Hm)])].
  - exists PError. apply px_wait_refuse; assumption.
  - exists (PNext (wait4_zero_result P e)).
    eapply px_wait_nohang_zero; eassumption.
  - set (status := bv_mul (bv_and code (Z_to_bv 64 255)) (Z_to_bv 64 256)).
    set (eff := mkEffect q (wait4_nohang_writes sa status ru some_rusage) []).
    exists (PNext (wait4_reap_result P e q eff model'')).
    apply (px_wait_nohang_reap ext cenv segs cfg P e q ez x8 sa ru some_rusage status eff
             model'' false);
      try assumption.
    + unfold pe_status. rewrite Hhz, Hkz. reflexivity.
    + unfold some_rusage. apply repeat_length.
    + reflexivity.
    + unfold eff. rewrite wait4_nohang_effect_accesses. exact Hm.
Qed.
