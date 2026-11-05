(** * LinuxProcessSem.Checks.CloneRefusersKept — no step changes the host's clone refusers

    Not part of the trusted specification: a theorem ABOUT it.

    [State.ProcInput.in_clone_refusers] is a launch value: [State.init_model]
    copies it into [State.procst_clone_refusers], [Procs.child_proc]
    copies it into a child, and nothing else writes it.  This file states
    the "nothing else" for the released step, the way
    [Checks.SelfkillEmbedding] states it for the self-kill declaration:
    [Run.run] and [Run.run_scfg] start with the value the input states
    ([init_config_clone_refusers]), and no step, under any configuration
    and any launch, changes it ([sstep_cfg_clone_refusers_kept],
    [sstep_clone_refusers_kept] and their [star] forms).  The per-answer
    fact is [Checks.ProcsChildPidsFrame.syscall_spec_clone_refusers_kept],
    one lemma per arm.  The multi-process core's form, every entry of
    every reachable table, children included, is
    [Checks.ProcsCloneRefusers]. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad StackLayout RiscvSemantics Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ProcsChildPidsFrame.
Import ListNotations.

(** [Run.run] and [Run.run_scfg] start from [Run.init_config], whose model
    carries the refusers the input states. *)
Lemma init_config_clone_refusers : forall segs pc ph sp brk0 mbase rnd lim inp,
  m_clone_refusers (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
  = in_clone_refusers inp.
Proof. intros. reflexivity. Qed.

Lemma clone_refusers_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' ->
  m_clone_refusers m'' = m_clone_refusers m.
Proof.
  intros m acc m'' H.
  destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_clone_refusers. rewrite Hp. reflexivity.
Qed.

(** No step writes the refusers, under every configuration and every
    launch. *)
Lemma sstep_cfg_clone_refusers_kept : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_clone_refusers (cfg_model c') = m_clone_refusers (cfg_model c).
Proof.
  intros segs cfg c evs c' H.
  inversion H; subst; cbn [cfg_model].
  - (* an instruction: the machine step keeps [State.m_proc] *)
    match goal with
    | Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
        destruct (mi_account_step_model_frame _ _ _ _ _ Ha)
          as (_ & _ & _ & _ & _ & Hp & _)
    end.
    unfold m_clone_refusers. rewrite Hp. reflexivity.
  - (* a vDSO call *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_clone_refusers m2); [reflexivity |];
        rewrite (clone_refusers_materialize _ _ _ Hm);
        exact (syscall_spec_clone_refusers_kept _ _ _ _ _ Hsp)
    end.
  - (* a system call that returns *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_clone_refusers m2); [reflexivity |];
        rewrite (clone_refusers_materialize _ _ _ Hm);
        exact (syscall_spec_clone_refusers_kept _ _ _ _ _ Hsp)
    end.
  - (* an exit *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_clone_refusers_kept _ _ _ _ _ Hsp)
    end.
  - (* a kill *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_clone_refusers_kept _ _ _ _ _ Hsp)
    end.
Qed.

Lemma sstep_clone_refusers_kept : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  m_clone_refusers (cfg_model c') = m_clone_refusers (cfg_model c).
Proof.
  intros segs c evs c' H.
  exact (sstep_cfg_clone_refusers_kept _ _ _ _ _
           (proj1 (sstep_cfg_may_fail segs c evs (SNext c')) H)).
Qed.

Corollary star_cfg_clone_refusers_kept : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  m_clone_refusers (cfg_model c') = m_clone_refusers (cfg_model c).
Proof.
  intros segs cfg c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_cfg_clone_refusers_kept _ _ _ _ _ Hs).
Qed.

Corollary star_clone_refusers_kept : forall segs c tr c',
  star segs c tr c' ->
  m_clone_refusers (cfg_model c') = m_clone_refusers (cfg_model c).
Proof.
  intros segs c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_clone_refusers_kept _ _ _ _ Hs).
Qed.

(** So a run whose launch the launch predicates admit meets no clone
    refuser at any reachable state. *)
Corollary star_valid_input_no_clone_refusers :
  forall segs pc ph sp brk0 mbase rnd lim inp tr c',
  valid_input inp ->
  star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c' ->
  m_clone_refusers (cfg_model c') = no_clone_refusers.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp tr c' Hv Hs.
  rewrite (star_clone_refusers_kept _ _ _ _ Hs), init_config_clone_refusers.
  exact (valid_input_no_clone_refusers inp Hv).
Qed.

Print Assumptions star_clone_refusers_kept.
Print Assumptions star_valid_input_no_clone_refusers.
