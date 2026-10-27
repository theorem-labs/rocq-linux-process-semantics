(** * Common.AllocMixSim — brk outcome sets with trace-silent erroring branches.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Outcomes are [(list (list byte) * word)] pairs, matching
    [AllocSim.to_outcomes]; the brk syscall number is Z-characterized
    (a pending [x8] with [bv_unsigned x8 = 214%Z]) exactly as in
    [AllocSim].

    [AllocSim.to_outcomes] characterizes a brk-branching run whose every
    resolution terminates in a (write buffers, exit code) outcome.  A
    MAY-erroring source — one where some brk resolutions run into the
    explicit error transition while others exit cleanly — does not fit:
    under the universal source-error rule ([Equivalence.equiv] via
    [bh_all_errors]) such a source does NOT free the target, so its
    trace set must still be characterized exactly.

    This file provides [to_outcomes_mix]: the same shape as
    [to_outcomes], plus an ERROR LEAF ([tom_fault]) for a branch that runs
    a deterministic instruction line into an illegal instruction.  Such
    a branch contributes NO outcome and NO events — every [star] run
    inside it is silent — so the trace set of the whole tree is still
    exactly the prefixes of the outcome traces of the surviving outcome
    set [U] (which must be nonempty, [alloc_mix_obs_iff]).

    The equivalence-level glue [alloc_mix_strong_equiv] pairs a
    may-erroring source ([to_outcomes_mix] with set [U]) with a
    never-erroring target ([to_outcomes] with the SAME set [U]): trace
    sets coincide, and [~ bh_errors] is required of the TARGET only —
    exactly the obligation [Equivalence.equiv] leaves when the source
    escape is unavailable. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatSim AllocSim ErrEscape.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(** [to_outcomes] with erroring branches: from [ms] under [model], the
    non-error resolutions produce EXACTLY the outcome set [U], and every
    other resolution runs a deterministic silent instruction line into
    the explicit error transition. *)
Inductive to_outcomes_mix :
    machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tom_out : forall ms model U,
    to_outcomes segs ms model U ->
    to_outcomes_mix ms model U
| tom_fault : forall ms ms' model (U : (list (list byte) * word) -> Prop),
    msteps segs ms ms' ->
    ms_svc_pending ms' = None ->
    RiscvSemantics.step segs ms' = MachineFault ->
    (forall o, ~ U o) ->
    to_outcomes_mix ms model U
| tom_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes_mix ms' model U ->
    to_outcomes_mix ms model U
| tom_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes_mix (advance_past_svc (apply_effect ms eff)) model'
                       (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes_mix ms model U.

(** Prepend a deterministic instruction run. *)
Lemma tom_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_outcomes_mix ms' model U -> to_outcomes_mix ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tom_step; eauto.
Qed.

(** Rewire the outcome set along an extensional equivalence. *)
Lemma tom_equiv : forall ms model U V,
  to_outcomes_mix ms model U ->
  (forall o, V o <-> U o) ->
  to_outcomes_mix ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model U Hout
    | ms ms' model U Hm Hsvc Hill HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros V HV.
  - apply tom_out. eapply tou_equiv; [exact Hout | exact HV].
  - eapply tom_fault; [exact Hm | exact Hsvc | exact Hill |].
    intros o Ho. exact (HU o (proj1 (HV o) Ho)).
  - eapply tom_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tom_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
    + intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
    + intro o. rewrite (HV o). apply HU.
Qed.

(** [tom_brk] specialized to a continuation family indexed by the
    resolved break value [r] (the mix analogue of [AllocSim.tou_brk_r]). *)
Lemma tom_brk_r : forall ms model x8 (T' : word -> (list (list byte) * word) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  (forall r,
     brk_resolution_ok model (ms_gpr ms 0) r ->
     to_outcomes_mix
       (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                          (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])))
       (brk_model (ms_gpr ms 0) r model)
       (T' r)) ->
  (forall o, U o <->
     (exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ T' r o)) ->
  to_outcomes_mix ms model U.
Proof.
  intros ms model x8 T' U Hsvc Hno Hcont HU.
  apply (tom_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
    [exact Hsvc | exact Hno | |].
  - intros eff model' evs Hspec.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    pose proof (Hcont (eff_ret eff) Hok) as H.
    rewrite <- Heff in H. exact H.
  - intro o. rewrite HU. split.
    + intros (r & Hok & Ht).
      exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                            (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
             (brk_model (ms_gpr ms 0) r model), [].
      split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
    + intros (eff & model' & evs & Hspec & Ht).
      apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
      destruct Hspec as (_ & _ & Hok & _).
      exists (eff_ret eff). auto.
Qed.

(** From a non-syscall state whose step is illegal, no [SNext]
    transition exists. *)
Lemma illegal_no_snext : forall ms model evs c',
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  ~ sstep segs (mkCfg ms model) evs (SNext c').
Proof.
  intros ms model evs c' Hlazy Hsvc Hill Hss.
  inversion Hss; subst; try congruence.
  match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
    discriminate
  end.
Qed.

(** Every [star] run inside a deterministic line into an illegal
    instruction is silent. *)
Lemma err_chain_star_silent : forall ms ms' model,
  msteps segs ms ms' ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  forall tr c, star segs (mkCfg ms model) tr c -> tr = [].
Proof.
  intros ms ms' model Hm Hlazy;
    induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Hm IH];
    intros Hsvc' Hill tr c Hstar.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst; [reflexivity|].
    exfalso. exact (illegal_no_snext ms0 model evs c2 Hlazy Hsvc' Hill Hss).
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst; [reflexivity|].
    destruct (sstep_instr_inv segs ms0 model ms1 evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    eapply IH; eauto.
Qed.

(** Trace characterization, "only" direction: every [star] trace is
    either empty or a prefix of an outcome trace of the surviving set. *)
Lemma tom_star_only : forall ms model U,
  to_outcomes_mix ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ exists o, U o /\ is_prefix tr (outcome_trace (m_fs model) o).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model U Hout
    | ms ms' model U Hm Hsvc Hill HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy tr c Hstar.
  - right. eapply to_outcomes_star_only; eauto.
  - left. eapply err_chain_star_silent; eauto.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    + left; reflexivity.
    + destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      eapply IH; eauto.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    + left; reflexivity.
    + destruct (sstep_brk_inv segs ms model x8 evs (SNext c2)
                  Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & Hevs & Hc2).
      subst evs. inversion Hc2; subst c2.
      destruct (brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      cbn [app].
      destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) tr2 c Hstar2)
        as [-> | (o & Ho & Hp)].
      * left; reflexivity.
      * right. exists o. split.
        -- apply HU. exists eff, model', []. auto.
        -- rewrite Hfs in Hp. exact Hp.
Qed.

(** Trace characterization, "admits" direction: every outcome in the
    surviving set is realized by a full run. *)
Lemma tom_star_admits : forall ms model U,
  to_outcomes_mix ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model U Hout
    | ms ms' model U Hm Hsvc Hill HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - eapply to_outcomes_star_admits; eauto.
  - exfalso. exact (HU o Ho).
  - destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec)
      as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
      as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model') o)
      by (rewrite Hfs; reflexivity).
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []);
      try assumption.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)).
    reflexivity.
Qed.

(** Coverage: a may-erroring brk tree is nonetheless fully MODELED.
    Each shape contributes its own reason — the surviving subtree never
    errors at all, the erroring subtree ends in a genuine
    [MachineFault], ordinary instructions are [MachineOk], and brk is
    receptive ([AllocSim.brk_no_unmodeled]), so no reachable configuration is
    one the model declined to interpret. *)
Lemma tom_no_unmodeled : forall ms model U,
  to_outcomes_mix ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model U Hout
    | ms ms' model U Hm Hsvc Hill HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - apply no_error_no_unmodeled.
    eapply to_outcomes_no_error; eassumption.
  - eapply msteps_fault_no_unmodeled; eassumption.
  - eapply instr_no_unmodeled;
      [exact Hlazy | exact Hsvc | exact Hstep | apply IH; assumption].
  - intros (tr & c & Hstar & Hun).
    inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    + destruct Hun as (_ & [(Hsvc' & _) | (x8' & Hsvc' & Herr)]); cbn in *.
      * congruence.
      * rewrite Hsvc in Hsvc'; inversion Hsvc'; subst x8'.
        exact (brk_no_unmodeled segs ms x8 model Hno Herr).
    + destruct (sstep_brk_inv segs ms model x8 evs (SNext c2)
                  Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & _ & Hc2).
      inversion Hc2; subst c2.
      destruct (brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & _ & _ & Hlazy').
      apply (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)).
      exists tr2, c. split; assumption.
Qed.

End WithSegs.

(* ========================================================================= *)
(* Run-level packaging and the equivalence glue.                             *)
(* ========================================================================= *)

(** The trace set of a may-erroring brk tree with a NONEMPTY surviving
    outcome set [U] is exactly the prefixes of [U]'s outcome traces (an
    erroring branch contributes only the empty trace, which is a prefix
    of every outcome trace). *)
Lemma alloc_mix_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes_mix segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                  (init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
  (exists o, U o) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (outcome_trace (in_fs inp) o).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto Hne tr.
  unfold init_config.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
    by reflexivity.
  assert (Hlazy : m_vm_lazy
      (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp)
    by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (tom_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
      as [Htr' | (o & Ho & Hp')].
    + subst tr'. destruct Hne as [o Ho].
      exists o. split; [exact Ho|].
      destruct tr; [apply is_prefix_nil | destruct Hp].
    + exists o. split; [exact Ho|].
      rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (tom_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    rewrite Hfs in Hstar.
    exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.

(** The [Equivalence]-level glue: a MAY-erroring source brk tree whose
    surviving outcome set is the (nonempty) [U], against a
    never-erroring target realizing the SAME [U].  The source escape is
    unavailable (some source resolution avoids error), so this
    discharges the non-escape disjunct of [equiv]: exact trace-set
    equality plus target no-error. *)
Lemma alloc_mix_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_outcomes_mix source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
  to_outcomes target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
  (exists o, U o) ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget Hne.
  split.
  { unfold Equivalence.modeled. cbn [run bh_unmodeled]. unfold init_config.
    eapply tom_no_unmodeled; [exact Hsource | reflexivity | reflexivity]. }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
               Hsource Hne tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U
               Htarget tr).
    reflexivity.
  - cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U
             Htarget).
Qed.

(** The omni equivalence for a may-faulting brk mix against a
    never-faulting target with the same outcome set, at the two role
    budgets: the source is COVERED (its faults are modeled crashes,
    [tom_no_unmodeled]) though not error-free, and the trace sets agree.
    Proved from the ingredients rather than through [strong_equiv_iff]
    so that the [covered_iff] route — the point of the omni reading of a
    crashing source — is visible. *)
Lemma alloc_mix_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_outcomes_mix source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U ->
  to_outcomes target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U ->
  (exists o, U o) ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget Hne.
  split.
  { cbn [omni_corun img_segments]. apply covered_iff. unfold init_config.
    eapply tom_no_unmodeled; [exact Hsource | reflexivity | reflexivity]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U
               Hsource Hne tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U
               Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U
             Htarget).
Qed.
