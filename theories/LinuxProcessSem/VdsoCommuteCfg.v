(** * LinuxProcessSem.VdsoCommuteCfg — the vDSO frame at the filtered step relation

    [VdsoCommuteSys.v] frames [Run.sstep] and [Run.star].  This file does the
    same for [Run.sstep_cfg] and [Run.star_cfg], the SPURIOUS-REFUSAL layer,
    which a proof tree reaches whenever it reasons about a run under an
    injected environment failure.

    NAMES.  The lemmas here are [_vdso_frame], not [_with_vdso], and that is
    deliberate: [VdsoCommuteSys.v] already has [sstep_cfg_with_vdso], where
    the [cfg] means a CONFIGURATION rather than a [SpuriousCfg].  Reusing
    that name here would shadow it for every consumer of both files, with no
    warning from Rocq, and six trees are expected to consume both.

    THE SYSCALL LAYER IS REUSED UNCHANGED.  [syscall_spec_vdso_commutes]
    carries no hypothesis and says nothing about which step relation
    consumes it, so the 93-arm walk is not repeated here.  What this file
    adds is the eleven arms of [Run.sstep_cfg] and the two premises that
    [Run.sstep] does not have:

    - the two syscall arms carry [~ spurious_refusal_cfg cfg …], a predicate
      over the MODEL whose third conjunct quantifies over [syscall_spec]
      outcomes.  BOTH directions of the syscall layer are used there, and
      only there: the forward one carrying the filter in, the inverse
      carrying it back out;

    - [sstep_cfg_instr_unmodeled] carries [vdso_entry_fn segs (ms_pc ms) =
      None] as a premise OF ITS OWN (Run.v:2236, the arm at 2232-2237),
      which [Run.sstep]'s corresponding arm also has (Run.v:669).  That arm
      is therefore PROVED, not excluded: it reuses its own premise and never
      consults this file's.

    HOW EACH OF THE ELEVEN ARMS IS DISCHARGED, so a consumer can see which
    ones the per-state premise excludes and which are carried:

      sstep_cfg_instr                       carried (mi_account_step frame)
      sstep_cfg_instr_fault                 carried (mi_account_step frame)
      sstep_cfg_instr_unmodeled             carried; its own = None premise
      sstep_cfg_vdso_call                   EXCLUDED by the premise
      sstep_cfg_vdso_materialization_fault  EXCLUDED by the premise
      sstep_cfg_vdso_unmodeled              EXCLUDED by the premise
      sstep_cfg_syscall                     carried (syscall layer + refusal frame)
      sstep_cfg_syscall_materialization_fault
                                            carried (syscall layer + refusal frame)
      sstep_cfg_exit                        carried (syscall layer)
      sstep_cfg_killed                      carried (syscall layer)
      sstep_cfg_syscall_unmodeled           carried (syscall layer)

    Three excluded, eight carried, which is [Run.sstep]'s split exactly.

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType Vdso State Monad Specs RiscvSemantics Run
  VdsoCommute VdsoCommuteArms VdsoCommuteSys.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   The refusal filter
   ========================================================================= *)

(** [Run.refusal_b] reads the break and the injected arms' own state, none
    of which the wrapper touches. *)
Lemma refusal_b_with_vdso : forall i v m ret,
  refusal_b i (with_vdso v m) ret = refusal_b i m ret.
Proof. intros i v m ret; vdso_model_eq. Qed.

(** THE FILTER FRAMES, AND ITS THIRD CONJUNCT IS WHY BOTH DIRECTIONS OF THE
    SYSCALL LAYER ARE NEEDED.  [spurious_refusal_cfg]'s last clause asserts
    that SOME admissible outcome is not a refusal.  Carried forward that is
    [syscall_spec_with_vdso]; carried back it is
    [syscall_spec_with_vdso_inv], and the witness model returns with [m]'s
    own draw — which costs nothing, because the clause reads [m] and [eff']
    and never the witness model, so only its EXISTENCE is asserted. *)
Lemma spurious_refusal_cfg_with_vdso : forall cfg i v m eff,
  spurious_refusal_cfg cfg i (with_vdso v m) eff
  <-> spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i v m eff. unfold spurious_refusal_cfg.
  rewrite !refusal_b_with_vdso.
  split; intros (Hoff & Href & (eff' & m' & evs' & Hspec & Hnr)).
  - split; [exact Hoff | split; [exact Href|]].
    exists eff', (with_vdso (m_vdso m) m'), evs'.
    split; [| exact Hnr].
    exact (syscall_spec_with_vdso_inv v i m _ Hspec).
  - split; [exact Hoff | split; [exact Href|]].
    exists eff', (with_vdso v m'), evs'.
    split; [| exact Hnr].
    exact (syscall_spec_with_vdso v i m _ Hspec).
Qed.

(* =========================================================================
   The filtered step relation
   ========================================================================= *)

(** THE STATEMENT, per state, exactly as at [Run.sstep].  The premise
    excludes the same three arms and nothing else: the only other arm
    naming [vdso_entry_fn] is [sstep_cfg_instr_unmodeled], whose own
    premise is [= None]. *)
Theorem sstep_cfg_vdso_frame : forall segs cfg v ms model evs st,
  vdso_entry_fn segs (ms_pc ms) = None ->
  sstep_cfg segs cfg (mkCfg ms model) evs st ->
  sstep_cfg segs cfg (mkCfg ms (with_vdso v model)) evs (step_to_with_vdso v st).
Proof.
  intros segs cfg v ms model evs st Hnv Hstep.
  remember (mkCfg ms model) as c eqn:Hc.
  destruct Hstep; injection Hc as <- <-.
  - (* instr *)
    apply sstep_cfg_instr; [exact H | exact H0 |].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* instr_fault *)
    apply sstep_cfg_instr_fault; [exact H | exact H0 |].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* instr_unmodeled: proved, on its OWN premise *)
    apply sstep_cfg_instr_unmodeled; [exact H | exact H0 | | exact H2].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* vdso_call: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* vdso_materialization_fault: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* vdso_unmodeled: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* syscall *)
    eapply sstep_cfg_syscall with (model' := with_vdso v model')
                                  (model'' := with_vdso v model'').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + intros Hsp. apply H2.
      exact (proj1 (spurious_refusal_cfg_with_vdso _ _ v _ _) Hsp).
    + exact H3.
    + rewrite materialize_model_accesses_with_vdso, H4. reflexivity.
  - (* syscall_materialization_fault *)
    eapply sstep_cfg_syscall_materialization_fault
      with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + intros Hsp. apply H2.
      exact (proj1 (spurious_refusal_cfg_with_vdso _ _ v _ _) Hsp).
    + exact H3.
    + rewrite materialize_model_accesses_with_vdso, H4. reflexivity.
  - (* exit *)
    eapply sstep_cfg_exit with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
    + exact H3.
  - (* killed *)
    eapply sstep_cfg_killed with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
  - (* syscall_unmodeled *)
    eapply sstep_cfg_syscall_unmodeled.
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
Qed.

(** On a configuration rather than its two halves.  [config] is an ordinary
    record, so a consumer holding an abstract [c] cannot get this by eta
    and would have to destruct its own configuration. *)
Corollary sstep_cfg_vdso_frame_c : forall segs cfg v c evs st,
  vdso_entry_fn segs (ms_pc (cfg_ms c)) = None ->
  sstep_cfg segs cfg c evs st ->
  sstep_cfg segs cfg (cfg_with_vdso v c) evs (step_to_with_vdso v st).
Proof. intros segs cfg v [ms model] evs st. apply sstep_cfg_vdso_frame. Qed.

(** THE INVERSE, free from the two identities, as at [Run.sstep].  This is
    the direction a [Common.ShapeAlg]-style consumer needs: [node_ok]
    quantifies over EVERY successor of a configuration, as does
    [Run.all_traces_error_cfg], so transporting either across the wrapper
    asks what a step of the WRAPPED configuration came from. *)
Theorem sstep_cfg_vdso_frame_inv : forall segs cfg v ms model evs st,
  vdso_entry_fn segs (ms_pc ms) = None ->
  sstep_cfg segs cfg (mkCfg ms (with_vdso v model)) evs st ->
  sstep_cfg segs cfg (mkCfg ms model) evs
            (step_to_with_vdso (m_vdso model) st).
Proof.
  intros segs cfg v ms model evs st Hnv Hstep.
  pose proof (sstep_cfg_vdso_frame segs cfg (m_vdso model) ms
                (with_vdso v model) evs st Hnv Hstep) as H.
  rewrite with_vdso_idem, with_vdso_same in H. exact H.
Qed.

Corollary sstep_cfg_vdso_frame_c_inv : forall segs cfg v c evs st,
  vdso_entry_fn segs (ms_pc (cfg_ms c)) = None ->
  sstep_cfg segs cfg (cfg_with_vdso v c) evs st ->
  sstep_cfg segs cfg c evs (step_to_with_vdso (m_vdso (cfg_model c)) st).
Proof.
  intros segs cfg v [ms model] evs st Hnv Hstep.
  exact (sstep_cfg_vdso_frame_inv segs cfg v ms model evs st Hnv Hstep).
Qed.

(** MANY FILTERED STEPS, under the caller's invariant, as at [Run.star].

    NOTE WHAT THE SECOND PREMISE ASKS, and that it asks LESS here than at
    [Run.star].  [P] must survive every successor of the FILTERED relation,
    not of [Run.sstep] — and [Run.sstep_cfg_sub] (Run.v:2316) makes the
    filtered relation the smaller one, so an invariant that already serves
    [star_with_vdso] serves this outright.  A caller holding only one trace
    still wants [P] to be a property of the segment list and the pc rather
    than of the trace. *)
Theorem star_cfg_vdso_frame : forall segs cfg v (P : config -> Prop),
  (forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None) ->
  (forall c evs c', P c -> sstep_cfg segs cfg c evs (SNext c') -> P c') ->
  forall c tr c', star_cfg segs cfg c tr c' -> P c ->
  star_cfg segs cfg (cfg_with_vdso v c) tr (cfg_with_vdso v c').
Proof.
  intros segs cfg v P Hpc Hstep c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hs Hstar IH]; intros HP.
  - apply star_cfg_refl.
  - eapply star_cfg_step.
    + exact (sstep_cfg_vdso_frame_c segs cfg v c1 evs (SNext c2)
               (Hpc c1 HP) Hs).
    + exact (IH (Hstep c1 evs c2 HP Hs)).
Qed.

(* =========================================================================
   The budget observable

   [Run.budget_refused_at] (Run.v:2849-2869) is not an arm of either step
   relation, but it gained a vDSO disjunct in the same revision
   (Run.v:2855-2863) and a consumer carrying it across the wrapper meets
   that disjunct.  It needs NO premise: the disjunct's own first conjunct
   is [vdso_entry_fn … = Some fn], and every clause under it reads the
   model only through frames this development already has.
   ========================================================================= *)

Lemma alloc_budget_refused_b_with_vdso : forall i v m,
  alloc_budget_refused_b i (with_vdso v m) = alloc_budget_refused_b i m.
Proof. intros i v m; vdso_model_eq. Qed.

Lemma materialize_model_accesses_none_with_vdso : forall v m acc,
  materialize_model_accesses (with_vdso v m) acc = None
  <-> materialize_model_accesses m acc = None.
Proof.
  intros v m acc. rewrite materialize_model_accesses_with_vdso.
  destruct (materialize_model_accesses m acc); cbn; split;
    intro H; congruence.
Qed.

(** One direction; the other is this one at [m_vdso], as everywhere else. *)
Lemma budget_refused_at_vdso_frame_fwd : forall segs v c,
  budget_refused_at segs c -> budget_refused_at segs (cfg_with_vdso v c).
Proof.
  intros segs v [ms model] H.
  unfold budget_refused_at, cfg_with_vdso in *;
    cbn [cfg_ms cfg_model] in *.
  destruct H as (Hh & Hdis). split; [exact Hh|].
  destruct Hdis as [(Hsvc & [ (report & Hacc & Hmat) | (Hacct & fn & n & eff & model' & evs & Hfn & Hno & Hspec & Hef & Hhm & Hmat) ])
                   | (x8 & Hsvc & [Hab | (eff & model' & evs & Hspec & Hhm & Hmat)]) ].
  - left. split; [exact Hsvc|]. left. exists report. split; [exact Hacc|].
    apply materialize_model_accesses_none_with_vdso. exact Hmat.
  - left. split; [exact Hsvc|]. right.
    split; [rewrite mi_account_step_with_vdso, Hacct; reflexivity|].
    exists fn, n, eff, (with_vdso v model'), evs.
    split; [exact Hfn | split; [exact Hno|]].
    split; [exact (syscall_spec_with_vdso v _ _ _ Hspec) | split; [exact Hef|]].
    split; [exact Hhm|].
    apply materialize_model_accesses_none_with_vdso. exact Hmat.
  - right. exists x8. split; [exact Hsvc|]. left.
    rewrite alloc_budget_refused_b_with_vdso. exact Hab.
  - right. exists x8. split; [exact Hsvc|]. right.
    exists eff, (with_vdso v model'), evs.
    split; [exact (syscall_spec_with_vdso v _ _ _ Hspec) | split; [exact Hhm|]].
    apply materialize_model_accesses_none_with_vdso. exact Hmat.
Qed.

Lemma budget_refused_at_vdso_frame : forall segs v c,
  budget_refused_at segs (cfg_with_vdso v c) <-> budget_refused_at segs c.
Proof.
  intros segs v [ms model]. split; intros H.
  - assert (Heq : cfg_with_vdso (m_vdso model)
                    (cfg_with_vdso v (mkCfg ms model)) = mkCfg ms model).
    { unfold cfg_with_vdso; cbn [cfg_ms cfg_model].
      rewrite with_vdso_idem, with_vdso_same. reflexivity. }
    pose proof (budget_refused_at_vdso_frame_fwd segs (m_vdso model) _ H) as H'.
    rewrite Heq in H'. exact H'.
  - exact (budget_refused_at_vdso_frame_fwd segs v _ H).
Qed.
