(** * LinuxProcessSem.Checks.Omni — what the omni judgments MEAN

    Not part of the trusted specification: QA on the definitions of
    [OmniRun] and [OmniEquivalence], in the style of [Checks/Examples.v].
    Every case here is UNIVERSALLY QUANTIFIED (admission reason 1 of
    that file: a [forall] over every execution of a run, which no
    finite set of traces establishes) or COMPARES TWO RUNS (reason 2).

    - PART 1, the two coinductive readings agree on THIS tree.
      [OmniRun.coexec] drops the progress premise so that a stuck
      configuration reads as silent; [sstep_receptive] lifts
      [Checks.Progress.receptive] to [Run.sstep] and shows no non-halted
      configuration is stuck, so [coexec_progress_iff] identifies the
      two judgments here.  The header of [OmniRun] says why the choice
      is nevertheless made at the definition.
    - PART 2, the exit-0 image SATISFIES the omni statements, for EVERY
      [execve] placement, EVERY input and ANY budget: one omni
      induction ([exits_c_exec]) delivers the exact trace, termination
      and error-freedom at once, which is what
      [exit0_omni_strong_universal] — the first
      [OmniEquivalence.omni_strong_universal_T] any concrete pair
      satisfies — is made of.  The legacy
      [Equivalence.strong_universal_T] follows through the [iff], and the
      module ascriptions at the end of the part show the two checker
      shapes accepting the same proof.
    - PART 3, the undecodable image REFUTES them: every error-related
      omni postcondition fails on it, the identical-pair statement
      fails with it as the source, and the differing pair
      exit-0/undecodable fails through the trace conjunct.
    - PART 4, a modeled CRASH separates the three error postconditions:
      an [ebreak] image satisfies [OmniRun.errors] and [OmniRun.covered]
      and refutes [OmniRun.never_errors], and its escape frees any
      target — the [OmniEquivalence.omni_strong_equiv] of a crashing
      source against the undecodable image holds.
    - PART 5, [exec]/[coexec] agreement is STRICTLY WEAKER than trace
      equivalence: "write one byte, then loop" and "loop" satisfy the
      same [coexec] postconditions (every one) and the same [exec]
      postconditions (none), yet their trace sets differ, so
      [OmniRun.cosafe] — and [Equivalence.equiv] through the [iff] —
      tells them apart.  This is [Checks.Examples.write_then_diverge_vs_diverge]
      on two real images, and the reason trace equivalence is stated on
      the prefix judgment.

    ** Computing on a machine state without reading it back

    Every fact below that is closed by [vm_compute] is a SCALAR: a
    boolean, a byte list, a checker verdict.  A machine state is never
    normalised into a goal — its stack memory is a closure over the
    initial stack image, and reading that closure back is where
    [vm_compute] runs out of memory (the same trap
    [Common/StepTac.v] guards against).  Where a lemma must name the
    successor STATE, the memory field is abstracted first: [with_mem]
    replaces it by a variable, [with_mem_eta] says nothing is lost, and
    an instruction that touches no memory then steps
    [with_mem ms mem] to [with_mem ms' mem] by computation on the
    remaining fields alone.  The syscall step, which does read memory,
    is characterised through [Checks.Cases.Fs.ReadWrite.write_channel_outcome]
    and the executable checker, both on the real memory. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples Progress.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier OmniEquivalence.
Import ListNotations.
Open Scope bv_scope.

(** The process input every concrete pin below runs on — the one
    [Checks.Examples.demo_input_valid] validates: one empty argument,
    no environment, an empty file system, end of input. *)
Definition demo_proc_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(* =========================================================================
   PART 1 — receptiveness lifted to [Run.sstep]
   ========================================================================= *)

(** No non-halted configuration is stuck: an instruction step answers
    one of [MachineOk]/[MachineFault]/[MachineUnmodeled], each with an
    [sstep] constructor, and a pending syscall admits some outcome by
    [Checks.Progress.receptive], each shape of which again has one. *)
Lemma sstep_receptive : forall segs c,
  m_halted (cfg_model c) = None ->
  exists evs st, sstep segs c evs st.
Proof.
  intros segs [ms model] Hh; cbn [cfg_model] in Hh.
  destruct (ms_svc_pending ms) as [x8 |] eqn:Hsvc.
  - (* the witness outcome, with its name generalised so that the case
       split rewrites the receptiveness fact itself *)
    pose proof (receptive (sys_input segs ms x8) model) as Hr.
    set (w := syscall_spec_witness (sys_input segs ms x8) model) in Hr.
    clearbody w. destruct w as [eff model' evs |].
    + destruct (m_halted model') as [code |] eqn:Hh'.
      * destruct (m_killed model') as [sig |] eqn:Hk'.
        -- eexists; eexists. eapply sstep_killed; eassumption.
        -- eexists; eexists. eapply sstep_exit; eassumption.
      * destruct (materialize_model_accesses model' (syscall_effect_accesses eff))
          as [model'' |] eqn:Hm.
        -- eexists; eexists. eapply sstep_syscall; eassumption.
        -- eexists; eexists. eapply sstep_syscall_materialization_fault; eassumption.
    + eexists; eexists. eapply sstep_syscall_unmodeled; eassumption.
  - destruct (mi_account_step segs ms model) as [[ms' model'] | |] eqn:Hacc.
    + eexists; eexists. eapply sstep_instr; eassumption.
    + eexists; eexists. eapply sstep_instr_fault; eassumption.
    + eexists; eexists. eapply sstep_instr_unmodeled; eassumption.
Qed.

(** Hence the progress-carrying variant is no stronger here. *)
Lemma coexec_coexec_progress : forall segs c Q,
  coexec segs c Q -> coexec_progress segs c Q.
Proof.
  cofix CH. intros segs c Q H.
  destruct H as [c Q Hh HQ | c Q Hh Herr Hnext].
  - apply coexec_progress_halt; assumption.
  - apply coexec_progress_step;
      [exact Hh | exact (sstep_receptive segs c Hh) | exact Herr |].
    intros evs c' Hss. exact (CH _ _ _ (Hnext evs c' Hss)).
Qed.

Lemma coexec_progress_iff : forall segs c Q,
  coexec segs c Q <-> coexec_progress segs c Q.
Proof.
  intros segs c Q; split;
    [apply coexec_coexec_progress | apply coexec_progress_implies].
Qed.

(* =========================================================================
   Machine states with the memory abstracted
   ========================================================================= *)

Definition with_mem (ms : machine_state) (mem : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mem; ms_rom := ms_rom ms |}.

Lemma with_mem_eta : forall ms, ms = with_mem ms (ms_mem ms).
Proof. intros []; reflexivity. Qed.

(** Erase the accounting on a model with no lazy mappings, in the goal
    or in a hypothesis; the model is read off the term, so the
    [reflexivity] that discharges [m_vm_lazy model = []] sees it. *)
Ltac no_lazy :=
  match goal with
  | |- context [mi_account_step ?segs ?ms ?model] =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
Ltac no_lazy_in H :=
  match type of H with
  | context [mi_account_step ?segs ?ms ?model] =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity)) in H
  end.
Ltac no_lazy_materialize_in H :=
  match type of H with
  | context [materialize_model_accesses ?m ?a] =>
      rewrite (materialize_model_accesses_no_lazy m a ltac:(reflexivity)) in H
  end.

(** From a configuration whose instruction step is a function answer,
    the only transition is that step, silently.  The same fact as
    [Common/ExitSim.v]'s [sstep_instr_inv], restated here because
    [Common] is not part of the package. *)
Lemma sstep_instr_only : forall segs ms model ms',
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  forall evs st, sstep segs (mkCfg ms model) evs st ->
    evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros segs ms model ms' Hlazy Hsvc Hstep evs st Hss.
  inversion Hss; subst;
    try (match goal with
         | H : mi_account_step _ _ _ = _ |- _ =>
             rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in H;
             first [ inversion H; subst; split; reflexivity | discriminate H ]
         end);
    congruence.
Qed.

(** ... and when the answer is a fault, the only transition is the
    error one. *)
Lemma sstep_fault_only : forall segs ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  forall evs st, sstep segs (mkCfg ms model) evs st -> evs = [] /\ st = SError.
Proof.
  intros segs ms model Hlazy Hsvc Hstep evs st Hss.
  inversion Hss; subst;
    try (match goal with
         | H : mi_account_step _ _ _ = _ |- _ =>
             rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in H;
             first [ split; reflexivity | discriminate H ]
         end);
    congruence.
Qed.

(** A configuration that steps to itself: silent forever. *)
Lemma fix_coexec_any : forall segs c,
  m_halted (cfg_model c) = None ->
  (forall evs st, sstep segs c evs st -> evs = [] /\ st = SNext c) ->
  forall Q, coexec segs c Q.
Proof.
  intros segs c Hh Hfix. cofix CH. intros Q.
  apply coexec_step; [exact Hh | |].
  - intros evs Hss. destruct (Hfix _ _ Hss) as (_ & Habs). discriminate Habs.
  - intros evs c' Hss. destruct (Hfix _ _ Hss) as (-> & Heq).
    injection Heq as ->. apply CH.
Qed.

Lemma fix_no_exec : forall segs c,
  m_halted (cfg_model c) = None ->
  (forall evs st, sstep segs c evs st -> evs = [] /\ st = SNext c) ->
  forall Q, ~ exec segs c Q.
Proof.
  intros segs c Hh Hfix Q Hex.
  assert (Hgen : forall c' Q', exec segs c' Q' -> c' = c -> False).
  { intros c' Q' H. induction H as [c' Q' Hh' HQ | c' Q' Hh' Hprog Herr Hnext IH]; intros ->.
    - exact (Hh' Hh).
    - destruct Hprog as (evs & st & Hss). destruct (Hfix _ _ Hss) as (-> & ->).
      exact (IH [] c Hss eq_refl). }
  exact (Hgen _ _ Hex eq_refl).
Qed.

Lemma fix_star_nil : forall segs c,
  (forall evs st, sstep segs c evs st -> evs = [] /\ st = SNext c) ->
  forall tr c', star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros segs c Hfix tr c' Hstar.
  remember c as c0 eqn:Hc in Hstar. revert Hc.
  induction Hstar as [c1 | c1 evs c2 tr c3 Hss Hstar IH]; intros ->.
  - split; reflexivity.
  - destruct (Hfix _ _ Hss) as (-> & Heq). injection Heq as ->.
    destruct (IH eq_refl) as (-> & ->). split; reflexivity.
Qed.

Lemma fix_obs_nil : forall segs c,
  (forall evs st, sstep segs c evs st -> evs = [] /\ st = SNext c) ->
  forall tr, obs_trace segs c tr -> tr = [].
Proof.
  intros segs c Hfix tr (tr' & c' & Hstar & Hp).
  destruct (fix_star_nil _ _ Hfix _ _ Hstar) as (-> & _).
  destruct tr; [reflexivity | destruct Hp].
Qed.

Lemma prefix_closed_nil : prefix_closed (fun tr => tr = []).
Proof. intros tr tr' -> Hp. destruct tr'; [reflexivity | destruct Hp]. Qed.

(* =========================================================================
   PART 2 — the exit-0 image satisfies the omni statements, universally
   ========================================================================= *)

(** The omni form of [Checks.Examples.exits_c_must_exit_at]: the same
    walk, but the postcondition records the exact trace and the
    exit code together, so trace equality below needs no second
    lemma.  The successor state at an instruction is discharged by
    [sstep_instr_only]; at the exit ecall the dispatch lemmas of
    [Checks/Examples.v] force the one outcome. *)
Lemma exits_c_exec : forall segs code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_c segs code fuel ms = true ->
  exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros segs code fuel. induction fuel as [|fuel IH]; intros ms model Hh Hlazy Hc;
    [discriminate|].
  cbn [exits_c] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - (* the terminating ecall *)
    apply andb_true_iff in Hc as [Hx8 Hcode].
    apply bv_eqb_eq in Hcode.
    assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))).
    { cbn [in_sysno sys_input].
      apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
        [left|right]; exact H. }
    assert (Harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0) by reflexivity.
    set (v := bv_and (in_arg (sys_input segs ms x8) 0) (Z_to_bv 64 255)).
    set (m' := with_halted v model).
    apply exec_step.
    + cbn [cfg_model]. exact Hh.
    + exists ([] ++ [ExitEv v (m_fs m')]), (SNext (mkCfg ms m')).
      eapply sstep_exit; [exact Hh | exact Hsvc | | | ].
      * subst m' v. exact (exit_dispatch_admits _ model Hno).
      * subst m' v. reflexivity.
      * subst m' v. apply m_killed_with_halted.
    + intros evs Hss. exfalso.
      inversion Hss; subst; try congruence; unify_svc x8.
      * (* materialization fault: an exit outcome halts, so its premise fails *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * (* unmodeled syscall: exit is modeled *)
        match goal with
        | [ H : syscall_spec _ _ Unmodeled |- _ ] =>
            exact (exit_dispatch_modeled _ _ Hno H)
        end.
    + intros evs c' Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * (* an ordinary syscall step: its post-model would have to run on *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * (* the exit transition, into the halted configuration *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _), Hh' : m_halted _ = Some _ |- _ ] =>
            destruct (exit_dispatch_forced _ _ _ _ _ Hno H) as (_ & -> & ->)
        end.
        match goal with
        | [ Hh' : m_halted (with_halted _ _) = Some _ |- _ ] =>
            rewrite m_halted_with_halted in Hh'; injection Hh' as Hcode'
        end.
        apply exec_halt.
        -- cbn [cfg_model]. rewrite m_halted_with_halted. discriminate.
        -- cbn beta. rewrite app_nil_r. cbn [app].
           rewrite m_fs_with_halted, <- Hcode', Harg.
           split; [reflexivity |].
           cbn [exits_with cfg_model]. split;
             [ rewrite m_halted_with_halted;
               try rewrite <- Hcode'; try rewrite Harg; reflexivity
             | apply m_killed_with_halted ].
      * (* the kill transition: an exit's post-model is not a killed one *)
        exfalso.
        match goal with
        | [ H : syscall_spec _ _ (Ok _ ?m' _), Hk : m_killed ?m' = Some _ |- _ ] =>
            rewrite (exit_dispatch_not_killed _ _ _ _ _ Hno H) in Hk; discriminate
        end.
  - (* an ordinary instruction *)
    destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + eapply sstep_instr; [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + exact (sstep_instr_only segs ms model ms' Hlazy Hsvc Hstep).
    + eapply exec_conseq; [apply IH; assumption |].
      intros tr o H. cbn [app]. exact H.
Qed.

(** The exit-0 image runs the same way from EVERY [execve] placement
    and on EVERY input: it makes no memory access beyond its own
    fetches, and the fetch reads the segment image, which no placement
    touches.  Stated with the stack memory abstracted, exactly so that
    [vm_compute] never has to look at it. *)
Lemma exit0_exits_c : forall sp rnd argv envp uid hw,
  exits_c exit0_segments verdict_accept 8
    (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd argv envp uid hw)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd
                        argv envp uid hw)).
  intros mem. vm_compute. reflexivity.
Qed.

(** One omni judgment for the whole image: every execution halts with
    code 0 after emitting exactly the exit event, at any budget. *)
Lemma exit0_exec : forall sp brk0 mbase rnd lim inp,
  exec exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
    (fun tr o => tr = [ExitEv verdict_accept (in_fs inp)]
                 /\ exits_with verdict_accept tr o).
Proof.
  intros. unfold init_config.
  refine (exits_c_exec exit0_segments verdict_accept 8
            (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd
               (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
            (init_model (segments_reserved exit0_segments) brk0 mbase sp lim inp)
            eq_refl eq_refl (exit0_exits_c _ _ _ _ _ _)).
Qed.

(** What the one judgment yields: the exact trace set ... *)
Lemma exit0_obs : forall sp brk0 mbase rnd lim inp tr,
  obs_trace exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr
  <-> is_prefix tr [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros. apply exec_obs_iff.
  eapply exec_conseq; [apply exit0_exec |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

(** ... and error-freedom, hence coverage. *)
Lemma exit0_never_errors : forall sp brk0 mbase rnd lim inp,
  coexec exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
    never_errors.
Proof.
  intros. apply exec_coexec. eapply exec_conseq; [apply exit0_exec |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** UNIVERSALLY QUANTIFIED (reason 1) and COMPARING TWO RUNS (reason 2):
    the first concrete pair on which
    [OmniEquivalence.omni_strong_universal_T] HOLDS.  It is not free —
    the two roles run at different budgets, and the statement ranges
    over every valid placement of each side and every valid input —
    and it needs none of the three validity premises, because the image
    never touches the stack or the heap. *)
(** The per-triple obligation, at EVERY input rather than only at a
    valid one.  The proof below reads none of the three validity
    premises — the image never touches the stack or the heap — so
    stating it without them is not a strengthening anyone has to check,
    it is what the proof already establishes.  It is a separate lemma
    because the quantifier shells differ in which validity predicate they
    name ([Run.valid_input], [Run.valid_input_abort],
    [Run.valid_input_either]), and a fact that holds at every input
    discharges all of them without a second proof. *)
Lemma exit0_omni_strong_equiv_any : forall en_source en_target inp,
  omni_strong_equiv exit0_image exit0_image en_source en_target inp.
Proof.
  intros [sps brks mbs rnds] [spt brkt mbt rndt] inp.
  unfold omni_strong_equiv, omni_equiv, omni_trace_equiv.
  cbn [omni_corun omni_cosafe exit0_image img_segments].
  split.
  - eapply coexec_conseq; [apply exit0_never_errors | apply never_errors_covered].
  - right. split.
    + intros P Hpc.
      rewrite (cosafe_obs_iff _ _ P Hpc), (cosafe_obs_iff _ _ P Hpc).
      split; intros Hall tr Hobs; apply Hall; apply exit0_obs; apply exit0_obs in Hobs;
        exact Hobs.
    + apply exit0_never_errors.
Qed.

Theorem exit0_omni_strong_universal :
  omni_strong_universal_T exit0_image exit0_image.
Proof. intros en_s en_t inp _ _ _. apply exit0_omni_strong_equiv_any. Qed.

(** The legacy statement, through the [iff]: this is the whole of what
    a consumer does to discharge [Equivalence.strong_universal_T] from
    an omni proof. *)
Theorem exit0_strong_universal : strong_universal_T exit0_image exit0_image.
Proof. apply strong_universal_iff. exact exit0_omni_strong_universal. Qed.

(** The same, at the module level a checker ascribes: the omni proof
    seals [OmniEquivalence.OMNI_SPEC], and [OmniEquivalence.SpecOfOmni]
    turns that into an [Equivalence.SPEC] sealing without a new proof. *)
Module Exit0Image <: MemImage.
  Definition loaded_segments := exit0_segments.
  Definition init_pc : N := 0x100.
  Definition phdrs := demo_phdrs.
End Exit0Image.

Module Exit0OmniChecked <: OMNI_SPEC Exit0Image Exit0Image.
  Definition omni_strong_universal := exit0_omni_strong_universal.
End Exit0OmniChecked.

Module Exit0Checked := SpecOfOmni Exit0Image Exit0Image Exit0OmniChecked.

(* -------------------------------------------------------------------------
   The abort stances, ascribed on the same pair
   ------------------------------------------------------------------------- *)

(** WHY THE EXIT-0 PAIR IS THE RIGHT PLACE FOR THESE.  The four sealing
    surfaces the abort declaration added to the classifier shape
    ([Equivalence.SPEC_SCFG_ABORT] and its three siblings) are module
    types, and a module type nothing ascribes is a statement nobody has
    shown can be met.  These ascriptions are the anti-vacuity check on
    the surfaces themselves: they say the four are inhabited, at a
    concrete pair, with proofs the type checker accepts.

    THE IMAGE NEVER ABORTS, and that is not a weakness of the example.
    What an ascription checks is that the SHAPE is satisfiable and that
    the module's parameters line up; what happens when a program does
    abort is [Checks.AbortWitness]'s subject, and that file refutes the
    error-free statement rather than satisfying it.  The two are the
    halves of the same claim and neither substitutes for the other. *)

(** At every input, so every quantifier shell below is discharged by the
    same fact. *)
Lemma exit0_strong_equiv_any : forall en_source en_target inp,
  strong_equiv exit0_image exit0_image en_source en_target inp.
Proof.
  intros en_source en_target inp.
  apply strong_equiv_iff. apply exit0_omni_strong_equiv_any.
Qed.

Theorem exit0_strong_universal_abort :
  strong_universal_T_abort exit0_image exit0_image.
Proof. intros en_s en_t inp _ _ _. apply exit0_strong_equiv_any. Qed.

Theorem exit0_strong_universal_either :
  strong_universal_T_either exit0_image exit0_image.
Proof. intros en_s en_t inp _ _ _. apply exit0_strong_equiv_any. Qed.

(** The image's whole trace set, read off [exit0_obs]: a prefix of the
    one exit event.  Nothing in it is a [State.KillEv], which is what
    the error-free abort triple asks beyond error-freedom. *)
Lemma exit0_not_dies_by_signal : forall lim en inp,
  ~ dies_by_signal (run exit0_image lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp (tr & sig & fs & Hobs & Hin).
  cbn [run bh_traces exit0_image] in Hobs.
  apply exit0_obs in Hobs.
  destruct tr as [|e tr]; [destruct Hin|].
  destruct Hobs as (-> & Hp). destruct tr as [|e' tr]; [|destruct Hp].
  destruct Hin as [Heq | []]. discriminate Heq.
Qed.

Lemma exit0_error_free_run : forall lim en inp,
  error_free (run exit0_image lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  apply error_free_iff. cbn [omni_corun exit0_image img_segments].
  apply exit0_never_errors.
Qed.

Lemma exit0_strong_equiv_error_free_abort_any : forall en_source en_target inp,
  strong_equiv_error_free_abort exit0_image exit0_image en_source en_target inp.
Proof.
  intros [sps brks mbs rnds] [spt brkt mbt rndt] inp.
  split; [| split].
  - split; [apply exit0_error_free_run | apply exit0_not_dies_by_signal].
  - split; [apply exit0_error_free_run | apply exit0_not_dies_by_signal].
  - intros tr. cbn [run bh_traces exit0_image].
    rewrite !exit0_obs. reflexivity.
Qed.

Theorem exit0_strong_universal_error_free_abort :
  strong_universal_error_free_T_abort exit0_image exit0_image.
Proof. intros en_s en_t inp _ _ _. apply exit0_strong_equiv_error_free_abort_any. Qed.

(** The declaration-off half, which the either conjunction needs beside
    it: the same per-input fact with [error_free_unkilled] weakened to
    [error_free], since the off triple asks only that. *)
Theorem exit0_strong_universal_error_free :
  strong_universal_error_free_T exit0_image exit0_image.
Proof.
  intros en_s en_t inp _ _ _.
  destruct (exit0_strong_equiv_error_free_abort_any en_s en_t inp)
    as (Hsef & Htef & Htr).
  split; [exact (error_free_unkilled_error_free _ Hsef)|].
  split; [exact (error_free_unkilled_error_free _ Htef) | exact Htr].
Qed.

Theorem exit0_strong_universal_error_free_either :
  strong_universal_error_free_T_either exit0_image exit0_image.
Proof.
  split;
    [exact exit0_strong_universal_error_free
    |exact exit0_strong_universal_error_free_abort].
Qed.

(** The classifier shape, at the configuration every existing statement
    carries.  [Run.may_fail_cfg] is where the two knobs meet: the
    meaning-preserved pins say each of these IS the baseline abort
    statement there, so the ascriptions below inherit their proofs
    rather than repeating them. *)
Theorem exit0_strong_universal_scfg_abort :
  strong_universal_T_scfg_abort may_fail_cfg exit0_image exit0_image.
Proof.
  apply strong_universal_T_scfg_abort_may_fail. exact exit0_strong_universal_abort.
Qed.

Theorem exit0_strong_universal_scfg_either :
  strong_universal_T_scfg_either may_fail_cfg exit0_image exit0_image.
Proof.
  apply strong_universal_T_scfg_either_may_fail. exact exit0_strong_universal_either.
Qed.

Theorem exit0_strong_universal_error_free_scfg_abort :
  strong_universal_error_free_T_scfg_abort may_fail_cfg exit0_image exit0_image.
Proof.
  apply strong_universal_error_free_T_scfg_abort_may_fail.
  exact exit0_strong_universal_error_free_abort.
Qed.

(** The either shapes are the pairs their stances make, so each is the
    two halves put together. *)
Theorem exit0_strong_universal_error_free_scfg :
  strong_universal_error_free_T_scfg may_fail_cfg exit0_image exit0_image.
Proof.
  apply strong_universal_error_free_T_scfg_may_fail.
  exact exit0_strong_universal_error_free.
Qed.

Theorem exit0_strong_universal_error_free_scfg_either :
  strong_universal_error_free_T_scfg_either may_fail_cfg exit0_image exit0_image.
Proof.
  split;
    [exact exit0_strong_universal_error_free_scfg
    |exact exit0_strong_universal_error_free_scfg_abort].
Qed.

(** The configuration, as the functor argument the four sealing
    surfaces take.  [Run.may_fail_cfg] is the default a task gets by
    saying nothing about spurious failure, which is the combination
    worth pinning first. *)
Module MayFailCfg <: SPURIOUS_CFG.
  Definition cfg := may_fail_cfg.
End MayFailCfg.

Module Exit0ErrorFreeEitherChecked
  <: SPEC_ERROR_FREE_EITHER Exit0Image Exit0Image.
  Definition strong_universal_error_free := exit0_strong_universal_error_free_either.
End Exit0ErrorFreeEitherChecked.

Module Exit0ScfgAbortChecked <: SPEC_SCFG_ABORT MayFailCfg Exit0Image Exit0Image.
  Definition strong_universal := exit0_strong_universal_scfg_abort.
End Exit0ScfgAbortChecked.

Module Exit0ScfgEitherChecked <: SPEC_SCFG_EITHER MayFailCfg Exit0Image Exit0Image.
  Definition strong_universal := exit0_strong_universal_scfg_either.
End Exit0ScfgEitherChecked.

Module Exit0ErrorFreeScfgAbortChecked
  <: SPEC_ERROR_FREE_SCFG_ABORT MayFailCfg Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_scfg_abort.
End Exit0ErrorFreeScfgAbortChecked.

Module Exit0ErrorFreeScfgEitherChecked
  <: SPEC_ERROR_FREE_SCFG_EITHER MayFailCfg Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_scfg_either.
End Exit0ErrorFreeScfgEitherChecked.

(** The classifier-side reading: [MustExit.must_exit_with] at the
    demo entry, in both directions of [OmniEquivalence.must_exit_with_iff]. *)
Example exit0_omni_exits_zero :
  omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_accept).
Proof. apply must_exit_with_iff. exact exit0_image_must_exit_zero. Qed.

Example exit0_omni_exits_zero_direct :
  omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_accept).
Proof.
  cbn [omni_run exit0_image demo_entry].
  eapply exec_conseq; [apply exit0_exec |]. intros tr o (_ & Hx). exact Hx.
Qed.

Example exit0_omni_exits_zero_legacy :
  must_exit_with verdict_accept exit0_image demo_limit demo_entry demo_proc_input.
Proof. apply must_exit_with_iff. exact exit0_omni_exits_zero_direct. Qed.

(** The wrong code is refuted: [exits_with] is not "halts". *)
Example exit0_omni_not_exits_one :
  ~ omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_reject).
Proof.
  intros H. cbn [omni_run exit0_image demo_entry] in H.
  destruct (exec_realizes _ _ _ H) as (tr & o & Hm & Hx).
  destruct (exec_sound _ _ _ (exit0_exec _ _ _ _ _ _) _ _ Hm) as (_ & Hx0).
  destruct o as [c | c]; [| exact Hx].
  cbn [exits_with] in Hx, Hx0. destruct Hx as (Hx & _). destruct Hx0 as (Hx0 & _).
  rewrite Hx0 in Hx. vm_compute in Hx. discriminate Hx.
Qed.

(* =========================================================================
   PART 3 — the undecodable image refutes them
   ========================================================================= *)

(** Its first fetch leaves the modeled surface, at the ASLR-valid
    entry and at either role budget. *)
Lemma undecodable_unmodeled_at_demo_entry : forall lim,
  bh_unmodeled (run undecodable_image lim demo_entry demo_proc_input).
Proof.
  intros lim.
  cbn [run bh_unmodeled undecodable_image demo_entry]. unfold init_config.
  apply reaches_unmodeled_intro; [reflexivity | reflexivity |].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap demo_proc_input].
  rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

Example undecodable_omni_not_covered : forall lim,
  ~ omni_corun undecodable_image lim demo_entry demo_proc_input (covered undecodable_segments).
Proof.
  intros lim H.
  exact (proj2 (bh_unmodeled_iff undecodable_image lim demo_entry demo_proc_input) H
           (undecodable_unmodeled_at_demo_entry lim)).
Qed.

Example undecodable_omni_not_never_errors : forall lim,
  ~ omni_corun undecodable_image lim demo_entry demo_proc_input never_errors.
Proof.
  intros lim H.
  exact (proj2 (bh_errors_iff undecodable_image lim demo_entry demo_proc_input) H
           (run_unmodeled_errors _ _ _ _ (undecodable_unmodeled_at_demo_entry lim))).
Qed.

(** The positive may-fact behind both: some maximal execution errors
    from an uncovered configuration. *)
Example undecodable_omni_may_uncovered : forall lim,
  omni_may undecodable_image lim demo_entry demo_proc_input (uncovered undecodable_segments).
Proof.
  intros lim. apply bh_unmodeled_may_iff. exact (undecodable_unmodeled_at_demo_entry lim).
Qed.

(** No exit code is ever reached — the omni form of
    [Checks.Examples.undecodable_image_refutes_must_exit], for every
    code at once. *)
Example undecodable_omni_no_exit : forall lim code,
  ~ omni_run undecodable_image lim demo_entry demo_proc_input (exits_with code).
Proof.
  intros lim code H. apply must_exit_with_iff in H.
  exact (must_exit_with_refuted_by_error _ _ _ _ _
           (run_unmodeled_errors _ _ _ _ (undecodable_unmodeled_at_demo_entry lim)) H).
Qed.

(** It is not the ALL-errors escape that fails on it — every execution
    of the undecodable image does error — but the coverage conjunct. *)
Example undecodable_omni_errors : forall lim,
  omni_run undecodable_image lim demo_entry demo_proc_input errors.
Proof.
  intros lim. cbn [omni_run undecodable_image demo_entry].
  apply exec_step; [reflexivity | | intros; exact I |].
  - unfold init_config. eexists; eexists. apply sstep_instr_unmodeled; [reflexivity | reflexivity |].
    match goal with
    | |- mi_account_step ?segs ?ms ?model = _ =>
        rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
    end.
    cbn [mkProcInput in_argv in_envp in_uid in_hwcap demo_proc_input].
    rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
  - intros evs c' Hss. exfalso. unfold init_config in Hss.
    revert Hss. apply unmodeled_no_next; [reflexivity |].
    match goal with
    | |- mi_account_step ?segs ?ms ?model = _ =>
        rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
    end.
    cbn [mkProcInput in_argv in_envp in_uid in_hwcap demo_proc_input].
    rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

(** With the undecodable image as SOURCE, the universal statement is
    refuted at one valid triple through the coverage conjunct — the
    vacuity the clause exists to block, seen from the omni side. *)
Theorem undecodable_source_refutes_omni_strong_universal :
  ~ omni_strong_universal_T undecodable_image exit0_image.
Proof.
  intros H.
  destruct (H demo_entry demo_entry demo_proc_input
              (demo_entry_valid_undecodable _ demo_input_valid)
              (demo_entry_valid_exit0 _ demo_input_valid)
              demo_input_valid) as (Hcov & _).
  exact (undecodable_omni_not_covered source_alloc_limit Hcov).
Qed.

(** The undecodable image emits nothing, at any budget: its initial
    configuration has no successor. *)
Lemma undecodable_cosafe_nil : forall lim,
  omni_cosafe undecodable_image lim demo_entry demo_proc_input (fun tr => tr = []).
Proof.
  intros lim. cbn [omni_cosafe undecodable_image demo_entry].
  apply cosafe_intro; [reflexivity |].
  intros evs c' Hss. exfalso. unfold init_config in Hss.
  revert Hss. apply unmodeled_no_next; [reflexivity |].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap demo_proc_input].
  rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

(** A DIFFERING pair with a sound source: exit-0 against the
    undecodable image is refuted through the trace conjunct — the
    prefix postcondition "nothing is ever emitted" holds of the target
    and fails on the source — after the escape is ruled out, because
    the source never errors. *)
Theorem exit0_vs_undecodable_refutes_omni_strong_universal :
  ~ omni_strong_universal_T exit0_image undecodable_image.
Proof.
  intros H.
  destruct (H demo_entry demo_entry demo_proc_input
              (demo_entry_valid_exit0 _ demo_input_valid)
              (demo_entry_valid_undecodable _ demo_input_valid)
              demo_input_valid) as (_ & [Hall | (Htr & _)]).
  - cbn [omni_run exit0_image demo_entry] in Hall.
    destruct (exec_realizes _ _ _ (exit0_exec (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw source_alloc_limit demo_proc_input))
      as (tr & o & Hm & _ & Hx).
    exact (exits_with_never_errors _ _ _ Hx (exec_sound _ _ _ Hall _ _ Hm)).
  - specialize (Htr _ prefix_closed_nil).
    destruct Htr as (_ & Hnil). specialize (Hnil (undecodable_cosafe_nil _)).
    cbn [omni_cosafe exit0_image demo_entry] in Hnil.
    destruct (exec_realizes _ _ _ (exit0_exec (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw source_alloc_limit demo_proc_input))
      as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
    subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
    discriminate (cosafe_star _ _ _ _ _ Hnil Hstar).
Qed.

(* =========================================================================
   PART 4 — a modeled crash separates the three error postconditions
   ========================================================================= *)

(** One [ebreak] at 0x100 (0x00100073, little-endian): a fault the
    model MODELS — a real process dies there too — as opposed to the
    undecodable word, where the model gives up. *)
Definition ebreak_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["73001000"%pstring]
|}.
Definition ebreak_segments : list Segment := [ebreak_segment].
Definition ebreak_image : Image := mkImage ebreak_segments 0x100 demo_phdrs.

Definition ebreak_ms : machine_state :=
  init_machine_state ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv demo_proc_input) (in_envp demo_proc_input) (in_uid demo_proc_input)
    (in_hwcap demo_proc_input).

Definition ebreak_model (lim : Z) : Model :=
  init_model (segments_reserved ebreak_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input.

Lemma ebreak_config : forall lim,
  init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input
  = mkCfg ebreak_ms (ebreak_model lim).
Proof. reflexivity. Qed.

Lemma ebreak_faults : RiscvSemantics.step ebreak_segments ebreak_ms = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Lemma ebreak_only : forall lim evs st,
  sstep ebreak_segments (mkCfg ebreak_ms (ebreak_model lim)) evs st ->
  evs = [] /\ st = SError.
Proof.
  intros lim. apply sstep_fault_only; [reflexivity | reflexivity | exact ebreak_faults].
Qed.

(** Every execution errors: the escape fires ... *)
Example ebreak_omni_errors : forall lim,
  omni_run ebreak_image lim demo_entry demo_proc_input errors.
Proof.
  intros lim. cbn [omni_run ebreak_image demo_entry]. rewrite ebreak_config.
  apply exec_step; [reflexivity | | intros; exact I |].
  - eexists; eexists. apply sstep_instr_fault; [reflexivity | reflexivity |].
    no_lazy. rewrite ebreak_faults. reflexivity.
  - intros evs c' Hss. destruct (ebreak_only _ _ _ Hss) as (_ & Habs). discriminate Habs.
Qed.

(** ... the crash is COVERED, because the configuration it is taken
    from is one the model has an answer for ... *)
Example ebreak_omni_covered : forall lim,
  omni_corun ebreak_image lim demo_entry demo_proc_input (covered ebreak_segments).
Proof.
  intros lim. cbn [omni_corun ebreak_image demo_entry]. rewrite ebreak_config.
  apply coexec_step; [reflexivity | |].
  - intros evs _ (_ & [(_ & Hun) | (x8 & Hsvc & _)]); cbn [cfg_ms cfg_model] in *.
    + no_lazy_in Hun. rewrite ebreak_faults in Hun. discriminate Hun.
    + vm_compute in Hsvc. discriminate Hsvc.
  - intros evs c' Hss. destruct (ebreak_only _ _ _ Hss) as (_ & Habs). discriminate Habs.
Qed.

(** ... and it is NOT error-free: the three postconditions are
    distinct on a real image. *)
Example ebreak_omni_not_never_errors : forall lim,
  ~ omni_corun ebreak_image lim demo_entry demo_proc_input never_errors.
Proof.
  intros lim H. cbn [omni_corun ebreak_image demo_entry] in H. rewrite ebreak_config in H.
  refine (coexec_sound _ _ _ _ (mexec_error _ _ _ _) _ H I).
  apply sstep_instr_fault; [reflexivity | reflexivity |].
  no_lazy. rewrite ebreak_faults. reflexivity.
Qed.

Example ebreak_omni_may_errors : forall lim,
  omni_may ebreak_image lim demo_entry demo_proc_input errors.
Proof.
  intros lim. apply bh_errors_may_iff. apply run_all_errors_errors.
  apply bh_all_errors_iff. exact (ebreak_omni_errors lim).
Qed.

(** The escape, positively: a crashing source frees ANY target, even
    the undecodable one, at this triple.  This is the per-triple shape
    of what the deliberate-bug examples prove universally. *)
Example ebreak_source_omni_strong_equiv_any : forall T et,
  omni_strong_equiv ebreak_image T demo_entry et demo_proc_input.
Proof.
  intros T et. split.
  - exact (ebreak_omni_covered source_alloc_limit).
  - left. exact (ebreak_omni_errors source_alloc_limit).
Qed.

Example ebreak_frees_undecodable_target :
  omni_strong_equiv ebreak_image undecodable_image demo_entry demo_entry demo_proc_input.
Proof. apply ebreak_source_omni_strong_equiv_any. Qed.

(** ... and the same crash REFUTES the error-free shape, which has no
    escape. *)
Example ebreak_refutes_omni_error_free :
  ~ omni_strong_equiv_error_free ebreak_image ebreak_image demo_entry demo_entry demo_proc_input.
Proof.
  apply omni_strong_equiv_error_free_no_all_errors_escape.
  exact (ebreak_omni_errors source_alloc_limit).
Qed.

(* =========================================================================
   PART 5 — [exec]/[coexec] agreement is strictly weaker than trace equality
   ========================================================================= *)

(** Two images.  [loop]: one [jal x0, 0] at 0x100 (0x0000006f), the
    process spins forever and emits nothing.  [wloop]: [write(1, 0x100, 1)]
    — [addi a7, x0, 64; addi a0, x0, 1; addi a1, x0, 0x100;
    addi a2, x0, 1; ecall] — then the same [jal x0, 0]: one byte of
    its own code (0x93) reaches stdout, then the process spins
    forever. *)
Definition loop_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["6f000000"%pstring]
|}.
Definition loop_segments : list Segment := [loop_segment].
Definition loop_image : Image := mkImage loop_segments 0x100 demo_phdrs.

Definition wloop_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["93080004130510009305001013061000730000006f000000"%pstring]
|}.
Definition wloop_segments : list Segment := [wloop_segment].
Definition wloop_image : Image := mkImage wloop_segments 0x100 demo_phdrs.

(** The byte the write delivers: the low byte of [addi a7, x0, 64]. *)
Definition wloop_byte : byte := Z_to_bv 8 0x93.
Definition wloop_trace : list event := [WriteEv (Z_to_bv 64 1) wloop_byte].

Definition loop_ms : machine_state :=
  init_machine_state loop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv demo_proc_input) (in_envp demo_proc_input) (in_uid demo_proc_input)
    (in_hwcap demo_proc_input).
Definition loop_model (lim : Z) : Model :=
  init_model (segments_reserved loop_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input.
Definition loop_c (lim : Z) : config := mkCfg loop_ms (loop_model lim).

Lemma loop_config : forall lim,
  init_config loop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input = loop_c lim.
Proof. reflexivity. Qed.

(** [jal x0, 0] maps the initial state to itself: the pc gains 0 and
    the write to x0 is dropped, so nothing changes.  With the memory
    abstracted, both sides normalise to the same term. *)
Lemma loop_fix : forall mem,
  RiscvSemantics.step loop_segments (with_mem loop_ms mem) = MachineOk (with_mem loop_ms mem).
Proof. intros. vm_compute. reflexivity. Qed.

Lemma loop_only : forall lim evs st,
  sstep loop_segments (loop_c lim) evs st -> evs = [] /\ st = SNext (loop_c lim).
Proof.
  intros lim. unfold loop_c.
  rewrite (with_mem_eta loop_ms).
  apply sstep_instr_only; [reflexivity | reflexivity | apply loop_fix].
Qed.

Example loop_coexec_any : forall lim Q, coexec loop_segments (loop_c lim) Q.
Proof. intros lim. apply fix_coexec_any; [reflexivity | apply loop_only]. Qed.

Example loop_no_exec : forall lim Q, ~ exec loop_segments (loop_c lim) Q.
Proof. intros lim. apply fix_no_exec; [reflexivity | apply loop_only]. Qed.

Example loop_obs_nil : forall lim tr, obs_trace loop_segments (loop_c lim) tr -> tr = [].
Proof. intros lim. apply fix_obs_nil. apply loop_only. Qed.

(** The write-then-loop run, one transition at a time.  [run_steps]
    walks the instruction stream; the states along it are named by
    their step count, and every step lemma is stated with the memory
    abstracted. *)
Fixpoint run_steps (n : nat) (segs : list Segment) (ms : machine_state)
    : option machine_state :=
  match n with
  | O => Some ms
  | S n' => match RiscvSemantics.step segs ms with
            | MachineOk ms' => run_steps n' segs ms'
            | MachineFault | MachineUnmodeled => None
            end
  end.

Definition wloop_ms0 : machine_state :=
  init_machine_state wloop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv demo_proc_input) (in_envp demo_proc_input) (in_uid demo_proc_input)
    (in_hwcap demo_proc_input).
Definition wloop_msk (k : nat) : machine_state :=
  match run_steps k wloop_segments wloop_ms0 with
  | Some ms => ms
  | None => wloop_ms0
  end.
(** The state after [k] instructions, with the memory of the real
    initial state — which no instruction of this image changes. *)
Definition wloop_s (k : nat) : machine_state := with_mem (wloop_msk k) (ms_mem wloop_ms0).

Definition wloop_model (lim : Z) : Model :=
  init_model (segments_reserved wloop_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input.
Definition wloop_c (lim : Z) : config := mkCfg (wloop_s 0) (wloop_model lim).

Lemma wloop_config : forall lim,
  init_config wloop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input = wloop_c lim.
Proof. intros lim. unfold init_config, wloop_c. f_equal; try exact (with_mem_eta wloop_ms0). Qed.

(** The effect the write is forced to have: one byte copied in from
    0x100, one byte reported written. *)
Definition wloop_eff : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x100, 1%nat)] (mkEffect (Z_to_bv 64 1) [] []).

(** After the syscall: the return value is in a0 and the pc sits on
    the [jal]. *)
Definition wloop_s6 : machine_state := advance_past_svc (apply_effect (wloop_s 5) wloop_eff).

Lemma wloop_step : forall k, (k < 5)%nat -> forall mem,
  RiscvSemantics.step wloop_segments (with_mem (wloop_msk k) mem)
  = MachineOk (with_mem (wloop_msk (S k)) mem).
Proof.
  intros k Hk mem.
  do 5 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma wloop_svc5 : ms_svc_pending (wloop_s 5) = Some (Z_to_bv 64 64).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

Lemma wloop_fix : forall mem,
  RiscvSemantics.step wloop_segments (with_mem wloop_s6 mem) = MachineOk (with_mem wloop_s6 mem).
Proof. intros. vm_compute. reflexivity. Qed.

(** The five instruction transitions, each the only one from its
    configuration. *)
Lemma wloop_instr_only : forall lim k, (k < 5)%nat -> forall evs st,
  sstep wloop_segments (mkCfg (wloop_s k) (wloop_model lim)) evs st ->
  evs = [] /\ st = SNext (mkCfg (wloop_s (S k)) (wloop_model lim)).
Proof.
  intros lim k Hk. unfold wloop_s.
  apply sstep_instr_only; [reflexivity | | apply wloop_step; exact Hk].
  do 5 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma wloop_instr_sstep : forall lim k, (k < 5)%nat ->
  sstep wloop_segments (mkCfg (wloop_s k) (wloop_model lim)) []
    (SNext (mkCfg (wloop_s (S k)) (wloop_model lim))).
Proof.
  intros lim k Hk. unfold wloop_s.
  apply sstep_instr; [reflexivity | |].
  - do 5 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (wloop_step k Hk). reflexivity.
Qed.

(** At the ecall.  The dispatcher at number 64 IS the write spec ... *)
Lemma write_dispatch_iff : forall i m o,
  bv_unsigned (in_sysno i) = 64%Z ->
  syscall_spec i m o <-> write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof.
  intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(** ... whose channel outcome is forced here: fd 1 is stdout, the
    buffer holds one readable byte, so the delivery is that byte. *)
Lemma wloop_write_forced : forall lim eff m' evs,
  syscall_spec (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) (wloop_model lim)
    (Ok eff m' evs) ->
  eff = wloop_eff /\ m' = wloop_model lim /\ evs = wloop_trace.
Proof.
  intros lim eff m' evs Hspec.
  apply write_dispatch_iff in Hspec; [| reflexivity].
  set (i := sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) in *.
  assert (Hfd : fd_lookup (m_fds (wloop_model lim)) (fd32 (in_arg i 0))
                = Some (FdChannel (Z_to_bv 64 1)))
    by (vm_compute; reflexivity).
  assert (Hch : Z_to_bv 64 1 <> 0)
    by (intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H).
  assert (Hrb : read_bytes_map (in_mem i) (in_arg i 1) (in_arg i 2) = Some [wloop_byte])
    by (vm_compute; reflexivity).
  assert (Hne : [wloop_byte] <> []) by discriminate.
  (* The count bound, which [write_channel_outcome] asks for by name.
     The channel arm's gate is [Uaccess.modeled_rw_range], a
     DISJUNCTION, so the lemma states the disjunct its proof uses instead
     of rederiving it from the gate.  This program's [a2] is 1 -- the
     [addi a2, x0, 1] in [wloop_segment]. *)
  assert (Hmax : (bv_unsigned (in_arg i 2) <= rw_bytes_max)%Z)
    by (vm_compute; discriminate).
  destruct (write_channel_outcome _ _ _ _ _ _ _ _ _ _ Hfd Hch Hmax Hrb Hne Hspec)
    as (_ & n & Hn1 & Hn2 & Heff & Hm & Hevs).
  cbn [length] in Hn2. assert (n = 1%nat) by lia. subst n.
  split; [| split; [exact Hm | exact Hevs]].
  rewrite Heff. unfold wloop_eff.
  assert (Ha1 : in_arg i 1 = Z_to_bv 64 0x100) by (apply bv_eq; vm_compute; reflexivity).
  assert (Hlen : len_word (firstn 1 [wloop_byte]) = Z_to_bv 64 1)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Ha1, Hlen. reflexivity.
Qed.

Lemma wloop_checker :
  forall lim,
    check_syscall (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) wloop_eff (wloop_model lim)
    = CheckOk (wloop_model lim) wloop_trace.
Proof. intros lim. vm_compute. reflexivity. Qed.

(** The syscall transition, and that it is the only one. *)
Lemma wloop_syscall_sstep : forall lim,
  sstep wloop_segments (mkCfg (wloop_s 5) (wloop_model lim)) wloop_trace
    (SNext (mkCfg wloop_s6 (wloop_model lim))).
Proof.
  intros lim. unfold wloop_s6.
  eapply sstep_syscall;
    [ reflexivity
    | exact wloop_svc5
    | apply check_syscall_ok_iff; exact (wloop_checker lim)
    | reflexivity
    | apply materialize_model_accesses_no_lazy; reflexivity ].
Qed.

Lemma wloop_syscall_only : forall lim evs st,
  sstep wloop_segments (mkCfg (wloop_s 5) (wloop_model lim)) evs st ->
  evs = wloop_trace /\ st = SNext (mkCfg wloop_s6 (wloop_model lim)).
Proof.
  intros lim evs st Hss.
  pose proof wloop_svc5 as Hsvc.
  inversion Hss; subst; try congruence;
    match goal with
    | [ H : ms_svc_pending (wloop_s 5) = Some ?y |- _ ] =>
        rewrite Hsvc in H; injection H as <-
    end.
  - (* the write, then materialization *)
    match goal with
    | [ H : syscall_spec _ _ (Ok _ _ _), Hmat : materialize_model_accesses _ _ = Some _ |- _ ] =>
        destruct (wloop_write_forced _ _ _ _ H) as (-> & -> & ->);
        no_lazy_materialize_in Hmat;
        injection Hmat as <-
    end.
    split; reflexivity.
  - (* materialization cannot fail: there are no lazy mappings *)
    match goal with
    | [ H : syscall_spec _ _ (Ok _ _ _), Hmat : materialize_model_accesses _ _ = None |- _ ] =>
        destruct (wloop_write_forced _ _ _ _ H) as (-> & -> & ->);
        no_lazy_materialize_in Hmat;
        discriminate Hmat
    end.
  - (* not an exit: the post-model still runs *)
    match goal with
    | [ H : syscall_spec _ _ (Ok _ _ _), Hh : m_halted _ = Some _ |- _ ] =>
        destruct (wloop_write_forced _ _ _ _ H) as (_ & -> & _);
        vm_compute in Hh; discriminate Hh
    end.
  - (* not a kill either, for the same reason *)
    match goal with
    | [ H : syscall_spec _ _ (Ok _ _ _), Hk : m_killed _ = Some _ |- _ ] =>
        destruct (wloop_write_forced _ _ _ _ H) as (_ & -> & _);
        vm_compute in Hk; discriminate Hk
    end.
  - (* not unmodeled: the checker accepts an outcome *)
    match goal with
    | [ H : syscall_spec _ _ Unmodeled |- _ ] =>
        pose proof (check_syscall_complete_unmodeled _ _ wloop_eff H) as Hc;
        rewrite wloop_checker in Hc; discriminate Hc
    end.
Qed.

Lemma wloop_s6_only : forall lim evs st,
  sstep wloop_segments (mkCfg wloop_s6 (wloop_model lim)) evs st ->
  evs = [] /\ st = SNext (mkCfg wloop_s6 (wloop_model lim)).
Proof.
  intros lim. rewrite (with_mem_eta wloop_s6).
  apply sstep_instr_only; [reflexivity | reflexivity | apply wloop_fix].
Qed.

(** The one maximal-looking path: five silent steps, the write, then
    the fixpoint. *)
Lemma wloop_star : forall lim,
  star wloop_segments (wloop_c lim) wloop_trace (mkCfg wloop_s6 (wloop_model lim)).
Proof.
  intros lim.
  change wloop_trace with ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (wloop_trace ++ [])))))).
  unfold wloop_c.
  eapply star_step; [exact (wloop_instr_sstep lim 0 ltac:(lia)) |].
  eapply star_step; [exact (wloop_instr_sstep lim 1 ltac:(lia)) |].
  eapply star_step; [exact (wloop_instr_sstep lim 2 ltac:(lia)) |].
  eapply star_step; [exact (wloop_instr_sstep lim 3 ltac:(lia)) |].
  eapply star_step; [exact (wloop_instr_sstep lim 4 ltac:(lia)) |].
  eapply star_step; [exact (wloop_syscall_sstep lim) |].
  apply star_refl.
Qed.

(** Every [coexec] postcondition holds of the write-then-loop run: no
    execution ends. *)
Example wloop_coexec_any : forall lim Q, coexec wloop_segments (wloop_c lim) Q.
Proof.
  intros lim Q. unfold wloop_c.
  eapply coexec_step_only;
    [exact (wloop_instr_sstep lim 0 ltac:(lia)) | apply wloop_instr_only; lia |].
  eapply coexec_step_only;
    [exact (wloop_instr_sstep lim 1 ltac:(lia)) | apply wloop_instr_only; lia |].
  eapply coexec_step_only;
    [exact (wloop_instr_sstep lim 2 ltac:(lia)) | apply wloop_instr_only; lia |].
  eapply coexec_step_only;
    [exact (wloop_instr_sstep lim 3 ltac:(lia)) | apply wloop_instr_only; lia |].
  eapply coexec_step_only;
    [exact (wloop_instr_sstep lim 4 ltac:(lia)) | apply wloop_instr_only; lia |].
  eapply coexec_step_only;
    [exact (wloop_syscall_sstep lim) | apply wloop_syscall_only |].
  apply fix_coexec_any; [reflexivity | apply wloop_s6_only].
Qed.

(** ... and no [exec] postcondition does. *)
Example wloop_no_exec : forall lim Q, ~ exec wloop_segments (wloop_c lim) Q.
Proof.
  intros lim Q Hex.
  exact (fix_no_exec wloop_segments (mkCfg wloop_s6 (wloop_model lim)) eq_refl
           (wloop_s6_only lim) _ (exec_star _ _ _ _ _ Hex (wloop_star lim))).
Qed.

Example wloop_obs_write : forall lim,
  obs_trace wloop_segments (wloop_c lim) wloop_trace.
Proof.
  intros lim. exists wloop_trace, (mkCfg wloop_s6 (wloop_model lim)).
  split; [exact (wloop_star lim) | apply is_prefix_refl].
Qed.

(** The finding, pinned.  COMPARES TWO RUNS (reason 2), at either
    budget on each side.  The two runs satisfy exactly the same [coexec]
    postconditions and exactly the same [exec] postconditions ... *)
Theorem loop_wloop_coexec_agree : forall lim1 lim2 Q,
  coexec loop_segments (loop_c lim1) Q <-> coexec wloop_segments (wloop_c lim2) Q.
Proof.
  intros lim1 lim2 Q. split; intros _; [apply wloop_coexec_any | apply loop_coexec_any].
Qed.

Theorem loop_wloop_exec_agree : forall lim1 lim2 Q,
  exec loop_segments (loop_c lim1) Q <-> exec wloop_segments (wloop_c lim2) Q.
Proof.
  intros lim1 lim2 Q. split; intros H; exfalso;
    [exact (loop_no_exec _ _ H) | exact (wloop_no_exec _ _ H)].
Qed.

(** ... yet their trace sets differ, so [cosafe] tells them apart ... *)
Theorem loop_wloop_cosafe_disagree : forall lim1 lim2,
  ~ (forall P, prefix_closed P ->
       (cosafe loop_segments (loop_c lim1) P <-> cosafe wloop_segments (wloop_c lim2) P)).
Proof.
  intros lim1 lim2 H.
  destruct (H _ prefix_closed_nil) as (Hnil & _).
  specialize (Hnil (star_cosafe _ _ _ (fun tr c' Hstar => proj1 (fix_star_nil _ _ (loop_only lim1) _ _ Hstar)))).
  discriminate (cosafe_star _ _ _ _ _ Hnil (wloop_star lim2)).
Qed.

Theorem loop_wloop_not_trace_equiv : forall lim1 lim2,
  ~ (forall tr, obs_trace loop_segments (loop_c lim1) tr <-> obs_trace wloop_segments (wloop_c lim2) tr).
Proof.
  intros lim1 lim2 H. apply (loop_wloop_cosafe_disagree lim1 lim2).
  apply obs_equiv_iff_cosafe. exact H.
Qed.

(** ... and so does the run-level equivalence, in both shapes: the omni
    statement through the [iff], the legacy one directly — this is
    [Checks.Examples.write_then_diverge_vs_diverge] on two real images. *)
Theorem loop_wloop_not_omni_trace_equiv :
  ~ omni_trace_equiv loop_image source_alloc_limit demo_entry
                     wloop_image target_alloc_limit demo_entry demo_proc_input.
Proof.
  unfold omni_trace_equiv. cbn [omni_cosafe loop_image wloop_image demo_entry].
  rewrite loop_config, wloop_config. apply loop_wloop_cosafe_disagree.
Qed.

Theorem loop_wloop_not_omni_equiv :
  ~ omni_equiv loop_image source_alloc_limit demo_entry
               wloop_image target_alloc_limit demo_entry demo_proc_input.
Proof.
  intros [Hall | (Htr & _)].
  - cbn [omni_run loop_image demo_entry] in Hall. rewrite loop_config in Hall.
    exact (loop_no_exec _ _ Hall).
  - exact (loop_wloop_not_omni_trace_equiv Htr).
Qed.

Theorem loop_wloop_not_equiv :
  ~ equiv (run loop_image source_alloc_limit demo_entry demo_proc_input)
          (run wloop_image target_alloc_limit demo_entry demo_proc_input).
Proof. intros H. apply loop_wloop_not_omni_equiv. apply equiv_iff. exact H. Qed.

(** Neither image errors or leaves the model, so what separates them
    is the byte and nothing else: both sides of
    [OmniEquivalence.omni_strong_equiv] other than the trace conjunct
    hold. *)
Example loop_wloop_never_errors : forall lim,
  omni_corun loop_image lim demo_entry demo_proc_input never_errors
  /\ omni_corun wloop_image lim demo_entry demo_proc_input never_errors.
Proof.
  intros lim. cbn [omni_corun loop_image wloop_image demo_entry].
  rewrite loop_config, wloop_config.
  split; [apply loop_coexec_any | apply wloop_coexec_any].
Qed.

(** Both images put their only segment inside the first page, so the
    demo entry is valid for either — which is what makes the
    universal refutation below a refutation at a VALID triple. *)
Example demo_entry_valid_loop : forall inp,
  valid_input inp -> valid_entry loop_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [loop_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Example demo_entry_valid_wloop : forall inp,
  valid_input inp -> valid_entry wloop_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [wloop_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Theorem loop_wloop_refutes_omni_strong_universal :
  ~ omni_strong_universal_T loop_image wloop_image.
Proof.
  intros H.
  destruct (H demo_entry demo_entry demo_proc_input
              (demo_entry_valid_loop _ demo_input_valid)
              (demo_entry_valid_wloop _ demo_input_valid)
              demo_input_valid) as (_ & Heq).
  exact (loop_wloop_not_omni_equiv Heq).
Qed.
