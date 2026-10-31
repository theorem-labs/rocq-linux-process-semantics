(** * Common.FileMixSim — file outcome sets with trace-silent erroring branches.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Sibling of [FileSim.v].  Outcomes are
    [(word * Fs.Fs)] pairs; errnos are [Z] ([Te : Z -> _]); fds are
    [word]s and the injected fd is [alloc_fd (m_fds model)]; the
    injectable errno set is [openat_errnos] (membership predicate
    [In e openat_errnos]).  The raw-ecall records carry the
    [ms_resv := None] field and a [bvmap 5 word] register file
    ([reg_get regs 10/11/12] are a0/a1/a2, [getr regs 17] is a7); the
    syscall number is Z-characterized ([bv_unsigned (getr regs 17) = 56%Z]).

    [FileSim.to_fout] characterizes a file-syscall-branching run whose
    every resolution terminates in an (exit code, final fs) outcome.  A
    MAY-erroring source — one where some syscall resolutions run into
    the explicit error transition while others exit cleanly — does not
    fit: under the universal source-error rule ([Equivalence.equiv] via
    [bh_all_errors]) such a source does NOT free the target, so its
    trace set must still be characterized exactly.

    An over-PATH_MAX path is a real -ENAMETOOLONG (see
    [Open.openat_spec]), so it gives an ordinary [FileSim.to_fout] tree,
    not this shape.  This file covers the general shape — a source that
    may error on SOME resolutions and exit cleanly on others — which any
    unmodeled syscall reached on only some resolutions produces.  No
    example instantiates it.

    This file provides [to_fout_mix]: the same shape as [to_fout], plus
    an ERROR LEAF ([tfm_unmodeled]) for a branch that runs a deterministic
    silent instruction line into a syscall whose relational spec is
    [Unmodeled].  Such a branch contributes NO outcome and NO events — every
    [star] run inside it is silent — so the trace set of the whole tree
    is still exactly the prefixes of the outcome traces of the
    surviving outcome set [U] (which must be nonempty,
    [fout_mix_obs_iff]).

    The equivalence-level glue [file_mix_equiv_only] pairs a
    may-erroring source ([to_fout_mix] with set [U]) with a
    never-erroring target ([to_fout] with the SAME set [U]): trace sets
    coincide, and [~ bh_errors] is required of the TARGET only —
    exactly the obligation [Equivalence.equiv] leaves when the source
    escape is unavailable.

    NOTE ([Equivalence.modeled]).  Unlike every other combinator in
    [Common/], this one does NOT supply the source-coverage clause, and
    cannot: [tfm_unmodeled]'s error leaf is a syscall whose spec is [Unmodeled],
    which is precisely [Run.unmodeled_at].  A source that needs
    [tfm_unmodeled] is a source this model failed to follow, so its caller has
    no way to discharge [Equivalence.strong_equiv]'s first conjunct.
    That is why the lemma is named [file_mix_equiv_only] and NOT
    [..._strong_equiv]: every [*_strong_equiv*] lemma in [Common/]
    closes BOTH conjuncts, and this one closes only [equiv], so sharing
    the name would invite a proof author to reach for it and land on an
    unclosable goal.  It has no callers ([openat_spec] answers an
    over-PATH_MAX pathname with an ordinary -ENAMETOOLONG); it is kept
    because the containment it proves is real and the fix for any
    future instance belongs in the SPEC, not in a weaker theorem.
    [AllocMixSim.to_outcomes_mix], whose error leaf is a genuine
    [MachineFault] rather than a spec [Unmodeled], DOES supply the clause —
    see [AllocMixSim.tom_no_unmodeled] for the contrast.

    Ergonomic nodes mirror FileSim's: [tfm_open_rd_rec] /
    [tfm_open_wr_rec] (openat branching with [to_fout_mix]
    continuations).  The error leaf is the generic [tfm_unmodeled]: a silent
    line into a syscall whose spec is [Unmodeled]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatSim ErrEscape FileSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

Section WithSegs.
Variable segs : list Segment.

(** [to_fout] with erroring branches: from [ms] under [model], the
    non-error resolutions produce EXACTLY the outcome set [U], and every
    other resolution runs a deterministic silent instruction line into a
    syscall whose spec is [Unmodeled] (the explicit error transition). *)
Inductive to_fout_mix :
    machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfm_out : forall ms model U,
    to_fout segs ms model U ->
    to_fout_mix ms model U
| tfm_unmodeled : forall ms ms' model x8 (U : (word * Fs.Fs) -> Prop),
    msteps segs ms ms' ->
    ms_svc_pending ms' = Some x8 ->
    syscall_spec (sys_input segs ms' x8) model Unmodeled ->
    (forall o, ~ U o) ->
    to_fout_mix ms model U
| tfm_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_fout_mix ms' model U ->
    to_fout_mix ms model U
| tfm_sys : forall ms model x8
    (T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
    (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (exists eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        to_fout_mix (advance_past_svc (apply_effect ms eff)) model'
                    (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_fout_mix ms model U.

(** Prepend a deterministic instruction run. *)
Lemma tfm_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_fout_mix ms' model U -> to_fout_mix ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tfm_step; eauto.
Qed.

(** Rewire the outcome set along an extensional equivalence. *)
Lemma tfm_equiv : forall ms model U V,
  to_fout_mix ms model U ->
  (forall o, V o <-> U o) ->
  to_fout_mix ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model U Hout
    | ms ms' model x8 U Hm Hsvc Herr HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros V HV.
  - apply tfm_out. eapply tfo_equiv; [exact Hout | exact HV].
  - eapply tfm_unmodeled; [exact Hm | exact Hsvc | exact Herr |].
    intros o Ho. exact (HU o (proj1 (HV o) Ho)).
  - eapply tfm_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tfm_sys ms model x8 T V);
      [exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
    intro o. rewrite (HV o). apply HU.
Qed.

(* ================================================================= *)
(* The error leaf is silent                                          *)
(* ================================================================= *)

(** A syscall configuration whose relational spec is [Unmodeled] has no
    [SNext] successor (completeness of the executable checker). *)
Lemma spec_err_no_snext : forall ms model x8 evs c',
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  ~ sstep segs (mkCfg ms model) evs (SNext c').
Proof.
  intros ms model x8 evs c' Hsvc Herr Hss.
  assert (Hno_ok : forall eff model' events,
      ~ syscall_spec (sys_input segs ms x8) model (Ok eff model' events)).
  { intros eff model' events Hok.
    pose proof Herr as Herr'.
    apply (check_syscall_complete_unmodeled _ _ eff) in Herr'.
    apply check_syscall_complete_ok in Hok.
    rewrite Herr' in Hok. discriminate Hok. }
  inversion Hss; subst; try congruence.
  all: match goal with
       | Hok : syscall_spec (sys_input _ _ ?actual) _
                 (Ok ?eff ?model' ?events) |- _ =>
           assert (Hax : actual = x8) by congruence;
           rewrite Hax in Hok;
           exact (Hno_ok eff model' events Hok)
       end.
Qed.

(** Every [star] run inside a deterministic line into a spec-[Unmodeled]
    syscall is silent. *)
Lemma spec_err_chain_star_silent : forall ms ms' model x8,
  msteps segs ms ms' ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8) model Unmodeled ->
  forall tr c, star segs (mkCfg ms model) tr c -> tr = [].
Proof.
  intros ms ms' model x8 Hm Hlazy;
    induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Hm IH];
    intros Hsvc' Herr tr c Hstar.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst; [reflexivity|].
    exfalso. exact (spec_err_no_snext ms0 model x8 evs c2 Hsvc' Herr Hss).
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst; [reflexivity|].
    destruct (sstep_instr_inv segs ms0 model ms1 evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    eapply IH; eauto.
Qed.

(** The [tfm_unmodeled] leaf is NOT covered: it is [Run.unmodeled_at]
    reached by a silent line, so [OmniRun.covered] is refuted -- the
    contrast with [ErrEscape.msteps_illegal_covered]. *)
Lemma msteps_spec_err_not_covered : forall ms ms' model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8) model Unmodeled ->
  ~ OmniRun.coexec segs (mkCfg ms model) (covered segs).
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Herr Hco.
  apply (coexec_covered segs _ Hco).
  exists [], (mkCfg ms' model). split.
  - apply ErrEscape.msteps_star_nil; assumption.
  - unfold unmodeled_at; cbn [cfg_ms cfg_model].
    split; [exact Hh | right; exists x8; split; assumption].
Qed.

Lemma msteps_spec_err_may_uncovered : forall ms ms' model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8) model Unmodeled ->
  exists tr o, mexec segs (mkCfg ms model) tr o /\ uncovered segs tr o.
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Herr.
  assert (Hun : unmodeled_at segs (mkCfg ms' model)).
  { unfold unmodeled_at; cbn [cfg_ms cfg_model].
    split; [exact Hh | right; exists x8; split; assumption]. }
  destruct (unmodeled_at_sstep_error _ _ Hun) as (evs & Hss).
  exists ([] ++ evs), (OError (mkCfg ms' model)). split.
  - eapply star_mexec with (tr := []) (c' := mkCfg ms' model); [apply ErrEscape.msteps_star_nil; assumption | apply mexec_error; exact Hss].
  - exact Hun.
Qed.

(* ================================================================= *)
(* Trace characterization                                            *)
(* ================================================================= *)

(** "Only" direction: every [star] trace is either empty or a prefix of
    an outcome trace of the surviving set. *)
Lemma tfm_star_only : forall ms model U,
  to_fout_mix ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model U Hout
    | ms ms' model x8 U Hm Hsvc Herr HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy tr c Hstar.
  - right. eapply to_fout_star_only; eauto.
  - left. eapply spec_err_chain_star_silent; eauto.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    + left; reflexivity.
    + destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      eapply IH; eauto.
  - inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    + left; reflexivity.
    + destruct (sstep_fsys_inv segs ms model x8 evs (SNext c2)
                  Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & Hspec & Hevs & Hc2).
      subst evs. inversion Hc2; subst c2.
      destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
      cbn [app].
      destruct (IH eff model' [] Hspec Hh' Hlazy' tr2 c Hstar2)
        as [-> | (o & Ho & Hp)].
      * left; reflexivity.
      * right. exists o. split; [|exact Hp].
        apply HU. exists eff, model', []. auto.
Qed.

(** "Admits" direction: every outcome in the surviving set is realized
    by a full run. *)
Lemma tfm_star_admits : forall ms model U,
  to_fout_mix ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (fout_trace o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model U Hout
    | ms ms' model x8 U Hm Hsvc Herr HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - eapply to_fout_star_admits; eauto.
  - exfalso. exact (HU o Ho).
  - destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
    rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.

(* ================================================================= *)
(* Ergonomic nodes                                                   *)
(* ================================================================= *)

(** Core open node over an abstract success-model builder [mk], with
    [to_fout_mix] continuations (mirror of [FileSim.tfo_open_core]). *)
Lemma tfm_open_core : forall ms model (mk : word -> Model) x8 reads
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None /\ m_vm_lazy (mk fd) = []) ->
  (forall e, In e openat_errnos ->
     to_fout_mix (advance_past_svc
                    (apply_effect ms
                      (with_copyins reads (mkEffect (errno_ret e) [] []))))
                 model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout_mix (advance_past_svc
                    (apply_effect ms (with_copyins reads (mkEffect fd [] []))))
                 (mk fd) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout_mix ms model U.
Proof.
  intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
  apply (tfm_sys ms model x8
    (fun eff model' =>
       if addr_is_error_b (eff_ret eff)
       then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
       else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
  - (* no Unmodeled *)
    intro Hspec.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
      in Hspec.
    rewrite Hchk in Hspec.
    exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
  - (* receptive: ENOMEM *)
    exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
    apply check_syscall_ok_iff. rewrite Hchk.
    apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
    repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
  - (* shape *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & _ & -> & -> & ->)
                      | (fd & _ & _ & -> & -> & ->) ].
    + repeat split; assumption.
    + destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
  - (* continuations *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & HIn & -> & -> & _)
                      | (fd & Hlk & Heq & -> & -> & _) ].
    + destruct (openat_errno_range e HIn) as [He1 He2].
      cbn [eff_ret with_copyins].
      rewrite (errno_ret_error_b e He1 He2).
      rewrite (errno_ret_recover e He1 He2).
      apply Herr; assumption.
    + cbn [eff_ret with_copyins].
      assert (Hne : addr_is_error_b fd = false)
        by (rewrite Heq; apply alloc_fd_not_error_b).
      rewrite Hne.
      apply Hok; assumption.
  - (* outcome set *)
    intro o. rewrite HU. split.
    + intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. left. exists e. auto. }
        { cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
          rewrite (errno_ret_recover e He1 He2). exact Ht. }
      * exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
        { cbn [eff_ret with_copyins].
          assert (Hne : addr_is_error_b fd = false)
            by (rewrite Heq; apply alloc_fd_not_error_b).
          rewrite Hne. exact Ht. }
    + intros (eff & model' & evs & Hspec & Ht).
      apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
      apply check_open_result_copyins_ok_iff in Hspec.
      destruct Hspec as [ (e & HIn & -> & -> & _)
                        | (fd & Hlk & Heq & -> & -> & _) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        cbn [eff_ret with_copyins] in Ht.
        rewrite (errno_ret_error_b e He1 He2) in Ht.
        rewrite (errno_ret_recover e He1 He2) in Ht.
        left. exists e. auto.
      * cbn [eff_ret with_copyins] in Ht.
        assert (Hne : addr_is_error_b fd = false)
          by (rewrite Heq; apply alloc_fd_not_error_b).
        rewrite Hne in Ht.
        right. exists fd. auto.
Qed.

(** O_RDONLY openat of a present file, at the raw ecall record: errno
    branch or any free fd, with [to_fout_mix] continuations. *)
Lemma tfm_open_rd_rec : forall regs pc mem model p d
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout_mix (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                       mem (seg_rom segs))
                 model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout_mix (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
                 (with_fds (fd_insert (m_fds model) fd
                              (FdFile p (Z_to_bv 64 0))) model)
                 (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout_mix {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                 ms_svc_pending := Some (getr regs 17);
                 ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
              model U.
Proof.
  intros regs pc mem model p d Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfm_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile p (Z_to_bv 64 0))) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hfs.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** O_WRONLY|O_CREAT|O_TRUNC openat at the raw ecall record, with
    [to_fout_mix] continuations.  Like [FileSim.tfo_open_wr_rec] it is
    the create lane only — a plain name nothing lives under; the
    implied-directory lane (a deterministic -EISDIR) has no mix-flavoured
    node because no proof on this route reaches one. *)
Lemma tfm_open_wr_rec : forall regs pc mem model p
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = false ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout_mix (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                       mem (seg_rom segs))
                 model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout_mix (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
                 (with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
                    (with_fs (fs_set (m_fs model) p []) model)) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout_mix {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                 ms_svc_pending := Some (getr regs 17);
                 ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
              model U.
Proof.
  intros regs pc mem model p Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfm_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW p (Z_to_bv 64 0)))
                        (with_fs (fs_set (m_fs model) p []) model))
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hun.
  - intro fd. split.
    + rewrite with_fds_halted, with_fs_halted. exact Hh.
    + exact Hlazy.
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(** There is no PATHNAME-shaped error leaf: on a flag word the
    model interprets, every pathname [openat_spec] can be handed gets an
    answer — the string, a real -ENAMETOOLONG, or a real -EFAULT — so an
    [Unmodeled] leaf for a path that does not resolve would be false.
    The generic [tfm_unmodeled] leaf covers a branch that runs silently
    into ANY syscall whose spec is [Unmodeled] — an unmodeled dirfd, an
    unmodeled open-flag combination (which [openat_spec] declines
    BEFORE it fetches the path), an unmodeled syscall number.  Such a
    branch survives no outcome. *)

End WithSegs.

(* ========================================================================= *)
(* Run-level packaging and the equivalence glue.                             *)
(* ========================================================================= *)

(** The trace set of a may-erroring file tree with a NONEMPTY surviving
    outcome set [U] is exactly the prefixes of [U]'s outcome traces (an
    erroring branch contributes only the empty trace, which is a prefix
    of every outcome trace). *)
Lemma fout_mix_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_fout_mix segs (init_machine_state segs pc ph sp mb rnd inp)
              (init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
  (exists o, U o) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto Hne tr.
  unfold init_config.
  set (ms := init_machine_state segs pc ph sp mb rnd inp) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
    by reflexivity.
  assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [])
    by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (tfm_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
      as [Htr' | (o & Ho & Hp')].
    + subst tr'. destruct Hne as [o Ho].
      exists o. split; [exact Ho|].
      destruct tr; [apply is_prefix_nil | destruct Hp].
    + exists o. split; [exact Ho|].
      eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (tfm_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    exists (fout_trace o), c. split; assumption.
Qed.

(** The [Equivalence]-level glue: a MAY-erroring source file tree whose
    surviving outcome set is the (nonempty) [U], against a
    never-erroring target realizing the SAME [U].  The source escape is
    unavailable (some source resolution avoids error), so this
    discharges the non-escape disjunct of [equiv]: exact trace-set
    equality plus target no-error.

    [equiv] ONLY — see the [Equivalence.modeled] note in the header for
    why this combinator cannot close [strong_equiv] and why it
    nonetheless stays. *)
Lemma file_mix_equiv_only :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_fout_mix source_segs
    (init_machine_state source_segs rpc rph rsp rmb rrnd inp)
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
  to_fout target_segs
    (init_machine_state target_segs apc aph asp amb arnd inp)
    (init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
  (exists o, U o) ->
  Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
        (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget Hne.
  right. split.
  - intro tr. cbn.
    rewrite (fout_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
               Hsource Hne tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U
               Htarget tr).
    reflexivity.
  - cbn.
    apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U
             Htarget).
Qed.

(** The omni equivalence — the [equiv] conjunct ONLY, as for
    [file_mix_equiv_only], and named the same way: the source's unmodeled
    leaf is a configuration [Run.unmodeled_at], so [covered] is refuted
    there ([msteps_spec_err_not_covered], [file_mix_unmodeled_leaf_not_covered])
    rather than merely unproved. *)
Lemma file_mix_omni_equiv_only :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_fout_mix source_segs
    (init_machine_state source_segs rpc rph rsp rmb rrnd inp)
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
  to_fout target_segs
    (init_machine_state target_segs apc aph asp amb arnd inp)
    (init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
  (exists o, U o) ->
  omni_equiv (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd)
             (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget Hne.
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (fout_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
               Hsource Hne tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U
               Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U
             Htarget).
Qed.

(** At run level: a source whose init line reaches a spec-[Unmodeled]
    syscall is not [covered], whatever its outcome set -- so no
    [to_fout_mix] combinator can supply [omni_strong_equiv]'s first
    conjunct for it. *)
Lemma file_mix_unmodeled_leaf_not_covered : forall segs pc ph sp brk0 mb rnd lim inp ms' x8,
  msteps segs (init_machine_state segs pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = Some x8 ->
  syscall_spec (sys_input segs ms' x8)
    (init_model (segments_reserved segs) brk0 mb sp lim inp) Unmodeled ->
  ~ omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (covered segs).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' x8 Hm Hsvc Herr.
  cbn [omni_corun]. unfold init_config.
  eapply msteps_spec_err_not_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Herr].
Qed.
End WithFP1.
