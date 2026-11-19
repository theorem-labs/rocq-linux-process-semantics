(** * Common.FileSimLoop — [FileSim.to_fout] with silent-loop leaves.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    [FileSim.to_fout] is inductive: every branch of a derivation ends at
    an exit.  A copying program that reads an endless source (the
    declared random stream of /dev/urandom, or a file whose length a
    word offset cannot reach the end of) never leaves its copy loop on
    some inputs.  [to_floop] is [to_fout] with one more leaf,
    [tfl_loop]: the state lies in a set of configurations from which
    every step is silent, none is an error, and every successor is in
    the set again ([fsilent]); such a leaf has no exit outcome.

    What a derivation gives at run level is what [to_fout]'s does, with
    the empty trace beside the exits: the run never errors, every
    observed trace is empty or a prefix of the exit event of an outcome
    in [U], and every outcome in [U] is reached ([floop_obs_iff]).  Two
    binaries with the same outcome set are equivalent
    ([floop_omni_strong_equiv]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim FileSim FileSimWalk.
From LinuxProcessSemantics.Common Require DivergeSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

Section WithSegs.
Variable segs : list Segment.

(** A SILENT LOOP REGION: no configuration in it is halted, and every step
    out of one is silent, is not the error transition, and lands in the
    region again. *)
Definition fsilent (L : config -> Prop) : Prop :=
  forall c, L c ->
    m_halted (cfg_model c) = None /\
    (forall evs st, sstep segs c evs st ->
       evs = [] /\ exists c', st = SNext c' /\ L c').

Inductive to_floop : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfl_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    (forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
    to_floop ms model U
| tfl_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_floop ms' model U ->
    to_floop ms model U
| tfl_sys : forall ms model x8
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
        to_floop (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_floop ms model U
| tfl_loop : forall ms model (L : config -> Prop) (U : (word * Fs.Fs) -> Prop),
    fsilent L ->
    L (mkCfg ms model) ->
    (forall o, ~ U o) ->
    to_floop ms model U.

(** Every [to_fout] derivation is one. *)
Lemma to_floop_of_fout : forall ms model U,
  to_fout segs ms model U -> to_floop ms model U.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
  - exact (tfl_exit ms model x8 U Hsvc Hx8 HU).
  - exact (tfl_step ms ms' model U Hsvc Hstep IH).
  - exact (tfl_sys ms model x8 T U Hsvc Hne Hrec Hshape IH HU).
Qed.

(** Prepend a deterministic instruction run. *)
Lemma tfl_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_floop ms' model U -> to_floop ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tfl_step; eauto.
Qed.

(** Rewire the outcome set along an extensional equivalence. *)
Lemma tfl_equiv : forall ms model U V,
  to_floop ms model U ->
  (forall o, V o <-> U o) ->
  to_floop ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU
    | ms model L U HL HLc HU ];
    intros V HV.
  - apply (tfl_exit ms model x8); [exact Hsvc | exact Hx8 |].
    intro o. rewrite (HV o). apply HU.
  - eapply tfl_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tfl_sys ms model x8 T V);
      [exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
    intro o. rewrite (HV o). apply HU.
  - apply (tfl_loop ms model L V HL HLc).
    intros o Ho. apply (HU o). apply HV. exact Ho.
Qed.

(* ------------------------------------------------------------------------- *)
(* The silent region                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma fsilent_halted : forall L, fsilent L ->
  forall c, L c -> m_halted (cfg_model c) = None.
Proof. intros L HL c Hc. exact (proj1 (HL c Hc)). Qed.

Lemma fsilent_no_error : forall L, fsilent L ->
  forall c evs, L c -> ~ sstep segs c evs SError.
Proof.
  intros L HL c evs Hc Hss.
  destruct (proj2 (HL c Hc) evs SError Hss) as (_ & c' & Hc' & _).
  discriminate Hc'.
Qed.

Lemma fsilent_next : forall L, fsilent L ->
  forall c evs c', L c -> sstep segs c evs (SNext c') -> L c'.
Proof.
  intros L HL c evs c' Hc Hss.
  destruct (proj2 (HL c Hc) evs (SNext c') Hss) as (_ & c'' & Hc'' & HL').
  injection Hc'' as <-. exact HL'.
Qed.

(** Every step from a silent region stays in it, and none is an error,
    so the region runs forever with no outcome. *)
Lemma fsilent_coexec : forall L, fsilent L ->
  forall c (Q : post), L c -> coexec segs c Q.
Proof.
  intros L HL. cofix CH. intros c Q Hc.
  apply coexec_step.
  - exact (fsilent_halted L HL c Hc).
  - intros evs Hss. exfalso. exact (fsilent_no_error L HL c evs Hc Hss).
  - intros evs c' Hss. exact (CH c' _ (fsilent_next L HL c evs c' Hc Hss)).
Qed.

Lemma fsilent_star : forall L, fsilent L ->
  forall c tr c', star segs c tr c' -> L c -> tr = [].
Proof.
  intros L HL c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH]; intros Hc.
  - reflexivity.
  - destruct (HL c1 Hc) as [_ Hst].
    destruct (Hst evs (SNext c2) Hss) as (Hev & c' & Hc' & HL').
    injection Hc' as <-. subst evs. cbn [app]. exact (IH HL').
Qed.

(* ------------------------------------------------------------------------- *)
(* Run-level readings                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma to_floop_coexec : forall ms model U,
  to_floop ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  coexec segs (mkCfg ms model) (fout_post U).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU
    | ms model L U HL HLc HU ];
    intros Hh Hlazy.
  - apply exec_coexec.
    exact (to_fout_exec segs ms model U (tfo_exit segs ms model x8 U Hsvc Hx8 HU) Hh Hlazy).
  - apply (coexec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply coexec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss.
      destruct (sstep_fsys_inv segs ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_fsys_inv segs ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
      eapply coexec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [cbn [app]; exact Heq | exact Hx].
  - exact (fsilent_coexec L HL _ _ HLc).
Qed.

Lemma to_floop_star_only : forall ms model U,
  to_floop ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU
    | ms model L U HL HLc HU ];
    intros Hh Hlazy tr c Hstar.
  - right.
    exact (to_fout_star_only segs ms model U (tfo_exit segs ms model x8 U Hsvc Hx8 HU)
             Hh Hlazy tr c Hstar).
  - destruct (DivergeSim.star_case segs _ _ _ Hstar)
      as [(-> & _) | (evs & c2 & tr2 & Hss & Hstar2 & ->)]; [left; reflexivity|].
    destruct (sstep_instr_inv segs ms model ms' evs _ Hlazy Hsvc Hstep Hss) as [-> Hst].
    injection Hst as ->. cbn [app].
    exact (IH Hh Hlazy tr2 c Hstar2).
  - destruct (DivergeSim.star_case segs _ _ _ Hstar)
      as [(-> & _) | (evs & c2 & tr2 & Hss & Hstar2 & ->)]; [left; reflexivity|].
    destruct (sstep_fsys_inv segs ms model x8 evs (SNext c2) Hh Hlazy Hsvc Hne Hshape Hss)
      as (eff & model' & Hspec & -> & Hc2). injection Hc2 as ->.
    destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
    cbn [app].
    destruct (IH eff model' [] Hspec Hh' Hlazy' tr2 c Hstar2) as [-> | (o & Ho & Hp)].
    + left. reflexivity.
    + right. exists o. split; [|exact Hp].
      apply HU. exists eff, model', []. split; [exact Hspec | exact Ho].
  - left. exact (fsilent_star L HL _ _ _ Hstar HLc).
Qed.

Lemma to_floop_star_admits : forall ms model U,
  to_floop ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (fout_trace o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU
    | ms model L U HL HLc HU ];
    intros Hh Hlazy o Ho.
  - exact (to_fout_star_admits segs ms model U (tfo_exit segs ms model x8 U Hsvc Hx8 HU)
             Hh Hlazy o Ho).
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
  - exfalso. exact (HU o Ho).
Qed.

(* ------------------------------------------------------------------------- *)
(* The open of an operand, with a continuation that may loop                 *)
(* ------------------------------------------------------------------------- *)

(** [FileSimWalk.tfo_sys_signed], continuing in [to_floop]. *)
Lemma tfl_sys_signed : forall ms model x8 pathp reads (c : SyscallEffect -> check_result)
    (mk : word -> Model) (ok : bool) (Uf Us U : (word * Fs.Fs) -> Prop),
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_getname_refusals (sys_input segs ms x8) [] pathp eff model
                   (Prelude.check_copyins_after reads eff (c (clear_copyins eff)))) ->
  (forall eff, c eff <> CheckUnmodeled) ->
  (exists r0, addr_is_error_b r0 = true /\ c (mkEffect r0 [] []) = CheckOk model []) ->
  (forall eff m' evs, c eff = CheckOk m' evs ->
     evs = [] /\
     ((addr_is_error_b (eff_ret eff) = true /\ m' = model
       /\ eff = mkEffect (eff_ret eff) [] [])
      \/ (ok = true /\ eff = mkEffect (alloc_fd (m_fds model)) [] []
          /\ m' = mk (alloc_fd (m_fds model))))) ->
  (ok = true -> c (mkEffect (alloc_fd (m_fds model)) [] [])
                = CheckOk (mk (alloc_fd (m_fds model))) []) ->
  m_halted (mk (alloc_fd (m_fds model))) = None ->
  m_vm_lazy (mk (alloc_fd (m_fds model))) = [] ->
  (forall r, addr_is_error_b r = true ->
     to_floop (advance_past_svc (apply_effect ms (with_copyins reads (mkEffect r [] []))))
       model Uf) ->
  (ok = true ->
     to_floop (advance_past_svc (apply_effect ms
                 (with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []))))
       (mk (alloc_fd (m_fds model))) Us) ->
  (forall o, U o <-> Uf o \/ (ok = true /\ Us o)) ->
  to_floop ms model U.
Proof.
  intros ms model x8 pathp reads c mk ok Uf Us U Hsvc Hh Hlazy Hchk Hnu Hex Hshape Hokc
    Hmkh Hmkl Herr Hok HU.
  assert (Hinv : forall eff m' evs,
    syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
    evs = [] /\
    ((addr_is_error_b (eff_ret eff) = true /\ m' = model
      /\ apply_effect ms eff
         = apply_effect ms (with_copyins reads (mkEffect (eff_ret eff) [] [])))
     \/ (ok = true
         /\ eff = with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])
         /\ m' = mk (alloc_fd (m_fds model))))).
  { intros eff m' evs Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_getname_refusals_ok_inv in Hs.
    destruct Hs as [Hs | (-> & -> & e & ci & He & ->)].
    - apply Prelude.check_copyins_after_ok_iff in Hs as [Hreads Hc].
      destruct (Hshape _ _ _ Hc) as [Hev [(He & Hm & Heq) | (Hokt & Heq & Hm)]].
      + split; [exact Hev|]. left. split; [exact He|]. split; [exact Hm|].
        f_equal. apply effect_from_copyins_and_clear; [exact Hreads | exact Heq].
      + split; [exact Hev|]. right. split; [exact Hokt|]. split; [|exact Hm].
        apply effect_from_copyins_and_clear; [exact Hreads | exact Heq].
    - split; [reflexivity|]. left.
      assert (HeR : (1 <= e <= 4095)%Z)
        by (cbn [getname_errnos In] in He; destruct He as [<- | []]; cbv [ENOMEM]; lia).
      destruct HeR as [He1 He2].
      split; [exact (errno_ret_error_b e He1 He2)|]. split; reflexivity. }
  assert (Hokw : forall r m1, c (mkEffect r [] []) = CheckOk m1 [] ->
    syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins reads (mkEffect r [] [])) m1 [])).
  { intros r m1 Hc. apply check_syscall_ok_iff. rewrite Hchk.
    apply check_getname_refusals_of_ok.
    apply Prelude.check_copyins_after_ok_iff. split; [reflexivity | exact Hc]. }
  apply (tfl_sys ms model x8
           (fun eff _ => if addr_is_error_b (eff_ret eff) then Uf else Us) U).
  - exact Hsvc.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    apply check_getname_refusals_unmodeled in Hs.
    apply Prelude.check_copyins_after_unmodeled in Hs.
    exact (Hnu _ Hs).
  - destruct Hex as (r0 & _ & Hr0).
    exists (with_copyins reads (mkEffect r0 [] [])), model, [].
    exact (Hokw r0 model Hr0).
  - intros eff m' evs Hs.
    destruct (Hinv _ _ _ Hs) as [Hev [(_ & Hm & _) | (_ & _ & Hm)]];
      subst m' evs.
    + split; [reflexivity|]. split; assumption.
    + split; [reflexivity|]. split; assumption.
  - intros eff m' evs Hs. cbv beta.
    destruct (Hinv _ _ _ Hs) as [_ [(He & Hm & Heq) | (Hokt & Heq & Hm)]];
      subst m'.
    + rewrite He. rewrite Heq. apply Herr. exact He.
    + rewrite Heq, eff_ret_copyins_mk, alloc_fd_not_error_b. exact (Hok Hokt).
  - intro o. rewrite HU. split.
    + intros [Hf | (Hokt & Hs)].
      * destruct Hex as (r0 & Hr0e & Hr0).
        exists (with_copyins reads (mkEffect r0 [] [])), model, [].
        split; [exact (Hokw r0 model Hr0)|]. cbv beta.
        rewrite eff_ret_copyins_mk, Hr0e. exact Hf.
      * exists (with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])),
          (mk (alloc_fd (m_fds model))), [].
        split; [exact (Hokw _ _ (Hokc Hokt))|]. cbv beta.
        rewrite eff_ret_copyins_mk, alloc_fd_not_error_b. exact Hs.
    + intros (eff & m' & evs & Hs & HT). cbv beta in HT.
      destruct (Hinv _ _ _ Hs) as [_ [(He & _ & _) | (Hokt & Heq & _)]].
      * left. rewrite He in HT. exact HT.
      * right. split; [exact Hokt|].
        rewrite Heq, eff_ret_copyins_mk, alloc_fd_not_error_b in HT. exact HT.
Qed.

(** [FileSimWalk.tfo_open_signed_rec], the descriptor continuing in
    [to_floop]; an errno exits ([to_fout]). *)
Lemma tfl_open_signed_rec : forall regs pc mem model p (rd : bool)
    (Uf Us U : (word * Fs.Fs) -> Prop),
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD ->
  reg_get regs 12 = open_flag_word rd ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  proc_self_fd p = None ->
  open_answered rd (m_fs model) (m_cwd model) p ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall r, addr_is_error_b r = true ->
     to_fout segs (mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs)) model Uf) ->
  (forall fe ofs, open_arm rd (m_fs model) (m_cwd model) p = inl (fe, ofs) ->
     to_floop (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem
                    (seg_rom segs))
       (open_model model (alloc_fd (m_fds model)) fe ofs) Us) ->
  (forall o, U o <-> Uf o \/ (open_ok rd (m_fs model) (m_cwd model) p = true /\ Us o)) ->
  to_floop {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17);
              ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p rd Uf Us U H17 H10 H12 Hpath Hpe Hpsf Hans Hfree
    Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = AT_FDCWD)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg2 : ms_gpr ms 2 = open_flag_word rd)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hpath' : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p).
  { unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath. }
  assert (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    by (rewrite Hg2; destruct rd; vm_compute; reflexivity).
  pose (c := fun e => check_walk_refusals (open_walk_mode (open_flag_word rd))
                        (sys_input segs ms (getr regs 17)) (ms_gpr ms 1) e model
                        (open_arm_check rd model p e)).
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = check_getname_refusals (sys_input segs ms (getr regs 17)) [] (ms_gpr ms 1) eff model
        (Prelude.check_copyins_after (open_copyins ms) eff (c (clear_copyins eff)))).
  { intro eff. unfold c.
    rewrite (openat_reduces_to_resolved segs ms (getr regs 17) model p eff
               H17 Hfl Hg0 Hpath' Hpe Hfree).
    rewrite Hg2.
    rewrite (check_openat_resolved_arm rd p (clear_copyins eff) model Hpsf Hans).
    reflexivity. }
  assert (Hwr : forall es,
    walk_reached (open_walk_mode (open_flag_word rd)) (sys_input segs ms (getr regs 17))
      model (ms_gpr ms 1) = Some es ->
    forall e, In e es -> (1 <= e <= 4095)%Z).
  { intros es Hes e He.
    rewrite (walk_reached_si (open_walk_mode (open_flag_word rd)) segs ms (getr regs 17)
               model p Hpath' Hpe) in Hes.
    injection Hes as <-. exact (walk_errnos_range _ _ e He). }
  assert (Hnu : forall eff, c eff <> CheckUnmodeled).
  { intros eff Hc. unfold c in Hc. cbv beta in Hc.
    apply check_walk_refusals_unmodeled in Hc.
    unfold open_arm_check in Hc.
    destruct (open_arm rd (m_fs model) (m_cwd model) p) as [[fe ofs]|e].
    - destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [apply check_open_write_existing_unmodeled in Hc|];
        exact (check_open_result_never_unmodeled _ _ _ Hc).
    - exact (check_ret_only_no_unmodeled _ _ _ _ Hc). }
  assert (Hrej : forall eff m' evs,
    open_arm_check rd model p eff = CheckReject ->
    c eff = CheckOk m' evs ->
    evs = [] /\ addr_is_error_b (eff_ret eff) = true /\ m' = model
    /\ eff = mkEffect (eff_ret eff) [] []).
  { intros eff m' evs Ha Hc. unfold c in Hc. cbv beta in Hc.
    unfold check_walk_refusals in Hc. rewrite Ha in Hc.
    destruct (walk_reached (open_walk_mode (open_flag_word rd))
                (sys_input segs ms (getr regs 17)) model (ms_gpr ms 1)) as [es|] eqn:Hw;
      [|discriminate Hc].
    destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate Hc]. destruct zs; [|discriminate Hc].
    destruct us; [|discriminate Hc]. destruct cs; [|discriminate Hc].
    destruct ci; [|discriminate Hc].
    destruct (errno_ret_in es r) eqn:Hin; [|discriminate Hc].
    injection Hc as <- <-.
    apply errno_ret_in_true in Hin. destruct Hin as (e & HIn & ->).
    assert (HeR : (1 <= e <= 4095)%Z)
      by first [exact (Hwr es Hw e HIn) | exact (Hwr es eq_refl e HIn)].
    destruct HeR as [He1 He2].
    split; [reflexivity|]. split; [|split; reflexivity].
    cbn [eff_ret]. exact (errno_ret_error_b e He1 He2). }
  assert (Herr' : forall r, addr_is_error_b r = true ->
    to_floop (advance_past_svc (apply_effect ms (with_copyins (open_copyins ms)
                                                   (mkEffect r [] [])))) model Uf).
  { intros r Hr. unfold ms. rewrite adv_eff_ret_copyins.
    exact (to_floop_of_fout _ _ _ (Herr r Hr)). }
  destruct (open_arm rd (m_fs model) (m_cwd model) p) as [[fe ofs]|e] eqn:Harm.
  - (* a descriptor, or an errno beside it, -ETXTBSY among them on an
       existing file's write open *)
    assert (Hacok : forall eff m1 evs1, open_arm_check rd model p eff = CheckOk m1 evs1 ->
              check_open_result eff model (fun fd => open_model model fd fe ofs)
                = CheckOk m1 evs1
              \/ (eff = mkEffect (errno_ret ETXTBSY) [] [] /\ m1 = model /\ evs1 = [])).
    { intros eff m1 evs1 Ha. unfold open_arm_check in Ha. rewrite Harm in Ha.
      destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [exact (check_open_write_existing_ok_cases _ _ _ _ _ _ Ha) | left; exact Ha]. }
    assert (Haclift : forall eff m1 evs1,
              check_open_result eff model (fun fd => open_model model fd fe ofs)
                = CheckOk m1 evs1 ->
              open_arm_check rd model p eff = CheckOk m1 evs1).
    { intros eff m1 evs1 Ho. unfold open_arm_check. rewrite Harm.
      destruct (open_arm_txtbsy rd (m_fs model) (m_cwd model) p);
        [exact (check_open_write_existing_lift _ _ _ _ _ _ Ho) | exact Ho]. }
    apply (tfl_sys_signed ms model (getr regs 17) (ms_gpr ms 1) (open_copyins ms) c
             (fun fd => open_model model fd fe ofs) true Uf Us U).
    + unfold ms. reflexivity.
    + exact Hh.
    + exact Hlazy.
    + exact Hchk.
    + exact Hnu.
    + exists (errno_ret ENOMEM).
      destruct (openat_errno_range ENOMEM ENOMEM_in_openat_errnos) as [He1 He2].
      split; [exact (errno_ret_error_b _ He1 He2)|].
      unfold c. cbv beta.
      rewrite (Haclift _ model []); [reflexivity|].
      apply (proj2 (check_open_result_ok_iff _ _ _ model [])).
      left; exists ENOMEM; repeat split; try reflexivity;
        apply ENOMEM_in_openat_errnos.
    + intros eff m' evs Hc.
      destruct (open_arm_check rd model p eff) as [m1 evs1| |] eqn:Ha.
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. cbn [check_walk_refusals] in Hc.
        injection Hc as <- <-.
        destruct (Hacok _ _ _ Ha) as [Ha' | (Heff & Hm & Hev)].
        -- apply check_open_result_ok_iff in Ha'.
           destruct Ha' as [(e & HIn & Heff & Hm & Hev) | (fd & Hlk & Hfd & Heff & Hm & Hev)].
           ++ split; [exact Hev|]. left.
              destruct (openat_errno_range e HIn) as [He1 He2].
              subst eff. rewrite eff_ret_mk.
              split; [exact (errno_ret_error_b e He1 He2)|]. split; [exact Hm | reflexivity].
           ++ split; [exact Hev|]. right. subst fd.
              split; [reflexivity|]. split; [exact Heff | exact Hm].
        -- split; [exact Hev|]. left.
           subst eff. rewrite eff_ret_mk.
           split; [exact (errno_ret_error_b ETXTBSY ltac:(cbv [ETXTBSY]; lia)
                            ltac:(cbv [ETXTBSY]; lia))|].
           split; [exact Hm | reflexivity].
      * destruct (Hrej eff m' evs Ha Hc) as (Hev & He & Hm & Heq).
        split; [exact Hev|]. left. exact (conj He (conj Hm Heq)).
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. discriminate Hc.
    + intros _. unfold c. cbv beta.
      rewrite (Haclift _ (open_model model (alloc_fd (m_fds model)) fe ofs) []);
        [reflexivity|].
      apply (proj2 (check_open_result_ok_iff _ _ _
                      (open_model model (alloc_fd (m_fds model)) fe ofs) [])).
      right; exists (alloc_fd (m_fds model)); repeat split; try reflexivity;
        exact Hfree.
    + unfold open_model. destruct ofs; exact Hh.
    + unfold open_model. destruct ofs; exact Hlazy.
    + exact Herr'.
    + intros _. unfold ms. rewrite adv_eff_ret_copyins.
      first [exact (Hok fe ofs Harm) | exact (Hok fe ofs eq_refl)].
    + intro o. rewrite HU. unfold open_ok. rewrite Harm. cbv beta iota. tauto.
  - (* the arm's own errno *)
    destruct (open_arm_errno_range rd (m_fs model) (m_cwd model) p e Harm) as [He1 He2].
    assert (Hac : forall eff, open_arm_check rd model p eff
                              = check_ret_only eff (errno_ret e) model []).
    { intro eff. unfold open_arm_check. rewrite Harm. reflexivity. }
    apply (tfl_sys_signed ms model (getr regs 17) (ms_gpr ms 1) (open_copyins ms) c
             (fun _ => model) false Uf Us U).
    + unfold ms. reflexivity.
    + exact Hh.
    + exact Hlazy.
    + exact Hchk.
    + exact Hnu.
    + exists (errno_ret e). split; [exact (errno_ret_error_b e He1 He2)|].
      unfold c. cbv beta. rewrite Hac.
      rewrite (proj2 (check_ret_only_ok_iff _ _ _ _ model []))
        by (repeat split; reflexivity).
      reflexivity.
    + intros eff m' evs Hc.
      destruct (open_arm_check rd model p eff) as [m1 evs1| |] eqn:Ha.
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. cbn [check_walk_refusals] in Hc.
        injection Hc as <- <-.
        rewrite Hac in Ha. apply check_ret_only_ok_iff in Ha.
        destruct Ha as (Heff & Hm & Hev).
        split; [exact Hev|]. left. subst eff. rewrite eff_ret_mk.
        split; [exact (errno_ret_error_b e He1 He2)|]. split; [exact Hm | reflexivity].
      * destruct (Hrej eff m' evs Ha Hc) as (Hev & He & Hm & Heq).
        split; [exact Hev|]. left. exact (conj He (conj Hm Heq)).
      * unfold c in Hc. cbv beta in Hc. rewrite Ha in Hc. discriminate Hc.
    + intros Hf. discriminate Hf.
    + exact Hh.
    + exact Hlazy.
    + exact Herr'.
    + intros Hf. discriminate Hf.
    + intro o. rewrite HU. unfold open_ok. rewrite Harm. cbv beta iota. tauto.
Qed.

(** [FileSimWalk.tfo_open_operand_rec], the descriptor continuing in
    [to_floop]. *)
Lemma tfl_open_operand_rec : forall regs pc mem model p (rd : bool)
    (Uf Us U : (word * Fs.Fs) -> Prop),
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD ->
  reg_get regs 12 = open_flag_word rd ->
  read_cstr (mrb segs mem) (reg_get regs 11)
    = (if Nat.ltb (length p) path_max then CstrOk p else CstrTooLong) ->
  (op_walked p = true -> proc_self_fd p = None) ->
  (op_walked p = true -> open_answered rd (m_fs model) (m_cwd model) p) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall r, addr_is_error_b r = true ->
     to_fout segs (mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs)) model Uf) ->
  (forall fe ofs, open_arm rd (m_fs model) (m_cwd model) p = inl (fe, ofs) ->
     to_floop (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem
                    (seg_rom segs))
       (open_model model (alloc_fd (m_fds model)) fe ofs) Us) ->
  (forall o, U o <-> Uf o \/ (op_walked p = true
                             /\ open_ok rd (m_fs model) (m_cwd model) p = true /\ Us o)) ->
  to_floop {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17);
              ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p rd Uf Us U H17 H10 H12 Hpath Hpsf Hans Hfree Hh Hlazy
    Herr Hok HU.
  assert (Hfl : modeled_open_flags (reg_get regs 12) = true)
    by (rewrite H12; destruct rd; vm_compute; reflexivity).
  destruct (Nat.ltb (length p) path_max) eqn:Hlt;
    rewrite ?Hlt in Hpath; cbv beta iota in Hpath.
  - destruct (path_eqb p []) eqn:Hpe.
    + (* the empty pathname: -ENOENT before the walk *)
      apply to_floop_of_fout.
      assert (Hw : op_walked p = false)
        by (unfold op_walked; rewrite Hpe; reflexivity).
      apply (tfo_equiv segs _ _ Uf U).
      2:{ intro o. rewrite HU, Hw. split;
            [ intros [Ho | (Hf & _)]; [exact Ho | discriminate Hf]
            | intros Ho; left; exact Ho ]. }
      set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                    ms_svc_pending := Some (getr regs 17);
                    ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem;
                    ms_rom := seg_rom segs |}).
      apply (tfo_openat_empty_enoent segs ms model (getr regs 17) p Uf).
      * unfold ms. reflexivity.
      * exact H17.
      * unfold ms. rewrite record_gpr, arg_reg_1.
        rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
      * exact Hpe.
      * unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
      * exact Hh.
      * exact Hlazy.
      * unfold ms. rewrite adv_eff_ret_copyins.
        apply Herr. apply errno_ret_error_b; cbv [ENOENT]; lia.
      * intros e He. unfold ms. rewrite adv_eff_ret_copyins.
        apply Herr. cbn [getname_errnos In] in He.
        destruct He as [<- | []]. apply errno_ret_error_b; cbv [ENOMEM]; lia.
    + (* the walk *)
      assert (Hw : op_walked p = true)
        by (unfold op_walked; rewrite Hpe, Hlt; reflexivity).
      apply (tfl_open_signed_rec regs pc mem model p rd Uf Us U H17 H10 H12 Hpath
               Hpe (Hpsf Hw) (Hans Hw) Hfree Hh Hlazy Herr Hok).
      intro o. rewrite HU, Hw. split.
      * intros [Ho | (_ & Ho)]; [left; exact Ho | right; exact Ho].
      * intros [Ho | Ho]; [left; exact Ho | right; split; [reflexivity | exact Ho]].
  - (* no NUL within PATH_MAX: -ENAMETOOLONG before the walk *)
    apply to_floop_of_fout.
    assert (Hw : op_walked p = false)
      by (unfold op_walked; rewrite Hlt, andb_false_r; reflexivity).
    apply (tfo_equiv segs _ _ Uf U).
    2:{ intro o. rewrite HU, Hw. split;
          [ intros [Ho | (Hf & _)]; [exact Ho | discriminate Hf]
          | intros Ho; left; exact Ho ]. }
    apply (tfo_open_toolong_rec segs regs pc mem model Uf H17 Hfl Hpath Hh Hlazy).
    + apply Herr. apply errno_ret_error_b; cbv [ENAMETOOLONG]; lia.
    + intros e He. apply Herr. cbn [getname_errnos In] in He.
      destruct He as [<- | []]. apply errno_ret_error_b; cbv [ENOMEM]; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Silent paths to anchors: how a loop region is shown silent                 *)
(* ------------------------------------------------------------------------- *)

(** A SILENT PATH TO AN ANCHOR: instruction steps, and syscalls every
    resolution of which is silent and goes on along such a path, ending at
    a configuration of [A]. *)
Inductive fpath (A : config -> Prop) : config -> Prop :=
| fp_anchor : forall c, A c -> fpath A c
| fp_instr : forall ms model ms',
    m_halted model = None ->
    m_vm_lazy model = [] ->
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    fpath A (mkCfg ms' model) ->
    fpath A (mkCfg ms model)
| fp_sys : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    m_halted model = None ->
    m_vm_lazy model = [] ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = [] /\
       fpath A (mkCfg (advance_past_svc (apply_effect ms eff)) model')) ->
    fpath A (mkCfg ms model).

(** Prepend a plain instruction run. *)
Lemma fpath_msteps : forall A ms ms' model,
  msteps segs ms ms' -> m_halted model = None -> m_vm_lazy model = [] ->
  fpath A (mkCfg ms' model) -> fpath A (mkCfg ms model).
Proof.
  intros A ms ms' model H; induction H; intros Hh Hlazy Hp; [exact Hp|].
  eapply fp_instr; eauto.
Qed.

(** A deterministic silent syscall on a path. *)
Lemma fpath_sys_det : forall A ms model x8 eff model',
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff2 m2 evs2,
     syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
     eff2 = eff /\ m2 = model' /\ evs2 = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  fpath A (mkCfg (advance_past_svc (apply_effect ms eff)) model') ->
  fpath A (mkCfg ms model).
Proof.
  intros A ms model x8 eff model' Hsvc Hh Hlazy Huniq Hne Hh' Hlazy' Hp.
  apply (fp_sys A ms model x8 Hsvc Hh Hlazy Hne).
  intros eff2 m2 evs2 Hs. destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & ->).
  repeat split; assumption.
Qed.

(** THE LOOP REGION OF A SET OF ANCHORS: if every anchor is a syscall
    state whose every resolution is silent and goes on along a silent
    path to an anchor, the configurations on such paths form a silent
    loop region. *)
Definition fanchored (A : config -> Prop) : Prop :=
  forall a, A a ->
    exists ms model x8, a = mkCfg ms model /\
      ms_svc_pending ms = Some x8 /\ m_halted model = None /\ m_vm_lazy model = [] /\
      ~ syscall_spec (sys_input segs ms x8) model Unmodeled /\
      (forall eff model' evs,
         syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
         evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = [] /\
         fpath A (mkCfg (advance_past_svc (apply_effect ms eff)) model')).

Lemma fsilent_fpath : forall A, fanchored A -> fsilent (fpath A).
Proof.
  intros A HA c Hc.
  (* a syscall state every resolution of which is silent onto a path *)
  assert (Hsys : forall ms model x8,
    ms_svc_pending ms = Some x8 -> m_halted model = None -> m_vm_lazy model = [] ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = [] /\
       fpath A (mkCfg (advance_past_svc (apply_effect ms eff)) model')) ->
    forall evs st, sstep segs (mkCfg ms model) evs st ->
      evs = [] /\ exists c', st = SNext c' /\ fpath A c').
  { intros ms model x8 Hsvc Hh Hlazy Hne Hres evs st Hss.
    assert (Hshape : forall eff model' evs',
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') ->
      evs' = [] /\ m_halted model' = None /\ m_vm_lazy model' = []).
    { intros eff model' evs' Hs. destruct (Hres eff model' evs' Hs) as (He & Hh' & Hl' & _).
      repeat split; assumption. }
    destruct (sstep_fsys_inv segs ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
      as (eff & model' & Hspec & Hev & Hst).
    split; [exact Hev|].
    exists (mkCfg (advance_past_svc (apply_effect ms eff)) model').
    split; [exact Hst|].
    destruct (Hres eff model' [] Hspec) as (_ & _ & _ & Hp). exact Hp. }
  destruct Hc as [a Ha | ms model ms' Hh Hlazy Hsvc Hstep Hp
                  | ms model x8 Hsvc Hh Hlazy Hne Hres].
  - destruct (HA a Ha) as (ms & model & x8 & -> & Hsvc & Hh & Hlazy & Hne & Hres).
    split; [exact Hh|].
    exact (Hsys ms model x8 Hsvc Hh Hlazy Hne Hres).
  - split; [exact Hh|].
    intros evs st Hss.
    destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) as [Hev Hst].
    split; [exact Hev|]. exists (mkCfg ms' model). split; [exact Hst | exact Hp].
  - split; [exact Hh|].
    exact (Hsys ms model x8 Hsvc Hh Hlazy Hne Hres).
Qed.

(* ------------------------------------------------------------------------- *)
(* What one read or write answers, as a set of resolutions                    *)
(* ------------------------------------------------------------------------- *)

(** read(2) of a regular file: the one resolution [FileSim.tfo_read_file]
    takes. *)
Lemma read_file_spec : forall ms model x8 p off data w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFile p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  Fs.fs_ino_data (m_fs model) p = data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (forall eff m' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     eff = mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                    (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
               (FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model
     /\ evs = [])
  /\ ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros ms model x8 p off data w Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
               (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    - cbv beta iota.
      rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
      tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  split.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
    unfold check_read in Hs.
    rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
    cbv beta iota in Hs.
    revert Hs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + discriminate.
Qed.

(** write(2) of a positive count to a regular file: the one resolution
    [FileSim.tfo_write_file] takes. *)
Lemma write_file_spec : forall ms model x8 p off data bs,
  bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  Fs.fs_ino_data (m_fs model) p = data ->
  negb (modeled_file_gap data off bs) = false ->
  w_is0 (ms_gpr ms 2) = false ->
  (forall eff m' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     eff = with_copyins [(ms_gpr ms 1, length bs)] (mkEffect (ms_gpr ms 2) [] [])
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
               (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)
     /\ evs = [])
  /\ ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros ms model x8 p off data bs Hno Hfd Hfd32 Hrd Hok Hcnt Hfs Hgap Hnz.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (Fs.fs_set_ino_data (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite Hok. cbn [negb]. cbv beta iota.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
      exfalso. apply andb_prop in Hg' as [Hnz' Hz].
      apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
      rewrite Hz in Hlen. cbn in Hlen.
      assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
      unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hnz. reflexivity. }
  split.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(** write(2) to /dev/null opened for writing: the count, nothing else
    ([FileSimWalk.tfo_write_null_rec]). *)
Lemma write_null_spec_rec : forall regs pc mem rom model fdv rd buf cnt,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdDevNull rd true) ->
  fd32 fdv = fdv ->
  access_okb buf (bv_unsigned cnt) = true ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall eff m' evs,
     syscall_spec (sys_input segs
       {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
          ms_svc_pending := Some (getr regs 17);
          ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
       (getr regs 17)) model (Ok eff m' evs) ->
     eff = mkEffect cnt [] [] /\ m' = model /\ evs = [])
  /\ ~ syscall_spec (sys_input segs
         {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
            ms_svc_pending := Some (getr regs 17);
            ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
         (getr regs 17)) model Unmodeled.
Proof.
  intros regs pc mem rom model fdv rd buf cnt H17 H10 H11 H12 Hfd Hfd32 Haok Hcnt.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = check_ret_only eff cnt model []).
  { intro eff.
    rewrite (check_syscall_64 segs ms _ eff model H17). unfold check_write.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    unfold modeled_rw_range. rewrite Haok, orb_true_r. cbn [negb].
    unfold check_access_ok_zero. rewrite Haok.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs. exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(** write(2) of a positive count to /dev/urandom opened for writing, from
    a buffer every byte of which reads: the whole count
    ([FileSimWalk.tfo_write_urandom_rec]). *)
Lemma write_urandom_spec_rec : forall regs pc mem model fdv rd buf cnt bs,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdUrandom rd true) ->
  fd32 fdv = fdv ->
  rdn segs mem buf (word_to_nat cnt) = Some bs ->
  access_okb buf (bv_unsigned cnt) = true ->
  (0 < bv_unsigned cnt <= page_size)%Z ->
  (forall eff m' evs,
     syscall_spec (sys_input segs
       {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
          ms_svc_pending := Some (getr regs 17);
          ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
       (getr regs 17)) model (Ok eff m' evs) ->
     eff = with_copyins [(buf, Z.to_nat (bv_unsigned cnt))] (mkEffect cnt [] [])
     /\ m' = model /\ evs = [])
  /\ ~ syscall_spec (sys_input segs
         {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
            ms_svc_pending := Some (getr regs 17);
            ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
         (getr regs 17)) model Unmodeled.
Proof.
  intros regs pc mem model fdv rd buf cnt bs H17 H10 H11 H12 Hfd Hfd32 Hrd Haok Hpg.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  assert (Hcnt : (bv_unsigned cnt <= rw_bytes_max)%Z)
    by (unfold rw_bytes_max, page_size in *; lia).
  assert (Hrb : read_bytes_map (ms_read_byte ms) buf cnt = Some bs).
  { rewrite read_bytes_map_read_byte.
    rewrite (ms_read_bytes_rdn segs ms) by reflexivity. exact Hrd. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (u64_range cnt) as Hrange.
  assert (Hdev : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = check_random_write (bv_unsigned cnt) (bv_unsigned cnt)
        (fun r => [(buf, Z.to_nat r)]) eff model).
  { intro eff.
    rewrite (check_syscall_64 segs ms _ eff model H17). unfold check_write.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    unfold modeled_rw_range. rewrite Haok, orb_true_r. cbn [negb].
    unfold check_access_ok_zero. rewrite Haok.
    rewrite in_mem_si.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    rewrite (rw_count_clamp_of_rw _ Hcnt), Hlen. reflexivity. }
  assert (Hn0 : Z.eqb (bv_unsigned cnt) 0 = false) by (apply Z.eqb_neq; lia).
  assert (H0n : Z.eqb 0 (bv_unsigned cnt) = false) by (apply Z.eqb_neq; lia).
  assert (Hiff : forall eff m' evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
    (eff = with_copyins [(buf, Z.to_nat (bv_unsigned cnt))] (mkEffect cnt [] [])
     /\ m' = model /\ evs = [])).
  { intros [ret ws zs us cs ci] m' evs.
    rewrite Hdev, check_random_write_eq, Hn0.
    destruct ws as [|w ws];
      [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
    destruct zs as [|z zs];
      [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
    destruct us as [|u us];
      [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
    destruct cs as [|c cs];
      [| split; [intro H; discriminate H | intros (H & _); discriminate H]].
    cbv beta iota.
    rewrite (random_write_countb_full (bv_unsigned cnt) (bv_unsigned ret)) by lia.
    rewrite (random_write_countb_full (bv_unsigned cnt) 0) by lia.
    rewrite H0n, !andb_false_r. cbn [andb].
    destruct (Z.eqb (bv_unsigned ret) (bv_unsigned cnt)) eqn:Hr.
    - apply Z.eqb_eq in Hr. apply bv_eq in Hr. subst ret.
      rewrite (w_is0_pos cnt) by lia. cbn [negb andb].
      destruct (access_ranges_eqb ci [(buf, Z.to_nat (bv_unsigned cnt))]) eqn:Hci.
      + apply access_ranges_eqb_eq in Hci. subst ci. split.
        * intro H. injection H as <- <-. split; [reflexivity|]. split; reflexivity.
        * intros (_ & -> & ->). reflexivity.
      + split; [intro H; discriminate H|].
        intros (H & _). apply (f_equal eff_copyins) in H. cbn in H. subst ci.
        rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl) in Hci. discriminate Hci.
    - rewrite andb_false_r. cbn [andb]. split; [intro H; discriminate H|].
      intros (H & _). apply (f_equal eff_ret) in H. cbn in H. subst ret.
      rewrite Z.eqb_refl in Hr. discriminate Hr. }
  split.
  - intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. apply Hiff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hdev in Hs. exact (check_random_write_no_unmodeled _ _ _ _ _ Hs).
Qed.

(** read(2) of /dev/urandom opened for reading, a count of at most a page
    into a writable buffer: the declared stream's first count bytes
    ([FileSimWalk.tfo_read_urandom_rec]). *)
Lemma read_urandom_spec_rec : forall regs pc mem rom model fdv wr buf cnt,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdUrandom true wr) ->
  fd32 fdv = fdv ->
  wseg_ok segs buf (word_to_nat cnt) = true ->
  (0 < bv_unsigned cnt <= page_size)%Z ->
  access_okb buf (bv_unsigned cnt) = true ->
  stream_infinite (m_urandom model) ->
  (forall eff m' evs,
     syscall_spec (sys_input segs
       {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
          ms_svc_pending := Some (getr regs 17);
          ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
       (getr regs 17)) model (Ok eff m' evs) ->
     eff = mkEffect cnt (delivered_writes buf
                           (fst (stream_take_z (m_urandom model) (bv_unsigned cnt)))) []
     /\ m' = with_urandom (snd (stream_take_z (m_urandom model) (bv_unsigned cnt))) model
     /\ evs = [])
  /\ ~ syscall_spec (sys_input segs
         {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
            ms_svc_pending := Some (getr regs 17);
            ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
         (getr regs 17)) model Unmodeled.
Proof.
  intros regs pc mem rom model fdv wr buf cnt H17 H10 H11 H12 Hfd Hfd32 Hwseg Hpos
    Haok Hinf.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hcnt : (bv_unsigned cnt <= rw_bytes_max)%Z)
    by (unfold rw_bytes_max, page_size in *; lia).
  assert (Hlenz : Z.of_nat (length (fst (stream_take_z (m_urandom model) (bv_unsigned cnt))))
                  = bv_unsigned cnt)
    by (apply stream_take_z_infinite_length; [exact Hinf | lia]).
  assert (Hlw : len_word (fst (stream_take_z (m_urandom model) (bv_unsigned cnt))) = cnt).
  { unfold len_word. rewrite Hlenz. apply Z_to_bv_bv_unsigned. }
  assert (Hbs_ne : fst (stream_take_z (m_urandom model) (bv_unsigned cnt)) <> []).
  { intro He. rewrite He in Hlenz. cbn in Hlenz. lia. }
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
  assert (Hw1 : exists w1, read_bytes_map (ms_writable_byte segs ms) buf (Z_to_bv 64 1)
                          = Some w1).
  { eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
    change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
  destruct Hw1 as [w1 Hw1].
  assert (Hdev : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = match eff with
      | mkEffectU ret [(a, bs')] [] [] [] [] =>
          if (bv_eqb a buf
              && (Z.eqb (Z.of_nat (length bs')) (bv_unsigned cnt)
                  || random_page_stopb (bv_unsigned cnt) (Z.of_nat (length bs')))
              && bv_eqb ret (len_word bs')
              && listN_eqb bs' (fst (stream_take_z (m_urandom model)
                                       (Z.of_nat (length bs')))))%bool
          then CheckOk (with_urandom (snd (stream_take_z (m_urandom model)
                                             (Z.of_nat (length bs')))) model) []
          else CheckReject
      | _ => CheckReject
      end).
  { intro eff.
    rewrite (check_syscall_63 segs ms _ eff model H17). unfold check_read.
    rewrite Hg0, Hfd32, Hfd, Hg1, Hg2. cbv beta iota. cbn [negb].
    rewrite Haok. cbn [negb]. cbv beta iota.
    unfold check_read_urandom.
    rewrite (w_is0_pos cnt) by lia. cbv beta iota.
    rewrite in_wmem_si, Hw1. cbv beta iota zeta.
    rewrite (rw_count_clamp_of_rw _ Hcnt).
    rewrite Hlenz, Z.eqb_refl. cbn [negb]. cbv beta iota.
    rewrite Hlw, Hw. cbv beta iota. reflexivity. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
    (eff = mkEffect cnt (delivered_writes buf
                           (fst (stream_take_z (m_urandom model) (bv_unsigned cnt)))) []
     /\ m' = with_urandom (snd (stream_take_z (m_urandom model) (bv_unsigned cnt))) model
     /\ evs = [])).
  { intros eff m' evs. rewrite Hdev.
    rewrite (delivered_writes_ne buf _ Hbs_ne).
    destruct eff as [ret ws zs us cs ci]. split.
    - intro H.
      destruct ws as [|[a bs'] [|? ?]]; try discriminate H.
      destruct zs as [|? ?]; [|discriminate H].
      destruct us as [|? ?]; [|discriminate H].
      destruct cs as [|? ?]; [|discriminate H].
      destruct ci as [|? ?]; [|discriminate H].
      rewrite (random_page_stopb_small (bv_unsigned cnt)) in H by lia.
      rewrite orb_false_r in H.
      match type of H with
      | (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate H]
      end.
      injection H as <- <-.
      repeat rewrite andb_true_iff in Hb. destruct Hb as [[[Ha Hk] Hr] Hl].
      apply bv_eqb_eq in Ha. apply Z.eqb_eq in Hk.
      apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hl.
      rewrite Hk in Hl. subst a. rewrite Hk. rewrite <- Hl.
      rewrite Hr. rewrite Hl, Hlw.
      split; [reflexivity|]. split; reflexivity.
    - intros (Heff & -> & ->).
      injection Heff as -> -> -> -> -> ->.
      rewrite Hlenz.
      rewrite (random_page_stopb_small (bv_unsigned cnt)) by lia.
      rewrite Hlw, !bv_eqb_refl, Z.eqb_refl.
      rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
      reflexivity. }
  split.
  - intros eff2 m2 evs2 Hs. apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hdev in Hs. discriminate Hs.
Qed.

End WithSegs.

(* ------------------------------------------------------------------------- *)
(* Run-level packaging and the equivalence glue                               *)
(* ------------------------------------------------------------------------- *)

Lemma floop_corun : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_floop (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
       (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  coexec (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) (fout_post U).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  unfold init_config.
  exact (to_floop_coexec (run_segments segs inp sp mb) _ _ U Hto eq_refl eq_refl).
Qed.

Lemma floop_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_floop (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
       (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
    <-> (tr = [] \/ exists o, U o /\ is_prefix tr (fout_trace o)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  set (m0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
               (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) in *.
  assert (Hh : m_halted m0 = None) by reflexivity.
  assert (Hlazy : m_vm_lazy m0 = []) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_floop_star_only (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy tr' c Hstar)
      as [-> | (o & Ho & Hp')].
    + left. exact (DivergeSim.is_prefix_nil_inv tr Hp).
    + right. exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
  - intros [-> | (o & Ho & Hp)].
    + exists [], (mkCfg ms m0). split; [apply star_refl | apply is_prefix_refl].
    + destruct (to_floop_star_admits (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy o Ho)
        as [c Hstar].
      exists (fout_trace o), c. split; assumption.
Qed.

(** The omni equivalence for two copying binaries with the SAME outcome
    set [U], at the two role budgets, each derivation allowed silent
    loops. *)
Lemma floop_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_floop (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          source_alloc_limit inp)) U ->
  to_floop (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          target_alloc_limit inp)) U ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (floop_corun source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (floop_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (floop_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - 
    eapply coexec_conseq;
      [exact (floop_corun target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget) |].
    intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithFP.
