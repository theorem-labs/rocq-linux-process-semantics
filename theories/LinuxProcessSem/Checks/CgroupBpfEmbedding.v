(** * LinuxProcessSem.Checks.CgroupBpfEmbedding — the absent-hook launch embedding

    Not part of the trusted specification: theorems ABOUT it.

    [ProcInput24] has exactly fields 1-24 of the process input before
    the cgroup-BPF setsockopt field. [embed24] appends false, the
    host's clone refusers (field 26) at [State.no_clone_refusers] and
    the SIGCHLD launch disposition (field 27) at [true], SIG_DFL;
    [forget24] drops fields 25 to 27, and [embeds24] carries field 26's
    pin and field 27's frame and pin after field 25's. No self-kill stance is lost: true and false
    both embed. Ordinary input predicates additionally pin self-kill
    false, as they did before field 25. [SelfkillEmbedding] composes
    both pins against its mechanically checked 604b5c371ed0 copies.

    [spec_table_pre25] retains the current arms, replacing only 208
    by its body without the hook guard. The predicate and option-body
    source comparisons in [tools/check_bpf_pre_copies.py] bind that
    body and the old predicates to the pre-field commit. This is the
    field-25 delta, not a claim that the separately added socket-pair
    arms were already present before this extension.

    With the field false, dispatch gives exactly the old outcomes.
    Initialization retains the launch value and every successful step
    and finite step sequence retains it. [image_observations24] covers
    every observation of an input in the image, including bounded runs,
    halting and agreement predicates; the step/run definitions themselves
    are unchanged and consult [Specs.syscall_spec]. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad StackLayout RiscvSemantics Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsChildPidsFrame SelfkillEmbedding.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
Import ListNotations.

Record ProcInput24 := mkProcInput24 {
  p24_argv : list (list byte);
  p24_envp : list (list byte);
  p24_image_fs : Fs.Fs;
  p24_stdin : InputStream;
  p24_uid : word;
  p24_gid : word;
  p24_groups : list word;
  p24_net : NetQueue;
  p24_nofile : word;
  p24_sigmask : word;
  p24_hwcap : word;
  p24_abort_terminal : bool;
  p24_va_size : VaSize;
  p24_urandom : InputStream;
  p24_tmp : Fs.Fs;
  p24_kernel : KernelBuild;
  p24_execfn : list byte;
  p24_channel_reader : bool;
  p24_sigpipe_default : bool;
  p24_sigpipe_terminal : bool;
  p24_ppid : word;
  p24_cap_inheritable : word;
  p24_inherited_fds : list (word * list byte);
  p24_selfkill_terminal : bool
}.

Definition embed24 (o : ProcInput24) : ProcInput :=
  {| in_argv := p24_argv o; in_envp := p24_envp o;
     in_image_fs := p24_image_fs o; in_stdin := p24_stdin o;
     in_uid := p24_uid o; in_gid := p24_gid o; in_groups := p24_groups o;
     in_net := p24_net o; in_nofile := p24_nofile o;
     in_sigmask := p24_sigmask o; in_hwcap := p24_hwcap o;
     in_abort_terminal := p24_abort_terminal o;
     in_va_size := p24_va_size o; in_urandom := p24_urandom o;
     in_tmp := p24_tmp o; in_kernel := p24_kernel o;
     in_execfn := p24_execfn o;
     in_channel_reader := p24_channel_reader o;
     in_sigpipe_default := p24_sigpipe_default o;
     in_sigpipe_terminal := p24_sigpipe_terminal o;
     in_ppid := p24_ppid o; in_cap_inheritable := p24_cap_inheritable o;
     in_inherited_fds := p24_inherited_fds o;
     in_selfkill_terminal := p24_selfkill_terminal o;
     in_cgroup_bpf_setsockopt := false;
     in_clone_refusers := no_clone_refusers;
     in_sigchld_default := true |}.

Definition forget24 (inp : ProcInput) : ProcInput24 :=
  {| p24_argv := in_argv inp; p24_envp := in_envp inp;
     p24_image_fs := in_image_fs inp; p24_stdin := in_stdin inp;
     p24_uid := in_uid inp; p24_gid := in_gid inp;
     p24_groups := in_groups inp; p24_net := in_net inp;
     p24_nofile := in_nofile inp; p24_sigmask := in_sigmask inp;
     p24_hwcap := in_hwcap inp;
     p24_abort_terminal := in_abort_terminal inp;
     p24_va_size := in_va_size inp; p24_urandom := in_urandom inp;
     p24_tmp := in_tmp inp; p24_kernel := in_kernel inp;
     p24_execfn := in_execfn inp;
     p24_channel_reader := in_channel_reader inp;
     p24_sigpipe_default := in_sigpipe_default inp;
     p24_sigpipe_terminal := in_sigpipe_terminal inp;
     p24_ppid := in_ppid inp; p24_cap_inheritable := in_cap_inheritable inp;
     p24_inherited_fds := in_inherited_fds inp;
     p24_selfkill_terminal := in_selfkill_terminal inp |}.

Lemma forget24_embed24 : forall o, forget24 (embed24 o) = o.
Proof. intros []. reflexivity. Qed.

Lemma embed24_forget24 : forall inp,
  in_cgroup_bpf_setsockopt inp = false ->
  in_clone_refusers inp = no_clone_refusers ->
  in_sigchld_default inp = true -> embed24 (forget24 inp) = inp.
Proof.
  intros [a e fs s u g gs n nf sm hc ab va r tm kb xf cr sd st pp ci ifd sk bp crf scd]
    H Hc Hs.
  cbn [in_cgroup_bpf_setsockopt] in H. cbn [in_clone_refusers] in Hc.
  cbn [in_sigchld_default] in Hs.
  subst bp crf scd. reflexivity.
Qed.

Lemma embed24_selfkill : forall o,
  in_selfkill_terminal (embed24 o) = p24_selfkill_terminal o.
Proof. reflexivity. Qed.

Lemma image_observations24 : forall (A : Type) (observe : ProcInput -> A) inp,
  in_cgroup_bpf_setsockopt inp = false ->
  in_clone_refusers inp = no_clone_refusers ->
  in_sigchld_default inp = true ->
  observe (embed24 (forget24 inp)) = observe inp.
Proof.
  intros A observe inp H Hc Hs. rewrite (embed24_forget24 inp H Hc Hs). reflexivity.
Qed.

Definition pre24 (V_pre : ProcInput -> Prop) (inp : ProcInput) : Prop :=
  V_pre inp /\ in_selfkill_terminal inp = false.

Definition embeds24 (V V24 : ProcInput -> Prop) : Prop :=
  (forall inp b, V24 (input_with_cgroup_bpf_setsockopt b inp) <-> V24 inp)
  /\ (forall inp b, V24 (input_with_sigchld_default b inp) <-> V24 inp)
  /\ (forall inp, V inp <-> V24 inp /\ in_cgroup_bpf_setsockopt inp = false
                            /\ in_clone_refusers inp = no_clone_refusers
                            /\ in_sigchld_default inp = true).

Lemma embeds24_of_embeds : forall V V_pre,
  embeds V V_pre -> embeds24 V (pre24 V_pre).
Proof.
  intros V V_pre [_ [Hframe [Hsframe HV]]]. split; [|split].
  - intros inp b. unfold pre24. split; intros [Hp Hsk]; split.
    + exact (proj1 (Hframe inp b) Hp).
    + exact Hsk.
    + exact (proj2 (Hframe inp b) Hp).
    + exact Hsk.
  - intros inp b. unfold pre24. split; intros [Hp Hsk]; split.
    + exact (proj1 (Hsframe inp b) Hp).
    + exact Hsk.
    + exact (proj2 (Hsframe inp b) Hp).
    + exact Hsk.
  - intros inp. unfold pre24. rewrite HV.
    split; intros H.
    + destruct H as [Hp [Hsk [Hbp [Hcrf Hscd]]]].
      exact (conj (conj Hp Hsk) (conj Hbp (conj Hcrf Hscd))).
    + destruct H as [[Hp Hsk] [Hbp [Hcrf Hscd]]].
      exact (conj Hp (conj Hsk (conj Hbp (conj Hcrf Hscd)))).
Qed.

Corollary valid_input_embeds24 : embeds24 valid_input (pre24 valid_input_pre).
Proof. apply embeds24_of_embeds, valid_input_embeds. Qed.
Corollary valid_input_abort_embeds24 :
  embeds24 valid_input_abort (pre24 valid_input_abort_pre).
Proof. apply embeds24_of_embeds, valid_input_abort_embeds. Qed.
Corollary valid_input_either_embeds24 :
  embeds24 valid_input_either (pre24 valid_input_either_pre).
Proof. apply embeds24_of_embeds, valid_input_either_embeds. Qed.
Corollary valid_input_sigpipe_ignored_embeds24 :
  embeds24 valid_input_sigpipe_ignored (pre24 valid_input_sigpipe_ignored_pre).
Proof. apply embeds24_of_embeds, valid_input_sigpipe_ignored_embeds. Qed.
Corollary valid_input_sigpipe_either_embeds24 :
  embeds24 valid_input_sigpipe_either (pre24 valid_input_sigpipe_either_pre).
Proof. apply embeds24_of_embeds, valid_input_sigpipe_either_embeds. Qed.
Corollary valid_input_channel_closed_embeds24 :
  embeds24 valid_input_channel_closed (pre24 valid_input_channel_closed_pre).
Proof. apply embeds24_of_embeds, valid_input_channel_closed_embeds. Qed.
Corollary valid_input_channel_either_embeds24 :
  embeds24 valid_input_channel_either (pre24 valid_input_channel_either_pre).
Proof. apply embeds24_of_embeds, valid_input_channel_either_embeds. Qed.
Corollary valid_input_paths_embeds24 :
  embeds24 valid_input_paths (pre24 valid_input_paths_pre).
Proof. apply embeds24_of_embeds, valid_input_paths_embeds. Qed.
Corollary valid_input_sigpipe_kills_embeds24 :
  embeds24 valid_input_sigpipe_kills (pre24 valid_input_sigpipe_kills_pre).
Proof. apply embeds24_of_embeds, valid_input_sigpipe_kills_embeds. Qed.
Corollary valid_input_sv39_embeds24 : embeds24 valid_input_sv39 (pre24 valid_input_sv39_pre).
Proof. apply embeds24_of_embeds, valid_input_sv39_embeds. Qed.
Corollary valid_input_sv57_embeds24 : embeds24 valid_input_sv57 (pre24 valid_input_sv57_pre).
Proof. apply embeds24_of_embeds, valid_input_sv57_embeds. Qed.
Corollary valid_input_va_any_embeds24 :
  embeds24 valid_input_va_any (pre24 valid_input_va_any_pre).
Proof. apply embeds24_of_embeds, valid_input_va_any_embeds. Qed.
Corollary valid_input_hwcap_rv64gc_embeds24 :
  embeds24 valid_input_hwcap_rv64gc (pre24 valid_input_hwcap_rv64gc_pre).
Proof. apply embeds24_of_embeds, valid_input_hwcap_rv64gc_embeds. Qed.
Corollary valid_input_hwcap_rv64gcv_embeds24 :
  embeds24 valid_input_hwcap_rv64gcv (pre24 valid_input_hwcap_rv64gcv_pre).
Proof. apply embeds24_of_embeds, valid_input_hwcap_rv64gcv_embeds. Qed.
Corollary valid_input_abort_hwcap_rv64gc_embeds24 :
  embeds24 valid_input_abort_hwcap_rv64gc (pre24 valid_input_abort_hwcap_rv64gc_pre).
Proof. apply embeds24_of_embeds, valid_input_abort_hwcap_rv64gc_embeds. Qed.
Corollary valid_input_abort_hwcap_rv64gcv_embeds24 :
  embeds24 valid_input_abort_hwcap_rv64gcv (pre24 valid_input_abort_hwcap_rv64gcv_pre).
Proof. apply embeds24_of_embeds, valid_input_abort_hwcap_rv64gcv_embeds. Qed.
Corollary finite_input_embeds24 : embeds24 finite_input (pre24 finite_input_pre).
Proof. apply embeds24_of_embeds, finite_input_embeds. Qed.

(** Copied from Run.v at the pre-field commit named by the source check. *)
Definition valid_input_inherited_pre24 (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ inherited_fds_ok (in_inherited_fds inp) = true.

Lemma valid_input_inherited_embeds24 :
  embeds24 valid_input_inherited valid_input_inherited_pre24.
Proof.
  split; [intros inp b; split; intros H; exact H|].
  split; [intros inp b; split; intros H; exact H|].
  intros inp. unfold valid_input_inherited, valid_input_inherited_pre24.
  embeds_conj.
Qed.

Corollary embeds24_image : forall V V24, embeds24 V V24 ->
  forall o, V (embed24 o) <-> V24 (embed24 o).
Proof.
  intros V V24 [_ [_ HV]] o. split.
  - intros H. exact (proj1 (proj1 (HV (embed24 o)) H)).
  - intros H. apply (proj2 (HV (embed24 o))).
    split; [exact H | split; [reflexivity | split; reflexivity]].
Qed.

Corollary embeds24_excludes : forall V V24, embeds24 V V24 ->
  forall inp, in_cgroup_bpf_setsockopt inp = true -> ~ V inp.
Proof.
  intros V V24 [_ [_ HV]] inp Ht Hv.
  destruct (proj1 (HV inp) Hv) as [_ [Hf _]]. rewrite Ht in Hf. discriminate Hf.
Qed.

Corollary embeds24_covers_images : forall V V24, embeds24 V V24 ->
  forall inp, V inp -> inp = embed24 (forget24 inp).
Proof.
  intros V V24 [_ [_ HV]] inp Hv.
  destruct (proj1 (HV inp) Hv) as [_ [Hf [Hc Hs]]].
  symmetry. exact (embed24_forget24 inp Hf Hc Hs).
Qed.

Lemma finite_input_bpf_default : forall f,
  in_cgroup_bpf_setsockopt (to_proc_input f) = false.
Proof. reflexivity. Qed.

Definition spec_table_pre25 : list SpecArm :=
  mkSpecArm 208%Z (fun i => setsockopt_no_cgroup_bpf_spec
    (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i) ::
  List.filter (fun a => negb (Z.eqb (sa_no a) 208%Z)) spec_table.

(** Keep table lookups over an abstract table, as [dispatch_no_arm] in
    SelfkillEmbedding does: the kernel check at Qed of a proof that
    reduced [lookup_arm] over the unfolded [spec_table_pre25] did not
    end within 420 s. *)
Local Lemma lookup_arm_cons_filter_other : forall a t k n,
  sa_no a = k -> n <> k ->
  lookup_arm (a :: List.filter (fun x => negb (Z.eqb (sa_no x) k)) t) n
  = lookup_arm t n.
Proof.
  intros a t k n Ha Hn. cbn [lookup_arm]. rewrite Ha.
  assert (E : Z.eqb k n = false) by (apply Z.eqb_neq; congruence).
  rewrite E. apply lookup_arm_filter_other. exact Hn.
Qed.

Lemma lookup_arm_pre25_other : forall n, n <> 208%Z ->
  lookup_arm spec_table_pre25 n = lookup_arm spec_table n.
Proof.
  intros n Hn. unfold spec_table_pre25.
  apply lookup_arm_cons_filter_other; [reflexivity | exact Hn].
Qed.

Lemma syscall_spec_bpf_off_pre25 : forall i m o,
  m_cgroup_bpf_setsockopt m = false ->
  (syscall_spec i m o <-> dispatch spec_table_pre25 i m o).
Proof.
  intros i m o Hoff.
  destruct (Z.eq_dec (bv_unsigned (in_sysno i)) 208%Z) as [Hn | Hn].
  - assert (Ha : exists a, lookup_arm spec_table 208%Z = Some a /\
      (sa_spec a i m o <-> setsockopt_spec (fd32 (in_arg i 0))
         (int32 (in_arg i 1)) (int32 (in_arg i 4)) i m o)).
    { eexists. split; [reflexivity |]. reflexivity. }
    assert (Hb : exists b, lookup_arm spec_table_pre25 208%Z = Some b /\
      (sa_spec b i m o <-> setsockopt_no_cgroup_bpf_spec (fd32 (in_arg i 0))
         (int32 (in_arg i 1)) (int32 (in_arg i 4)) i m o)).
    { eexists. split; [reflexivity |]. reflexivity. }
    destruct Ha as (a & Hla & Hsa). destruct Hb as (b & Hlb & Hsb).
    rewrite <- Hn in Hla, Hlb.
    pose proof (dispatch_arm spec_table i m o a Hla) as Hda.
    pose proof (dispatch_arm spec_table_pre25 i m o b Hlb) as Hdb.
    pose proof (setsockopt_no_cgroup_bpf (fd32 (in_arg i 0)) (int32 (in_arg i 1))
                  (int32 (in_arg i 4)) i m o Hoff) as Hs.
    unfold syscall_spec. split.
    + intros H. exact (proj2 Hdb (proj2 Hsb (proj1 Hs (proj1 Hsa (proj1 Hda H))))).
    + intros H. exact (proj2 Hda (proj2 Hsa (proj2 Hs (proj1 Hsb (proj1 Hdb H))))).
  - unfold syscall_spec, dispatch. rewrite (lookup_arm_pre25_other _ Hn).
    reflexivity.
Qed.

Lemma init_model_cgroup_bpf_setsockopt : forall reserved brk0 mbase sp lim inp,
  m_cgroup_bpf_setsockopt (init_model reserved brk0 mbase sp lim inp)
  = in_cgroup_bpf_setsockopt inp.
Proof. reflexivity. Qed.

Lemma init_config_cgroup_bpf_setsockopt : forall segs pc ph sp brk0 mbase rnd lim inp,
  m_cgroup_bpf_setsockopt
    (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
  = in_cgroup_bpf_setsockopt inp.
Proof. reflexivity. Qed.

Lemma bpf_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' ->
  m_cgroup_bpf_setsockopt m'' = m_cgroup_bpf_setsockopt m.
Proof.
  intros m acc m'' H.
  destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_cgroup_bpf_setsockopt. rewrite Hp. reflexivity.
Qed.

Lemma sstep_cfg_cgroup_bpf_setsockopt_kept : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_cgroup_bpf_setsockopt (cfg_model c') = m_cgroup_bpf_setsockopt (cfg_model c).
Proof.
  intros segs cfg c evs c' H. inversion H; subst; cbn [cfg_model].
  - match goal with
    | Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
        destruct (mi_account_step_model_frame _ _ _ _ _ Ha)
          as (_ & _ & _ & _ & _ & Hp & _)
    end.
    unfold m_cgroup_bpf_setsockopt. rewrite Hp. reflexivity.
  - match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_cgroup_bpf_setsockopt m2); [reflexivity |];
        rewrite (bpf_materialize _ _ _ Hm);
        exact (syscall_spec_cgroup_bpf_setsockopt_kept _ _ _ _ _ Hsp)
    end.
  - match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_cgroup_bpf_setsockopt m2); [reflexivity |];
        rewrite (bpf_materialize _ _ _ Hm);
        exact (syscall_spec_cgroup_bpf_setsockopt_kept _ _ _ _ _ Hsp)
    end.
  - match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_cgroup_bpf_setsockopt_kept _ _ _ _ _ Hsp)
    end.
  - match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_cgroup_bpf_setsockopt_kept _ _ _ _ _ Hsp)
    end.
Qed.

Lemma sstep_cgroup_bpf_setsockopt_kept : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  m_cgroup_bpf_setsockopt (cfg_model c') = m_cgroup_bpf_setsockopt (cfg_model c).
Proof.
  intros segs c evs c' H.
  exact (sstep_cfg_cgroup_bpf_setsockopt_kept _ _ _ _ _
    (proj1 (sstep_cfg_may_fail segs c evs (SNext c')) H)).
Qed.

Corollary star_cfg_cgroup_bpf_setsockopt_kept : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  m_cgroup_bpf_setsockopt (cfg_model c') = m_cgroup_bpf_setsockopt (cfg_model c).
Proof.
  intros segs cfg c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_cfg_cgroup_bpf_setsockopt_kept _ _ _ _ _ Hs).
Qed.

Corollary star_cgroup_bpf_setsockopt_kept : forall segs c tr c',
  star segs c tr c' ->
  m_cgroup_bpf_setsockopt (cfg_model c') = m_cgroup_bpf_setsockopt (cfg_model c).
Proof.
  intros segs c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_cgroup_bpf_setsockopt_kept _ _ _ _ Hs).
Qed.

(** At every reachable prefix of an embedded old launch, all syscall
    outcomes use the source-bound pre-field table. This includes either
    old self-kill value and every outcome, not just successful calls. *)
Corollary embed24_prefix_dispatch_cfg :
  forall segs cfg pc ph sp brk0 mbase rnd lim old tr c' i outcome,
  star_cfg segs cfg
    (init_config segs pc ph sp brk0 mbase rnd lim (embed24 old)) tr c' ->
  (syscall_spec i (cfg_model c') outcome <->
   dispatch spec_table_pre25 i (cfg_model c') outcome).
Proof.
  intros segs cfg pc ph sp brk0 mbase rnd lim old tr c' i outcome H.
  apply syscall_spec_bpf_off_pre25.
  rewrite (star_cfg_cgroup_bpf_setsockopt_kept _ _ _ _ _ H).
  reflexivity.
Qed.

Corollary embed24_prefix_dispatch :
  forall segs pc ph sp brk0 mbase rnd lim old tr c' i outcome,
  star segs
    (init_config segs pc ph sp brk0 mbase rnd lim (embed24 old)) tr c' ->
  (syscall_spec i (cfg_model c') outcome <->
   dispatch spec_table_pre25 i (cfg_model c') outcome).
Proof.
  intros segs pc ph sp brk0 mbase rnd lim old tr c' i outcome H.
  apply syscall_spec_bpf_off_pre25.
  rewrite (star_cgroup_bpf_setsockopt_kept _ _ _ _ H).
  reflexivity.
Qed.

Print Assumptions embed24_forget24.
Print Assumptions image_observations24.
Print Assumptions valid_input_embeds24.
Print Assumptions valid_input_inherited_embeds24.
Print Assumptions finite_input_embeds24.
Print Assumptions syscall_spec_bpf_off_pre25.
Print Assumptions star_cfg_cgroup_bpf_setsockopt_kept.
Print Assumptions embed24_prefix_dispatch_cfg.
Print Assumptions embed24_prefix_dispatch.
