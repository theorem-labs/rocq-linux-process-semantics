(** * LinuxProcessSem.Checks.Cases.Ns.CloneFilterCases — the forced-only filter of a failed clone

    The check cases of P11 (b): which errno answers of a clone the filter
    keeps ([Procs.clone_kept]) and which it removes
    ([Procs.clone_removed]), under [Ns.Spec.ns_ext] and under
    [Ns.Ext.no_ext], for callers in the namespace world or words with a
    namespace bit.  An answer it keeps is a step of [Procs.px_clone_fail]'s
    premise ([Procs.clone_fail_step_kept]); one it removes is not
    ([Procs.clone_fail_step_removed]).  Three examples at the end take
    cases (1) and (2) to a step, from a machine state at a clone ecall.

    A clone into a closed children's pid namespace answers ENOMEM after
    the model cursors advance.  The cases below check that the forced-only
    filter keeps that table answer, reaching the process step.  Thread
    forms still wait for their rules.  At the default launch, where the
    children's namespace is the active namespace, every namespace-table
    errno is EPERM, EINVAL or ENOSPC, none in [Fork.clone_errnos];
    [NsProcs.ns_clone_filter_released] gives the unchanged filter there.
    Under [no_ext], [Procs.clone_kept_unchanged] and
    [Procs.clone_removed_unchanged] still give it at every launch. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Clone Spec.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require SpuriousCfg.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require Import CloneCases.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require SpecCases.
From LinuxProcessSemantics.EquivalenceDefinition Require Import NsProcs.
Import ListNotations.
Open Scope Z_scope.

Abbreviation errno_eff := SpuriousCfg.errno_eff.

(** The clone family (FamFd) forced-only, every other family may fail. *)
Abbreviation fd_off_cfg := SpecCases.fd_off_cfg.

(** The answer every removal below compares with: clone(2) gives a pid. *)
Definition pid_eff : SyscallEffect := mkEffect (Z_to_bv 64 4242) [] [].

(** An errno answer [e] is removed when the family is forced-only, [e] is
    a refusal, the spec admits a pid at the same input (a non-refusal), and
    the tables do not decide [e]. *)
Lemma removed_of : forall ext cfg i m m1 f ctx st hq e,
  injected_family_off cfg i = true ->
  refusal_b i m (errno_ret e) = true ->
  check_syscall i pid_eff m = CheckOk m1 [] ->
  refusal_b i m (Z_to_bv 64 4242) = false ->
  ~ clone_table_kept ext f m ctx st hq e ->
  clone_removed ext cfg i m f ctx st hq e (errno_eff e).
Proof.
  intros ext cfg i m m1 f ctx st hq e Hoff Hr Hok Hnr Hnk.
  split; [|exact Hnk]. split; [exact Hoff|]. split; [exact Hr|].
  exists pid_eff, m1, []. split; [apply check_syscall_sound_ok; exact Hok | exact Hnr].
Qed.

(** A fork word from the shell inside the pid namespace the model made
    (CloneCases.v: [shell], [inside]): the namespace world, and the tables
    answer a child. *)
Definition fork_w : word := Z_to_bv 64 17.

Example fork_inside_is_namespace_world :
  flat_view shell inside = false
  /\ exists c r s, clone_ns_exact 17 clone_case_model shell inside 140 = CnOk c r s.
Proof. split; [vm_compute; reflexivity|]. vm_compute. do 3 eexists. reflexivity. Qed.

(** There the tables decide no errno. *)
Lemma fork_inside_tables_keep_nothing : forall m e,
  ~ clone_table_kept ns_ext 17 m shell inside 140 e.
Proof. intros m e (_ & [(s & H) | H]); vm_compute in H; discriminate H. Qed.

(** (1) Every family allowed: today's answers.  Each of the four errnos
    is an answer of the spec, and is kept. *)
Example p11b_may_fail_keeps_every_errno : forall e,
  In e clone_errnos ->
  check_syscall (clone_in fork_w) (errno_eff e) clone_case_model = CheckOk clone_case_model []
  /\ clone_kept ns_ext may_fail_cfg (clone_in fork_w) clone_case_model 17 shell inside 140 e
       (errno_eff e).
Proof.
  intros e He. split; [|apply clone_kept_may_fail].
  cbn [clone_errnos In] in He.
  repeat destruct He as [<- | He]; try contradiction; check_eq.
Qed.

(** (2) FamFd forced-only, the namespace-world fork word whose
    [clone_ns_exact] is [CnOk]: ENOMEM, EAGAIN, EMFILE and EACCES are
    removed, as today. *)
Example p11b_fd_off_fork_word_removes_four : forall e,
  In e clone_errnos ->
  clone_removed ns_ext fd_off_cfg (clone_in fork_w) clone_case_model 17 shell inside 140 e
    (errno_eff e).
Proof.
  intros e He. cbn [clone_errnos In] in He.
  repeat destruct He as [<- | He]; try contradiction;
    (apply removed_of with (m1 := with_child (Z_to_bv 64 4242) clone_case_model);
     [vm_compute; reflexivity | vm_compute; reflexivity | check_eq | vm_compute; reflexivity
     | apply fork_inside_tables_keep_nothing]).
Qed.

(** (3) FamFd forced-only, CLONE_NEWNS from a task without CAP_SYS_ADMIN
    inside the user namespace the model made: the tables answer EPERM
    ([clone_newns_inside_needs_admin]).  ENOMEM and EAGAIN are removed and
    EPERM is kept, as today; EPERM is the tables' answer. *)
Definition newns_f : Z := Z.lor CLONE_NEWNS 17.
Definition newns_w : word := Z_to_bv 64 newns_f.

(** A model whose credentials are uid 65534, as CloneCases.v's callers. *)
Definition creds_m : Model := with_creds (creds 65534) clone_case_model.

Example p11b_fd_off_newns_eperm :
  clone_ns_exact newns_f creds_m no_admin_inside inside 140 = CnErr EPERM inside
  /\ clone_removed ns_ext fd_off_cfg (clone_in newns_w) creds_m newns_f no_admin_inside
       inside 140 ENOMEM (errno_eff ENOMEM)
  /\ clone_removed ns_ext fd_off_cfg (clone_in newns_w) creds_m newns_f no_admin_inside
       inside 140 EAGAIN (errno_eff EAGAIN)
  /\ check_syscall (clone_in newns_w) (errno_eff EPERM) creds_m = CheckOk creds_m []
  /\ clone_kept ns_ext fd_off_cfg (clone_in newns_w) creds_m newns_f no_admin_inside
       inside 140 EPERM (errno_eff EPERM)
  /\ clone_table_kept ns_ext newns_f creds_m no_admin_inside inside 140 EPERM.
Proof.
  assert (Hnk : forall e', e' <> EPERM ->
            ~ clone_table_kept ns_ext newns_f creds_m no_admin_inside inside 140 e')
    by (intros e' Hne (_ & [(s & H) | H]); vm_compute in H;
        [injection H as H _; apply Hne; symmetry; exact H | discriminate H]).
  split; [vm_compute; reflexivity|].
  split; [|split; [|split; [|split]]].
  - apply removed_of with (m1 := with_child (Z_to_bv 64 4242) creds_m);
      [vm_compute; reflexivity | vm_compute; reflexivity | check_eq | vm_compute; reflexivity
      | apply Hnk; discriminate].
  - apply removed_of with (m1 := with_child (Z_to_bv 64 4242) creds_m);
      [vm_compute; reflexivity | vm_compute; reflexivity | check_eq | vm_compute; reflexivity
      | apply Hnk; discriminate].
  - check_eq.
  - apply clone_kept_not_refusal. vm_compute. reflexivity.
  - apply (proj2 (ns_clone_table_kept _ _ _ _ _ _)). left. exists inside.
    vm_compute. reflexivity.
Qed.

(** (5) Every family forced-only, CLONE_NEWUSER from the host where
    [clone_count_undecided] holds (the host's user namespace is not sealed,
    so the tables cannot tell the count): ENOSPC is an answer of the spec,
    of the run's clone environment ([clone_tables_failures]), and is kept.
    The caller is in the released world; the word makes a namespace. *)
Definition newuser_f : Z := Z.lor CLONE_NEWUSER 17.
Definition newuser_w : word := Z_to_bv 64 newuser_f.

Example p11b_forced_only_newuser_enospc_kept :
  has_ns_bits newuser_f = true
  /\ clone_count_undecided newuser_f creds_m caller host = true
  /\ check_syscall (clone_in newuser_w) (errno_eff ENOSPC) creds_m = CheckOk creds_m []
  /\ clone_tables_failures newuser_f creds_m caller host 138 ENOSPC host
  /\ clone_kept ns_ext forced_only_cfg (clone_in newuser_w) creds_m newuser_f caller host 138
       ENOSPC (errno_eff ENOSPC).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [check_eq|].
  split; [right; right; split; [reflexivity | split; [reflexivity | vm_compute; reflexivity]]|].
  apply clone_kept_not_refusal. vm_compute. reflexivity.
Qed.

(** (6) Under [no_ext]: today's answers exactly.  For bubblewrap's
    namespace word from the shell inside the namespaces, both decisions are
    the released filter's at every configuration and errno; under
    forced-only, ENOSPC is an answer and is kept, and ENOMEM is removed,
    as the released filter removes it. *)
Definition bwrap_f : Z := bv_unsigned bwrap_clone_flags.

Example p11b_no_ext_is_released : forall cfg en eff,
  (clone_kept no_ext cfg (clone_in bwrap_clone_flags) clone_case_model bwrap_f shell inside 140
     en eff
   <-> ~ spurious_refusal_cfg cfg (clone_in bwrap_clone_flags) clone_case_model eff)
  /\ (clone_removed no_ext cfg (clone_in bwrap_clone_flags) clone_case_model bwrap_f shell inside
        140 en eff
      <-> spurious_refusal_cfg cfg (clone_in bwrap_clone_flags) clone_case_model eff).
Proof.
  intros cfg en eff. split;
    [apply clone_kept_unchanged | apply clone_removed_unchanged]; left; reflexivity.
Qed.

Example p11b_no_ext_bwrap_answers :
  check_syscall (clone_in bwrap_clone_flags) (errno_eff ENOSPC) clone_case_model
    = CheckOk clone_case_model []
  /\ clone_kept no_ext forced_only_cfg (clone_in bwrap_clone_flags) clone_case_model bwrap_f
       shell inside 140 ENOSPC (errno_eff ENOSPC)
  /\ clone_removed no_ext forced_only_cfg (clone_in bwrap_clone_flags) clone_case_model bwrap_f
       shell inside 140 ENOMEM (errno_eff ENOMEM).
Proof.
  split; [check_eq|]. split.
  - apply clone_kept_not_refusal. vm_compute. reflexivity.
  - apply (proj2 (proj2 (p11b_no_ext_is_released _ _ _))).
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    exists pid_eff, (with_child (Z_to_bv 64 4242) clone_case_model), [].
    split; [apply check_syscall_sound_ok; check_eq | vm_compute; reflexivity].
Qed.

(** TO THE STEP.  A machine state at a clone ecall (220 pending, a0 the
    fork word), the shell's call of case (1) and case (2): with every
    family allowed the ENOMEM answer is a step of [px_clone_fail]'s
    premise, and with FamFd forced-only it is none. *)
Definition clone_ms : machine_state := {|
  ms_regs := bvmap_set (Z_to_bv 5 10) fork_w bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := Some (Z_to_bv 64 220);
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None; ms_rom := fun _ => None |}.

Example p11b_step_may_fail_enomem_kept :
  clone_fail_step ns_ext [] may_fail_cfg (mkCfg clone_ms clone_case_model) shell inside 140
    ENOMEM [] (mkCfg (advance_past_svc (apply_effect clone_ms (errno_eff ENOMEM))) clone_case_model).
Proof.
  apply clone_fail_step_kept with (x8 := Z_to_bv 64 220) (model' := clone_case_model);
    [reflexivity | reflexivity | apply check_syscall_sound_ok; check_eq | reflexivity
    | vm_compute; reflexivity | apply clone_kept_may_fail].
Qed.

Example p11b_step_fd_off_enomem_removed : forall evs m'',
  ~ clone_fail_step ns_ext [] fd_off_cfg (mkCfg clone_ms clone_case_model) shell inside 140
      ENOMEM evs (mkCfg (advance_past_svc (apply_effect clone_ms (errno_eff ENOMEM))) m'').
Proof.
  intros evs m''. apply clone_fail_step_removed with (x8 := Z_to_bv 64 220); [reflexivity|].
  apply removed_of with (m1 := with_child (Z_to_bv 64 4242) clone_case_model);
    [vm_compute; reflexivity | vm_compute; reflexivity | check_eq | vm_compute; reflexivity|].
  intros (_ & [(s & H) | H]); vm_compute in H; discriminate H.
Qed.

(** Case (1) at the step: with every family allowed, the premise of
    [px_clone_fail] is today's released step, whatever the errno. *)
Example p11b_step_may_fail_is_released : forall en evs c',
  clone_fail_step ns_ext [] may_fail_cfg (mkCfg clone_ms clone_case_model) shell inside 140
    en evs c'
  <-> sstep_cfg [] may_fail_cfg (mkCfg clone_ms clone_case_model) evs (SNext c').
Proof. intros en evs c'. apply clone_fail_step_may_fail. Qed.

(** A closed children's namespace gives its own ENOMEM, even when FamFd
    is forced-only.  It advances every model cursor without resetting
    the closed namespace, and the failed clone updates the shared state. *)
Definition closed_children_model : Model := launch_children_model clone_case_model.
Definition closed_children_state : NsState := pid_failed launch_children_state 3.
Definition closed_children_after : NsState := pid_advanced closed_children_state 3.

Lemma closed_children_table :
  clone_ns_exact 17 closed_children_model launch_children_ctx closed_children_state 141
    = CnErr ENOMEM closed_children_after.
Proof. exact (proj1 (closed_children_enomem clone_case_model)). Qed.

Example closed_children_forced_enomem_kept :
  clone_table_kept ns_ext 17 closed_children_model launch_children_ctx closed_children_state 141 ENOMEM /\
  clone_kept ns_ext fd_off_cfg (clone_in fork_w) closed_children_model 17
    launch_children_ctx closed_children_state 141 ENOMEM (errno_eff ENOMEM).
Proof.
  assert (Htable : clone_table_kept ns_ext 17 closed_children_model launch_children_ctx
      closed_children_state 141 ENOMEM).
  { apply (proj2 (ns_clone_table_kept _ _ _ _ _ _)).
    left. exists closed_children_after. exact closed_children_table. }
  split; [exact Htable|]. right. exact Htable.
Qed.

Definition closed_children_config_after : config :=
  mkCfg (advance_past_svc (apply_effect clone_ms (errno_eff ENOMEM))) closed_children_model.

Example closed_children_forced_enomem_step :
  clone_fail_step ns_ext [] fd_off_cfg (mkCfg clone_ms closed_children_model)
    launch_children_ctx closed_children_state 141 ENOMEM [] closed_children_config_after.
Proof.
  apply clone_fail_step_kept with (x8 := Z_to_bv 64 220) (model' := closed_children_model);
    [reflexivity | reflexivity | apply check_syscall_sound_ok; check_eq | reflexivity
    | vm_compute; reflexivity | right; exact (proj1 closed_children_forced_enomem_kept)].
Qed.

Definition closed_children_entry : ProcessEntry :=
  with_nsctx (one_entry (mkCfg clone_ms closed_children_model)) launch_children_ctx.
Definition closed_children_system : pconfig :=
  mkPCfg [(one_pid, closed_children_entry)] one_pid
    (with_sh_ns (pcfg_shared (one_proc (mkCfg clone_ms closed_children_model))) closed_children_state).

Example closed_children_forced_enomem_process_step :
  pstep_x_at ns_ext clone_tables_failures [] fd_off_cfg one_pid closed_children_system []
    (PNext (absorb_x closed_children_system closed_children_entry closed_children_config_after
      launch_children_ctx closed_children_after)).
Proof.
  apply px_clone_fail with (e := closed_children_entry) (en := ENOMEM) (hq := 141).
  - vm_compute. reflexivity.
  - reflexivity.
  - exact closed_children_forced_enomem_step.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - left. exact closed_children_table.
  - right. left. exact closed_children_table.
Qed.

Print Assumptions closed_children_table.
Print Assumptions closed_children_forced_enomem_kept.
Print Assumptions closed_children_forced_enomem_step.
Print Assumptions closed_children_forced_enomem_process_step.
Print Assumptions clone_ns_exact_errno.
Print Assumptions ns_clone_filter_released.
Print Assumptions ns_clone_fail_step_released.

(** The closed-namespace ENOMEM prevents later hooks from running.
    An environment EPERM can occur earlier, but cannot move pid cursors. *)
Example closed_children_early_eperm_keeps_state : forall st',
  clone_ns 17 closed_children_model launch_children_ctx closed_children_state 141
    (CnErr EPERM st') -> st' = closed_children_state.
Proof.
  intros st' H. unfold clone_ns in H. rewrite closed_children_table in H.
  destruct H as [Ho | (_ & en & s & _ & Hstate & Ho)]; [discriminate Ho|].
  injection Ho as -> ->.
  destruct Hstate as [H | [Hmove _]]; [exact H|].
  vm_compute in Hmove. discriminate Hmove.
Qed.

Print Assumptions closed_children_early_eperm_keeps_state.
