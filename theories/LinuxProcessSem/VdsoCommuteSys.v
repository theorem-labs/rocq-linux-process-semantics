(** * LinuxProcessSem.VdsoCommuteSys — the frame at the dispatcher and the step relation

    [VdsoCommute.v] frames the combinators, [VdsoCommuteArms.v] frames each
    specification.  This file closes the two statements a consumer wants:

    - [syscall_spec_vdso_commutes], at [Specs.syscall_spec].  NO HYPOTHESIS:
      the syscall table has no vDSO arm, so the expensive half of the work is
      premise-free.

    - [sstep_with_vdso] and [star_with_vdso], at [Run.sstep] and [Run.star].
      These DO carry a hypothesis, and they have to.  [Run.sstep]'s vDSO arms
      bump the count ([State.with_vdso_bump]) and read the draw
      ([Run.vdso_post], through [vdr_draw] and [vdr_calls]), so at
      a pc that is an exported vDSO entry the commutation is FALSE, not
      merely unproved.  The hypothesis is per state —
      [vdso_entry_fn segs (ms_pc ms) = None] — so a caller discharges it node
      by node along a plan.  [vdso_entry_fn_none_of_no_text] is the per-tree
      corollary, for a run whose segments carry no vDSO text at all.

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType Vdso State Monad Specs RiscvSemantics Run
  VdsoCommute VdsoCommuteArms.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   The dispatcher
   ========================================================================= *)

(** The arm a lookup finds is an arm of the table.  Needed because the walk
    is a [Forall] over the table and the dispatcher reaches an arm through
    [Sys.Dispatch.lookup_arm]. *)
Lemma lookup_arm_In : forall t n a, lookup_arm t n = Some a -> In a t.
Proof.
  induction t as [|b r IH]; intros n a H; cbn in H; [discriminate|].
  destruct (Z.eqb (sa_no b) n) eqn:E.
  - injection H as <-. left. reflexivity.
  - right. exact (IH n a H).
Qed.

(** A table whose every arm is framed dispatches to a framed specification.
    The fail-closed arm is [unmodeled], which is framed outright. *)
Lemma vc_dispatch : forall t,
  Forall (fun a => vdso_commutes (sa_spec a)) t -> vdso_commutes (dispatch t).
Proof.
  intros t Ht v i m o H. unfold dispatch in *.
  destruct (lookup_arm t (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - exact (proj1 (Forall_forall _ t) Ht a (lookup_arm_In _ _ _ E) v i m o H).
  - exact (vc_unmodeled v i m o H).
Qed.

(** An arm of the table is a specification applied to arguments read off the
    input, so its lemma is the one for that specification. *)
Ltac vc_arm L := intros ? ? ? ? ?; eapply L; eassumption.

(** THE WALK, assembled.  93 arms, in [Sys.SyscallTable.spec_table]'s order.
    A new arm with no lemma in [VdsoCommuteArms.v] fails here. *)
Lemma spec_table_vdso_commutes :
  Forall (fun a => vdso_commutes (sa_spec a)) spec_table.
Proof.
  unfold spec_table.
  repeat apply Forall_cons.
  - vc_arm vc_getcwd_spec.                (* 17  getcwd *)
  - vc_arm vc_eventfd2_spec.              (* 19  eventfd2 *)
  - vc_arm vc_epoll_create1_spec.         (* 20  epoll_create1 *)
  - vc_arm vc_epoll_ctl_spec.             (* 21  epoll_ctl *)
  - vc_arm vc_epoll_pwait_spec.           (* 22  epoll_pwait *)
  - vc_arm vc_dup_spec.                   (* 23  dup *)
  - vc_arm vc_dup3_spec.                  (* 24  dup3 *)
  - vc_arm vc_fcntl_spec.                 (* 25  fcntl *)
  - vc_arm vc_ioctl_spec.                 (* 29  ioctl *)
  - vc_arm vc_flock_spec.                 (* 32  flock *)
  - vc_arm vc_unlinkat_spec.              (* 35  unlinkat *)
  - vc_arm vc_ftruncate_spec.             (* 46  ftruncate *)
  - vc_arm vc_faccessat_spec.             (* 48  faccessat *)
  - vc_arm vc_openat_spec.                (* 56  openat *)
  - vc_arm vc_close_spec.                 (* 57  close *)
  - vc_arm vc_pipe2_spec.                 (* 59  pipe2 *)
  - vc_arm vc_getdents64_spec.            (* 61  getdents64 *)
  - vc_arm vc_lseek_spec.                 (* 62  lseek *)
  - vc_arm vc_read_spec.                  (* 63  read *)
  - vc_arm vc_write_spec.                 (* 64  write *)
  - vc_arm vc_readv_spec.                 (* 65  readv *)
  - vc_arm vc_writev_spec.                (* 66  writev *)
  - vc_arm vc_pread64_spec.               (* 67  pread64 *)
  - vc_arm vc_pwrite64_spec.              (* 68  pwrite64 *)
  - vc_arm vc_pselect6_spec.              (* 72  pselect6 *)
  - vc_arm vc_ppoll_spec.                 (* 73  ppoll *)
  - vc_arm vc_readlinkat_spec.            (* 78  readlinkat *)
  - vc_arm vc_newfstatat_spec.            (* 79  newfstatat *)
  - vc_arm vc_fstat_spec.                 (* 80  fstat *)
  - vc_arm vc_fsync_spec.                 (* 82  fsync *)
  - vc_arm vc_fsync_spec.                 (* 83  fdatasync *)
  - vc_arm vc_timerfd_create_spec.        (* 85  timerfd_create *)
  - vc_arm vc_exit_spec.                  (* 93  exit *)
  - vc_arm vc_exit_spec.                  (* 94  exit_group *)
  - vc_arm vc_set_tid_address_spec.       (* 96  set_tid_address *)
  - vc_arm vc_futex_spec.                 (* 98  futex *)
  - vc_arm vc_set_robust_list_spec.       (* 99  set_robust_list *)
  - vc_arm vc_nanosleep_spec.             (* 101 nanosleep *)
  - vc_arm vc_clock_gettime_spec.         (* 113 clock_gettime *)
  - vc_arm vc_clock_getres_spec.          (* 114 clock_getres *)
  - vc_arm vc_sched_setscheduler_spec.    (* 119 sched_setscheduler *)
  - vc_arm vc_sched_getaffinity_spec.     (* 123 sched_getaffinity *)
  - vc_arm vc_sched_yield_spec.           (* 124 sched_yield *)
  - vc_arm vc_tkill_spec.                 (* 130 tkill *)
  - vc_arm vc_tgkill_spec.                (* 131 tgkill *)
  - vc_arm vc_sigaltstack_spec.           (* 132 sigaltstack *)
  - vc_arm vc_rt_sigaction_spec.          (* 134 rt_sigaction *)
  - vc_arm vc_rt_sigprocmask_spec.        (* 135 rt_sigprocmask *)
  - vc_arm vc_setid_spec.                 (* 144 setgid *)
  - vc_arm vc_setid_spec.                 (* 146 setuid *)
  - vc_arm vc_setresid_spec.              (* 147 setresuid *)
  - vc_arm vc_setresid_spec.              (* 149 setresgid *)
  - vc_arm vc_setsid_spec.                (* 157 setsid *)
  - vc_arm vc_getgroups_spec.             (* 158 getgroups *)
  - vc_arm vc_setgroups_spec.             (* 159 setgroups *)
  - vc_arm vc_uname_spec.                 (* 160 uname *)
  - vc_arm vc_prctl_spec.                 (* 167 prctl *)
  - vc_arm vc_gettimeofday_spec.          (* 169 gettimeofday *)
  - vc_arm vc_getpid_spec.                (* 172 getpid *)
  - vc_arm vc_getid_spec.                 (* 174 getuid *)
  - vc_arm vc_getid_spec.                 (* 175 geteuid *)
  - vc_arm vc_getid_spec.                 (* 176 getgid *)
  - vc_arm vc_getid_spec.                 (* 177 getegid *)
  - vc_arm vc_gettid_spec.                (* 178 gettid *)
  - vc_arm vc_socket_spec.                (* 198 socket *)
  - vc_arm vc_socketpair_spec.            (* 199 socketpair *)
  - vc_arm vc_bind_spec.                  (* 200 bind *)
  - vc_arm vc_listen_spec.                (* 201 listen *)
  - vc_arm vc_accept4_spec.               (* 202 accept *)
  - vc_arm vc_connect_spec.               (* 203 connect *)
  - vc_arm vc_getsockname_spec.           (* 204 getsockname *)
  - vc_arm vc_getpeername_spec.           (* 205 getpeername *)
  - vc_arm vc_sendto_spec.                (* 206 sendto *)
  - vc_arm vc_recvfrom_spec.              (* 207 recvfrom *)
  - vc_arm vc_setsockopt_spec.            (* 208 setsockopt *)
  - vc_arm vc_getsockopt_spec.            (* 209 getsockopt *)
  - vc_arm vc_shutdown_spec.              (* 210 shutdown *)
  - vc_arm vc_sendmsg_spec.               (* 211 sendmsg *)
  - vc_arm vc_recvmsg_spec.               (* 212 recvmsg *)
  - vc_arm vc_brk_spec.                   (* 214 brk *)
  - vc_arm vc_munmap_spec.                (* 215 munmap *)
  - vc_arm vc_mremap_spec.                (* 216 mremap *)
  - vc_arm vc_clone_spec.                 (* 220 clone *)
  - vc_arm vc_mmap_spec.                  (* 222 mmap *)
  - vc_arm vc_mprotect_spec.              (* 226 mprotect *)
  - vc_arm vc_madvise_spec.               (* 233 madvise *)
  - vc_arm vc_accept4_spec.               (* 242 accept4 *)
  - vc_arm vc_wait4_spec.                 (* 260 wait4 *)
  - vc_arm vc_prlimit64_spec.             (* 261 prlimit64 *)
  - vc_arm vc_getrandom_spec.             (* 278 getrandom *)
  - vc_arm vc_pwritev2_spec.              (* 287 pwritev2 *)
  - vc_arm vc_clone3_spec.                (* 435 clone3 *)
  - vc_arm vc_faccessat2_spec.            (* 439 faccessat2 *)
  - apply Forall_nil.
Qed.

(** THE SYSCALL-LAYER STATEMENT.  No hypothesis. *)
Theorem syscall_spec_vdso_commutes : vdso_commutes syscall_spec.
Proof. apply vc_dispatch, spec_table_vdso_commutes. Qed.

Corollary syscall_spec_with_vdso : forall v i m o,
  syscall_spec i m o -> syscall_spec i (with_vdso v m) (outcome_with_vdso v o).
Proof. apply syscall_spec_vdso_commutes. Qed.

Corollary syscall_spec_with_vdso_inv : forall v i m o,
  syscall_spec i (with_vdso v m) o ->
  syscall_spec i m (outcome_with_vdso (m_vdso m) o).
Proof. apply (vdso_commutes_inv _ syscall_spec_vdso_commutes). Qed.

Corollary syscall_spec_with_vdso_iff : forall v i m x m' evs,
  m_vdso m' = m_vdso m ->
  (syscall_spec i (with_vdso v m) (Ok x (with_vdso v m') evs)
   <-> syscall_spec i m (Ok x m' evs)).
Proof. apply (vdso_commutes_iff_ok _ syscall_spec_vdso_commutes). Qed.

(* =========================================================================
   The model frames the step relation needs besides the syscall layer
   ========================================================================= *)

(** Materialization reads the backing ledgers and the limit, none of which
    the wrapper touches, and writes through [State.with_vm_backing], which
    commutes with it. *)
Lemma materialize_model_accesses_with_vdso : forall v m acc,
  materialize_model_accesses (with_vdso v m) acc
  = option_map (with_vdso v) (materialize_model_accesses m acc).
Proof.
  intros v m acc. unfold materialize_model_accesses.
  change (m_vm_lazy (with_vdso v m)) with (m_vm_lazy m).
  change (m_vm_materialized (with_vdso v m)) with (m_vm_materialized m).
  change (vm_backing_used (with_vdso v m)) with (vm_backing_used m).
  change (m_vmmaps (with_vdso v m)) with (m_vmmaps m).
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
              (vm_backing_used m) (vm_limit (m_vmmaps m)) acc); reflexivity.
Qed.

(** The accounted instruction step reads the model only through
    materialization. *)
Lemma mi_account_step_with_vdso : forall segs v ms m,
  mi_account_step segs ms (with_vdso v m)
  = match mi_account_step segs ms m with
    | MachineOk (ms', m') => MachineOk (ms', with_vdso v m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros segs v ms m. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try reflexivity.
  rewrite materialize_model_accesses_with_vdso.
  destruct (materialize_model_accesses m (@accessed_ranges _ report));
    reflexivity.
Qed.

(* =========================================================================
   The step relation
   ========================================================================= *)

(** Carry the wrapper through a configuration and through a transition. *)
Definition cfg_with_vdso (v : VdsoRun) (c : config) : config :=
  mkCfg (cfg_ms c) (with_vdso v (cfg_model c)).

Definition step_to_with_vdso (v : VdsoRun) (st : step_to) : step_to :=
  match st with
  | SNext c => SNext (cfg_with_vdso v c)
  | SError  => SError
  end.

(** THE STEP-LAYER STATEMENT, per state.  [Run.sstep] has eleven arms;
    three are ruled out by the premise and the other eight are proved.

    THE HYPOTHESIS IS NOT A CONVENIENCE.  At an exported vDSO entry the
    conclusion is FALSE: [Run.sstep_vdso_call] leaves [with_vdso_bump
    model''], so a step from the wrapped model leaves the BUMPED wrapper and
    not the wrapper, and [Run.vdso_post] reads the draw itself, so even the
    machine state differs.  The three vDSO arms all require
    [vdso_entry_fn … = Some fn]; this premise rules out exactly those
    three, and it rules out nothing else: the only other arm that mentions
    [vdso_entry_fn] is [Run.sstep_instr_unmodeled], whose own premise is
    [= None] and which is proved rather than excluded. *)
Theorem sstep_with_vdso : forall segs v ms model evs st,
  vdso_entry_fn segs (ms_pc ms) = None ->
  sstep segs (mkCfg ms model) evs st ->
  sstep segs (mkCfg ms (with_vdso v model)) evs (step_to_with_vdso v st).
Proof.
  intros segs v ms model evs st Hnv Hstep.
  remember (mkCfg ms model) as c eqn:Hc.
  destruct Hstep; injection Hc as <- <-.
  - (* sstep_instr *)
    apply sstep_instr; [exact H | exact H0 |].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* sstep_instr_fault *)
    apply sstep_instr_fault; [exact H | exact H0 |].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* sstep_instr_unmodeled *)
    apply sstep_instr_unmodeled; [exact H | exact H0 | | exact H2].
    rewrite mi_account_step_with_vdso, H1. reflexivity.
  - (* sstep_vdso_call: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* sstep_vdso_materialization_fault: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* sstep_vdso_unmodeled: excluded *)
    rewrite Hnv in H2. discriminate H2.
  - (* sstep_syscall *)
    eapply sstep_syscall with (model' := with_vdso v model')
                              (model'' := with_vdso v model'').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
    + rewrite materialize_model_accesses_with_vdso, H3. reflexivity.
  - (* sstep_syscall_materialization_fault *)
    eapply sstep_syscall_materialization_fault
      with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
    + rewrite materialize_model_accesses_with_vdso, H3. reflexivity.
  - (* sstep_exit *)
    eapply sstep_exit with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
    + exact H3.
  - (* sstep_killed *)
    eapply sstep_killed with (model' := with_vdso v model').
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
    + exact H2.
  - (* sstep_syscall_unmodeled *)
    eapply sstep_syscall_unmodeled.
    + exact H.
    + exact H0.
    + exact (syscall_spec_with_vdso v _ _ _ H1).
Qed.

(** The same on a configuration rather than its two halves. *)
Corollary sstep_cfg_with_vdso : forall segs v c evs st,
  vdso_entry_fn segs (ms_pc (cfg_ms c)) = None ->
  sstep segs c evs st ->
  sstep segs (cfg_with_vdso v c) evs (step_to_with_vdso v st).
Proof. intros segs v [ms model] evs st. apply sstep_with_vdso. Qed.

(** THE INVERSE, which is the direction a [realizes]-style consumer needs:
    [Common.ShapeAlg]'s [node_ok] quantifies over EVERY successor of the
    configuration, so transporting it across the wrapper asks what a step
    of the WRAPPED configuration came from.  Free, by the same two
    identities as [VdsoCommute.vdso_commutes_inv]: the draw put back is the
    bare model's own. *)
Theorem sstep_with_vdso_inv : forall segs v ms model evs st,
  vdso_entry_fn segs (ms_pc ms) = None ->
  sstep segs (mkCfg ms (with_vdso v model)) evs st ->
  sstep segs (mkCfg ms model) evs (step_to_with_vdso (m_vdso model) st).
Proof.
  intros segs v ms model evs st Hnv Hstep.
  pose proof (sstep_with_vdso segs (m_vdso model) ms (with_vdso v model)
                evs st Hnv Hstep) as H.
  rewrite with_vdso_idem, with_vdso_same in H. exact H.
Qed.

Corollary sstep_cfg_with_vdso_inv : forall segs v c evs st,
  vdso_entry_fn segs (ms_pc (cfg_ms c)) = None ->
  sstep segs (mkCfg (cfg_ms c) (with_vdso v (cfg_model c))) evs st ->
  sstep segs c evs (step_to_with_vdso (m_vdso (cfg_model c)) st).
Proof.
  intros segs v [ms model] evs st Hnv Hstep.
  exact (sstep_with_vdso_inv segs v ms model evs st Hnv Hstep).
Qed.

(** MANY STEPS.  The premise is carried by an INVARIANT the caller supplies,
    which is how a plan discharges it node by node: [P] is what the caller
    knows about the configurations its plan visits, and the two premises say
    that [P] keeps the pc away from a vDSO entry and survives a step.  A
    caller that knows its plan's pcs outright instantiates [P] with exactly
    that.

    NOTE WHAT THE SECOND PREMISE ASKS.  [P] must survive EVERY [sstep]
    successor, not only the one this star takes.  That is the right shape
    for a [node_ok]-style consumer, whose own clause already quantifies
    over every successor, and it is a real obligation for a caller holding
    one trace: such a caller wants [P] to be a property of the segment list
    and the pc rather than of the trace. *)
Theorem star_with_vdso : forall segs v (P : config -> Prop),
  (forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None) ->
  (forall c evs c', P c -> sstep segs c evs (SNext c') -> P c') ->
  forall c tr c', star segs c tr c' -> P c ->
  star segs (cfg_with_vdso v c) tr (cfg_with_vdso v c').
Proof.
  intros segs v P Hpc Hstep c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hs Hstar IH]; intros HP.
  - apply star_refl.
  - eapply star_step.
    + exact (sstep_cfg_with_vdso segs v c1 evs (SNext c2) (Hpc c1 HP) Hs).
    + exact (IH (Hstep c1 evs c2 HP Hs)).
Qed.

(* =========================================================================
   Discharging the premise
   ========================================================================= *)

(** A run whose segments carry no vDSO text has no exported entry at any pc.
    This is the per-tree corollary, and it is cheap where it applies.

    It does NOT apply to a run whose segment list is [Run.run_segments]:
    that appends [Run.vdso_segments], and the pair is empty only for a
    launch [Run.vdso_segments] declines (Run.v:290-295), which Run.v:285-289
    says Linux does not make.  A consumer over [run_segments] wants
    [vdso_entry_fn_none_below_base] instead. *)
Lemma vdso_entry_fn_none_of_no_text : forall segs pc,
  vdso_text_seg segs = None -> vdso_entry_fn segs pc = None.
Proof.
  intros segs pc H. unfold vdso_entry_fn, vdso_image. rewrite H. reflexivity.
Qed.

(** And the same when the image's bytes are not one this development
    measured: an unmeasured kernel exports no entry. *)
Lemma vdso_entry_fn_none_of_unmeasured : forall segs pc seg,
  vdso_text_seg segs = Some seg ->
  vdso_image_of_bytes vdso_images (seg_bytes seg) = None ->
  vdso_entry_fn segs pc = None.
Proof.
  intros segs pc seg Hseg Him.
  unfold vdso_entry_fn, vdso_image. rewrite Hseg, Him. reflexivity.
Qed.

(** A pc BELOW the vDSO text base is not an entry.  This is the form a plan
    discharges by arithmetic: the entry test is an interval test against the
    published base, so a pc below the base fails it whatever the image is. *)
Lemma vdso_entry_fn_none_below_base : forall segs pc seg im,
  vdso_text_seg segs = Some seg ->
  vdso_image_of_bytes vdso_images (seg_bytes seg) = Some im ->
  (bv_unsigned pc < Z.of_N (seg_base seg))%Z ->
  vdso_entry_fn segs pc = None.
Proof.
  intros segs pc seg im Hseg Him Hlt.
  unfold vdso_entry_fn, vdso_image. rewrite Hseg, Him.
  replace (Z.leb (Z.of_N (seg_base seg)) (bv_unsigned pc)) with false
    by (symmetry; apply Z.leb_gt; exact Hlt).
  reflexivity.
Qed.
