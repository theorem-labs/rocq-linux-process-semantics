(** * LinuxProcessSem.Checks.NsCloneRefusers — the namespace extension keeps the host's clone refusers

    Not part of the trusted specification: QA on
    [State.procst_clone_refusers] under [Ns.Spec.ns_ext], in the sense of
    [Checks.Examples]'s header, under its first reason.

    In the namespace world a clone reads the host's clone refusers
    ([Kernel.Fork.clone_refusable]) from the caller's model, and the
    caller's model is whatever the namespace arms left there.  So the
    multi-process preservation of [Checks.ProcsCloneRefusers] needs, for
    [ns_ext], that no answer of [Ns.Spec.ns_spec] changes the field:
    [ns_spec_clone_refusers_kept], one lemma per arm of [Ns.Spec.ns_table],
    and the released answer through
    [Checks.ProcsChildPidsFrame.syscall_spec_clone_refusers_kept].  An arm
    that rebuilt the task's [ProcState] without the field would fail here.
    [ns_ext_keeps_clone_refusers] is the obligation
    [Checks.ProcsCloneRefusers.ext_keeps_clone_refusers];
    [pxruns_clone_refusers_reachable] and its [ns_ext] form say that every
    entry of every state a run of [Procs.pstep_x_cfg] reaches carries the
    launch's value. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import
  Tables Ext Arm Task Clone Files UserArms MountArms Net FsOps Pass Spec.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsChildPidsFrame ProcsCloneRefusers.
Import ListNotations.

(** An outcome keeps the field of the model it was computed from. *)
Definition keeps (m : Model) (o : ext_outcome) : Prop :=
  match o with
  | EOk _ m' _ _ _ => m_clone_refusers m' = m_clone_refusers m
  | EUnmodeled => True
  end.

(** Every outcome of an arm keeps the field. *)
Definition arm_keeps (a : NsArm) : Prop :=
  forall i m ctx st o, a i m ctx st o -> keeps m o.

Lemma keeps_released : forall i m ctx st o, released i m ctx st o -> keeps m o.
Proof.
  intros i m ctx st [eff m' ctx' st' evs|] H; cbn [keeps]; [|exact I].
  destruct H as (_ & _ & H). exact (syscall_spec_clone_refusers_kept _ _ _ _ _ H).
Qed.

Lemma released_keeps : arm_keeps released.
Proof. intros i m ctx st o H. exact (keeps_released _ _ _ _ _ H). Qed.

(** The injected refusal keeps the caller's model. *)
Lemma with_injected_keeps : forall P a, arm_keeps a -> arm_keeps (with_injected P a).
Proof.
  intros P a Ha i m ctx st o [H | (ok & _ & H)].
  - exact (Ha _ _ _ _ _ H).
  - unfold injected_after in H. destruct ok as [eff m' ctx' st' evs|]; [|destruct H].
    destruct H as (e & _ & ->). reflexivity.
Qed.

(** An outcome an arm names through an equation keeps the field when the
    term it equals does: so the outcome's own computation is what the
    tactics below open. *)
Lemma keeps_some : forall m t o,
  t = Some o -> match t with Some o' => keeps m o' | None => True end -> keeps m o.
Proof. intros m t o -> H. exact H. Qed.

Lemma keeps_eq : forall m t o, t = o -> keeps m t -> keeps m o.
Proof. intros m t o -> H. exact H. Qed.

(** The function at the head of an application. *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(** Open the innermost stuck [match] of the goal: a scrutinee that computes
    an outcome (its type mentions [ext_outcome]) has its function unfolded,
    any other scrutinee is split into its cases.  A scrutinee that itself
    holds a [match] fails, so [context] moves on to an inner one. *)
Ltac open_scrut x :=
  lazymatch x with
  | context [match _ with _ => _ end] => fail
  | _ =>
      let T := type of x in
      first
        [ lazymatch T with context [ext_outcome] => idtac end;
          let h := head_of x in is_const h; unfold h
        | destruct x ]
  end.

(** Take an arm's hypothesis apart down to the outcome it fixes. *)
Ltac keeps_hyps :=
  repeat match goal with
  | H : released _ _ _ _ ?o |- keeps _ ?o => exact (keeps_released _ _ _ _ _ H)
  | H : False |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : ?o = _ |- keeps _ ?o => is_var o; subst o
  | H : _ = ?o |- keeps _ ?o => is_var o; subst o
  | H : ?t = Some ?o |- keeps ?m ?o => is_var o; refine (keeps_some m t o H _); clear H
  | H : ?T |- keeps _ ?o =>
      match T with context [o] => progress (cbv beta iota zeta in H) end
  | H : context [match ?x with _ => _ end] |- keeps _ ?o =>
      match type of H with context [o] =>
        first [ is_var x; destruct x | destruct x eqn:? ]
      end
  | H : ?T |- keeps _ ?o =>
      match T with context [o] => progress hnf in H end
  end.

(** Compute the outcome the goal names: every model an arm returns is the
    caller's, a [with_fds] or [with_setsid_succeeded] of it (both carry the
    field by conversion), or the released answer's. *)
Ltac keeps_goal :=
  repeat first
    [ match goal with |- True => exact I end
    | match goal with |- m_clone_refusers _ = m_clone_refusers _ => reflexivity end
    | match goal with
      | H : released _ _ _ _ ?o |- keeps _ ?o => exact (keeps_released _ _ _ _ _ H)
      | H : released _ ?m _ _ (EOk _ ?m' _ _ _)
        |- m_clone_refusers ?m' = m_clone_refusers ?m =>
          exact (keeps_released _ _ _ _ _ H)
      | H : ?t = Some (EOk ?e ?m0 ?c ?s ?v)
        |- m_clone_refusers ?m0 = m_clone_refusers ?m =>
          refine (keeps_some m t (EOk e m0 c s v) H _); clear H
      | H : ?t = EOk ?e ?m0 ?c ?s ?v
        |- m_clone_refusers ?m0 = m_clone_refusers ?m =>
          refine (keeps_eq m t (EOk e m0 c s v) H _); clear H
      end
    | progress cbn [keeps]
    | progress (cbv beta iota zeta)
    | match goal with |- keeps _ _ => unfold keeps end
    | match goal with |- context [match ?x with _ => _ end] => open_scrut x end ].

Ltac arm_keeps_tac :=
  first
    [ apply released_keeps
    | apply with_injected_keeps; arm_keeps_tac
    | let i := fresh "i" in let m := fresh "m" in let ctx := fresh "ctx" in
      let st := fresh "st" in let o := fresh "o" in let H := fresh "H" in
      intros i m ctx st o H; hnf in H; keeps_hyps; keeps_goal ].

(** One lemma per arm, each closed by its own [Qed]: the kernel checks
    each arm's proof against that arm's own statement.  Checked inside one
    [Forall] proof over a whole table, the same proofs took the kernel
    past 16 GiB on [net_arms]. *)
Lemma capget_arm_keeps : arm_keeps capget_arm.
Proof. arm_keeps_tac. Qed.

Lemma capset_arm_keeps : arm_keeps capset_arm.
Proof. arm_keeps_tac. Qed.

Lemma setsid_arm_keeps : arm_keeps setsid_arm.
Proof. arm_keeps_tac. Qed.

Lemma uname_arm_keeps : arm_keeps uname_arm.
Proof. arm_keeps_tac. Qed.

Lemma sethostname_arm_keeps : arm_keeps sethostname_arm.
Proof. arm_keeps_tac. Qed.

Lemma setdomainname_arm_keeps : arm_keeps setdomainname_arm.
Proof. arm_keeps_tac. Qed.

Lemma umask_arm_keeps : arm_keeps umask_arm.
Proof. arm_keeps_tac. Qed.

Lemma prctl_arm_keeps : arm_keeps prctl_arm.
Proof. arm_keeps_tac. Qed.

Lemma getpid_arm_keeps : arm_keeps getpid_arm.
Proof. arm_keeps_tac. Qed.

Lemma getcwd_arm_keeps : arm_keeps getcwd_arm.
Proof. arm_keeps_tac. Qed.

Lemma fcntl_arm_keeps : arm_keeps fcntl_arm.
Proof. arm_keeps_tac. Qed.

Lemma statfs_arm_keeps : arm_keeps statfs_arm.
Proof. arm_keeps_tac. Qed.

Lemma fstatfs_arm_keeps : arm_keeps fstatfs_arm.
Proof. arm_keeps_tac. Qed.

Lemma faccessat_arm_keeps : arm_keeps faccessat_arm.
Proof. arm_keeps_tac. Qed.

Lemma chdir_arm_keeps : arm_keeps chdir_arm.
Proof. arm_keeps_tac. Qed.

Lemma fchdir_arm_keeps : arm_keeps fchdir_arm.
Proof. arm_keeps_tac. Qed.

Lemma openat_arm_keeps : arm_keeps openat_arm.
Proof. arm_keeps_tac. Qed.

Lemma close_arm_keeps : arm_keeps close_arm.
Proof. arm_keeps_tac. Qed.

Lemma getdents64_arm_keeps : arm_keeps getdents64_arm.
Proof. arm_keeps_tac. Qed.

Lemma readlinkat_arm_keeps : arm_keeps readlinkat_arm.
Proof. arm_keeps_tac. Qed.

Lemma newfstatat_arm_keeps : arm_keeps newfstatat_arm.
Proof. arm_keeps_tac. Qed.

Lemma fstat_arm_keeps : arm_keeps fstat_arm.
Proof. arm_keeps_tac. Qed.

Lemma openat2_arm_keeps : arm_keeps openat2_arm.
Proof. arm_keeps_tac. Qed.

Lemma mkdirat_arm_keeps : arm_keeps mkdirat_arm.
Proof. arm_keeps_tac. Qed.

Lemma unlinkat_arm_keeps : arm_keeps unlinkat_arm.
Proof. arm_keeps_tac. Qed.

Lemma symlinkat_arm_keeps : arm_keeps symlinkat_arm.
Proof. arm_keeps_tac. Qed.

Lemma fchmod_arm_keeps : arm_keeps fchmod_arm.
Proof. arm_keeps_tac. Qed.

Lemma read_arm_keeps : arm_keeps read_arm.
Proof. arm_keeps_tac. Qed.

Lemma write_arm_keeps : arm_keeps write_arm.
Proof. arm_keeps_tac. Qed.

Lemma unshare_arm_keeps : arm_keeps unshare_arm.
Proof. arm_keeps_tac. Qed.

Lemma umount2_arm_keeps : arm_keeps umount2_arm.
Proof. arm_keeps_tac. Qed.

Lemma mount_arm_keeps : arm_keeps mount_arm.
Proof. arm_keeps_tac. Qed.

Lemma pivot_root_arm_keeps : arm_keeps pivot_root_arm.
Proof. arm_keeps_tac. Qed.

Lemma mount_setattr_arm_keeps : arm_keeps mount_setattr_arm.
Proof. arm_keeps_tac. Qed.

Lemma ioctl_arm_keeps : arm_keeps ioctl_arm.
Proof. arm_keeps_tac. Qed.

Lemma socket_arm_keeps : arm_keeps socket_arm.
Proof. arm_keeps_tac. Qed.

Lemma bind_arm_keeps : arm_keeps bind_arm.
Proof. arm_keeps_tac. Qed.

Lemma sendto_arm_keeps : arm_keeps sendto_arm.
Proof. arm_keeps_tac. Qed.

Lemma recvfrom_arm_keeps : arm_keeps recvfrom_arm.
Proof. arm_keeps_tac. Qed.

Lemma task_arms_keep : Forall (fun na => arm_keeps (snd na)) task_arms.
Proof.
  unfold task_arms.
  constructor; [exact capget_arm_keeps |].
  constructor; [exact capset_arm_keeps |].
  constructor; [exact setsid_arm_keeps |].
  constructor; [exact uname_arm_keeps |].
  constructor; [exact sethostname_arm_keeps |].
  constructor; [exact setdomainname_arm_keeps |].
  constructor; [exact umask_arm_keeps |].
  constructor; [exact prctl_arm_keeps |].
  constructor; [exact getpid_arm_keeps |].
  constructor; [exact getpid_arm_keeps |].
  constructor.
Qed.

Lemma file_arms_keep : Forall (fun na => arm_keeps (snd na)) file_arms.
Proof.
  unfold file_arms.
  constructor; [exact (with_injected_keeps _ _ getcwd_arm_keeps) |].
  constructor; [exact fcntl_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ statfs_arm_keeps) |].
  constructor; [exact fstatfs_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ faccessat_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ chdir_arm_keeps) |].
  constructor; [exact fchdir_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ openat_arm_keeps) |].
  constructor; [exact close_arm_keeps |].
  constructor; [exact getdents64_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ readlinkat_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ newfstatat_arm_keeps) |].
  constructor; [exact fstat_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ openat2_arm_keeps) |].
  constructor.
Qed.

Lemma fsops_arms_keep : Forall (fun na => arm_keeps (snd na)) fsops_arms.
Proof.
  unfold fsops_arms.
  constructor; [exact (with_injected_keeps _ _ mkdirat_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ unlinkat_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ symlinkat_arm_keeps) |].
  constructor; [exact fchmod_arm_keeps |].
  constructor; [exact read_arm_keeps |].
  constructor; [exact write_arm_keeps |].
  constructor.
Qed.

Lemma user_arms_keep : Forall (fun na => arm_keeps (snd na)) user_arms.
Proof.
  unfold user_arms.
  constructor; [exact unshare_arm_keeps |].
  constructor.
Qed.

Lemma mount_arms_keep : Forall (fun na => arm_keeps (snd na)) mount_arms.
Proof.
  unfold mount_arms.
  constructor; [exact (with_injected_keeps _ _ umount2_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ mount_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ pivot_root_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ mount_setattr_arm_keeps) |].
  constructor.
Qed.

Lemma net_arms_keep : Forall (fun na => arm_keeps (snd na)) net_arms.
Proof.
  unfold net_arms.
  constructor; [exact ioctl_arm_keeps |].
  constructor; [exact (with_injected_keeps _ _ socket_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ bind_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ sendto_arm_keeps) |].
  constructor; [exact (with_injected_keeps _ _ recvfrom_arm_keeps) |].
  constructor.
Qed.

Lemma pass_arms_keep : Forall (fun na => arm_keeps (snd na)) pass_arms.
Proof.
  apply Forall_forall. intros [n a] Hin. cbn [snd].
  intros i m ctx st o H.
  apply (keeps_released i m ctx st o).
  exact (proj1 (pass_arms_released n a Hin i m ctx st o) H).
Qed.

Lemma Forall_app_intro : forall (A : Type) (P : A -> Prop) l1 l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 H1 H2. induction H1 as [|x l Hx _ IH]; [exact H2|].
  cbn [app]. constructor; [exact Hx | exact IH].
Qed.

(** Part by part, each part named: a search with [Forall_app] over the
    unfolded table did not end within 16 GiB. *)
Lemma ns_table_keeps : Forall (fun na => arm_keeps (snd na)) ns_table.
Proof.
  unfold ns_table.
  exact (Forall_app_intro _ _ _ _ task_arms_keep
          (Forall_app_intro _ _ _ _ file_arms_keep
          (Forall_app_intro _ _ _ _ fsops_arms_keep
          (Forall_app_intro _ _ _ _ user_arms_keep
          (Forall_app_intro _ _ _ _ mount_arms_keep
          (Forall_app_intro _ _ _ _ net_arms_keep pass_arms_keep)))))).
Qed.

Lemma lookup_ns_arm_keeps : forall t n a,
  Forall (fun na => arm_keeps (snd na)) t -> lookup_ns_arm t n = Some a -> arm_keeps a.
Proof.
  induction t as [|[k a0] t IH]; intros n a Hall H; cbn [lookup_ns_arm] in H;
    [discriminate H|].
  apply Forall_cons_iff in Hall as [Ha0 Hrest].
  destruct (Z.eqb k n).
  - injection H as <-. exact Ha0.
  - exact (IH n a Hrest H).
Qed.

(** EVERY ANSWER OF THE NAMESPACE EXTENSION KEEPS THE FIELD: the released
    answer in the released world, and every arm of [Ns.Spec.ns_table]. *)
Theorem ns_spec_clone_refusers_kept : forall i m ctx st o,
  ns_spec i m ctx st o -> keeps m o.
Proof.
  intros i m ctx st o H. unfold ns_spec in H.
  destruct (flat_view ctx st).
  - exact (keeps_released _ _ _ _ _ H).
  - destruct (lookup_ns_arm ns_table (ns_sysno i)) as [a|] eqn:Hl.
    + exact (lookup_ns_arm_keeps _ _ _ ns_table_keeps Hl _ _ _ _ _ H).
    + subst o. exact I.
Qed.

Corollary ns_ext_keeps_clone_refusers : ext_keeps_clone_refusers ns_ext.
Proof.
  intros i m ctx st eff m' ctx' st' evs H.
  exact (ns_spec_clone_refusers_kept _ _ _ _ _ H).
Qed.

(* =========================================================================
   Runs of the core under an extension
   ========================================================================= *)

(** Any run of the core under an extension. *)
Inductive pxruns (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment)
    (cfg : SpuriousCfg) : pconfig -> pconfig -> Prop :=
| pxruns_refl : forall P, pxruns ext cenv segs cfg P P
| pxruns_step : forall P evs P' P'',
    pstep_x_cfg ext cenv segs cfg P evs (PNext P') ->
    pxruns ext cenv segs cfg P' P'' -> pxruns ext cenv segs cfg P P''.

Theorem pxruns_clone_refusers_reachable : forall r ext cenv segs cfg P Q,
  ext_keeps_clone_refusers ext ->
  refusers_all r P -> pxruns ext cenv segs cfg P Q -> refusers_all r Q.
Proof.
  intros r ext cenv segs cfg P Q Hext Hall Hr.
  induction Hr as [P0 | P0 evs P1 P2 Hs _ IH]; [exact Hall|].
  apply IH. exact (pstep_x_cfg_preserves_clone_refusers _ _ _ _ _ _ _ _ Hext Hall Hs).
Qed.

(** Under the namespace extension, from a launch with any shared state:
    every entry of every reachable state carries the launch's value. *)
Corollary ns_pxruns_clone_refusers_reachable : forall cenv segs cfg c sh Q,
  pxruns ns_ext cenv segs cfg
    (mkPCfg (pcfg_procs (one_proc c)) (pcfg_root (one_proc c)) sh) Q ->
  refusers_all (m_clone_refusers (cfg_model c)) Q.
Proof.
  intros cenv segs cfg c sh Q Hr.
  refine (pxruns_clone_refusers_reachable _ _ _ _ _ _ _ ns_ext_keeps_clone_refusers
            _ Hr).
  exact (refusers_all_one_proc c).
Qed.

Print Assumptions ns_spec_clone_refusers_kept.
Print Assumptions ns_pxruns_clone_refusers_reachable.
