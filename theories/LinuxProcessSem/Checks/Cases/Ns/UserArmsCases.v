(** * LinuxProcessSem.Checks.Cases.Ns.UserArmsCases — unshare (CLONE_NEWUSER)

    Each example runs [Ns.UserArms.unshare_arm] on a task whose user
    namespace, mounts and credentials the tables hold, and states what the
    arm answers. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm UserArms Spec.
Import ListNotations.
Open Scope Z_scope.

Definition call (flags : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 97) [Z_to_bv 64 flags] (fun _ => None) (fun _ => None).

(** A task with euid and egid [id]. *)
Definition creds (id : Z) : Creds :=
  mkCreds (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id)
          (Z_to_bv 64 id) [].

Definition no_flags : MountFlags := mkMountFlags false false false false.

(** Namespace 1, the initial one, maps every id; its limit and its seal
    are given.  Mount 1 is the root of mount namespace 1; the task's root
    is mount 1, dentry 1, unless [chroot]. *)
Definition full : list IdExtent := [mkExtent 0 0 4294967295].
Definition init_uns (max : Z) (sealed : bool) : UserNs :=
  mkUserNs 1 None 0 0 (Some full) (Some full) true true max sealed.

Definition world (us : list UserNs) : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 no_flags no_flags false false None None] us
            [mkMntNs 1 1 1 false] [] [] [] [] [] [] (ns_env empty_nsstate).

Definition task (user : positive) (root : positive * positive) (caps : CapSets) : NsCtx :=
  mkNsCtx user 1 1 1 [(1%positive, 2)] root root 18 caps 0 [].

Definition nocaps : CapSets := mkCaps 0 0 0 (2 ^ 41 - 1) 0.

(** The new namespace: 2, a child of 1 owned by kuid 1000 with no maps, and
    the task in it with every capability. *)
Example unshare_creates : forall m,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
              (world [init_uns 100 true])
              (ns_ret (Z_to_bv 64 0) (with_creds (creds 1000) m)
                      (in_new_userns (task 1 (1%positive, 1%positive) nocaps) 2)
                      (with_userns (world [init_uns 100 true])
                                   [mkUserNs 2 (Some 1%positive) 1 1000 None None true false
                                             INT_MAX true; init_uns 100 true])).
Proof.
  intros m. rewrite (unshare_arm_newuser _ _ _ _ _ (init_uns 100 true) false);
    [left; vm_compute; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(** The task in the new namespace holds every capability there, none
    inheritable or ambient. *)
Example new_caps :
  cx_caps (in_new_userns (task 1 (1%positive, 1%positive) nocaps) 2)
  = mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0 := eq_refl.

(** An unknown flag bit: EINVAL. *)
Example unshare_bad_flag : forall m o,
  unshare_arm (call (Z.lor CLONE_NEWUSER 1)) m (task 1 (1%positive, 1%positive) nocaps)
              (world [init_uns 100 true]) o
  <-> o = ns_errno EINVAL m (task 1 (1%positive, 1%positive) nocaps) (world [init_uns 100 true]).
Proof. intros m o. vm_compute. tauto. Qed.

(** Other namespace flags decline. *)
Example unshare_newns_declines : forall m o,
  unshare_arm (call CLONE_NEWNS) m (task 1 (1%positive, 1%positive) nocaps)
              (world [init_uns 100 true]) o <-> o = EUnmodeled.
Proof. intros m o. vm_compute. tauto. Qed.

(** A chrooted task (root at dentry 5, not the mount's root): EPERM. *)
Example unshare_chrooted : forall m o,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 5%positive) nocaps)
              (world [init_uns 100 true]) o
  -> o = ns_errno EPERM (with_creds (creds 1000) m) (task 1 (1%positive, 5%positive) nocaps)
                  (world [init_uns 100 true])
     \/ env_refusal o (with_creds (creds 1000) m) (task 1 (1%positive, 5%positive) nocaps)
                    (world [init_uns 100 true]).
Proof.
  intros m o H.
  rewrite (unshare_arm_newuser _ _ _ _ _ (init_uns 100 true) true) in H;
    [| reflexivity | reflexivity | reflexivity].
  destruct H as [H|H]; [left; vm_compute in H; exact H | right; exact H].
Qed.

(** The owner unmapped in the parent: from namespace 2, whose maps are not
    written, EPERM. *)
Definition ns2 : UserNs := mkUserNs 2 (Some 1%positive) 1 1000 None None true false INT_MAX true.

Example unshare_unmapped_owner : forall m o,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 2 (1%positive, 1%positive) nocaps)
              (world [ns2; init_uns 100 true]) o
  -> o = ns_errno EPERM (with_creds (creds 1000) m) (task 2 (1%positive, 1%positive) nocaps)
                  (world [ns2; init_uns 100 true])
     \/ env_refusal o (with_creds (creds 1000) m) (task 2 (1%positive, 1%positive) nocaps)
                    (world [ns2; init_uns 100 true]).
Proof.
  intros m o H.
  rewrite (unshare_arm_newuser _ _ _ _ _ ns2 false) in H; [| reflexivity | reflexivity | reflexivity].
  destruct H as [H|H]; [left; vm_compute in H; exact H | right; exact H].
Qed.

(** [only_or_env] is "this answer, or one of the environment's refusals
    ([env_refusal]: ENOMEM, ENOSPC, EAGAIN)". *)
Definition only_or_env (o expect : ext_outcome) (m : Model) (ctx : NsCtx) (st : NsState) : Prop :=
  o = expect \/ env_refusal o m ctx st.

(** The limit of a sealed namespace reached by a namespace the caller is
    in: namespace 2 (limit 1) has one child, namespace 3, owned by kuid
    1000, and the caller is in 3, so 3 is held; a new namespace from 3 is
    also charged to (2, 1000): ENOSPC, and no success. *)
Definition ns2lim : UserNs := mkUserNs 2 (Some 1%positive) 1 1000 None None true false 1 true.
Definition ns3 : UserNs := mkUserNs 3 (Some 2%positive) 2 1000 None None true false INT_MAX true.

Example unshare_limit_sealed : forall m o,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 3 (1%positive, 1%positive) nocaps)
              (world [ns3; ns2lim; init_uns 100 true]) o
  -> only_or_env o (ns_errno ENOSPC (with_creds (creds 1000) m) (task 3 (1%positive, 1%positive) nocaps)
                             (world [ns3; ns2lim; init_uns 100 true]))
                 (with_creds (creds 1000) m) (task 3 (1%positive, 1%positive) nocaps)
                 (world [ns3; ns2lim; init_uns 100 true]).
Proof.
  intros m o H. unfold only_or_env.
  rewrite (unshare_arm_newuser _ _ _ _ _ ns3 false) in H;
    [| reflexivity | reflexivity | reflexivity].
  destruct H as [H|H]; [left; vm_compute in H; exact H | right; exact H].
Qed.

(** The same count reached by a namespace the caller is not in: Linux may
    have freed it, so the new namespace may fit: ENOSPC and the success
    are both answers. *)
Example unshare_limit_unheld_enospc : forall m,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
              (world [ns2; init_uns 1 true])
              (ns_errno ENOSPC (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
                        (world [ns2; init_uns 1 true])).
Proof.
  intros m. rewrite (unshare_arm_newuser _ _ _ _ _ (init_uns 1 true) false);
    [left; vm_compute; left; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(** Under a namespace that is not sealed, ENOSPC is one answer among
    others, and so is the success. *)
Example unshare_unsealed_enospc : forall m,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
              (world [init_uns 100 false])
              (ns_errno ENOSPC (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
                        (world [init_uns 100 false])).
Proof.
  intros m. rewrite (unshare_arm_newuser _ _ _ _ _ (init_uns 100 false) false);
    [left; vm_compute; left; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Example unshare_unsealed_success : forall m,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
              (world [init_uns 100 false])
              (ns_ret (Z_to_bv 64 0) (with_creds (creds 1000) m)
                      (in_new_userns (task 1 (1%positive, 1%positive) nocaps) 2)
                      (with_userns (world [init_uns 100 false])
                                   [mkUserNs 2 (Some 1%positive) 1 1000 None None true false
                                             INT_MAX true; init_uns 100 false])).
Proof.
  intros m. rewrite (unshare_arm_newuser _ _ _ _ _ (init_uns 100 false) false);
    [left; vm_compute; right; reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(** A parent at level 33: ENOSPC, and no success. *)
Definition deep : UserNs := mkUserNs 1 None 33 0 (Some full) (Some full) true true 100 true.
Example unshare_too_deep : forall m o,
  unshare_arm (call CLONE_NEWUSER) (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
              (world [deep]) o
  -> only_or_env o (ns_errno ENOSPC (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps)
                             (world [deep]))
                 (with_creds (creds 1000) m) (task 1 (1%positive, 1%positive) nocaps) (world [deep]).
Proof.
  intros m o H. unfold only_or_env.
  rewrite (unshare_arm_newuser _ _ _ _ _ deep false) in H; [| reflexivity | reflexivity | reflexivity].
  destruct H as [H|H]; [left; vm_compute in H; exact H | right; exact H].
Qed.

(** The environment's refusals are listed for the forced-only filter:
    ENOMEM, ENOSPC and EAGAIN, the allocations' ([env_refusal]); ENOSPC is
    also the tables' answer ([ni_forced]). *)
Example injected_lists_97 :
  map ni_no user_injected = [97] /\ map ni_forced user_injected = [[ENOSPC]] := conj eq_refl eq_refl.

(** Under forced-only, at a parent above level 32: ENOSPC is the tables'
    answer, so the injected ENOMEM is filtered beside it, and ENOSPC, the
    one errno [ni_forced] lists, is kept, although the environment can
    inject it too: every other answer is an environment refusal. *)
Definition t_deep : NsCtx := task 1 (1%positive, 1%positive) nocaps.

Lemma ns_spec_deep : forall m o,
  ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_deep (world [deep]) o
  <-> unshare_exact deep false (with_creds (creds 1000) m) t_deep (world [deep]) o
      \/ env_refusal o (with_creds (creds 1000) m) t_deep (world [deep]).
Proof.
  intros m o. unfold ns_spec.
  replace (flat_view t_deep (world [deep])) with false by (vm_compute; reflexivity).
  change (lookup_ns_arm ns_table (ns_sysno (call CLONE_NEWUSER))) with (Some unshare_arm).
  cbv beta iota.
  apply unshare_arm_newuser; reflexivity.
Qed.

Lemma deep_filter : forall m eff,
  ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_deep (world [deep]) eff
  <-> ns_refusal_off_b forced_only_cfg (call CLONE_NEWUSER) (eff_ret eff) = true
      /\ exists eff' m' ctx' st' evs',
           ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_deep (world [deep])
                   (EOk eff' m' ctx' st' evs')
           /\ ns_witness (call CLONE_NEWUSER) (eff_ret eff) (eff_ret eff') = true.
Proof. intros m eff. apply ns_refusal_ns. vm_compute. reflexivity. Qed.

Example unshare_too_deep_forced_only : forall m,
  ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_deep (world [deep])
             (mkEffect (errno_ret ENOMEM) [] [])
  /\ ~ ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_deep (world [deep])
               (mkEffect (errno_ret ENOSPC) [] []).
Proof.
  intros m. split.
  - apply (proj2 (deep_filter m _)). split; [vm_compute; reflexivity|].
    exists (mkEffect (errno_ret ENOSPC) [] []), (with_creds (creds 1000) m), t_deep, (world [deep]), [].
    split; [|vm_compute; reflexivity].
    apply (proj2 (ns_spec_deep m _)). left. vm_compute. reflexivity.
  - intros H. apply (proj1 (deep_filter m _)) in H.
    destruct H as (_ & eff' & m' & ctx' & st' & evs' & Hspec & Hw).
    apply (proj1 (ns_spec_deep m _)) in Hspec.
    destruct Hspec as [Hspec | (e & He & Hspec)].
    + vm_compute in Hspec. injection Hspec; intros; subst. vm_compute in Hw. discriminate Hw.
    + unfold ns_errno, ns_ret in Hspec. injection Hspec; intros; subst.
      unfold errno_in, user_env_errnos in He. cbn [existsb] in He.
      repeat (apply orb_true_iff in He; destruct He as [He | He];
              [apply Z.eqb_eq in He; subst e; vm_compute in Hw; discriminate Hw |]).
      discriminate He.
Qed.

(** Under forced-only, an injected ENOSPC beside a success: namespace 1
    has room under its limit, so the tables create the new namespace
    ([unshare_creates]), and ENOSPC, although [ni_forced] lists it, is
    filtered as ENOMEM is: the success matches no pair. *)
Definition t_init : NsCtx := task 1 (1%positive, 1%positive) nocaps.
Definition w_room : NsState := world [init_uns 100 true].

Lemma ns_spec_room : forall m o,
  ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_init w_room o
  <-> unshare_exact (init_uns 100 true) false (with_creds (creds 1000) m) t_init w_room o
      \/ env_refusal o (with_creds (creds 1000) m) t_init w_room.
Proof.
  intros m o. unfold ns_spec.
  replace (flat_view t_init w_room) with false by (vm_compute; reflexivity).
  change (lookup_ns_arm ns_table (ns_sysno (call CLONE_NEWUSER))) with (Some unshare_arm).
  cbv beta iota.
  apply unshare_arm_newuser; reflexivity.
Qed.

Lemma room_filter : forall m eff,
  ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_init w_room eff
  <-> ns_refusal_off_b forced_only_cfg (call CLONE_NEWUSER) (eff_ret eff) = true
      /\ exists eff' m' ctx' st' evs',
           ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_init w_room
                   (EOk eff' m' ctx' st' evs')
           /\ ns_witness (call CLONE_NEWUSER) (eff_ret eff) (eff_ret eff') = true.
Proof. intros m eff. apply ns_refusal_ns. vm_compute. reflexivity. Qed.

Example unshare_room_enospc_forced_only : forall m,
  ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_init w_room
             (mkEffect (errno_ret ENOSPC) [] []).
Proof.
  intros m. apply (proj2 (room_filter m _)). split; [vm_compute; reflexivity|].
  exists (mkEffect (Z_to_bv 64 0) [] []), (with_creds (creds 1000) m), (in_new_userns t_init 2),
         (with_userns w_room [mkUserNs 2 (Some 1%positive) 1 1000 None None true false INT_MAX true;
                              init_uns 100 true]), [].
  split; [|vm_compute; reflexivity].
  apply (proj2 (ns_spec_room m _)). left. vm_compute. reflexivity.
Qed.

(** Under forced-only, a forced ENOSPC is kept: namespace 2 is at its
    limit through namespace 3, which the caller is in
    ([unshare_limit_sealed]), so ENOSPC is the tables' answer and every
    other answer is an environment refusal. *)
Definition t_full : NsCtx := task 3 (1%positive, 1%positive) nocaps.
Definition w_full : NsState := world [ns3; ns2lim; init_uns 100 true].

Lemma ns_spec_full : forall m o,
  ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_full w_full o
  <-> unshare_exact ns3 false (with_creds (creds 1000) m) t_full w_full o
      \/ env_refusal o (with_creds (creds 1000) m) t_full w_full.
Proof.
  intros m o. unfold ns_spec.
  replace (flat_view t_full w_full) with false by (vm_compute; reflexivity).
  change (lookup_ns_arm ns_table (ns_sysno (call CLONE_NEWUSER))) with (Some unshare_arm).
  cbv beta iota.
  apply unshare_arm_newuser; reflexivity.
Qed.

Lemma full_filter : forall m eff,
  ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_full w_full eff
  <-> ns_refusal_off_b forced_only_cfg (call CLONE_NEWUSER) (eff_ret eff) = true
      /\ exists eff' m' ctx' st' evs',
           ns_spec (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_full w_full
                   (EOk eff' m' ctx' st' evs')
           /\ ns_witness (call CLONE_NEWUSER) (eff_ret eff) (eff_ret eff') = true.
Proof. intros m eff. apply ns_refusal_ns. vm_compute. reflexivity. Qed.

Example unshare_limit_enospc_forced_only : forall m,
  ~ ns_refusal forced_only_cfg (call CLONE_NEWUSER) (with_creds (creds 1000) m) t_full w_full
               (mkEffect (errno_ret ENOSPC) [] []).
Proof.
  intros m H. apply (proj1 (full_filter m _)) in H.
  destruct H as (_ & eff' & m' & ctx' & st' & evs' & Hspec & Hw).
  apply (proj1 (ns_spec_full m _)) in Hspec.
  destruct Hspec as [Hspec | (e & He & Hspec)].
  - vm_compute in Hspec. injection Hspec; intros; subst. vm_compute in Hw. discriminate Hw.
  - unfold ns_errno, ns_ret in Hspec. injection Hspec; intros; subst.
    unfold errno_in, user_env_errnos in He. cbn [existsb] in He.
    repeat (apply orb_true_iff in He; destruct He as [He | He];
            [apply Z.eqb_eq in He; subst e; vm_compute in Hw; discriminate Hw |]).
    discriminate He.
Qed.
