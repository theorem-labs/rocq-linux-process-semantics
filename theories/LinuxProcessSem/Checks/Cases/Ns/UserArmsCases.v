(** * LinuxProcessSem.Checks.Cases.Ns.UserArmsCases — unshare (CLONE_NEWUSER)

    Each example runs [Ns.UserArms.unshare_arm] on a task whose user
    namespace, mounts and credentials the tables hold, and states what the
    arm answers. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm UserArms.
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
  mkNsCtx user 1 1 1 [(1%positive, 2)] root root 18 caps 0 [] false 0 1.

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
     \/ exists e, (1 <= e <= 4095) /\ o = ns_errno e (with_creds (creds 1000) m)
                    (task 1 (1%positive, 5%positive) nocaps) (world [init_uns 100 true]).
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
     \/ exists e, (1 <= e <= 4095) /\ o = ns_errno e (with_creds (creds 1000) m)
                    (task 2 (1%positive, 1%positive) nocaps) (world [ns2; init_uns 100 true]).
Proof.
  intros m o H.
  rewrite (unshare_arm_newuser _ _ _ _ _ ns2 false) in H; [| reflexivity | reflexivity | reflexivity].
  destruct H as [H|H]; [left; vm_compute in H; exact H | right; exact H].
Qed.

(** Every refusal the environment can add is an errno; [only_or_env] is
    "this answer, or one of the environment's". *)
Definition only_or_env (o expect : ext_outcome) (m : Model) (ctx : NsCtx) (st : NsState) : Prop :=
  o = expect \/ exists e, (1 <= e <= 4095) /\ o = ns_errno e m ctx st.

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
    ENOMEM as an allocation failure, any errno as a security module's. *)
Example injected_lists_97 : map ni_no user_injected = [97] := eq_refl.
