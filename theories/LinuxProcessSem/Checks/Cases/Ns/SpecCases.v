(** * LinuxProcessSem.Checks.Cases.Ns.SpecCases — which calls the namespace model answers

    [Ns.Spec.ns_ext] claims every call but [clone] (220), [clone3] (435)
    and [wait4] (260), which the core answers, and the extension that
    claims nothing claims nothing.  In the released world a claimed call
    has exactly the released answers ([ns_spec_flat]). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Spec.
Import ListNotations.
Open Scope bv_scope.

Definition call (n : word) : SyscallInput := mkInput n [] (fun _ => None) (fun _ => None).

Example ns_leaves_clone : ext_claims ns_ext (call 220) = false := eq_refl.
Example ns_leaves_clone3 : ext_claims ns_ext (call 435) = false := eq_refl.
Example ns_leaves_wait4 : ext_claims ns_ext (call 260) = false := eq_refl.
Example ns_claims_openat : ext_claims ns_ext (call 56) = true := eq_refl.
Example ns_claims_mount : ext_claims ns_ext (call 40) = true := eq_refl.
Example ns_claims_exit_group : ext_claims ns_ext (call 94) = true := eq_refl.

Example no_ext_leaves_openat : ext_claims no_ext (call 56) = false := eq_refl.

(** Every task of [empty_nsstate] is in the released world. *)
Example empty_is_flat : forall ctx, flat_view ctx empty_nsstate = true := flat_view_empty.

(** A task with pid 2 in pid namespace 1, mount namespace 1, user
    namespace [u] and umask [umask]. *)
Definition task_in (u : positive) (pid : Z) (umask : Z) : NsCtx :=
  mkNsCtx u 1 1 1 [(1%positive, pid)] (1%positive, 1%positive) (1%positive, 1%positive) umask
          (mkCaps 0 0 0 0 0) 0 [] (Some false) (Some 1%Z).
Definition task (pid : Z) (umask : Z) : NsCtx := task_in 1 pid umask.

Definition nf : MountFlags := mkMountFlags false false false false.

(** One mount in mount namespace 1, which is the host's when [host], on
    a host superblock whose root directory is dentry 1; user namespace 1
    is the initial one, 2 a child of it. *)
Definition world (host : bool) : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 nf nf false false None None]
            [mkUserNs 1 None 0 0 None None true true 100 false;
             mkUserNs 2 (Some 1%positive) 1 0 None None true true 100 true]
            [mkMntNs 1 1 1 host] [] []
            [mkSb 1 SbHost 1 1 false 0 false false false] [mkDentry 1 1 None [] 1]
            [mkInode 1 IDir 493 0 0 0 [] false] [] (ns_env empty_nsstate).
Definition one_mount : NsState := world false.

(** A task in a mount namespace the tables model is not in the released
    world; in the host's mount namespace and the initial user namespace it
    is; in a user namespace below the initial one it is not. *)
Example mounted_not_flat : flat_view (task 2 18) one_mount = false := eq_refl.
Example host_task_flat : flat_view (task 2 18) (world true) = true := eq_refl.
Example child_userns_not_flat : flat_view (task_in 2 2 18) (world true) = false := eq_refl.

(** Outside the released world a number with no arm fails closed. *)
Example unlisted_fails_closed : forall m o,
  ns_spec (call 9999) m (task 2 18) one_mount o <-> o = EUnmodeled.
Proof. intros m o. vm_compute. tauto. Qed.

Example getpid_own_pid : forall m,
  ns_spec (call 172) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 2) m (task 2 18) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

Example gettid_own_pid : forall m,
  ns_spec (call 178) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 2) m (task 2 18) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

(** [umask (0777 | 01000)]: the old mask back, the permission bits kept. *)
Definition call1 (n a : word) : SyscallInput := mkInput n [a] (fun _ => None) (fun _ => None).

Example umask_swaps : forall m,
  ns_spec (call1 166 1023) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 18) m (task 2 511) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

(** In the released world the same calls are the released model's. *)
Example getpid_flat_is_released : forall m ctx o,
  ns_spec (call 172) m ctx empty_nsstate o <-> released (call 172) m ctx empty_nsstate o.
Proof. intros m ctx o. apply ns_spec_flat. reflexivity. Qed.

(** While other processes are live: a task in the released world gets
    the core's guard alone; outside it a call that reads only its own or
    the shared namespace state is admitted ([getpid]), and a [read] on a
    regular file the released model opened, whose offset a multi-process
    core keeps per process, is not. *)
Example multiproc_flat_core_guard : forall i m ctx,
  ext_multiproc ns_ext i m ctx empty_nsstate = false.
Proof. intros i m ctx. reflexivity. Qed.

Example multiproc_getpid_inside : forall m,
  ext_multiproc ns_ext (call 172) m (task 2 18) one_mount = true.
Proof. intros m. reflexivity. Qed.

Example multiproc_released_file_read_inside : forall m,
  fd_lookup (m_fds m) (in_arg (call1 63 3) 0) = Some (FdFile [] (Z_to_bv 64 0)) ->
  ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = false.
Proof.
  intros m H. change (ext_multiproc ns_ext) with ns_multiproc.
  unfold ns_multiproc, released_private_fd. rewrite H. reflexivity.
Qed.

(** A descriptor the released model opened resolves in the host's mount
    namespace: "/" is the root of its root mount.  With no released mount
    namespace, or for a relative path, it does not resolve. *)
Definition slash : list byte := [Z_to_bv 8 47].

Example host_loc_root : host_loc (world true) slash = Some (LDentry 1 1) := eq_refl.
Example host_loc_needs_host_ns : host_loc (world false) slash = None := eq_refl.
Example host_loc_relative : host_loc (world true) [Z_to_bv 8 112] = None := eq_refl.
