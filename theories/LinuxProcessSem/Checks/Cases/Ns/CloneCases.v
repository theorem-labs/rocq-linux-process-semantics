(** * LinuxProcessSem.Checks.Cases.Ns.CloneCases — clone with namespace flags

    Each example runs [Ns.Clone.clone_ns_exact] from a task in the host's
    namespaces, or from a task in a pid namespace the model made, and
    states the child's context or the errno. *)

From Stdlib Require Import ZArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm UserArms Net Clone.
Import ListNotations.
Open Scope Z_scope.

Definition creds (id : Z) : Creds :=
  mkCreds (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id) (Z_to_bv 64 id)
          (Z_to_bv 64 id) [].

Definition nf : MountFlags := mkMountFlags false false false false.
Definition full : list IdExtent := [mkExtent 0 0 4294967295].

(** The host: user namespace 1 (initial, every id mapped), mount namespace
    1 (the host's, root mount 1 at dentry 1), pid namespace 1 and network
    namespace 1, all the host's. *)
Definition host : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 nf nf false false None None]
            [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
            [mkMntNs 1 1 1 true] [mkPidNs 1 None 1 0 0] [mkNetNs 1 1 [] false]
            [] [] [] [] (ns_env empty_nsstate).

Definition nocaps : CapSets := mkCaps 0 0 0 (2 ^ 41 - 1) 0.

(** The caller: pid 136 of the host. *)
Definition caller : NsCtx :=
  mkNsCtx 1 1 1 1 [(1%positive, 136)] (1%positive, 1%positive) (1%positive, 1%positive) 18 nocaps 0 []
          (Some false) (Some 1).

Definition SIGCHLD : Z := 17.
Definition ALL_NS : Z :=
  fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWUSER; CLONE_NEWPID; CLONE_NEWNET;
                   SIGCHLD] 0.

Definition child_of (o : CloneNs) : option NsCtx := match o with CnOk c _ => Some c | _ => None end.
Definition st_of (o : CloneNs) : option NsState := match o with CnOk _ s => Some s | _ => None end.

(** The child is in a new user, mount, pid and network namespace (2 each),
    pid 1 in its own and 138 in the host's, with every capability, its
    root on the copy of the root mount, and, having left the released
    world, a no_new_privs bit and dumpable mode the model does not know. *)
Example clone_all_child : forall m,
  child_of (clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller host 138)
  = Some (mkNsCtx 2 2 2 2 [(2%positive, 1); (1%positive, 138)] (2%positive, 1%positive)
                  (2%positive, 1%positive) 18 (mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0) 0 []
                  None None).
Proof. intros m. vm_compute. reflexivity. Qed.

(** The new user namespace: a child of 1 owned by kuid 65534 with no maps;
    the new pid namespace's last pid is 1; the copy of the root mount is a
    mount of the new mount namespace; the new network namespace is
    sealed. *)
Example clone_all_tables : forall m,
  option_map (fun s => (map uns_id (ns_userns s), map pidns_last (ns_pidns s),
                        map mnt_ns (ns_mounts s), map netns_sealed (ns_netns s),
                        map mntns_owner (ns_mntns s)))
    (st_of (clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller host 138))
  = Some ([2%positive; 1%positive], [0; 1], [1%positive; 2%positive], [false; true],
          [1%positive; 2%positive]).
Proof. intros m. vm_compute. reflexivity. Qed.

(** Leaving the released world without CLONE_NEWUSER declines: the
    caller's capability sets, which decide CAP_SYS_ADMIN, are the released
    model's to derive, not this one's. *)
Example clone_newns_from_host_declines : forall m,
  clone_ns_exact (Z.lor CLONE_NEWNS SIGCHLD) (with_creds (creds 65534) m) caller host 138 = CnUnmodeled.
Proof. intros m. vm_compute. reflexivity. Qed.

(** Inside a user namespace the model made, a namespace flag without
    CLONE_NEWUSER needs CAP_SYS_ADMIN there: a task without it gets
    EPERM. *)
Definition no_admin_inside : NsCtx :=
  mkNsCtx 2 1 2 1 [(2%positive, 1); (1%positive, 136)] (1%positive, 1%positive) (1%positive, 1%positive) 18
          nocaps 0 [] (Some false) (Some 1).

(** A task in the released world that makes no namespace: the core's own
    clone decides the flag word (CLONE_VM here), and the namespace model
    gives the child the caller's context and keeps the state. *)
Example clone_vm_from_host_is_released : forall m,
  clone_ns_exact (Z.lor CLONE_VM SIGCHLD) m caller host 138 = CnOk caller host.
Proof. intros m. vm_compute. reflexivity. Qed.

Example plain_fork_from_host : forall m,
  clone_ns SIGCHLD m caller host 138 (CnOk caller host).
Proof. intros m. apply clone_ns_flat_fork_ok; reflexivity. Qed.

(** From inside the new pid namespace (the shell, pid 1 there and 136 on
    the host), a plain fork with host pid 140 gives pid 2 there and 140 on
    the host, and the shell's call returns 2. *)
Definition inside : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 nf nf false false None None]
            [mkUserNs 2 (Some 1%positive) 1 65534 None None true false 2147483647 true;
             mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
            [mkMntNs 1 1 1 true] [mkPidNs 1 None 1 0 0; mkPidNs 2 (Some 1%positive) 2 1 1]
            [mkNetNs 1 1 [] false] [] [] [] [] (ns_env empty_nsstate).

Definition shell : NsCtx :=
  mkNsCtx 2 1 2 1 [(2%positive, 1); (1%positive, 136)] (1%positive, 1%positive) (1%positive, 1%positive) 18
          (mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0) 0 [] (Some false) (Some 1).

Example clone_newns_inside_needs_admin : forall m,
  clone_ns_exact (Z.lor CLONE_NEWNS SIGCHLD) (with_creds (creds 65534) m) no_admin_inside inside 140
  = CnErr 1 inside.
Proof. intros m. vm_compute. reflexivity. Qed.

Example fork_inside_pid_2 : forall m,
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell inside 140))
  = Some [(2%positive, 2); (1%positive, 140)].
Proof. intros m. vm_compute. reflexivity. Qed.

Example fork_inside_returns_2 : forall m,
  option_map (clone_ret shell) (child_of (clone_ns_exact SIGCHLD m shell inside 140)) = Some (Some 2).
Proof. intros m. vm_compute. reflexivity. Qed.

Example fork_inside_advances_last : forall m,
  option_map (fun s => map pidns_last (ns_pidns s)) (st_of (clone_ns_exact SIGCHLD m shell inside 140))
  = Some [0; 2].
Proof. intros m. vm_compute. reflexivity. Qed.

(** A C library's [fork] (CLONE_CHILD_SETTID | CLONE_CHILD_CLEARTID |
    SIGCHLD) inside the new pid namespace gives the same child. *)
Example libc_fork_inside_pid_2 : forall m,
  option_map cx_pids
    (child_of (clone_ns_exact (Z.lor (Z.lor CLONE_CHILD_SETTID CLONE_CHILD_CLEARTID) SIGCHLD) m shell inside 140))
  = Some [(2%positive, 2); (1%positive, 140)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** Outside the released world a flag the model does not hold (CLONE_VM)
    declines. *)
Example clone_vm_inside_declines : forall m,
  clone_ns_exact (Z.lor CLONE_VM SIGCHLD) m shell inside 140 = CnUnmodeled.
Proof. intros m. vm_compute. reflexivity. Qed.

(** A fork that fails after [alloc_pid] leaves the cursor of the pid
    namespace the model made one further, so the next fork there gives
    pid 3; a failure before it leaves the state as it was.  Both are
    answers. *)
Example fork_failure_advances_cursor :
  map pidns_last (ns_pidns (pid_advanced inside 2)) = [0; 1 + 1] := eq_refl.

Example fork_failure_after_alloc_is_answer : forall m,
  clone_ns SIGCHLD m shell inside 140 (CnErr 12 (pid_advanced inside 2)).
Proof.
  intros m. right. split.
  - vm_compute. intros H. discriminate H.
  - exists 12, (pid_advanced inside 2). split; [lia | split; [right; reflexivity | reflexivity]].
Qed.

Example fork_after_failure_pid_3 : forall m,
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell (pid_advanced inside 2) 141))
  = Some [(2%positive, 3); (1%positive, 141)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** A pid namespace at level 32 can have no child: ENOSPC. *)
Definition deep : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 nf nf false false None None]
            [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
            [mkMntNs 1 1 1 true] [mkPidNs 1 None 1 0 0; mkPidNs 7 (Some 1%positive) 1 32 5]
            [mkNetNs 1 1 [] false] [] [] [] [] (ns_env empty_nsstate).

Definition admin_in_deep : NsCtx :=
  mkNsCtx 1 1 7 1 [(7%positive, 1)] (1%positive, 1%positive) (1%positive, 1%positive) 18
          (mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0) 0 [] (Some false) (Some 1).

Example clone_pid_level_32 : forall m,
  clone_ns_exact (Z.lor CLONE_NEWPID SIGCHLD) m admin_in_deep deep 6 = CnErr 28 deep.
Proof. intros m. vm_compute. reflexivity. Qed.

(** The forced-only filter ([clone_ns_refusal]): when every family is off,
    an environment failure of a namespace clone (here ENOMEM, where the
    tables give the child) is dropped; with the families on it is not; and
    the tables' own failure (EPERM without CAP_SYS_ADMIN) is never dropped. *)
Example clone_env_failure_dropped_forced_only : forall m,
  clone_ns_refusal forced_only_cfg ALL_NS (with_creds (creds 65534) m) caller host 138 12 host.
Proof.
  intros m. split; [reflexivity | split; [reflexivity |]].
  intros H. vm_compute in H. discriminate H.
Qed.

Example clone_env_failure_kept_may_fail : forall m,
  ~ clone_ns_refusal may_fail_cfg ALL_NS (with_creds (creds 65534) m) caller host 138 12 host.
Proof. intros m (H & _). discriminate H. Qed.

Example clone_tables_failure_kept : forall m,
  ~ clone_ns_refusal forced_only_cfg (Z.lor CLONE_NEWNS SIGCHLD) (with_creds (creds 65534) m)
      no_admin_inside inside 140 1 inside.
Proof. intros m (_ & _ & H). apply H. vm_compute. reflexivity. Qed.
