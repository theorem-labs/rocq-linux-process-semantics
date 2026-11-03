(** * LinuxProcessSem.Checks.Cases.Ns.SpecCases — which calls the namespace model answers

    [Ns.Spec.ns_ext] claims every call but [clone] (220), [clone3] (435)
    and [wait4] (260), which the core answers, and the extension that
    claims nothing claims nothing.  In the released world a claimed call
    has exactly the released answers ([ns_spec_flat]). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require SpuriousCfg.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm UserArms Files Pass Spec.
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

(** While other processes are live ([Spec.ns_multiproc]): a task in the
    released world gets the core's guard alone.  Outside it, the calls the
    setup child makes are admitted where their answer reads and writes
    only the shared namespace state, the task's own context and table, or
    nothing a peer can change: [getpid], [mount], [capget], an anonymous
    [mmap] (the address space is per process after a clone without
    CLONE_VM), a [read] of a namespace file or of an eventfd, a [writev] of
    a standard channel, a [close] of an opaque descriptor, [fcntl] F_SETFD
    on any descriptor.  Not admitted: a file [mmap], a [read] or [writev]
    of a regular file the released model opened, a [close] of a released
    pipe, [fcntl] F_SETFL on a released file (each reads or moves state the
    core keeps per process), and a call the child does not make
    ([clock_gettime]). *)
Example multiproc_flat_core_guard : forall i m ctx,
  ext_multiproc ns_ext i m ctx empty_nsstate = false.
Proof. intros i m ctx. reflexivity. Qed.

Example multiproc_getpid_inside : forall m,
  ext_multiproc ns_ext (call 172) m (task 2 18) one_mount = true.
Proof. intros m. reflexivity. Qed.

Example multiproc_mount_inside : forall m,
  ext_multiproc ns_ext (call 40) m (task 2 18) one_mount = true.
Proof. intros m. reflexivity. Qed.

Example multiproc_clock_not_inside : forall m,
  ext_multiproc ns_ext (call 113) m (task 2 18) one_mount = false.
Proof. intros m. reflexivity. Qed.

Example multiproc_capget_inside : forall m,
  ext_multiproc ns_ext (call 90) m (task 2 18) one_mount = true.
Proof. intros m. reflexivity. Qed.

(** mmap(NULL, 4096, PROT_READ|PROT_WRITE, flags, fd, 0): MAP_PRIVATE|MAP_ANONYMOUS
    (0x22) is admitted, MAP_PRIVATE (0x02) on a descriptor is not. *)
Definition mmap_in (flags fd : word) : SyscallInput :=
  mkInput 222 [0; 4096; 3; flags; fd; 0] (fun _ => None) (fun _ => None).
Example multiproc_mmap_rules : forall m,
  ext_multiproc ns_ext (mmap_in 34 (Z_to_bv 64 (2 ^ 64 - 1))) m (task 2 18) one_mount = true
  /\ ext_multiproc ns_ext (mmap_in 2 3) m (task 2 18) one_mount = false.
Proof.
  intros m. change (ext_multiproc ns_ext) with ns_multiproc.
  unfold ns_multiproc, ns_multiproc_call. cbv zeta. split; reflexivity.
Qed.

Definition call2 (n a b : word) : SyscallInput :=
  mkInput n [a; b] (fun _ => None) (fun _ => None).

(** The descriptor a call names, in the caller's table. *)
Definition fd3 (i : SyscallInput) (m : Model) : option FdEntry :=
  fd_lookup (m_fds m) (fd_word (in_arg i 0)).

Example multiproc_descriptor_rules : forall m,
  (fd3 (call1 63 3) m = Some (FdOpaque (ONsFile 1)) ->
   ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 63 3) m = Some (FdOpaque (OEventFd (Z_to_bv 64 0))) ->
      ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 63 3) m = Some (FdFile [] (Z_to_bv 64 0)) ->
      ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = false)
  /\ (fd3 (call1 66 3) m = Some (FdChannel (Z_to_bv 64 2)) ->
      ext_multiproc ns_ext (call1 66 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 66 3) m = Some (FdFileW [] (Z_to_bv 64 0)) ->
      ext_multiproc ns_ext (call1 66 3) m (task 2 18) one_mount = false)
  /\ (fd3 (call1 57 3) m = Some (FdOpaque (OProcPath [])) ->
      ext_multiproc ns_ext (call1 57 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 57 3) m = Some (FdPipe (Z_to_bv 64 0) true) ->
      ext_multiproc ns_ext (call1 57 3) m (task 2 18) one_mount = false)
  /\ (fd3 (call2 25 3 2) m = Some (FdFile [] (Z_to_bv 64 0)) ->
      ext_multiproc ns_ext (call2 25 3 2) m (task 2 18) one_mount = true)
  /\ (fd3 (call2 25 3 4) m = Some (FdFile [] (Z_to_bv 64 0)) ->
      ext_multiproc ns_ext (call2 25 3 4) m (task 2 18) one_mount = false).
Proof.
  intros m.
  repeat split; intros H; change (ext_multiproc ns_ext) with ns_multiproc;
    unfold ns_multiproc, ns_multiproc_call, fd_entry_handle, eventfd_flags_of, fd_entry_opaque;
    unfold fd3 in H; cbv zeta; rewrite H; reflexivity.
Qed.

(** A descriptor the released model opened resolves in the host's mount
    namespace: "/" is the root of its root mount.  With no released mount
    namespace, or for a relative path, it does not resolve. *)
Definition slash : list byte := [Z_to_bv 8 47].

Example host_loc_root : host_loc (world true) slash = Some (LDentry 1 1) := eq_refl.
Example host_loc_needs_host_ns : host_loc (world false) slash = None := eq_refl.
Example host_loc_relative : host_loc (world true) [Z_to_bv 8 112] = None := eq_refl.

(** As on Linux: the host namespace's root mount is rootfs (mount 1, root
    dentry 1) and "/" is mount 2, mounted on rootfs's root, with "/etc"
    (dentry 3) in it.  A released path resolves from mount 2's root, the
    root of a task that is not chrooted, not from rootfs; and such a task's
    root (2, 2) is not chrooted. *)
Definition rootfs_world : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 nf nf false false None None;
             mkMount 2 1 (Some 1%positive) 1 2 2 nf nf false false None None]
            [mkUserNs 1 None 0 0 None None true true 100 false]
            [mkMntNs 1 1 1 true] [] []
            [mkSb 1 SbHost 1 1 false 0 false false false; mkSb 2 SbHost 2 1 false 0 false false false]
            [mkDentry 1 1 None [] 1; mkDentry 2 2 None [] 2;
             mkDentry 3 2 (Some 2%positive) [Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 99] 3]
            [mkInode 1 IDir 493 0 0 0 [] false; mkInode 2 IDir 493 0 0 0 [] false;
             mkInode 3 IDir 493 0 0 0 [] false] [] (ns_env empty_nsstate).

Example host_loc_from_top : host_loc rootfs_world slash = Some (LDentry 2 2) := eq_refl.
Example host_loc_below_top :
  host_loc rootfs_world [Z_to_bv 8 47; Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 99] = Some (LDentry 2 3)
  := eq_refl.
Example top_root_not_chrooted :
  UserArms.current_chrooted rootfs_world
    (mkNsCtx 1 1 1 1 [] (2%positive, 2%positive) (2%positive, 2%positive) 18 (mkCaps 0 0 0 0 0) 0 []
             (Some false) (Some 1%Z)) = Some false := eq_refl.

(** A pass-through call outside the released world gets the released
    forced-only filter ([Spec.ns_refusal_pass]): an anonymous [mmap] of a
    task in [one_mount] within the budget has its injected ENOMEM removed,
    as in the released world, because the grant is also an answer
    ([Checks.SpuriousCfg.mmap_enomem_spurious_within_budget]); beyond the
    budget ENOMEM is forced and kept
    ([Checks.SpuriousCfg.mmap_enomem_forced_beyond_budget]). *)
Definition mmap_small : SyscallInput := Cases.Mm.Mmap.mmap_at_in 131072 4096.
Definition mmap_large : SyscallInput := Cases.Mm.Mmap.mmap_in 8192.

Lemma mmap_passes : forall i, ns_sysno i = 222%Z -> In (ns_sysno i) pass_numbers.
Proof. intros i ->. vm_compute. repeat (first [left; reflexivity | right]). Qed.

Example mmap_enomem_filter_outside_released :
  flat_view (task 2 18) one_mount = false
  /\ ns_refusal forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18) one_mount
                (Checks.SpuriousCfg.errno_eff ENOMEM)
  /\ ~ ns_refusal forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18) one_mount
                  (Checks.SpuriousCfg.errno_eff ENOMEM).
Proof.
  split; [reflexivity|].
  split.
  - apply (proj2 (ns_refusal_pass forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18)
                    one_mount (Checks.SpuriousCfg.errno_eff ENOMEM) (mmap_passes mmap_small eq_refl))).
    exact Checks.SpuriousCfg.mmap_enomem_spurious_within_budget.
  - intros H.
    apply (proj1 (ns_refusal_pass forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18)
                    one_mount (Checks.SpuriousCfg.errno_eff ENOMEM) (mmap_passes mmap_large eq_refl))) in H.
    exact (Checks.SpuriousCfg.mmap_enomem_forced_beyond_budget H).
Qed.
