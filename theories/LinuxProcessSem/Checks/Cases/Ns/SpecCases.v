(** * LinuxProcessSem.Checks.Cases.Ns.SpecCases — which calls the namespace model answers

    [Ns.Spec.ns_ext] claims every call but [clone] (220), [clone3] (435)
    and [wait4] (260), which the core answers, and the extension that
    claims nothing claims nothing.  In the released world a claimed call
    has exactly the released answers ([ns_spec_flat]). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require SpuriousCfg.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs Require ReadWrite.
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

(** The empty tables are released when the children's pid namespace
    agrees with the active one, as the default does. *)
Example empty_is_flat : forall ctx,
  pidns_children ctx = cx_pidns ctx -> flat_view ctx empty_nsstate = true := flat_view_empty.

(** A task with pid 2 in pid namespace 1, mount namespace 1, user
    namespace [u] and umask [umask]. *)
Definition task_in (u : positive) (pid : Z) (umask : Z) : NsCtx :=
  with_umask (with_pids (with_user_ns init_nsctx u) [(1%positive, pid)]) umask.
Definition task (pid : Z) (umask : Z) : NsCtx := task_in 1 pid umask.

Definition nf : MountFlags := mkMountFlags false false false false.

(** One mount in mount namespace 1, which is the host's when [host], on
    a host superblock whose root directory is dentry 1; user namespace 1
    is the initial one, 2 a child of it. *)
Definition world (host : bool) : NsState :=
  let w := with_mounts empty_nsstate [mkMount 1 1 None 1 1 1 nf nf false false None None] in
  let w := with_userns w [mkUserNs 1 None 0 0 None None true true 100 false;
                          mkUserNs 2 (Some 1%positive) 1 0 None None true true 100 true] in
  let w := with_mntns w [mk_mntns 1 1 1 host] in
  let w := with_sbs w [mkSb 1 SbHost 1 1 false 0 false false false] in
  let w := with_dentries w [mkDentry 1 1 None [] 1] in
  with_inodes w [mkInode 1 IDir 493 0 0 0 [] false].
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
  pidns_children ctx = cx_pidns ctx ->
  (ns_spec (call 172) m ctx empty_nsstate o <-> released (call 172) m ctx empty_nsstate o).
Proof. intros m ctx o H. apply ns_spec_flat. now apply flat_view_empty. Qed.

(** While other processes are live ([Spec.ns_multiproc]): a task in the
    released world gets the core's guard alone.  Outside it, the calls the
    setup child makes are admitted where their answer reads and writes
    only the shared namespace state, the task's own context and table, or
    nothing a peer can change: [getpid], [mount], [capget], an anonymous
    [mmap] (the address space is per process after a clone without
    CLONE_VM), a [read] of a namespace file, of an eventfd or of an
    inherited file that holds its offset, a [writev] of a standard
    channel, a [close] of an opaque descriptor, [fcntl] F_SETFD on any
    descriptor, an [fchmod] of a namespace file.  Not admitted: a file
    [mmap], a [read] or [writev] of a regular file the released model
    opened, a [read] of an inherited file whose offset the caller gave up
    at a clone, a [close] of a released pipe, [fcntl] F_SETFL on a
    released file (each reads or moves state the core keeps per process),
    and [clock_gettime] and [unlinkat], which the core admits itself
    ([multiproc_core_admits_unlinkat_and_clock]). *)
Example multiproc_flat_core_guard : forall i m ctx,
  pidns_children ctx = cx_pidns ctx -> ext_multiproc ns_ext i m ctx empty_nsstate = false.
Proof.
  intros i m ctx H. exact (ns_multiproc_coherent i m ctx empty_nsstate (flat_view_empty ctx H)).
Qed.

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

(** AN INHERITED FILE THAT HOLDS ITS OFFSET ([State.OInherited] with
    [Some]) is held live by one process only: a clone of either word
    leaves the offset with the child ([Kernel.Fork.forfeit_inherited]).
    So the child's [read] of it is admitted while the parent lives, and
    its [close] is the opaque case.  THE CONTROLS: the parent's copy after
    the clone, [OInherited None], whose [read] is not admitted, and a
    [write] of the live one, which is not admitted either: the released
    arm answers it -EBADF from the description's access mode
    ([Fs.ReadWrite.write_opaque_spec]), but this guard lists no call on
    an inherited file but [read] of a live one and [close], so the core
    refuses the step while another process lives.  [fchmod] (52) of a
    namespace file writes the inode in the shared namespace state and is
    admitted; of a file the released model opened it is not. *)
Example multiproc_inherited_and_fchmod_rules : forall m,
  (fd3 (call1 63 3) m = Some (FdOpaque (OInherited (Some ([], Z_to_bv 64 0)))) ->
   ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 63 3) m = Some (FdOpaque (OInherited None)) ->
      ext_multiproc ns_ext (call1 63 3) m (task 2 18) one_mount = false)
  /\ (fd3 (call1 57 3) m = Some (FdOpaque (OInherited (Some ([], Z_to_bv 64 0)))) ->
      ext_multiproc ns_ext (call1 57 3) m (task 2 18) one_mount = true)
  /\ (fd3 (call1 64 3) m = Some (FdOpaque (OInherited (Some ([], Z_to_bv 64 0)))) ->
      ext_multiproc ns_ext (call1 64 3) m (task 2 18) one_mount = false)
  /\ (fd3 (call2 52 3 384) m = Some (FdOpaque (ONsFile 1)) ->
      ext_multiproc ns_ext (call2 52 3 384) m (task 2 18) one_mount = true)
  /\ (fd3 (call2 52 3 384) m = Some (FdFile [] (Z_to_bv 64 0)) ->
      ext_multiproc ns_ext (call2 52 3 384) m (task 2 18) one_mount = false).
Proof.
  intros m.
  repeat split; intros H; change (ext_multiproc ns_ext) with ns_multiproc;
    unfold ns_multiproc, ns_multiproc_call, fd_entry_handle, eventfd_flags_of, fd_entry_opaque;
    unfold fd3 in H; cbv zeta; rewrite H; reflexivity.
Qed.

(** [unlinkat] (35) and [clock_gettime] (113) are not this guard's: the
    core admits them itself, through its gated and synced lists
    ([Procs.multiproc_gated_sysnos], [Procs.multiproc_synced_sysnos]), in
    [Procs.multiproc_base], which [Procs.multiproc_ok] asks before the
    extension.  THE CONTROL is [read] (63), a class number, which the
    base guard does not admit while another process lives. *)
Lemma multiproc_core_admits_unlinkat_and_clock : forall P c x8,
  RiscvSemantics.ms_svc_pending (cfg_ms c) = Some x8 ->
  (bv_unsigned x8 = 35%Z \/ bv_unsigned x8 = 113%Z) ->
  Procs.multiproc_base P c = true.
Proof.
  intros P c x8 Hs Hx. unfold Procs.multiproc_base. rewrite Hs. cbv beta iota.
  destruct Hx as [Hx|Hx]; rewrite Hx; destruct (Nat.leb _ _); reflexivity.
Qed.

Example multiproc_core_lists : forall m,
  ext_multiproc ns_ext (call 35) m (task 2 18) one_mount = false
  /\ existsb (Z.eqb 35) Procs.multiproc_gated_sysnos = true
  /\ existsb (Z.eqb 113) Procs.multiproc_synced_sysnos = true
  /\ existsb (Z.eqb 63) Procs.multiproc_core_sysnos = false
  /\ existsb (Z.eqb 63) Procs.multiproc_owned_sysnos = false.
Proof.
  intros m. repeat match goal with |- _ /\ _ => split end; reflexivity.
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
  let w := with_mounts empty_nsstate [mkMount 1 1 None 1 1 1 nf nf false false None None;
                                      mkMount 2 1 (Some 1%positive) 1 2 2 nf nf false false None None] in
  let w := with_userns w [mkUserNs 1 None 0 0 None None true true 100 false] in
  let w := with_mntns w [mk_mntns 1 1 1 true] in
  let w := with_sbs w [mkSb 1 SbHost 1 1 false 0 false false false; mkSb 2 SbHost 2 1 false 0 false false false] in
  let w := with_dentries w [mkDentry 1 1 None [] 1; mkDentry 2 2 None [] 2;
                            mkDentry 3 2 (Some 2%positive) [Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 99] 3] in
  with_inodes w [mkInode 1 IDir 493 0 0 0 [] false; mkInode 2 IDir 493 0 0 0 [] false;
                 mkInode 3 IDir 493 0 0 0 [] false].

Example host_loc_from_top : host_loc rootfs_world slash = Some (LDentry 2 2) := eq_refl.
Example host_loc_below_top :
  host_loc rootfs_world [Z_to_bv 8 47; Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 99] = Some (LDentry 2 3)
  := eq_refl.
Example top_root_not_chrooted :
  UserArms.current_chrooted rootfs_world
    (with_cwd (with_root init_nsctx (2%positive, 2%positive)) (2%positive, 2%positive)) = Some false := eq_refl.

(** "/" (mount 2), or rootfs (mount 1), in peer group 7, which has a
    member outside the tables ([env_open_groups]): the host can mount on
    the root of either, or unmount "/", without a call of the model, so the
    topmost mount on the namespace's root mount is not the tables'
    ([Walk.ns_top_open]).  A released path does not resolve, and whether a
    task is chrooted is not decided ([current_chrooted],
    fs/namespace.c:6118-6132).  With no open group, or with one that
    reaches no mount of the stack, both answer as in [rootfs_world]. *)
Definition rootfs_peers (p1 p2 : option positive) (gs : list positive) : NsState :=
  with_open_groups
    (with_mounts rootfs_world [mkMount 1 1 None 1 1 1 nf nf false false p1 None;
                               mkMount 2 1 (Some 1%positive) 1 2 2 nf nf false false p2 None])
    gs.

Definition top_task : NsCtx :=
  with_cwd (with_root init_nsctx (2%positive, 2%positive)) (2%positive, 2%positive).

Example open_top_undecided :
  host_loc (rootfs_peers None (Some 7%positive) [7%positive]) slash = None
  /\ UserArms.current_chrooted (rootfs_peers None (Some 7%positive) [7%positive]) top_task = None.
Proof. vm_compute. split; reflexivity. Qed.

Example open_rootfs_undecided :
  host_loc (rootfs_peers (Some 7%positive) None [7%positive]) slash = None
  /\ UserArms.current_chrooted (rootfs_peers (Some 7%positive) None [7%positive]) top_task = None.
Proof. vm_compute. split; reflexivity. Qed.

Example closed_stack_decided :
  host_loc (rootfs_peers (Some 7%positive) (Some 7%positive) []) slash = Some (LDentry 2 2)
  /\ host_loc (rootfs_peers (Some 7%positive) (Some 7%positive) [8%positive]) slash = Some (LDentry 2 2)
  /\ UserArms.current_chrooted (rootfs_peers (Some 7%positive) (Some 7%positive) []) top_task
     = Some false
  /\ UserArms.current_chrooted (rootfs_peers (Some 7%positive) (Some 7%positive) [8%positive]) top_task
     = Some false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A pass-through call outside the released world gets the released
    forced-only filter ([Spec.ns_refusal_eff_pass]): an anonymous [mmap] of a
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
  /\ ns_refusal_eff forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18) one_mount
                (Checks.SpuriousCfg.errno_eff ENOMEM)
  /\ ~ ns_refusal_eff forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18) one_mount
                  (Checks.SpuriousCfg.errno_eff ENOMEM).
Proof.
  split; [reflexivity|].
  split.
  - apply (proj2 (ns_refusal_eff_pass forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18)
                    one_mount (Checks.SpuriousCfg.errno_eff ENOMEM) (mmap_passes mmap_small eq_refl))).
    exact Checks.SpuriousCfg.mmap_enomem_spurious_within_budget.
  - intros H.
    apply (proj1 (ns_refusal_eff_pass forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18)
                    one_mount (Checks.SpuriousCfg.errno_eff ENOMEM) (mmap_passes mmap_large eq_refl))) in H.
    exact (Checks.SpuriousCfg.mmap_enomem_forced_beyond_budget H).
Qed.

(** THE FILTER READS THE WHOLE OUTCOME AND KEEPS ITS ANSWERS.  The core
    filters a claimed call's [EOk] outcome ([Ext.ext_refusal]), and for
    every call but [sendto] [Spec.ns_refusal] filters it as
    [Spec.ns_refusal_eff] filters its effect ([Spec.ns_refusal_outcome_eff]),
    whatever model, context, state and events it leaves: the [mmap]
    answers above are the same on outcomes. *)
Example mmap_enomem_outcome_filter : forall m' ctx' st' evs,
  ns_refusal forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18) one_mount
    (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs)
  /\ ~ ns_refusal forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18) one_mount
         (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs).
Proof.
  intros m' ctx' st' evs.
  destruct mmap_enomem_filter_outside_released as (_ & Hs & Hl).
  split.
  - apply (proj2 (ns_refusal_outcome_eff forced_only_cfg mmap_small Cases.Prelude.tight_model
                    (task 2 18) one_mount (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs)
                    (Checks.SpuriousCfg.errno_eff ENOMEM) eq_refl eq_refl)).
    exact Hs.
  - intros H. apply Hl.
    apply (proj1 (ns_refusal_outcome_eff forced_only_cfg mmap_large Cases.Prelude.tight_model
                    (task 2 18) one_mount (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs)
                    (Checks.SpuriousCfg.errno_eff ENOMEM) eq_refl eq_refl)).
    exact H.
Qed.

(** THE RELEASED WORLD KEEPS ITS FILTER ([Ext.ext_refusal_released]).  For
    a task of the host's namespaces ([host_task_flat]) the filter of a
    claimed call's outcome is the released filter of its effect, the one
    it was when the filter read the effect alone: whatever the outcome
    leaves, an anonymous [mmap]'s injected ENOMEM is removed within the
    budget and kept beyond it, the released answers
    ([Checks.SpuriousCfg.mmap_enomem_spurious_within_budget],
    [Checks.SpuriousCfg.mmap_enomem_forced_beyond_budget]). *)
Example released_world_filter_unchanged : forall m' ctx' st' evs,
  ext_refusal ns_ext forced_only_cfg mmap_small Cases.Prelude.tight_model (task 2 18) (world true)
    (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs)
  /\ ~ ext_refusal ns_ext forced_only_cfg mmap_large Cases.Prelude.tight_model (task 2 18) (world true)
         (EOk (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs).
Proof.
  intros m' ctx' st' evs. split.
  - apply (proj2 (ext_refusal_released ns_ext forced_only_cfg mmap_small Cases.Prelude.tight_model
                    (task 2 18) (world true) (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs
                    host_task_flat eq_refl)).
    exact Checks.SpuriousCfg.mmap_enomem_spurious_within_budget.
  - intros H.
    apply (proj1 (ext_refusal_released ns_ext forced_only_cfg mmap_large Cases.Prelude.tight_model
                    (task 2 18) (world true) (Checks.SpuriousCfg.errno_eff ENOMEM) m' ctx' st' evs
                    host_task_flat eq_refl)) in H.
    exact (Checks.SpuriousCfg.mmap_enomem_forced_beyond_budget H).
Qed.

(** THE RULE OF A ROW IS CHECKED ([Spec.ns_injected_forced]).  A
    deliberately bad row: [openat]'s, as if its tables also answered ENOMEM,
    an errno a pair matches, without ENOMEM in its [ni_forced].  Written in
    Ns/Files.v as

      Definition openat_injected : NsInjected :=
        mkNsInjected 56 open_pairs (ENOMEM :: open_answers) [].

    it makes [ns_injected_forced] false, so Ns/Spec.v does not compile.  The
    check refuses that row; it accepts the same row with ENOMEM in
    [ni_forced]; it also refuses a row whose [ni_forced] lists an errno its
    tables do not answer; and it accepts the real row. *)
Example bad_row_fails :
  ni_forced_ok (mkNsInjected 56%Z open_pairs (ENOMEM :: open_answers) []) = false
  /\ ni_forced_ok (mkNsInjected 56%Z open_pairs (ENOMEM :: open_answers) [ENOMEM]) = true
  /\ ni_forced_ok (mkNsInjected 56%Z open_pairs open_answers [ENOMEM]) = false
  /\ ni_forced_ok openat_injected = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ONE FAMILY PER FAILURE.  [new_inode]'s ENOSPC is FamAlloc in every row
    where it can happen, a tmpfs create's ([openat], [mkdirat],
    [symlinkat]) and a new tmpfs's root ([mount]); only a create's ENOSPC is
    also FamFs, the instance's inode limit.  A write's ENOMEM on a file of
    the model is FamAlloc alone. *)
Example one_family_per_failure :
  map snd (ns_matching (call 56) (errno_ret ENOSPC)) = [FamAlloc; FamFs]
  /\ map snd (ns_matching (call 34) (errno_ret ENOSPC)) = [FamAlloc; FamFs]
  /\ map snd (ns_matching (call 36) (errno_ret ENOSPC)) = [FamAlloc; FamFs]
  /\ map snd (ns_matching (call 40) (errno_ret ENOSPC)) = [FamAlloc]
  /\ map snd (ns_matching (call 64) (errno_ret ENOMEM)) = [FamAlloc].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** FAMILIES BY KERNEL CAUSE.  [netlink_insert]'s ENOMEM, a failed
    [bucket_table_alloc] (lib/rhashtable.c:466-470), is FamAlloc in [bind]
    and [sendto], and its EOVERFLOW, the table's -EBUSY
    (net/netlink/af_netlink.c:573-574), FamNet.  [alloc_empty_file]'s
    ENFILE, the system-wide file limit (fs/file_table.c:278), is FamFd in
    [openat] and [openat2]; [socket]'s ENFILE is also [sock_alloc]'s
    failed allocation, so FamAlloc and FamFd.  So the filter's family test
    ([ns_refusal_off_b]) holds of [bind]'s ENOMEM with the allocation
    family off and not with the net family off, of [openat]'s ENFILE with
    the fd family off, and of [socket]'s ENFILE only with both off. *)
Definition fd_off_cfg : SpuriousCfg := mkSpuriousCfg true true false true true true.
Definition net_off_cfg : SpuriousCfg := mkSpuriousCfg true true true false true true.

Example families_by_cause :
  map snd (ns_matching (call 200) (errno_ret ENOMEM)) = [FamAlloc]
  /\ map snd (ns_matching (call 200) (errno_ret EOVERFLOW)) = [FamNet]
  /\ map snd (ns_matching (call 206) (errno_ret ENOMEM)) = [FamAlloc]
  /\ map snd (ns_matching (call 206) (errno_ret EOVERFLOW)) = [FamNet]
  /\ map snd (ns_matching (call 56) (errno_ret ENFILE)) = [FamFd]
  /\ map snd (ns_matching (call 437) (errno_ret ENFILE)) = [FamFd]
  /\ map snd (ns_matching (call 198) (errno_ret ENFILE)) = [FamAlloc; FamFd]
  /\ ns_refusal_off_b (alloc_only_cfg false) (call 200) (errno_ret ENOMEM) = true
  /\ ns_refusal_off_b net_off_cfg (call 200) (errno_ret ENOMEM) = false
  /\ ns_refusal_off_b fd_off_cfg (call 56) (errno_ret ENFILE) = true
  /\ ns_refusal_off_b (alloc_only_cfg false) (call 56) (errno_ret ENFILE) = false
  /\ ns_refusal_off_b fd_off_cfg (call 198) (errno_ret ENFILE) = false
  /\ ns_refusal_off_b (alloc_only_cfg false) (call 198) (errno_ret ENFILE) = false
  /\ ns_refusal_off_b forced_only_cfg (call 198) (errno_ret ENFILE) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE SAME FILTER IN BOTH WORLDS.  A write on a descriptor of the
    released model outside the released world ([mounted_not_flat]) gets
    the released filter itself ([Spec.ns_refusal_eff_released_fd]): a write
    into an empty pipe answered ENOMEM
    ([Checks.SpuriousCfg.write_pipe_enomem_i]), whose family the released
    table makes fs, is removed when the fs family alone is off and kept when
    the allocation family alone is off, as in the released world
    ([Checks.SpuriousCfg.write_pipe_enomem_spurious_under_forced_only],
    [Checks.SpuriousCfg.write_pipe_enomem_kept_under_alloc_only]). *)
Definition fs_off_cfg : SpuriousCfg := mkSpuriousCfg true false true true true true.

Example write_pipe_released_fd :
  released_fd_call Checks.SpuriousCfg.write_pipe_enomem_i Cases.Fs.ReadWrite.pipe_empty_model
    one_mount = true.
Proof. vm_compute. reflexivity. Qed.

Example write_pipe_enomem_same_filter :
  ns_refusal_eff fs_off_cfg Checks.SpuriousCfg.write_pipe_enomem_i Cases.Fs.ReadWrite.pipe_empty_model
             (task 2 18) one_mount (Checks.SpuriousCfg.errno_eff ENOMEM)
  /\ ~ ns_refusal_eff (alloc_only_cfg false) Checks.SpuriousCfg.write_pipe_enomem_i
         Cases.Fs.ReadWrite.pipe_empty_model (task 2 18) one_mount (Checks.SpuriousCfg.errno_eff ENOMEM).
Proof.
  split.
  - apply (proj2 (ns_refusal_eff_released_fd fs_off_cfg _ _ (task 2 18) one_mount _ write_pipe_released_fd)).
    destruct Checks.SpuriousCfg.write_pipe_enomem_spurious_under_forced_only as (_ & Hr & Hex).
    split; [vm_compute; reflexivity | split; [exact Hr | exact Hex]].
  - intros H.
    apply (proj1 (ns_refusal_eff_released_fd (alloc_only_cfg false) _ _ (task 2 18) one_mount _
                    write_pipe_released_fd)) in H.
    exact (Checks.SpuriousCfg.write_pipe_enomem_kept_under_alloc_only H).
Qed.
