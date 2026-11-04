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

(** Tables with mounts [ms], user namespaces [us] and pid namespaces [ps],
    mount namespace 1 (the host's, root mount 1) and network namespace 1
    (the host's). *)
Definition tables (ms : list Mount) (us : list UserNs) (ps : list PidNs) : NsState :=
  let st := with_mounts empty_nsstate ms in
  let st := with_userns st us in
  let st := with_mntns st [mkMntNs 1 1 1 true] in
  let st := with_pidns st ps in
  with_netns st [mkNetNs 1 1 [] false].

(** The host: user namespace 1 (initial, every id mapped), mount namespace
    1 (the host's, root mount 1 at dentry 1), pid namespace 1, network
    namespace 1 and UTS namespace 1, all the host's. *)
Definition host : NsState :=
  tables [mkMount 1 1 None 1 1 1 nf nf false false None None]
         [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
         [mk_pidns 1 None 1 0 0].

Definition nocaps : CapSets := mkCaps 0 0 0 (2 ^ 41 - 1) 0.
Definition fullcaps : CapSets := mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0.

(** The caller: pid 136 of the host. *)
Definition caller : NsCtx := with_caps (with_pids init_nsctx [(1%positive, 136)]) nocaps.

Definition SIGCHLD : Z := 17.
Definition ALL_NS : Z :=
  fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWUSER; CLONE_NEWPID; CLONE_NEWNET;
                   SIGCHLD] 0.

Definition child_of (o : CloneNs) : option NsCtx := match o with CnOk c _ _ => Some c | _ => None end.
Definition st_of (o : CloneNs) : option NsState := match o with CnOk _ _ s => Some s | _ => None end.
Definition ret_of (o : CloneNs) : option (option Z) := match o with CnOk _ r _ => Some r | _ => None end.

(** The child is in a new user, mount, pid, network and UTS namespace (2
    each), pid 1 in its own and 138 in the host's, with every capability
    and its root on the copy of the root mount.  Its no_new_privs bit and
    dumpable mode are its process record's ([Procs.child_proc]), not this
    context's. *)
Example clone_all_child : forall m,
  child_of (clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller host 138)
  = Some (let c := with_user_ns init_nsctx 2 in
          let c := with_mount_ns c 2 in
          let c := with_pid_ns c 2 in
          let c := with_net_ns c 2 in
          let c := with_uts_ns c 2 in
          let c := with_pids c [(2%positive, 1); (1%positive, 138)] in
          let c := with_root c (2%positive, 1%positive) in
          let c := with_cwd c (2%positive, 1%positive) in
          with_caps c fullcaps).
Proof. intros m. vm_compute. reflexivity. Qed.

(** As on Linux: the host's mount namespace has rootfs (mount 1) as its root
    mount and "/" (mount 2) mounted on rootfs's root; the caller's root is
    "/"'s root.  A new mount namespace copies both, so the child's root
    mount (the copy of "/") has a parent, the copy of rootfs: so the
    child's later pivot_root does not stop at "the root mount has no
    parent" (EINVAL). *)
Definition host_rootfs : NsState :=
  tables [mkMount 1 1 None 1 1 1 nf nf false false None None;
          mkMount 2 1 (Some 1%positive) 1 2 2 nf nf false false None None]
         [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
         [mk_pidns 1 None 1 0 0].

Definition caller_rootfs : NsCtx := with_cwd (with_root caller (2%positive, 2%positive)) (2%positive, 2%positive).

Example clone_root_mount_has_parent : forall m,
  match clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller_rootfs host_rootfs 138 with
  | CnOk child _ s =>
      match find_mount (ns_mounts s) (fst (cx_root child)) with
      | Some r => match mnt_parent r with Some _ => mnt_ns r = cx_mount child | None => False end
      | None => False
      end
  | _ => False
  end.
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
  with_caps (with_pids (with_pid_ns (with_user_ns init_nsctx 2) 2) [(2%positive, 1); (1%positive, 136)])
            nocaps.

(** A task in the released world that makes no namespace: the core's own
    clone decides the flag word (CLONE_VM here), and the namespace model
    gives the child the caller's context and keeps the state. *)
Example clone_vm_from_host_is_released : forall m,
  clone_ns_exact (Z.lor CLONE_VM SIGCHLD) m caller host 138 = CnOk caller None host.
Proof. intros m. vm_compute. reflexivity. Qed.

Example plain_fork_from_host : forall m,
  clone_ns SIGCHLD m caller host 138 (CnOk caller None host).
Proof. intros m. apply clone_ns_flat_fork_ok; reflexivity. Qed.

(** From inside the new pid namespace (the shell, pid 1 there and 136 on
    the host), a plain fork with host pid 140 gives pid 2 there and 140 on
    the host, and the shell's call returns 2. *)
Definition inside : NsState :=
  tables [mkMount 1 1 None 1 1 1 nf nf false false None None]
         [mkUserNs 2 (Some 1%positive) 1 65534 None None true false 2147483647 true;
          mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
         [mk_pidns 1 None 1 0 0; mk_pidns 2 (Some 1%positive) 2 1 1].

Definition shell : NsCtx := with_caps no_admin_inside fullcaps.

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

(** The answer carries that return value, so a core gives the shell 2,
    not the host's pid 140; a caller in the host's namespaces gets the
    core's pid ([None]). *)
Example fork_inside_parent_gets_2 : forall m,
  ret_of (clone_ns_exact SIGCHLD m shell inside 140) = Some (Some 2)
  /\ ret_of (clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller host 138) = Some None.
Proof. intros m. split; vm_compute; reflexivity. Qed.

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
  - exists 12, (pid_advanced inside 2). split; [lia|]. split; [|reflexivity].
    right. split; [vm_compute; reflexivity|left; reflexivity].
Qed.

Example fork_after_failure_pid_3 : forall m,
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell (pid_advanced inside 2) 141))
  = Some [(2%positive, 3); (1%positive, 141)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** Allocation visits namespace 3 before 2.  A failure at 2 leaves 3's
    cursor advanced but 2's unchanged (kernel/pid.c:191-251,294-299). *)
Definition nested_pids : NsState :=
  with_pidns inside [mk_pidns 1 None 1 0 0;
    mk_pidns 2 (Some 1%positive) 2 1 7; mk_pidns 3 (Some 2%positive) 2 2 1].
Definition nested_shell : NsCtx :=
  with_pids (with_pid_ns shell 3) [(3%positive, 1); (2%positive, 7); (1%positive, 139)].
Definition inner_cursor_advanced : NsState :=
  with_pidns nested_pids [mk_pidns 1 None 1 0 0;
    mk_pidns 2 (Some 1%positive) 2 1 7; mk_pidns 3 (Some 2%positive) 2 2 2].

Example partial_failure_state_is_new :
  inner_cursor_advanced <> nested_pids /\
  inner_cursor_advanced <> pid_advanced nested_pids 3.
Proof. split; vm_compute; discriminate. Qed.

Example fork_partial_allocation_is_answer : forall m,
  clone_ns SIGCHLD m nested_shell nested_pids 140 (CnErr 12 inner_cursor_advanced).
Proof.
  intros m. right. split.
  - vm_compute. intros H. discriminate H.
  - exists 12, inner_cursor_advanced. split; [lia|]. split; [|reflexivity].
    right. split; [vm_compute; reflexivity|].
    right. exists 1%nat. split; [vm_compute; lia|vm_compute; reflexivity].
Qed.

Example fork_nested_old_failure_states_remain : forall m,
  clone_ns SIGCHLD m nested_shell nested_pids 140 (CnErr 12 nested_pids) /\
  clone_ns SIGCHLD m nested_shell nested_pids 140 (CnErr 12 (pid_advanced nested_pids 3)).
Proof.
  intros m. split; right; split.
  - vm_compute. intros H. discriminate H.
  - exists 12, nested_pids. split; [lia|]. split; [left; reflexivity|reflexivity].
  - vm_compute. intros H. discriminate H.
  - exists 12, (pid_advanced nested_pids 3). split; [lia|].
    split; [|reflexivity]. right. split; [vm_compute; reflexivity|left; reflexivity].
Qed.

Example fork_single_model_level_failure_states : forall m e st',
  clone_ns SIGCHLD m shell inside 140 (CnErr e st')
  <-> 1 <= e <= 4095 /\ (st' = inside \/ st' = pid_advanced inside 2).
Proof.
  intros m e st'. unfold clone_ns. split.
  - intros [H | (_ & en & s & He & Hstate & Ho)].
    + pose proof (fork_inside_pid_2 m) as Hpid. rewrite <- H in Hpid. discriminate Hpid.
    + injection Ho as -> ->. split; [exact He|].
      destruct Hstate as [H | [_ [H | (k & Hk & H)]]].
      * left. exact H.
      * right. exact H.
      * change (k < 2)%nat in Hk. destruct k as [|[|k]].
        -- left. exact H.
        -- right. exact H.
        -- lia.
  - intros [He Hstate]. right. split.
    + pose proof (fork_inside_pid_2 m) as Hpid. intros H. rewrite H in Hpid. discriminate Hpid.
    + exists e, st'. split; [exact He|]. split; [|reflexivity].
      destruct Hstate as [H|H].
      * left. exact H.
      * right. split; [vm_compute; reflexivity|left; exact H].
Qed.

Example fork_released_failure_state_unchanged : forall m e st',
  clone_ns SIGCHLD m caller host 140 (CnErr e st')
  <-> 1 <= e <= 4095 /\ st' = host.
Proof.
  intros m e st'. rewrite clone_ns_coherent by reflexivity.
  unfold released_clone. split.
  - intros [H | (en & He & Ho)]; [discriminate H|]. injection Ho as -> ->. auto.
  - intros [He ->]. right. exists e. auto.
Qed.

Print Assumptions fork_single_model_level_failure_states.
Print Assumptions fork_released_failure_state_unchanged.
Print Assumptions pid_partial_flat.
Print Assumptions clone_ns_coherent.

(** copy_namespaces fails before alloc_pid (kernel/fork.c:2188-2208,
    Linux v6.18.46): no environment refusal can move a pid cursor there. *)
Example early_newns_error_keeps_pid_state : forall m e st',
  clone_ns (Z.lor CLONE_NEWNS SIGCHLD) m (with_caps nested_shell nocaps) nested_pids 140
    (CnErr e st') <-> 1 <= e <= 4095 /\ st' = nested_pids.
Proof.
  intros m e st'.
  assert (Htable : clone_ns_exact (Z.lor CLONE_NEWNS SIGCHLD) m
      (with_caps nested_shell nocaps) nested_pids 140 = CnErr EPERM nested_pids)
    by (vm_compute; reflexivity).
  unfold clone_ns. rewrite Htable. cbn. split.
  - intros [Ho | (_ & en & s & He & Hstate & Ho)].
    + injection Ho as -> ->. split; [unfold EPERM; lia|reflexivity].
    + injection Ho as -> ->. split; [exact He|].
      destruct Hstate as [H | [Halloc _]]; [exact H|discriminate Halloc].
  - intros [He ->]. right. split; [discriminate|].
    exists e, nested_pids. split; [exact He|]. split; [left; reflexivity|reflexivity].
Qed.

Print Assumptions early_newns_error_keeps_pid_state.

(** A pid namespace at level 32 can have no child: ENOSPC. *)
Definition deep : NsState :=
  tables [mkMount 1 1 None 1 1 1 nf nf false false None None]
         [mkUserNs 1 None 0 0 (Some full) (Some full) true true 100 false]
         [mk_pidns 1 None 1 0 0; mk_pidns 7 (Some 1%positive) 1 32 5].

Definition admin_in_deep : NsCtx := with_caps (with_pids (with_pid_ns init_nsctx 7) [(7%positive, 1)]) fullcaps.

Example clone_pid_level_32 : forall m,
  clone_ns_exact (Z.lor CLONE_NEWPID SIGCHLD) m admin_in_deep deep 6 = CnErr 28 deep.
Proof. intros m. vm_compute. reflexivity. Qed.

(** [clone_tables_failures], the clone environment of a run in which the
    host can make the namespaces: an environment failure of a namespace
    clone (here ENOMEM, where the tables give the child) is outside it; the
    tables' own failure (EPERM without CAP_SYS_ADMIN) is in it; and so is
    every failure of the released clone (a plain fork from the host). *)
Example clone_env_failure_outside : forall m,
  ~ clone_tables_failures ALL_NS (with_creds (creds 65534) m) caller host 138 12 host.
Proof. intros m [H | [H | (H & _)]]; vm_compute in H; discriminate H. Qed.

Example clone_tables_failure_inside : forall m,
  clone_tables_failures (Z.lor CLONE_NEWNS SIGCHLD) (with_creds (creds 65534) m)
    no_admin_inside inside 140 1 inside.
Proof. intros m. right. left. vm_compute. reflexivity. Qed.

Example released_fork_failure_inside : forall m,
  clone_tables_failures SIGCHLD m caller host 138 12 host.
Proof. intros m. apply clone_tables_failures_flat; reflexivity. Qed.

(** A RUN THE ENVIRONMENT PREMISE ADMITS (the satisfiability witness): a
    caller with pid 136 in the host's pid namespace, uid 65534, no
    capabilities, clones with the word 0x7c020011 (a new mount, UTS, IPC,
    user, pid and network namespace, exit signal SIGCHLD) and the host
    gives the child pid 138, as a recorded run on Linux 6.18.44 did.  The
    tables' answer is the child ([clone_all_child]), so the clone succeeds
    and no failure is needed: [clone_tables_failures] restricts failures
    only. *)
Example clone_tables_run_succeeds : forall m,
  ALL_NS = 2080505873 /\
  exists child r st', clone_ns_exact ALL_NS (with_creds (creds 65534) m) caller host 138 = CnOk child r st'.
Proof. intros m. split; [reflexivity|]. vm_compute. do 3 eexists. reflexivity. Qed.

(** A launch with a different children's namespace states the whole
    measured context, not only that one field.  The launcher is pid 1 of
    A (2), root in the host user namespace, with full capability sets,
    root/cwd at (1,1), umask 022, no securebits or close-on-exec entries.
    B (3) was made by its unshare, with creation-to-launch exclusion of
    outside entry/allocation/control writes; hence B is empty at cursor 0.
    A's clear range is a separate launch fact, not inferred from B. *)
Definition launch_children_ctx : NsCtx :=
  with_pidns_children
    (with_cloexec (with_securebits (with_caps
      (with_umask (with_cwd (with_root
        (with_pids (with_uts_ns (with_net_ns (with_pid_ns
          (with_mount_ns (with_user_ns init_nsctx 1) 1) 2) 1) host_uts)
          [(2%positive, 1); (1%positive, 137)]) (1%positive, 1%positive))
        (1%positive, 1%positive)) 18) fullcaps) 0) []) 3.

Definition launch_children_state : NsState :=
  with_pidns host [mk_pidns 1 None 1 0 0;
    pidns_with_cursor_clear (pidns_with_alloc (mk_pidns 2 (Some 1%positive) 1 1 7) PaInit) true;
    pidns_with_alloc (mk_pidns 3 (Some 2%positive) 1 2 0) PaEmpty].

Definition launch_children_model (m : Model) : Model :=
  with_dumpable (Z_to_bv 64 1) (with_no_new_privs false (with_creds (creds 0) m)).

Example clone_into_empty_children : forall m,
  let o := clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx launch_children_state 140 in
  option_map cx_pids (child_of o) = Some [(3%positive, 1); (2%positive, 8); (1%positive, 140)] /\
  ret_of o = Some (Some 8) /\
  option_map cx_pidns_children (child_of o) = Some None /\
  option_map (fun st => option_map pidns_alloc (find_pidns st 3)) (st_of o) = Some (Some PaInit).
Proof. intros m. repeat split; vm_compute; reflexivity. Qed.

Example clone_newpid_with_other_children_is_einval : forall m,
  clone_ns_exact (Z.lor CLONE_NEWPID SIGCHLD) (launch_children_model m)
    launch_children_ctx launch_children_state 140 = CnErr 22 launch_children_state.
Proof. intros m. vm_compute. reflexivity. Qed.

Example other_children_is_not_flat :
  flat_view launch_children_ctx launch_children_state = false /\
  flat_view (with_pidns_children init_nsctx 3) empty_nsstate = false.
Proof. split; reflexivity. Qed.

Example equal_children_is_default : forall m,
  clone_ns_exact SIGCHLD m (with_pidns_children shell (cx_pidns shell)) inside 140
    = clone_ns_exact SIGCHLD m shell inside 140.
Proof. intros m. vm_compute. reflexivity. Qed.

Example released_equal_children_keeps_context : forall m,
  let ctx := with_pidns_children caller (cx_pidns caller) in
  clone_ns_exact SIGCHLD m ctx host 140 = CnOk ctx None host.
Proof. intros m. vm_compute. reflexivity. Qed.

Example unknown_children_declines : forall m,
  clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx
    (with_pidns launch_children_state [mk_pidns 1 None 1 0 0;
      mk_pidns 2 (Some 1%positive) 1 1 7; mk_pidns 3 (Some 2%positive) 1 2 1]) 140
    = CnUnmodeled.
Proof. intros m. vm_compute. reflexivity. Qed.

Example initialized_children_declines : forall m,
  match clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx launch_children_state 140 with
  | CnOk _ _ st => clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx st 141 = CnUnmodeled
  | _ => False
  end.
Proof. intros m. vm_compute. reflexivity. Qed.

Example failed_first_child_closes_namespace : forall m,
  let st := pid_failed launch_children_state 3 in
  option_map pidns_alloc (find_pidns st 3) = Some PaClosed /\
  map pidns_last (ns_pidns st) = [0; 8; 1] /\
  clone_ns SIGCHLD (launch_children_model m) launch_children_ctx launch_children_state 140 (CnErr 12 st).
Proof.
  intros m. split; [reflexivity|]. split; [reflexivity|]. right. split.
  - vm_compute. intros H. discriminate H.
  - exists 12, (pid_failed launch_children_state 3). split; [lia|].
    split; [|reflexivity]. right. split; [vm_compute; reflexivity|left; reflexivity].
Qed.

Example partial_first_child_resets_only_inner :
  map pidns_last (ns_pidns (pid_partial launch_children_state 3 2)) = [0; 8; 0] /\
  option_map pidns_alloc (find_pidns (pid_partial launch_children_state 3 2) 3) = Some PaEmpty.
Proof. split; reflexivity. Qed.

(** Outside interference and launch occupancy are distinct inputs. *)
Example outside_pid_allocator_declines : forall m,
  clone_ns_exact SIGCHLD m shell
    (with_env inside (env_with_outside_pids (ns_env inside) true)) 140 = CnUnmodeled /\
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell
    (with_env inside (env_with_outside_pids (ns_env inside) false)) 140))
    = Some [(2%positive, 2); (1%positive, 140)].
Proof. intros m. split; vm_compute; reflexivity. Qed.

Definition cursor_launch (limit : Z) (clear : bool) (last : Z) : NsState :=
  with_pidns inside [mk_pidns 1 None 1 0 0;
    pidns_with_cursor_clear (pidns_with_max (mk_pidns 2 (Some 1%positive) 2 1 last) limit) clear].

Example cursor_at_measured_limit_declines : forall m,
  clone_ns_exact SIGCHLD m shell (cursor_launch 500 true 499) 140 = CnUnmodeled /\
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell
    (cursor_launch 4194304 true 499) 140)) = Some [(2%positive, 500); (1%positive, 140)].
Proof. intros m. split; vm_compute; reflexivity. Qed.

Example occupied_next_pid_declines : forall m,
  clone_ns_exact SIGCHLD m shell (cursor_launch 4194304 false 7) 140 = CnUnmodeled /\
  option_map cx_pids (child_of (clone_ns_exact SIGCHLD m shell
    (cursor_launch 4194304 true 7) 140)) = Some [(2%positive, 8); (1%positive, 140)].
Proof. intros m. split; vm_compute; reflexivity. Qed.

Example empty_child_does_not_establish_parent_clear_range : forall m,
  clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx
    (with_pidns launch_children_state [mk_pidns 1 None 1 0 0;
      pidns_with_cursor_clear (mk_pidns 2 (Some 1%positive) 1 1 7) false;
      pidns_with_alloc (mk_pidns 3 (Some 2%positive) 1 2 0) PaEmpty]) 140 = CnUnmodeled.
Proof. intros m. vm_compute. reflexivity. Qed.

(** No provenance or readlink alone is encoded as an allocation fact:
    the default remains unknown; PaEmpty is an explicit measured or
    creation-to-launch exclusion fact supplied by the launch. *)
Example no_provenance_keeps_allocation_unknown :
  pidns_alloc (mk_pidns 3 (Some 2%positive) 1 2 0) = PaUnknown /\
  pidns_alloc (pidns_with_alloc (mk_pidns 3 (Some 2%positive) 1 2 0) PaEmpty) = PaEmpty.
Proof. split; reflexivity. Qed.

(** A closed children's namespace refuses allocation after all model
    cursors advance, with no first-pid reset (kernel/pid.c:262,276-303,
    Linux v6.18.46). *)
Example closed_children_enomem : forall m,
  let st := pid_failed launch_children_state 3 in
  clone_ns_exact SIGCHLD (launch_children_model m) launch_children_ctx st 141
    = CnErr ENOMEM (pid_advanced st 3) /\
  map pidns_last (ns_pidns (pid_advanced st 3)) = [0; 9; 2] /\
  option_map pidns_alloc (find_pidns (pid_advanced st 3) 3) = Some PaClosed.
Proof. intros m. repeat split; vm_compute; reflexivity. Qed.

Print Assumptions flat_view_empty.
Print Assumptions flat_view_pidns_children.
Print Assumptions pid_advanced_flat.
Print Assumptions flat_model_pidns_updates.
Print Assumptions pid_failed_flat.
Print Assumptions pid_reset_empty_flat.
Print Assumptions pid_partial_flat.
Print Assumptions pid_partial_children_flat.
Print Assumptions clone_ns_coherent.
