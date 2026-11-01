(** * LinuxProcessSem.Ns.Clone — what a clone does to namespaces

    [clone_ns] is what [clone(2)] does to the namespace model, for a core
    that takes the call itself: the child's namespace context and the new
    shared namespace state, or the errno, following Linux 6.18.44
    kernel/fork.c ([copy_process]: the flag checks, [copy_creds],
    [copy_namespaces], [alloc_pid]), kernel/cred.c
    ([copy_creds]: CLONE_NEWUSER makes a user namespace with
    [create_user_ns]), kernel/nsproxy.c ([copy_namespaces],
    [create_new_namespaces]: CAP_SYS_ADMIN over the child's user namespace,
    then the mount, UTS, IPC, pid and network namespaces in that order),
    fs/namespace.c ([copy_mnt_ns]), kernel/pid_namespace.c
    ([create_pid_namespace]) and net/core/net_namespace.c
    ([copy_net_ns]).

    The model answers clone flags made of an exit signal and CLONE_NEWNS,
    CLONE_NEWUTS, CLONE_NEWIPC, CLONE_NEWUSER, CLONE_NEWPID and
    CLONE_NEWNET, with or without CLONE_CHILD_SETTID and
    CLONE_CHILD_CLEARTID (the form a C library's [fork] uses), whose
    effects on the child's memory are the core's ([copy_process] stores
    the child's pid in its own pid namespace, [CnOk]'s first pid); any
    other flag declines.  The UTS and IPC namespaces are not in the
    tables: no modelled call reads them.

    The child's pid in each pid namespace from its own outwards: in a
    namespace a modelled call made, the next after the namespace's last
    ([alloc_pid] walks the idr cyclically; a pid at [pid_max] or above
    declines); in the host's (the outermost), [hq], the pid the core
    chooses, by which the core keys its process table.  What the parent's
    call returns is the child's pid in the caller's own pid namespace
    ([clone_ret]).

    The environment's refusals (ENOMEM from the allocations, ENOSPC from
    the namespace counts of the host's user namespace, EAGAIN from
    RLIMIT_NPROC or a cgroup controller, EINTR, any errno of a security
    module) are admitted for every clone the model answers; one that
    comes after [alloc_pid] leaves the pid cursors advanced
    ([pid_advanced]).  A core takes a failed clone's shared state from
    [CnErr] too.  A statement that names [clone_tables_failures] admits
    only the tables' failures for a clone that makes a namespace: that the
    host can make the namespaces is its environment premise. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm UserArms Net.
Import ListNotations.
Local Open Scope Z_scope.

Definition CSIGNAL : Z := 255.
Definition PID_MAX : Z := 4194304.
Definition CLONE_CHILD_CLEARTID : Z := 2097152.   (* 0x00200000 *)
Definition CLONE_CHILD_SETTID : Z := 16777216.    (* 0x01000000 *)

(** The flags the model answers: an exit signal, these six, and the two
    child-tid flags. *)
Definition clone_ns_flags : Z :=
  fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWUSER; CLONE_NEWPID;
                   CLONE_NEWNET; CLONE_CHILD_CLEARTID; CLONE_CHILD_SETTID] 0.

Definition has_flag (f k : Z) : bool := negb (Z.land f k =? 0).

Definition any_new_ns (f : Z) : bool :=
  has_flag f (fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWPID;
                               CLONE_NEWNET] 0).

Definition find_pidns (st : NsState) (p : positive) : option PidNs :=
  find (fun x => Pos.eqb (pidns_id x) p) (ns_pidns st).

(** [in_userns a b]: [b] is [a] or below it. *)
Definition in_userns (U : list UserNs) (a b : positive) : bool :=
  match find_userns U b with
  | Some x => existsb (fun y => Pos.eqb (uns_id y) a) (ancestry U x)
  | None => Pos.eqb a b
  end.

(** The pid namespaces from [p] outwards. *)
Fixpoint pidns_chain (fuel : nat) (st : NsState) (p : positive) : list PidNs :=
  match fuel with
  | O => []
  | S f => match find_pidns st p with
           | Some x => x :: match pidns_parent x with
                            | Some q => pidns_chain f st q
                            | None => []
                            end
           | None => []
           end
  end.

(** The child's pids from its own pid namespace outwards, and the pid
    namespaces with their new last pid: each namespace the model made
    gives the next pid; the host's gives [hq].  [None] when a namespace
    has run out of pids. *)
Definition alloc_pids (chain : list PidNs) (hq : Z)
    : option (list (positive * Z) * list PidNs) :=
  fold_right (fun x acc =>
    match acc with
    | None => None
    | Some (ps, ns) =>
        match pidns_parent x with
        | Some _ =>
            let p := pidns_last x + 1 in
            if PID_MAX <=? p then None
            else Some ((pidns_id x, p) :: ps,
                       mkPidNs (pidns_id x) (pidns_parent x) (pidns_owner x) (pidns_level x) p :: ns)
        | None => Some ((pidns_id x, hq) :: ps, ns)
        end
    end) (Some ([], [])) chain.

Definition replace_pidns (l : list PidNs) (x : PidNs) : list PidNs :=
  map (fun y => if Pos.eqb (pidns_id y) (pidns_id x) then x else y) l.

Definition max_pidns_id (st : NsState) : positive :=
  fold_left (fun acc x => Pos.max acc (pidns_id x)) (ns_pidns st) 1%positive.
Definition max_mntns_id (st : NsState) : positive :=
  fold_left (fun acc x => Pos.max acc (mntns_id x)) (ns_mntns st) 1%positive.
Definition max_netns_id (st : NsState) : positive :=
  fold_left (fun acc x => Pos.max acc (netns_id x)) (ns_netns st) 1%positive.

(** The child's capability sets and securebits, and its user namespace:
    with CLONE_NEWUSER a new namespace in which it holds every capability
    ([set_cred_user_ns]); else the caller's. *)
Record CloneCreds := mkCloneCreds { cc_user : positive; cc_caps : CapSets; cc_secure : Z;
                                    cc_users : list UserNs }.

Definition clone_creds (m : Model) (ctx : NsCtx) (st : NsState) (f : Z) : NsResult CloneCreds :=
  if negb (has_flag f CLONE_NEWUSER) then
    NsOk (mkCloneCreds (cx_user ctx) (cx_caps ctx) (cx_securebits ctx) (ns_userns st))
  else
    let euid := bv_unsigned (cr_euid (m_creds m)) in
    let egid := bv_unsigned (cr_egid (m_creds m)) in
    match find_userns (ns_userns st) (cx_user ctx), current_chrooted st ctx with
    | Some p, Some chrooted =>
        if Nat.ltb 32 (uns_level p) then NsErr ENOSPC
        else match ucount_check (ns_userns st) (cx_user ctx) p euid with
             | ChargeFull => NsErr ENOSPC
             | _ =>
                 if chrooted then NsErr EPERM
                 else if negb (kid_has_mapping (uns_uid_map p) euid && kid_has_mapping (uns_gid_map p) egid)
                 then NsErr EPERM
                 else match create_user_ns (ns_userns st) (cx_user ctx) euid
                                           (Z.testbit (cap_effective (cx_caps ctx)) CAP_SETFCAP) with
                      | NsOk (n, U') =>
                          NsOk (mkCloneCreds n (mkCaps CAP_FULL_SET CAP_FULL_SET 0 CAP_FULL_SET 0) 0 U')
                      | NsErr e => NsErr e
                      end
             end
    | _, _ => NsErr 0
    end.

(** A clone that takes a task out of the released world (a flat caller,
    any namespace flag) meets state the released model does not keep: the
    caller's capability sets (it derives them) and its no_new_privs bit
    and dumpable mode (it stores neither).  With CLONE_NEWUSER the child's
    sets are the new namespace's full sets whatever the caller's; without
    it the clone declines.  The child's no_new_privs bit and dumpable mode
    are then unknown. *)
Definition leaves_flat (f : Z) (ctx : NsCtx) (st : NsState) : bool :=
  flat_view ctx st && (any_new_ns f || has_flag f CLONE_NEWUSER).

(** What [clone_ns] answers when the environment refuses nothing. *)
Definition clone_ns_exact (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) (hq : Z) : CloneNs :=
  (* A task in the released world that makes no namespace: the core's own
     clone, whatever the rest of the flag word ([Ext.ext_clone_coherent]). *)
  if flat_view ctx st && negb (has_ns_bits f) then CnOk ctx st
  else if negb (Z.land f (Z.lnot (Z.lor CSIGNAL clone_ns_flags)) =? 0) then CnUnmodeled
  else if leaves_flat f ctx st && negb (has_flag f CLONE_NEWUSER) then CnUnmodeled
  else
    match clone_creds m ctx st f with
    | NsErr 0 => CnUnmodeled
    | NsErr e => CnErr e st
    | NsOk cc =>
        let U := cc_users cc in
        let cred := mkIdCred (cc_user cc) (bv_unsigned (cr_euid (m_creds m)))
                             (bv_unsigned (cr_egid (m_creds m))) (cap_effective (cc_caps cc)) in
        if any_new_ns f && negb (cap_capable U cred (cc_user cc) CAP_SYS_ADMIN) then CnErr EPERM st
        else
          (* the mount namespace *)
          let mnt_part :=
            if has_flag f CLONE_NEWNS then
              match find_mntns st (cx_mount ctx) with
              | Some old =>
                  let nid := Pos.succ (max_mntns_id st) in
                  let '(T', where_) := copy_mnt_ns (ns_mounts st) (mntns_root old) nid
                                                   (negb (Pos.eqb (cc_user cc) (mntns_owner old))) in
                  Some (nid, T', [mkMntNs nid (cc_user cc) (where_ (mntns_root old)) false], where_)
              | None => None
              end
            else Some (cx_mount ctx, ns_mounts st, [], fun i => i) in
          match mnt_part with
          | None => CnUnmodeled
          | Some (mntns, T', new_mntns, where_) =>
              (* the pid namespace *)
              let active := cx_pidns ctx in
              let pid_part :=
                if has_flag f CLONE_NEWPID then
                  match find_pidns st active with
                  | Some par =>
                      if negb (in_userns U (pidns_owner par) (cc_user cc)) then inl EINVAL
                      else if Nat.leb 32 (pidns_level par) then inl ENOSPC
                      else let nid := Pos.succ (max_pidns_id st) in
                           inr (nid, [mkPidNs nid (Some active) (cc_user cc) (S (pidns_level par)) 0])
                  | None => inl 0
                  end
                else inr (active, []) in
              match pid_part with
              | inl 0 => CnUnmodeled
              | inl e => CnErr e st
              | inr (child_ns, new_pidns) =>
                  let st_p := ns_pidns st ++ new_pidns in
                  let chain := pidns_chain (length st_p)
                                 (mkNsState [] [] [] st_p [] [] [] [] [] (ns_env st)) child_ns in
                  match alloc_pids chain hq with
                  | None => CnUnmodeled
                  | Some (pids, updated) =>
                        let pidns' := fold_left replace_pidns updated st_p in
                        (* the network namespace *)
                        let '(net, new_net) :=
                          if has_flag f CLONE_NEWNET then
                            let nid := Pos.succ (max_netns_id st) in
                            (nid, [new_netns nid (cc_user cc) (env_net_fallback (ns_env st))])
                          else (cx_net ctx, []) in
                        let child :=
                          mkNsCtx (cc_user cc) mntns child_ns net pids
                                  (where_ (fst (cx_root ctx)), snd (cx_root ctx))
                                  (where_ (fst (cx_cwd ctx)), snd (cx_cwd ctx))
                                  (cx_umask ctx) (cc_caps cc) (cc_secure cc) (cx_cloexec ctx)
                                  (if leaves_flat f ctx st then None else cx_no_new_privs ctx)
                                  (if leaves_flat f ctx st then None else cx_dumpable ctx) in
                        CnOk child
                             (mkNsState T' U (ns_mntns st ++ new_mntns) pidns' (ns_netns st ++ new_net)
                                        (ns_sbs st) (ns_dentries st) (ns_inodes st) (ns_files st)
                                        (ns_env st))
                  end
              end
          end
    end.

(** What the parent's clone returns: the child's pid in the caller's own
    pid namespace ([task_pid_vnr] of the child, seen from the parent). *)
Definition clone_ret (ctx child : NsCtx) : option Z := pid_in (cx_pids child) (cx_pidns ctx).

(** The pid namespaces the model made, from [active] outwards, each with
    its cursor one further: what an [alloc_pid] that a later failure undid
    ([free_pid] does not move the cursor) leaves. *)
Definition pid_advanced (st : NsState) (active : positive) : NsState :=
  let chain := pidns_chain (length (ns_pidns st)) st active in
  let bumped := flat_map (fun x => match pidns_parent x with
                                   | Some _ => [mkPidNs (pidns_id x) (pidns_parent x) (pidns_owner x)
                                                        (pidns_level x) (pidns_last x + 1)]
                                   | None => []
                                   end) chain in
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (fold_left replace_pidns bumped (ns_pidns st))
            (ns_netns st) (ns_sbs st) (ns_dentries st) (ns_inodes st) (ns_files st) (ns_env st).

(** The answers: the tables' answer, or one of the environment's refusals
    (an allocation failure, a namespace count of the host's user
    namespace, RLIMIT_NPROC, a cgroup controller, a pending fatal signal,
    a security module), which leaves the shared state as it was or, when
    it came after [alloc_pid], with the pid cursors advanced. *)
Definition clone_ns (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) (hq : Z) (o : CloneNs) : Prop :=
  o = clone_ns_exact f m ctx st hq
  \/ (clone_ns_exact f m ctx st hq <> CnUnmodeled
      /\ exists e st', 1 <= e <= 4095 /\ (st' = st \/ st' = pid_advanced st (cx_pidns ctx))
                       /\ o = CnErr e st').

(** A task in the released world has no pid namespace the model made
    above it, so an undone [alloc_pid] moves no cursor. *)
Lemma pid_advanced_flat : forall ctx st,
  flat_view ctx st = true -> pid_advanced st (cx_pidns ctx) = st.
Proof.
  intros ctx st H. unfold flat_view in H.
  apply andb_true_iff in H as [H Hnet]. apply andb_true_iff in H as [H Hpid].
  unfold pid_advanced.
  assert (Hb : flat_map (fun x => match pidns_parent x with
                                  | Some _ => [mkPidNs (pidns_id x) (pidns_parent x) (pidns_owner x)
                                                       (pidns_level x) (pidns_last x + 1)]
                                  | None => []
                                  end)
                        (pidns_chain (length (ns_pidns st)) st (cx_pidns ctx)) = []).
  { destruct (length (ns_pidns st)) as [|n]; [reflexivity|].
    cbn [pidns_chain]. unfold find_pidns.
    destruct (find (fun p => Pos.eqb (pidns_id p) (cx_pidns ctx)) (ns_pidns st)) as [x|] eqn:Ef;
      [|reflexivity].
    try rewrite Ef in Hpid. cbv beta iota in Hpid |- *.
    destruct (pidns_parent x) as [q|] eqn:Ep;
      [try rewrite Ep in Hpid; discriminate Hpid|].
    simpl. try rewrite Ep. reflexivity. }
  cbv zeta. rewrite Hb. cbn [fold_left]. destruct st; reflexivity.
Qed.

(** A task in the released world that makes no namespace: the clone is
    the core's own; the child gets the caller's context and the state is
    unchanged. *)
Lemma clone_ns_exact_flat_fork : forall f m ctx st hq,
  flat_view ctx st = true -> has_ns_bits f = false ->
  clone_ns_exact f m ctx st hq = CnOk ctx st.
Proof.
  intros f m ctx st hq Hf Hb. unfold clone_ns_exact. rewrite Hf, Hb. reflexivity.
Qed.

Lemma clone_ns_flat_fork_ok : forall f m ctx st hq,
  flat_view ctx st = true -> has_ns_bits f = false ->
  clone_ns f m ctx st hq (CnOk ctx st).
Proof.
  intros f m ctx st hq Hf Hb. left. symmetry. apply clone_ns_exact_flat_fork; assumption.
Qed.

(** [Ext.ext_clone_coherent] for [clone_ns]. *)
Lemma clone_ns_coherent : forall f m ctx st hq o,
  flat_view ctx st = true -> has_ns_bits f = false ->
  (clone_ns f m ctx st hq o <-> released_clone ctx st o).
Proof.
  intros f m ctx st hq o Hf Hb. unfold clone_ns, released_clone.
  rewrite (clone_ns_exact_flat_fork f m ctx st hq Hf Hb), (pid_advanced_flat ctx st Hf).
  split.
  - intros [Ho | (_ & e & st' & He & Hst & Ho)]; [left; exact Ho|].
    right. exists e. split; [exact He|]. destruct Hst as [-> | ->]; exact Ho.
  - intros [Ho | (e & He & Ho)]; [left; exact Ho|].
    right. split; [intros Hc; discriminate Hc|].
    exists e, st. split; [exact He | split; [left; reflexivity | exact Ho]].
Qed.

(** The clone failures of a run in which THE HOST CAN MAKE THE NAMESPACES:
    an ENVIRONMENT PREMISE of every statement that names this
    [Ext.CloneEnv].  A clone that makes a namespace, or one by a task
    outside the released world, fails only as the tables say
    ([clone_ns_exact]: EPERM, EINVAL, ENOSPC from the model's own
    namespaces); a run in which the host refuses on an allocation, a
    namespace count, a cgroup controller, RLIMIT_NPROC, a pending fatal
    signal or a security module is outside such a statement.  The released
    clone (a task in the released world, a word with no namespace bit)
    keeps every failure the core admits. *)
Definition clone_tables_failures : CloneEnv := fun f m ctx st hq e st' =>
  (flat_view ctx st && negb (has_ns_bits f)) = true \/ CnErr e st' = clone_ns_exact f m ctx st hq.

(** In the released world, for a word with no namespace bit, it admits
    every failure. *)
Lemma clone_tables_failures_flat : forall f m ctx st hq e st',
  flat_view ctx st = true -> has_ns_bits f = false -> clone_tables_failures f m ctx st hq e st'.
Proof. intros f m ctx st hq e st' Hf Hb. left. rewrite Hf, Hb. reflexivity. Qed.
