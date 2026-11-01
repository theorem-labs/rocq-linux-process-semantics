(** * LinuxProcessSem.Ns.Clone — what a clone does to namespaces

    [clone_ns] is what [clone(2)] does to the namespace model, for a core
    that takes the call itself: the child's namespace context and the new
    shared namespace state, or the errno, following Linux 6.18.44
    kernel/fork.c ([copy_process]: the flag checks, [copy_creds],
    [copy_namespaces], [alloc_pid], [pdeath_signal]), kernel/cred.c
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
    declines); in the host's, the pid the core gives ([q], what the
    parent's call returns) when that is the caller's own pid namespace,
    else not recorded.  When the caller's pid namespace is one the model
    made, [q] must be the pid the model allocates there.

    The environment's refusals (ENOMEM from the allocations, ENOSPC from
    the namespace counts of the host's user namespace, EAGAIN from
    RLIMIT_NPROC or a cgroup controller, EINTR, any errno of a security
    module) are admitted for every clone the model answers; one that
    comes after [alloc_pid] leaves the pid cursors advanced
    ([pid_advanced]).  A core takes a failed clone's shared state from
    [CnErr] too. *)

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

(** A clone's answer: the child's context and the new shared state; or the
    errno and the shared state after the failure (a failure after
    [alloc_pid] leaves the pid cursors advanced); or no answer. *)
Inductive CloneNs :=
  | CnOk (child : NsCtx) (st : NsState)
  | CnErr (e : Z) (st : NsState)
  | CnUnmodeled.

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
    gives the next pid; the host's gives [q] when it is [caller_ns],
    else nothing.  [None] when a namespace has run out of pids. *)
Definition alloc_pids (chain : list PidNs) (caller_ns : positive) (q : Z)
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
        | None => if Pos.eqb (pidns_id x) caller_ns then Some ((pidns_id x, q) :: ps, ns)
                  else Some (ps, ns)
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

(** What [clone_ns] answers when the environment refuses nothing. *)
Definition clone_ns_exact (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) (q : Z) : CloneNs :=
  if negb (Z.land f (Z.lnot (Z.lor CSIGNAL clone_ns_flags)) =? 0) then CnUnmodeled
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
                  match alloc_pids chain active q with
                  | None => CnUnmodeled
                  | Some (pids, updated) =>
                      let q_ok := match find_pidns st active with
                                  | Some a => match pidns_parent a with
                                              | Some _ => match find (fun pq => Pos.eqb (fst pq) active) pids with
                                                          | Some (_, p) => p =? q
                                                          | None => false
                                                          end
                                              | None => true
                                              end
                                  | None => true
                                  end in
                      if negb q_ok then CnUnmodeled
                      else
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
                                  (cx_no_new_privs ctx) 0 (cx_dumpable ctx) in
                        CnOk child
                             (mkNsState T' U (ns_mntns st ++ new_mntns) pidns' (ns_netns st ++ new_net)
                                        (ns_sbs st) (ns_dentries st) (ns_inodes st) (ns_files st)
                                        (ns_env st))
                  end
              end
          end
    end.

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
Definition clone_ns (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) (q : Z) (o : CloneNs) : Prop :=
  o = clone_ns_exact f m ctx st q
  \/ (clone_ns_exact f m ctx st q <> CnUnmodeled
      /\ exists e st', 1 <= e <= 4095 /\ (st' = st \/ st' = pid_advanced st (cx_pidns ctx))
                       /\ o = CnErr e st').
