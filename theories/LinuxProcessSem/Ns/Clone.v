(** * LinuxProcessSem.Ns.Clone — what a clone does to namespaces

    [clone_ns] is what [clone(2)] does to the namespace model, for a core
    that takes the call itself: the child's namespace context and the new
    shared namespace state, or the errno, following Linux v6.18.46
    kernel/fork.c ([copy_process]: the flag checks, [copy_creds],
    [copy_namespaces], [alloc_pid]), kernel/cred.c
    ([copy_creds]: CLONE_NEWUSER makes a user namespace with
    [create_user_ns]), kernel/nsproxy.c ([copy_namespaces],
    [create_new_namespaces]: CAP_SYS_ADMIN over the child's user namespace,
    then the mount, UTS, IPC, pid and network namespaces in that order),
    fs/namespace.c ([copy_mnt_ns]), kernel/pid_namespace.c
    ([create_pid_namespace]) and net/core/net_namespace.c
    ([copy_net_ns]).

    The clone's input is what the core decodes ([Fork.CloneIn]): the
    argument record of [clone]'s registers or of a [clone3] struct, or no
    record.  A record the argument checks of [kernel_clone] and
    [copy_process] refuse ([Fork.clone_arg_checks]) answers -EINVAL.
    Otherwise, in the namespace world the model answers SIGCHLD alone or
    with CLONE_NEWNS, CLONE_NEWUTS, CLONE_NEWIPC, CLONE_NEWUSER,
    CLONE_NEWPID and CLONE_NEWNET, and no other bit of the namespace
    flags, and with bits of [Fork.clone_extra_bits] ([CLONE_SYSVSEM] and
    the four tid bits [CLONE_PARENT_SETTID], [CLONE_CHILD_SETTID],
    [CLONE_CHILD_CLEARTID], [CLONE_SETTLS]): the wider mask is
    [clone_ns_ext_flags].  [CLONE_NEWIPC] with [CLONE_SYSVSEM] is
    refused by [copy_namespaces] (kernel/nsproxy.c:161-162, 171-173,
    Linux v6.18.46) and answers -EINVAL.  The core's
    [CLONE_CHILD_SETTID] store writes the child's own pid
    ([child_tid_value]).  Linux's
    [copy_process] stores the tid pointers (kernel/fork.c:2040,2044);
    [schedule_tail] writes the child's pid (kernel/sched/core.c:5272-5273),
    and [mm_release] clears it (kernel/fork.c:1436-1447), v6.18.46.
    The IPC namespace is not in the tables: no modelled call reads it.

    With CLONE_NEWUTS the child gets a new UTS namespace (Linux v6.18.46:
    [copy_utsname], kernel/utsname.c:79-94, called by
    [create_new_namespaces] at kernel/nsproxy.c:84, and [clone_uts_ns],
    kernel/utsname.c:36-71).  Its owner is the child's user namespace
    ([copy_namespaces] passes the child's [task_cred_xxx(tsk, user_ns)],
    kernel/nsproxy.c:150 and :175, which is the new one when CLONE_NEWUSER
    is set too; kernel/utsname.c:60), and it holds the caller's UTS
    namespace's names as they are ([clone_uts_ns] copies the whole
    [ns->name], kernel/utsname.c:59): a name still the pin's stays so.  Its
    failures, ENOSPC from [inc_uts_namespaces] (:43-46), ENOMEM (:48-51)
    and [ns_common_init]'s (:53-55), are among the environment's refusals
    below.  Without CLONE_NEWUTS the child shares the caller's UTS
    namespace ([copy_utsname], :87-88).

    The child is allocated in [pidns_children], or in its new child when
    CLONE_NEWPID is set.  A children's namespace that is neither the active
    namespace nor below it declines: Linux never holds one
    ([pidns_install], [copy_pid_ns]).  Its pids run from its own namespace outwards:
    each model-held level gives the next pid under the clear-range and
    no-outside-allocation launch facts, below its measured limit; the host gives [hq], the pid the core
    chooses, by which the core keys its process table.  What the parent's
    call returns is the child's pid in the caller's own pid namespace
    ([clone_ret]).

    The environment's refusals (ENOMEM from the allocations, ENOSPC from
    the namespace counts of the host's user namespace, EAGAIN from
    RLIMIT_NPROC or a cgroup controller, EINTR, and the failures of every
    namespace's init function, which cannot be listed with confidence: any
    errno) are admitted for every clone the model answers.  A partial
    allocation leaves [pid_partial]; one after complete allocation leaves
    [pid_failed], closing each empty namespace whose first pid is freed.
    A core takes a failed clone's shared state from
    [CnErr] too.  A statement that names [clone_tables_failures] admits
    only the tables' failures for a clone that makes a namespace: that the
    host can make the namespaces is its environment premise. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Propagation Userns Walk Arm UserArms Net.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Fork.
Import ListNotations.
Local Open Scope Z_scope.

Definition CSIGNAL : Z := 255.
Definition CLONE_CHILD_CLEARTID : Z := 2097152.   (* 0x00200000 *)
Definition CLONE_CHILD_SETTID : Z := 16777216.    (* 0x01000000 *)

(** Namespace flags the model answers; the exit signal is SIGCHLD. *)
Definition clone_ns_flags : Z :=
  fold_left Z.lor [CLONE_NEWNS; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWUSER; CLONE_NEWPID;
                   CLONE_NEWNET] 0.


(** The namespace flags widened with the core's extra bits:
    [CLONE_SYSVSEM] and the four tid bits.  A record whose flags have
    no bit outside this mask and whose exit signal is SIGCHLD is one
    [Fork.clone_class] classifies. *)
Definition clone_ns_ext_flags : Z := Z.lor clone_ns_flags Fork.clone_extra_bits.
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

(** [pidns_below st a c]: the pid namespace [a] is in the chain of [c],
    that is [c] is [a] or below it in the tables. *)
Definition pidns_below (st : NsState) (a c : positive) : bool :=
  existsb (fun x => Pos.eqb (pidns_id x) a) (pidns_chain (length (ns_pidns st)) st c).

(** The child's pids from its own namespace outwards.  Every model level
    needs its clear-range launch fact, no outside allocator/control write,
    and a next pid below its measured limit.  [initialize] marks empty
    namespaces initialized on success; it is false for a closed-namespace
    failure, which advances cursors without changing allocation states.
    The host's pid remains the core's [hq]. *)
Definition alloc_pids (outside initialize : bool) (chain : list PidNs) (hq : Z)
    : option (list (positive * Z) * list PidNs) :=
  fold_right (fun x acc =>
    match acc with
    | None => None
    | Some (ps, ns) =>
        match pidns_parent x with
        | Some _ =>
            let p := pidns_last x + 1 in
            if outside || negb (pidns_cursor_clear x) || (pidns_max x <=? p) then None
            else Some ((pidns_id x, p) :: ps,
                       pidns_with_last_alloc x p
                         (match pidns_alloc x with
                          | PaEmpty => if initialize then PaInit else PaEmpty
                          | a => a end) :: ns)
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
Definition max_utsns_id (st : NsState) : positive :=
  fold_left (fun acc x => Pos.max acc (utsns_id x)) (ns_utsns st) 1%positive.

(** The new UTS namespace [nid] a clone with CLONE_NEWUTS makes for a
    child in user namespace [owner]: the caller's UTS namespace's names,
    the pin's ([None]) where the tables do not hold it. *)
Definition new_utsns (st : NsState) (ctx : NsCtx) (nid owner : positive) : UtsNs :=
  match find_utsns st (cx_uts ctx) with
  | Some u => mkUtsNs nid owner (utsns_nodename u) (utsns_domainname u)
  | None => mkUtsNs nid owner None None
  end.

(** The child's capability sets and securebits, and its user namespace:
    with CLONE_NEWUSER a new namespace in which it holds every capability
    ([set_cred_user_ns]); else the caller's. With CLONE_NEWUSER the level
    and count ENOSPC checks come before the chroot test
    (kernel/user_namespace.c:91-107, v6.18.46). No answer ([NsErr 0])
    when the tables lack the caller's user namespace, or, after those
    checks pass, do not decide whether it is chrooted
    ([UserArms.current_chrooted]: absent mount namespace/root, or an open
    mount of the root stack). *)
Record CloneCreds := mkCloneCreds { cc_user : positive; cc_caps : CapSets; cc_secure : Z;
                                    cc_users : list UserNs }.

Definition clone_creds (m : Model) (ctx : NsCtx) (st : NsState) (f : Z) : NsResult CloneCreds :=
  if negb (has_flag f CLONE_NEWUSER) then
    NsOk (mkCloneCreds (cx_user ctx) (cx_caps ctx) (cx_securebits ctx) (ns_userns st))
  else
    let euid := bv_unsigned (cr_euid (m_creds m)) in
    let egid := bv_unsigned (cr_egid (m_creds m)) in
    match find_userns (ns_userns st) (cx_user ctx) with
    | Some p =>
        if Nat.ltb 32 (uns_level p) then NsErr ENOSPC
        else match ucount_check (ns_userns st) (cx_user ctx) p euid with
             | ChargeFull => NsErr ENOSPC
             | _ =>
                 match current_chrooted st ctx with
                 | None => NsErr 0
                 | Some true => NsErr EPERM
                 | Some false =>
                     if negb (kid_has_mapping (uns_uid_map p) euid && kid_has_mapping (uns_gid_map p) egid)
                     then NsErr EPERM
                     else match create_user_ns (ns_userns st) (cx_user ctx) euid
                                               (Z.testbit (cap_effective (cx_caps ctx)) CAP_SETFCAP) with
                          | NsOk (n, U') =>
                              NsOk (mkCloneCreds n (mkCaps CAP_FULL_SET CAP_FULL_SET 0 CAP_FULL_SET 0) 0 U')
                          | NsErr e => NsErr e
                          end
                 end
             end
    | None => NsErr 0
    end.

(** A clone that takes a task out of the released world (a flat caller,
    any namespace flag) meets state the released model does not keep: the
    caller's capability sets (it derives them).  With CLONE_NEWUSER the
    child's sets are the new namespace's full sets whatever the caller's;
    without it the clone declines.  The no-new-privs bit and the dumpable
    mode are the released model's and the child's process record copies
    them ([Procs.child_proc]). *)
Definition leaves_flat (f : Z) (ctx : NsCtx) (st : NsState) : bool :=
  flat_view ctx st && (any_new_ns f || has_flag f CLONE_NEWUSER).

(** What the parent's clone returns: the child's pid in the caller's own
    pid namespace ([task_pid_vnr] of the child, seen from the parent). *)
Definition clone_ret (ctx child : NsCtx) : option Z := pid_in (cx_pids child) (cx_pidns ctx).

(** The child's own pid: its pid in its own pid namespace, the value the
    [CLONE_CHILD_SETTID] store writes at [schedule_tail]
    (kernel/sched/core.c:5272-5273, Linux v6.18.46).  Without
    [CLONE_NEWPID] (which [Fork.child_tid_ok] excludes with
    [CLONE_CHILD_SETTID]) this equals [clone_ret], the caller's answer,
    because the child shares the caller's pid namespace. *)
Definition child_tid_value (child : NsCtx) : option Z :=
  pid_in (cx_pids child) (cx_pidns child).

(** The tables' answer for a clone flag word [f] (the record's flags, no
    exit signal) that the namespace mask and the SIGCHLD test of
    [clone_ns_exact] passed.  The parent's return value is the core's pid
    for a caller in the released world (its pid namespace is the host's,
    where the core's pid is the child's), and [clone_ret] otherwise. *)
Definition clone_ns_answer (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) (hq : Z) : CloneNs :=
  if leaves_flat f ctx st && negb (has_flag f CLONE_NEWUSER) then CnUnmodeled
  else
    match clone_creds m ctx st f with
    | NsErr 0 => CnUnmodeled
    | NsErr e => CnErr e st
    | NsOk cc =>
        let U := cc_users cc in
        let cred := mkIdCred (cc_user cc) (bv_unsigned (cr_euid (m_creds m)))
                             (bv_unsigned (cr_egid (m_creds m))) (cap_effective (cc_caps cc)) in
        if any_new_ns f && negb (cap_capable U cred (cc_user cc) CAP_SYS_ADMIN) then CnErr EPERM st
        (* [CLONE_NEWIPC] with [CLONE_SYSVSEM]: [copy_namespaces] refuses
           the pair after the capability gate (kernel/nsproxy.c:162,
           172-173, Linux v6.18.46). *)
        else if has_flag f CLONE_NEWIPC && has_flag f CLONE_SYSVSEM then CnErr EINVAL st
        else
          (* the mount namespace, and the order data of its copies
             ([Propagation.copy_ns_links]) *)
          let mnt_part :=
            if has_flag f CLONE_NEWNS then
              match find_mntns st (cx_mount ctx) with
              | Some old =>
                  let nid := Pos.succ (max_mntns_id st) in
                  let other := negb (Pos.eqb (cc_user cc) (mntns_owner old)) in
                  let '(T', where_) := copy_mnt_ns (ns_mounts st) (mntns_root old) nid other in
                  Some (nid, T', [mk_mntns nid (cc_user cc) (where_ (mntns_root old)) false], where_,
                        copy_ns_links st (mntns_root old) other)
              | None => None
              end
            else Some (cx_mount ctx, ns_mounts st, [], fun i => i, ns_prop st) in
          match mnt_part with
          | None => CnUnmodeled
          | Some (mntns, T', new_mntns, where_, links) =>
              (* the pid namespace *)
              let active := cx_pidns ctx in
              let children := pidns_children ctx in
              let pid_part :=
                if has_flag f CLONE_NEWPID then
                  (* [copy_pid_ns] refuses a new pid namespace unless the
                     children's namespace is the active one
                     (kernel/pid_namespace.c:180-181, Linux v6.18.46). *)
                  if negb (Pos.eqb children active) then inl EINVAL else
                  match find_pidns st active with
                  | Some par =>
                      if negb (in_userns U (pidns_owner par) (cc_user cc)) then inl EINVAL
                      else if Nat.leb 32 (pidns_level par) then inl ENOSPC
                      else let nid := Pos.succ (max_pidns_id st) in
                           inr (nid, [fresh_pidns nid children (cc_user cc) (S (pidns_level par))], false)
                  | None => inl 0
                  end
                else if Pos.eqb children active then inr (children, [], false)
                (* Linux keeps the children's namespace at the active one or
                   below it: [pidns_install] refuses any other
                   (kernel/pid_namespace.c:419-420) and [copy_pid_ns] makes
                   a child of the active one (:175-183), Linux v6.18.46.
                   The model declines the state Linux never reaches. *)
                else if negb (pidns_below st active children) then inl 0
                else match find_pidns st children with
                     | Some p => match pidns_alloc p with
                       | PaEmpty => if pidns_last p =? 0 then inr (children, [], false) else inl 0
                       | PaClosed => inr (children, [], true)
                       | PaInit | PaUnknown => inl 0
                       end
                     | None => inl 0
                     end in
              match pid_part with
              | inl 0 => CnUnmodeled
              | inl e => CnErr e st
              | inr (child_ns, new_pidns, closed) =>
                  let st_p := ns_pidns st ++ new_pidns in
                  let chain := pidns_chain (length st_p) (with_pidns st st_p) child_ns in
                  match alloc_pids (ns_outside_pids st) (negb closed) chain hq with
                  | None => CnUnmodeled
                  | Some (pids, updated) =>
                        let pidns' := fold_left replace_pidns updated st_p in
                        (* PIDNS_ADDING is checked only after all ids have
                           been allocated (kernel/pid.c:262,276-303,
                           Linux v6.18.46).  Closed namespaces do not reset. *)
                        if closed then CnErr ENOMEM (with_pidns st pidns') else
                        (* the network namespace *)
                        let '(net, new_net) :=
                          if has_flag f CLONE_NEWNET then
                            let nid := Pos.succ (max_netns_id st) in
                            (nid, [new_netns nid (cc_user cc) (env_net_fallback (ns_env st))])
                          else (cx_net ctx, []) in
                        (* the UTS namespace *)
                        let '(uts, new_uts) :=
                          if has_flag f CLONE_NEWUTS then
                            let nid := Pos.succ (max_utsns_id st) in
                            (nid, [new_utsns st ctx nid (cc_user cc)])
                          else (cx_uts ctx, []) in
                        (* the child's context: the caller's, with what the
                           clone changes *)
                        let child := with_user_ns ctx (cc_user cc) in
                        let child := with_mount_ns child mntns in
                        let child := with_pid_ns child child_ns in
                        let child := with_active_pidns_children child in
                        let child := with_net_ns child net in
                        let child := with_uts_ns child uts in
                        let child := with_pids child pids in
                        let child := with_root child (where_ (fst (cx_root ctx)), snd (cx_root ctx)) in
                        let child := with_cwd child (where_ (fst (cx_cwd ctx)), snd (cx_cwd ctx)) in
                        let child := with_caps child (cc_caps cc) in
                        let child := with_securebits child (cc_secure cc) in
                        let st' := with_ns_prop (with_mounts st T') links in
                        let st' := with_userns st' U in
                        let st' := with_mntns st' (ns_mntns st ++ new_mntns) in
                        (* A copy of a listed real namespace is exposed too. *)
                        let st' :=
                          if has_flag f CLONE_NEWNS then
                            match find_mntns st (cx_mount ctx) with
                            | Some old =>
                                if negb (mntns_anon old) &&
                                   mem (cx_mount ctx) (env_entered_mntns (ns_env st))
                                then with_entered_mntns st'
                                       (mntns :: env_entered_mntns (ns_env st))
                                else st'
                            | None => st'
                            end
                          else st' in
                        let st' := with_pidns st' pidns' in
                        let st' := with_netns st' (ns_netns st ++ new_net) in
                        let st' := with_utsns st' (ns_utsns st ++ new_uts) in
                        CnOk child (if flat_view ctx st then None else clone_ret ctx child) st'
                  end
              end
          end
    end.

(** What [clone_ns] answers when the environment refuses nothing, for the
    clone's input ([Fork.CloneIn]):
    - a task in the released world whose clone makes no namespace
      ([Ext.makes_ns]): the core's own clone, whatever the rest of the
      record ([Ext.ext_clone_coherent]).  A record the argument checks
      refuse makes no namespace, so there the core's own -EINVAL stands;
    - a call the core does not answer from a record ([Fork.CiNoArgs]:
      among them a [clone3] whose own tests refuse its struct, or whose
      struct cannot be copied): the core's own answer, with no namespace
      change;
    - otherwise the record.  A record the argument checks refuse
      ([Fork.clone_arg_checks]) answers -EINVAL with the state
      unchanged: those checks come before every other step of
      [copy_process] (kernel/fork.c:1951-1999, and [kernel_clone]'s K0
      at 2588-2591, Linux v6.18.46), so before [copy_creds] and
      [copy_namespaces] (2188).  Then the wider mask [clone_ns_ext_flags]
      reads its flags and the SIGCHLD test its exit signal, then
      [clone_ns_answer] its flags; there [CLONE_NEWIPC] with
      [CLONE_SYSVSEM] answers -EINVAL after the capability gate
      ([copy_namespaces], kernel/nsproxy.c:162, 172-173, Linux
      v6.18.46). *)
Definition clone_ns_exact (f : Fork.CloneIn) (m : Model) (ctx : NsCtx) (st : NsState) (hq : Z)
    : CloneNs :=
  if flat_view ctx st && negb (makes_ns f) then CnOk ctx None st
  else match f with
  | Fork.CiNoArgs => CnOk ctx None st
  | Fork.CiArgs r =>
      if Fork.clone_arg_checks r then CnErr EINVAL st
      else if negb (Z.land (Fork.cla_flags r) (Z.lnot clone_ns_ext_flags) =? 0) then CnUnmodeled
      else if negb (Fork.cla_exit_signal r =? Fork.SIGCHLD) then CnUnmodeled
      else clone_ns_answer (Fork.cla_flags r) m ctx st hq
  end.

(** A call with no record is the core's own in either world. *)
Lemma clone_ns_exact_no_args : forall m ctx st hq,
  clone_ns_exact Fork.CiNoArgs m ctx st hq = CnOk ctx None st.
Proof.
  intros m ctx st hq. unfold clone_ns_exact. destruct (flat_view ctx st); reflexivity.
Qed.

(** The namespace mask and signal tests imply the core's gate.  This is
    derived from the masks, not another test in [clone_ns_exact]. *)
Lemma clone_ns_mask_core_gate : forall flags,
  Z.land (bv_unsigned flags) (Z.lnot (Z.lor CSIGNAL clone_ns_flags)) = 0 ->
  Z.land (bv_unsigned flags) CSIGNAL = Fork.SIGCHLD ->
  Fork.clone_fork_flags_b flags = true \/ Fork.clone_ns_flags_b flags = true.
Proof.
  intros flags Hmask Hsignal.
  assert (Hcover : bv_unsigned flags =
      Z.land (bv_unsigned flags) (Z.lor CSIGNAL clone_ns_flags)).
  { rewrite <- (Z.land_m1_r (bv_unsigned flags)) at 1.
    rewrite <- (Z.lor_lnot_diag (Z.lor CSIGNAL clone_ns_flags)),
      Z.land_lor_distr_r, Hmask, Z.lor_0_r. reflexivity. }
  assert (Hout : Z.land (bv_unsigned flags) (Z.lnot Fork.clone_ns_mask) = Fork.SIGCHLD).
  { rewrite Hcover at 1. rewrite <- Z.land_assoc.
    change (Z.land (bv_unsigned flags) CSIGNAL = Fork.SIGCHLD).
    exact Hsignal. }
  destruct (Z.eqb (Z.land (bv_unsigned flags) Fork.clone_ns_mask) 0) eqn:Hns.
  - apply Z.eqb_eq in Hns. left. unfold Fork.clone_fork_flags_b, bv_eqb.
    assert (Hword : bv_unsigned flags = Fork.SIGCHLD).
    { rewrite <- (Z.land_m1_r (bv_unsigned flags)),
        <- (Z.lor_lnot_diag Fork.clone_ns_mask), Z.land_lor_distr_r,
        Hns, Hout, Z.lor_0_l. reflexivity. }
    rewrite Hword. reflexivity.
  - right. unfold Fork.clone_ns_flags_b. rewrite Hout, Z.eqb_refl, Hns. reflexivity.
Qed.

(** Every answered [clone] (220) outside the released no-namespace fast
    path whose decoded record the argument checks pass is a record the
    core classifies ([Fork.clone_class]): a fork-image record, a
    namespace record, or the refused [CLONE_NEWIPC] with
    [CLONE_SYSVSEM] record.  That fast path remains unrestricted, as
    [Ext.ext_clone_coherent] requires.  A record the checks refuse is
    answered -EINVAL ([clone_ns_exact_arg_checks]).

    THE CALLS WITH NO RECORD are guarded elsewhere, because this gate
    says nothing about them: [Procs.clone_success_has_record] is the
    theorem that the core resolves none of them successfully, so the
    core's own answer that [clone_ns_exact Fork.CiNoArgs] gives
    ([clone_ns_exact_no_args]) can create no child. *)
Theorem clone_ns_exact_core_gate : forall r m ctx st hq,
  Fork.clone_arg_checks r = false ->
  (flat_view ctx st && negb (makes_ns (Fork.CiArgs r))) = false ->
  clone_ns_exact (Fork.CiArgs r) m ctx st hq <> CnUnmodeled ->
  Fork.clone_class r <> Fork.CcNone.
Proof.
  intros r m ctx st hq Hc Hfast Hanswer Hclass.
  (* Step 1: unfold clone_ns_exact and use Hanswer to extract the mask
     and signal hypotheses. *)
  unfold clone_ns_exact in Hanswer. rewrite Hfast in Hanswer. cbv beta iota in Hanswer.
  rewrite Hc in Hanswer.
  destruct (negb (Z.land (Fork.cla_flags r) (Z.lnot clone_ns_ext_flags) =? 0))
    eqn:Hmask; [apply Hanswer; reflexivity|].
  destruct (negb (Fork.cla_exit_signal r =? Fork.SIGCHLD))
    eqn:Hsignal; [apply Hanswer; reflexivity|].
  apply negb_false_iff in Hmask, Hsignal. apply Z.eqb_eq in Hmask, Hsignal.
  (* Step 2: unfold clone_class and discharge its first two branches. *)
  unfold Fork.clone_class in Hclass.
  rewrite Hsignal, Z.eqb_refl in Hclass. cbn [negb] in Hclass.
  (* Step 3: the wider mask implies no bit outside extra|ns_mask.
     The constant fact: clone_ns_ext_flags ⊆ extra | ns_mask. *)
  assert (Hcov : Z.land clone_ns_ext_flags
    (Z.lnot (Z.lor Fork.clone_extra_bits Fork.clone_ns_mask)) = 0)
    by (vm_compute; reflexivity).
  assert (Hext : Fork.clone_has (Fork.cla_flags r)
    (Z.lnot (Z.lor Fork.clone_extra_bits Fork.clone_ns_mask)) = false).
  { unfold Fork.clone_has. apply negb_false_iff. apply Z.eqb_eq.
    (* ext_flags ⊆ extra|mask, so lnot(extra|mask) ⊆ lnot(ext_flags). *)
    assert (Hmon : Z.lnot (Z.lor Fork.clone_extra_bits Fork.clone_ns_mask) =
      Z.land (Z.lnot clone_ns_ext_flags)
             (Z.lnot (Z.lor Fork.clone_extra_bits Fork.clone_ns_mask)))
      by (vm_compute; reflexivity).
    rewrite Hmon. rewrite Z.land_assoc. rewrite Hmask. apply Z.land_0_l. }
  rewrite Hext in Hclass. cbn [negb] in Hclass.
  (* Step 4: after the first two CcNone tests pass, clone_class is not CcNone. *)
  destruct (negb (Fork.clone_has (Fork.cla_flags r) Fork.clone_ns_mask)) eqn:Hns;
    rewrite Hns in Hclass; cbn in Hclass;
    [| destruct (Fork.clone_has (Fork.cla_flags r) CLONE_NEWIPC
                 && Fork.clone_has (Fork.cla_flags r) CLONE_SYSVSEM) eqn:Hipc;
       rewrite Hipc in Hclass; cbn in Hclass];
    exact (Hclass eq_refl).
Qed.

(** A record the argument checks refuse ([Fork.clone_arg_checks]),
    outside the released fast path, answers exactly -EINVAL with the
    state unchanged.  For example CLONE_SIGHAND without CLONE_VM:
    [copy_process] returns -EINVAL (kernel/fork.c:1969-1970, Linux
    v6.18.46) before any other step, so before [copy_namespaces]. *)
Theorem clone_ns_exact_arg_checks : forall r m ctx st hq,
  (flat_view ctx st && negb (makes_ns (Fork.CiArgs r))) = false ->
  Fork.clone_arg_checks r = true ->
  clone_ns_exact (Fork.CiArgs r) m ctx st hq = CnErr EINVAL st.
Proof.
  intros r m ctx st hq Hfast Hc.
  unfold clone_ns_exact. rewrite Hfast. cbv beta iota. rewrite Hc. reflexivity.
Qed.

(** THE CORE GATE, FOR EVERY DECODED [clone] (220) WORD.  No answered
    word bypasses the core: it is a record the core classifies
    ([Fork.clone_class]) or the one the core itself answers -EINVAL
    ([Fork.clone_legacy_einval_b], which [Fork.clone_einval] answers).
    The first disjunct alone is [clone_ns_exact_core_gate], for a
    record the checks pass. *)
Theorem clone_ns_exact_core_gate_word : forall r m ctx st hq,
  (flat_view ctx st && negb (makes_ns (Fork.CiArgs r))) = false ->
  clone_ns_exact (Fork.CiArgs r) m ctx st hq <> CnUnmodeled ->
  Fork.clone_class r <> Fork.CcNone
  \/ Fork.clone_arg_checks r = true.
Proof.
  intros r m ctx st hq Hfast Hanswer.
  destruct (Fork.clone_arg_checks r) eqn:Hc.
  - right. reflexivity.
  - left. exact (clone_ns_exact_core_gate r m ctx st hq Hc Hfast Hanswer).
Qed.


Definition bump_pid_cursor (x : PidNs) : list PidNs :=
  match pidns_parent x with
  | Some _ => [pidns_with_last x (pidns_last x + 1)]
  | None => []
  end.

(** The model-held pid namespaces, from [active] outwards, with cursors
    advanced and allocation states unchanged.  This is the cursor effect
    alone; freeing a completed first allocation uses [pid_failed]. *)
Definition pid_advanced (st : NsState) (active : positive) : NsState :=
  let chain := pidns_chain (length (ns_pidns st)) st active in
  let bumped := flat_map bump_pid_cursor chain in
  with_pidns st (fold_left replace_pidns bumped (ns_pidns st)).

(** After successful alloc_pid, freeing a first pid closes that namespace
    (kernel/pid.c:136-139, v6.18.46), without resetting its cursor. *)
Definition pid_failure_record (p : PidNs) : PidNs :=
  pidns_with_last_alloc p (pidns_last p + 1)
    (match pidns_alloc p with PaEmpty => PaClosed | a => a end).

Definition pid_failed (st : NsState) (active : positive) : NsState :=
  let chain := pidns_chain (length (ns_pidns st)) st active in
  let bumped := flat_map (fun p => match pidns_parent p with
    | Some _ => [pid_failure_record p] | None => [] end) chain in
  with_pidns st (fold_left replace_pidns bumped (ns_pidns st)).

(** out_free resets an empty innermost namespace, not its ancestors
    (kernel/pid.c:301-303).  The host's cursor is not represented. *)
Definition pid_reset_empty (st : NsState) (active : positive) : NsState :=
  match find_pidns st active with
  | Some p => match pidns_parent p, pidns_alloc p with
              | Some _, PaEmpty => with_pidns st (replace_pidns (ns_pidns st) (pidns_with_last p 0))
              | _, _ => st
              end
  | None => st
  end.

Definition pid_partial (st : NsState) (active : positive) (k : nat) : NsState :=
  let chain := firstn k (pidns_chain (length (ns_pidns st)) st active) in
  let bumped := flat_map bump_pid_cursor chain in
  pid_reset_empty (with_pidns st (fold_left replace_pidns bumped (ns_pidns st))) active.

(** Earlier table errors, from copy_creds or copy_namespaces, stop before
    alloc_pid (kernel/fork.c:2054-2056, 2188-2208).  In a closed namespace,
    cursor-moving failures are only the allocator's ENOMEM or EAGAIN;
    its final ENOMEM prevents later failure sites (kernel/pid.c:238-303,
    Linux v6.18.46). *)
Definition clone_pid_failure_can_move (o : CloneNs) (en : Z) : bool :=
  match o with
  | CnOk _ _ _ => true
  | CnErr e _ => (e =? ENOMEM) && ((en =? ENOMEM) || (en =? EAGAIN))
  | CnUnmodeled => false
  end.

(** The answers for a record: the tables' answer, or one of the
    environment's refusals (an allocation failure, a namespace count of
    the host's user namespace, RLIMIT_NPROC, a cgroup controller, a
    pending fatal signal, a namespace's init function).  Cursor movement
    requires that the tables reach pid allocation.  For a closed namespace
    only an allocation's ENOMEM or EAGAIN can have moved cursors; its final
    ENOMEM prevents reaching later failure sites (kernel/pid.c:238-303,
    Linux v6.18.46).  A partial allocation resets an empty innermost
    namespace's cursor; freeing a completed first allocation closes it.
    A call with no record ([Fork.CiNoArgs]) is the core's own: any errno,
    with the namespace state unchanged ([Ext.released_clone]).  Such a
    call never reaches [alloc_pid] in this model, for one of two reasons.

    Either it FAILS before [copy_process]: a [clone3] whose own tests
    refuse its struct ([Fork.clone3_pre] gives [Fork.CdErr]), or one
    whose [uargs] range [access_ok] refuses, which is -EFAULT before a
    field is read.

    Or THE CORE DECLINES IT, which is what happens to every other call
    without a record, the ones Linux would take into [copy_process]
    among them.  The whole set, from [Procs.clone_in_of]: a [clone]
    (220) a0 with a bit above 31 (the raw-input guard of
    [Fork.clone_args_of_clone]); a [clone3] (435) of any size but
    [Fork.CLONE_ARGS_SIZE]; a [clone3] whose range [access_ok] admits
    and whose memory does not wholly back it (a DECLINE, not a failure:
    which bytes Linux read before it faulted is not something the ledger
    can state); a [clone3] struct [clone3_pre] declines -- a non-zero
    [set_tid], CLONE_INTO_CGROUP or CLONE_NEWTIME; and every [clone3]
    record that is neither the fork image ([Fork.clone3_fork_args_b]),
    nor refused by the argument checks, nor in [Fork.clone_class]'s fork
    class, for example CLONE_VM alone or a namespace bit.

    Those declines are what makes the core's own answer sound here: the
    core resolves no call without a record
    ([Procs.clone_success_has_record]), so none of them creates a
    child. *)
Definition clone_ns (f : Fork.CloneIn) (m : Model) (ctx : NsCtx) (st : NsState) (hq : Z)
    (o : CloneNs) : Prop :=
  match f with
  | Fork.CiNoArgs => released_clone ctx st o
  | Fork.CiArgs _ =>
      o = clone_ns_exact f m ctx st hq
      \/ (clone_ns_exact f m ctx st hq <> CnUnmodeled
          /\ exists e st', 1 <= e <= 4095
              /\ (st' = st \/ (clone_pid_failure_can_move (clone_ns_exact f m ctx st hq) e = true
                  /\ (st' = pid_failed st (pidns_children ctx)
                      \/ exists k, (k < length (pidns_chain (length (ns_pidns st)) st (pidns_children ctx)))%nat
                            /\ st' = pid_partial st (pidns_children ctx) k)))
                           /\ o = CnErr e st')
  end.

(** A task in the released world has no pid namespace the model made
    above it, so an undone [alloc_pid] moves no cursor. *)
Lemma pid_advanced_flat : forall ctx st,
  flat_view ctx st = true -> pid_advanced st (cx_pidns ctx) = st.
Proof.
  intros ctx st H. unfold flat_view in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hnet]. apply andb_true_iff in H as [H Hpid].
  unfold pid_advanced.
  assert (Hb : flat_map bump_pid_cursor
      (pidns_chain (length (ns_pidns st)) st (cx_pidns ctx)) = []).
  { unfold bump_pid_cursor. destruct (length (ns_pidns st)) as [|n]; [reflexivity|].
    cbn [pidns_chain]. unfold find_pidns.
    destruct (find (fun p => Pos.eqb (pidns_id p) (cx_pidns ctx)) (ns_pidns st)) as [x|] eqn:Ef;
      [|reflexivity].
    try rewrite Ef in Hpid. cbv beta iota in Hpid |- *.
    destruct (pidns_parent x) as [q|] eqn:Ep;
      [try rewrite Ep in Hpid; discriminate Hpid|].
    simpl. try rewrite Ep. reflexivity. }
  cbv zeta. rewrite Hb. cbn [fold_left]. destruct st; reflexivity.
Qed.

(** The released world's chain contains no model level to update. *)
Lemma flat_model_pidns_updates : forall ctx st (update : PidNs -> PidNs) k,
  flat_view ctx st = true ->
  with_pidns st (fold_left replace_pidns
    (flat_map (fun p => match pidns_parent p with Some _ => [update p] | None => [] end)
      (firstn k (pidns_chain (length (ns_pidns st)) st (cx_pidns ctx)))) (ns_pidns st)) = st.
Proof.
  intros ctx st update k H. unfold flat_view in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hnet]. apply andb_true_iff in H as [H Hpid].
  assert (Hb : flat_map (fun p => match pidns_parent p with
      Some _ => [update p] | None => [] end)
      (firstn k (pidns_chain (length (ns_pidns st)) st (cx_pidns ctx))) = []).
  { destruct (length (ns_pidns st)) as [|n].
    - destruct k; reflexivity.
    - cbn [pidns_chain]. unfold find_pidns.
      destruct (find (fun p => Pos.eqb (pidns_id p) (cx_pidns ctx)) (ns_pidns st)) as [p|] eqn:Ef.
      + try rewrite Ef in Hpid. cbv beta iota in Hpid |- *.
        destruct (pidns_parent p) as [q|] eqn:Ep;
          [try rewrite Ep in Hpid; discriminate Hpid|].
        destruct k; simpl; try rewrite Ep; rewrite ?firstn_nil; reflexivity.
      + destruct k; reflexivity. }
  rewrite Hb. cbn [fold_left]. destruct st; reflexivity.
Qed.

Lemma pid_failed_flat : forall ctx st,
  flat_view ctx st = true -> pid_failed st (pidns_children ctx) = st.
Proof.
  intros ctx st H. rewrite (flat_view_pidns_children ctx st H). unfold pid_failed.
  pose proof (flat_model_pidns_updates ctx st pid_failure_record
    (length (pidns_chain (length (ns_pidns st)) st (cx_pidns ctx))) H) as Hsame.
  rewrite firstn_all in Hsame. exact Hsame.
Qed.

Lemma pid_reset_empty_flat : forall ctx st,
  flat_view ctx st = true -> pid_reset_empty st (cx_pidns ctx) = st.
Proof.
  intros ctx st H. unfold flat_view in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hnet]. apply andb_true_iff in H as [_ Hpid].
  unfold pid_reset_empty, find_pidns.
  destruct (find (fun p => Pos.eqb (pidns_id p) (cx_pidns ctx)) (ns_pidns st)) as [p|] eqn:Ef;
    [|reflexivity].
  try rewrite Ef in Hpid. cbv beta iota in Hpid |- *.
  destruct (pidns_parent p) as [q|] eqn:Ep;
    [try rewrite Ep in Hpid; discriminate Hpid|].
  reflexivity.
Qed.

Lemma pid_partial_flat : forall ctx st k,
  flat_view ctx st = true -> pid_partial st (cx_pidns ctx) k = st.
Proof.
  intros ctx st k H.
  unfold pid_partial, bump_pid_cursor. cbv zeta.
  rewrite (flat_model_pidns_updates ctx st (fun p => pidns_with_last p (pidns_last p + 1)) k H).
  now apply pid_reset_empty_flat.
Qed.

Lemma pid_partial_children_flat : forall ctx st k,
  flat_view ctx st = true -> pid_partial st (pidns_children ctx) k = st.
Proof.
  intros ctx st k H. rewrite (flat_view_pidns_children ctx st H).
  now apply pid_partial_flat.
Qed.

(** A task in the released world whose clone makes no namespace
    ([Ext.makes_ns]): the clone is the core's own; the child gets the
    caller's context and the state is unchanged. *)
Lemma clone_ns_exact_flat_fork : forall f m ctx st hq,
  flat_view ctx st = true -> makes_ns f = false ->
  clone_ns_exact f m ctx st hq = CnOk ctx None st.
Proof.
  intros f m ctx st hq Hf Hb. unfold clone_ns_exact. rewrite Hf, Hb. reflexivity.
Qed.

Lemma clone_ns_flat_fork_ok : forall f m ctx st hq,
  flat_view ctx st = true -> makes_ns f = false ->
  clone_ns f m ctx st hq (CnOk ctx None st).
Proof.
  intros f m ctx st hq Hf Hb. destruct f as [r|].
  - left. symmetry. apply clone_ns_exact_flat_fork; assumption.
  - left. reflexivity.
Qed.

(** [Ext.ext_clone_coherent] for [clone_ns]. *)
Lemma clone_ns_coherent : forall f m ctx st hq o,
  flat_view ctx st = true -> makes_ns f = false ->
  (clone_ns f m ctx st hq o <-> released_clone ctx st o).
Proof.
  intros f m ctx st hq o Hf Hb.
  destruct f as [r|]; [|split; intros Ho; exact Ho].
  unfold clone_ns, released_clone. cbv beta iota.
  rewrite (clone_ns_exact_flat_fork (Fork.CiArgs r) m ctx st hq Hf Hb), (pid_failed_flat ctx st Hf).
  split.
  - intros [Ho | (_ & e & st' & He & Hst & Ho)]; [left; exact Ho|].
    right. exists e. split; [exact He|].
    destruct Hst as [-> | [_ [-> | (k & _ & ->)]]]; try exact Ho.
    rewrite (pid_partial_children_flat ctx st k Hf) in Ho. exact Ho.
  - intros [Ho | (e & He & Ho)]; [left; exact Ho|].
    right. split; [intros Hc; discriminate Hc|].
    exists e, st. split; [exact He | split; [left; reflexivity | exact Ho]].
Qed.

(** THE THREE ABOVE AS THEY READ BEFORE, over a record whose FLAGS hold
    no namespace bit.  Each was stated with the premise
    [has_ns_bits f = false] on the flag word the core passed; the record
    it passes now makes no namespace wherever that held
    ([Ext.makes_ns_no_ns_bits]), so each old statement is still provable,
    and these are its proof. *)
Lemma clone_ns_exact_flat_fork_word : forall r m ctx st hq,
  flat_view ctx st = true -> has_ns_bits (Fork.cla_flags r) = false ->
  clone_ns_exact (Fork.CiArgs r) m ctx st hq = CnOk ctx None st.
Proof.
  intros r m ctx st hq Hf Hb.
  apply clone_ns_exact_flat_fork; [exact Hf | apply makes_ns_no_ns_bits; exact Hb].
Qed.

Lemma clone_ns_flat_fork_ok_word : forall r m ctx st hq,
  flat_view ctx st = true -> has_ns_bits (Fork.cla_flags r) = false ->
  clone_ns (Fork.CiArgs r) m ctx st hq (CnOk ctx None st).
Proof.
  intros r m ctx st hq Hf Hb.
  apply clone_ns_flat_fork_ok; [exact Hf | apply makes_ns_no_ns_bits; exact Hb].
Qed.

Lemma clone_ns_coherent_word : forall r m ctx st hq o,
  flat_view ctx st = true -> has_ns_bits (Fork.cla_flags r) = false ->
  (clone_ns (Fork.CiArgs r) m ctx st hq o <-> released_clone ctx st o).
Proof.
  intros r m ctx st hq o Hf Hb.
  apply clone_ns_coherent; [exact Hf | apply makes_ns_no_ns_bits; exact Hb].
Qed.

(** Where [clone_creds]'s count check is not decided by the tables
    ([ucount_check] gives [ChargeEither]: a level's count is at its limit,
    but the namespaces the tables hold for the caller are under it), Linux
    answers ENOSPC or goes on, depending on whether namespaces made earlier
    are still alive, which the tables do not hold; [unshare_exact] admits
    both there too. *)
Definition clone_count_undecided (f : Z) (m : Model) (ctx : NsCtx) (st : NsState) : bool :=
  has_flag f CLONE_NEWUSER
  && match find_userns (ns_userns st) (cx_user ctx) with
     | Some p =>
         negb (Nat.ltb 32 (uns_level p))
         && match ucount_check (ns_userns st) (cx_user ctx) p (bv_unsigned (cr_euid (m_creds m))) with
            | ChargeEither => true
            | _ => false
            end
     | None => false
     end.

(** The flags of a clone's input; a call with no record has none. *)
Definition clone_in_flags (f : Fork.CloneIn) : Z :=
  match f with
  | Fork.CiArgs r => Fork.cla_flags r
  | Fork.CiNoArgs => 0
  end.

(** The clone failures of a run in which THE HOST CAN MAKE THE NAMESPACES
    AND THE PROCESSES: an ENVIRONMENT PREMISE of every statement that names
    this [Ext.CloneEnv].  A clone that makes a namespace, or one by a task
    outside the released world (a fork inside the namespaces included),
    fails only as the tables say: [clone_ns_exact]'s answer (EPERM, EINVAL,
    ENOSPC from the model's own namespaces), or ENOSPC where the tables do
    not decide the namespace count ([clone_count_undecided]).  A run in
    which the host refuses on an allocation, a namespace count of its own,
    a cgroup controller, RLIMIT_NPROC, a pending fatal signal or a
    namespace's init function, or in which a pid namespace's init has
    exited (ENOMEM from [alloc_pid]: which processes live is the core's
    table, not the namespace state), is outside such a statement.  The
    released clone (a task in the released world, a clone that makes no
    namespace) keeps every failure the core admits, and so does a call
    with no record ([Fork.CiNoArgs]: the core's own failure, before
    [copy_process]), with the namespace state unchanged. *)
Definition clone_tables_failures : CloneEnv := fun f m ctx st hq e st' =>
  (flat_view ctx st && negb (makes_ns f)) = true
  \/ CnErr e st' = clone_ns_exact f m ctx st hq
  \/ (e = ENOSPC /\ st' = st /\ clone_count_undecided (clone_in_flags f) m ctx st = true)
  \/ (f = Fork.CiNoArgs /\ st' = st).

(** In the released world, for a clone that makes no namespace, it admits
    every failure. *)
Lemma clone_tables_failures_flat : forall f m ctx st hq e st',
  flat_view ctx st = true -> makes_ns f = false -> clone_tables_failures f m ctx st hq e st'.
Proof. intros f m ctx st hq e st' Hf Hb. left. rewrite Hf, Hb. reflexivity. Qed.

(** EVERY FAILURE THE OLD ENVIRONMENT ADMITTED, IT STILL ADMITS.  The
    definition above reads the record where it read the flag word, and
    it gained a fourth disjunct for a call with no record.  Its three old
    disjuncts, read over a record's flags, still hold of it: the first
    through [Ext.makes_ns_no_ns_bits], the other two unchanged.  So no
    statement that takes [clone_tables_failures] as its environment
    premise covers fewer runs than it did. *)
Lemma clone_tables_failures_record : forall r m ctx st hq e st',
  ((flat_view ctx st && negb (has_ns_bits (Fork.cla_flags r))) = true
   \/ CnErr e st' = clone_ns_exact (Fork.CiArgs r) m ctx st hq
   \/ (e = ENOSPC /\ st' = st
       /\ clone_count_undecided (Fork.cla_flags r) m ctx st = true)) ->
  clone_tables_failures (Fork.CiArgs r) m ctx st hq e st'.
Proof.
  intros r m ctx st hq e st' [H | [H | H]].
  - left. apply andb_true_iff in H as [Hf Hb]. apply negb_true_iff in Hb.
    rewrite Hf, (makes_ns_no_ns_bits r Hb). reflexivity.
  - right. left. exact H.
  - right. right. left. cbn [clone_in_flags]. exact H.
Qed.

Lemma clone_tables_failures_flat_word : forall r m ctx st hq e st',
  flat_view ctx st = true -> has_ns_bits (Fork.cla_flags r) = false ->
  clone_tables_failures (Fork.CiArgs r) m ctx st hq e st'.
Proof.
  intros r m ctx st hq e st' Hf Hb.
  apply clone_tables_failures_flat; [exact Hf | apply makes_ns_no_ns_bits; exact Hb].
Qed.
