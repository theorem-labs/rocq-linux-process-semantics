(** * LinuxProcessSem.Ns.Spec — the namespace model's answers, as a step extension

    [ns_ext] is the namespace and mount model as an [Ns.Ext.ExtSpec]: a
    core that takes it answers every system call but [clone] (220),
    [clone3] (435) and [wait4] (260), which stay the core's own, through
    [ns_spec].

    [ns_spec] has two regimes.
    - For a task in the released world ([flat_view]: each of its
      namespaces is the host's) it is the released [Specs.syscall_spec],
      with the namespace context and state unchanged ([released]).  That is
      [ns_coherent], the obligation [ExtSpec] carries, and it holds by
      construction.
    - For a task in a namespace the tables model, the call's arm in
      [ns_table] answers; a number with no arm is [EUnmodeled]: the model
      fails closed, it never falls back to the released arm, whose path
      walks read the host's file system.  An arm that answers some shapes
      as the released arm does says so in its header and calls [released]
      for them.

    Every arm's header names the Linux functions it follows, with the
    version they were read at (6.18.44 or 6.18.46), and
    its kind: exact (every Linux outcome for the accepted shape, and no
    other), over (every Linux outcome, plus outcomes the model does not
    decide), or declines. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Task Clone Files UserArms MountArms Net FsOps Pass.
Import ListNotations.

(** The arms, by call number: the task's own state and its UTS namespace's
    names ([Ns.Task]), files and paths ([Ns.Files], [Ns.FsOps]), user
    namespaces ([Ns.UserArms]), mounts ([Ns.MountArms]), NETLINK_ROUTE and
    SIOCGIFINDEX ([Ns.Net]), and the calls a namespace does not change
    ([Ns.Pass]).  A number not listed fails closed; no number is listed
    twice ([ns_table_nodup]). *)
Definition ns_table : list (Z * NsArm) :=
  task_arms ++ file_arms ++ fsops_arms ++ user_arms ++ mount_arms ++ net_arms ++ pass_arms.

Fixpoint lookup_ns_arm (t : list (Z * NsArm)) (n : Z) : option NsArm :=
  match t with
  | [] => None
  | (k, a) :: r => if Z.eqb k n then Some a else lookup_ns_arm r n
  end.

Definition ns_sysno (i : SyscallInput) : Z := bv_unsigned (in_sysno i).

(** The calls the core answers itself: [clone] (220), [clone3] (435) and
    [wait4] (260).  The core creates and reaps children; [ext_clone] says
    what a clone does to the namespace model. *)
Definition core_sysnos : list Z := [220; 260; 435]%Z.

Definition ns_claims (i : SyscallInput) : bool :=
  negb (existsb (Z.eqb (ns_sysno i)) core_sysnos).

Definition ns_spec : NsArm := fun i m ctx st o =>
  if flat_view ctx st then released i m ctx st o
  else match lookup_ns_arm ns_table (ns_sysno i) with
       | Some a => a i m ctx st o
       | None => o = EUnmodeled
       end.

Lemma ns_coherent : forall i m ctx st,
  flat_view ctx st = true -> ns_claims i = true ->
  forall o, ns_spec i m ctx st o <-> released i m ctx st o.
Proof. intros i m ctx st Hflat _ o. unfold ns_spec. rewrite Hflat. reflexivity. Qed.

(* =========================================================================
   Injected refusals
   ========================================================================= *)

(** The injected refusals of the namespace arms [ns_table] holds, with the
    kernel functions that return them in each arm file; no security module
    but the capability one runs (SCOPE.md), so none of its refusals is
    listed.  An answer of a namespace arm whose refusals are not listed is
    never filtered.  Two kinds of answer are not listed here, because their
    answer is the released answer and [ns_refusal] gives them the released
    filter itself ([Run.spurious_refusal_cfg], which also knows [brk]'s
    refusal by value): the pass-through calls ([Pass.pass_numbers]) in
    every world, and a call on a descriptor of the released model
    ([released_fd_call]).  Each row also lists the errnos its arm answers
    from the tables ([Arm.ni_answers]); [ns_injected_forced] below checks
    the rule [ns_witness] needs of them. *)
Definition ns_injected_table : list NsInjected :=
  task_injected ++ file_injected ++ fsops_injected ++ user_injected ++ mount_injected
  ++ net_injected.

Fixpoint lookup_ns_injected (t : list NsInjected) (n : Z) : option NsInjected :=
  match t with
  | [] => None
  | r :: t' => if Z.eqb (ni_no r) n then Some r else lookup_ns_injected t' n
  end.

(** The pairs whose predicate holds of the errno the answer [ret] returns. *)
Definition ns_matching (i : SyscallInput) (ret : word) : list ((Z -> bool) * SpuriousFamily) :=
  match lookup_ns_injected ns_injected_table (ns_sysno i) with
  | Some r => List.filter (fun p : (Z -> bool) * SpuriousFamily => fst p (Z.opp (bv_signed ret)))
                          (ni_pairs r)
  | None => []
  end.

(** [ret] is an errno the tables can force for this call although the
    environment can inject it too ([ni_forced]). *)
Definition ns_forced (i : SyscallInput) (ret : word) : bool :=
  match lookup_ns_injected ns_injected_table (ns_sysno i) with
  | Some r => errno_in (ni_forced r) (Z.opp (bv_signed ret))
  | None => false
  end.

(** The answer [ret'] shows that the state did not force the refusal [ret]:
    it matches no pair, or it is an errno the tables can force while [ret]
    is not one.  Every answer that matches no pair is kept, and so is every
    [ni_forced] errno where no answer matches no pair; so the filter never
    removes every answer the model admits.  This is sound only because
    every errno the tables answer that a pair matches is in [ni_forced]:
    otherwise that answer, forced by the state, would be removed beside an
    injected [ni_forced] errno.  [Arm.ni_forced_ok] states that rule of a
    row, [ns_injected_forced] checks it of every row by computation, so a
    row that breaks it does not compile, and [ns_forced_rule] states it as
    a lemma. *)
Definition ns_witness (i : SyscallInput) (ret ret' : word) : bool :=
  match ns_matching i ret' with [] => true | _ :: _ => false end
  || (ns_forced i ret' && negb (ns_forced i ret)).

(** [ret] is an injected refusal every family of which [cfg] switches off:
    it matches some pair, and every pair it matches is of a family that may
    not fail.  A refusal one enabled family can produce is never filtered. *)
Definition ns_refusal_off_b (cfg : SpuriousCfg) (i : SyscallInput) (ret : word) : bool :=
  match ns_matching i ret with
  | [] => false
  | ps => forallb (fun p => negb (family_may_fail cfg (snd p))) ps
  end.

(** The call [i] names a descriptor of the released model, on which its
    namespace arm answers exactly as the released arm does: [write] (64)
    on a descriptor that is not one of the namespace model's files, and
    [getdents64] (61) on such a descriptor that is open
    ([released_fd_call_released]).  No other call with a row in
    [ns_injected_table] gives the released arm's answer on such a
    descriptor (the net arms answer [Net.sock_of]'s EBADF or ENOTSOCK, or
    decline), and the calls that do ([read], [close], [fcntl], [fstat],
    [fchmod]) have no row here and no injecting released arm, so both
    filters keep every answer of theirs. *)
Definition released_fd_call (i : SyscallInput) (m : Model) (st : NsState) : bool :=
  if Z.eqb (ns_sysno i) 64 then
    match ns_file_of m st (fd_word (in_arg i 0)) with None => true | Some _ => false end
  else if Z.eqb (ns_sysno i) 61 then
    match fd_lookup (m_fds m) (fd_word (in_arg i 0)) with
    | Some _ => match ns_file_of m st (fd_word (in_arg i 0)) with None => true | Some _ => false end
    | None => false
    end
  else false.

(** The forced-only filter of [ns_ext] on a call's effect: the released
    filter for a task in the released world, for a pass-through call in
    every world (its answer is the released answer,
    [Pass.pass_arms_released]), and for a call on a descriptor of the
    released model ([released_fd_call]), so the released question "did
    the state force this refusal?" is the same question, under the
    released table's family; elsewhere, a refusal of switched-off families
    where the model also admits an answer that shows the state did not
    force it ([ns_witness]): one that is no refusal at all, or the tables'
    own answer where that is an errno the environment can also inject (a
    count limit's ENOSPC against an allocation's ENOMEM). *)
Definition ns_refusal_eff (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (ctx : NsCtx)
    (st : NsState) (eff : SyscallEffect) : Prop :=
  if flat_view ctx st || existsb (Z.eqb (ns_sysno i)) pass_numbers || released_fd_call i m st
  then spurious_refusal_cfg cfg i m eff
  else ns_refusal_off_b cfg i (eff_ret eff) = true
       /\ exists eff' m' ctx' st' evs',
            ns_spec i m ctx st (EOk eff' m' ctx' st' evs')
            /\ ns_witness i (eff_ret eff) (eff_ret eff') = true.

(** The forced-only filter of the allocation failures [sendto] (206)
    shows only in the state after it ([Net.nl_alloc_after]): outside the
    released world, with the allocation family off, an answer whose state
    [st'] shows one is removed where the model also admits the same effect
    with a state that shows none, the answer reached without the failure.
    With the allocation family on it removes nothing. *)
Definition ns_alloc_refusal (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (ctx : NsCtx)
    (st : NsState) (eff : SyscallEffect) (st' : NsState) : Prop :=
  negb (flat_view ctx st) && Z.eqb (ns_sysno i) 206 && negb (family_may_fail cfg FamAlloc)
  && nl_alloc_after i m st st' = true
  /\ exists m2 ctx2 st2 evs2,
       ns_spec i m ctx st (EOk eff m2 ctx2 st2 evs2) /\ nl_alloc_after i m st st2 = false.

(** The forced-only filter of [ns_ext] ([Ext.ext_refusal]): an [EOk]
    outcome is filtered as its effect is ([ns_refusal_eff]), or as an
    allocation failure its state shows ([ns_alloc_refusal]).
    [EUnmodeled] is never filtered. *)
Definition ns_refusal (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (ctx : NsCtx)
    (st : NsState) (o : ext_outcome) : Prop :=
  match o with
  | EOk eff _ _ st' _ => ns_refusal_eff cfg i m ctx st eff \/ ns_alloc_refusal cfg i m ctx st eff st'
  | EUnmodeled => False
  end.

(** The filter of an outcome is the filter of its effect for every call
    but [sendto], and for [sendto] too while the allocation family may
    fail: there the filter keeps every answer it kept when it read the
    effect alone, and removes no other. *)
Lemma ns_refusal_outcome_eff : forall cfg i m ctx st o eff,
  outcome_eff o = Some eff ->
  (family_may_fail cfg FamAlloc || negb (Z.eqb (ns_sysno i) 206)) = true ->
  (ns_refusal cfg i m ctx st o <-> ns_refusal_eff cfg i m ctx st eff).
Proof.
  intros cfg i m ctx st o eff Ho Hk.
  destruct o as [eff0 m' ctx' st' evs|]; cbn in Ho; [|discriminate Ho].
  injection Ho as Ho. subst eff0. split.
  - intros [H | H]; [exact H|]. exfalso.
    destruct H as [Hb _].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Hf].
    apply andb_prop in Hb as [_ He].
    apply negb_true_iff in Hf. rewrite Hf, He in Hk. cbn in Hk. discriminate Hk.
  - intros H. left. exact H.
Qed.

Lemma ns_refusal_coherent : forall cfg i m ctx st o eff,
  flat_view ctx st = true -> ns_claims i = true -> outcome_eff o = Some eff ->
  (ns_refusal cfg i m ctx st o <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros cfg i m ctx st o eff H _ Ho.
  destruct o as [eff0 m' ctx' st' evs|]; cbn in Ho; [|discriminate Ho].
  injection Ho as Ho. subst eff0. split.
  - intros [Hr | Hr].
    + unfold ns_refusal_eff in Hr. rewrite H in Hr. exact Hr.
    + exfalso. destruct Hr as [Hb _].
      apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _].
      apply andb_prop in Hb as [Hv _].
      rewrite H in Hv. cbn in Hv. discriminate Hv.
  - intros Hs. left. unfold ns_refusal_eff. rewrite H. exact Hs.
Qed.

(** A pass-through call gets the released filter in every world. *)
Lemma ns_refusal_eff_pass : forall cfg i m ctx st eff,
  In (ns_sysno i) pass_numbers ->
  (ns_refusal_eff cfg i m ctx st eff <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros cfg i m ctx st eff H. unfold ns_refusal_eff.
  assert (Hp : existsb (Z.eqb (ns_sysno i)) pass_numbers = true).
  { apply existsb_exists. exists (ns_sysno i). split; [exact H | apply Z.eqb_refl]. }
  rewrite Hp, orb_true_r. reflexivity.
Qed.

(** A call on a descriptor of the released model gets the released filter
    in every world, under the released table's family. *)
Lemma ns_refusal_eff_released_fd : forall cfg i m ctx st eff,
  released_fd_call i m st = true ->
  (ns_refusal_eff cfg i m ctx st eff <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros cfg i m ctx st eff H. unfold ns_refusal_eff. rewrite H, orb_true_r. reflexivity.
Qed.

(** Elsewhere outside the released world the filter is the namespace
    one. *)
Lemma ns_refusal_eff_ns : forall cfg i m ctx st eff,
  (flat_view ctx st || existsb (Z.eqb (ns_sysno i)) pass_numbers || released_fd_call i m st) = false ->
  (ns_refusal_eff cfg i m ctx st eff
   <-> ns_refusal_off_b cfg i (eff_ret eff) = true
       /\ exists eff' m' ctx' st' evs',
            ns_spec i m ctx st (EOk eff' m' ctx' st' evs')
            /\ ns_witness i (eff_ret eff) (eff_ret eff') = true).
Proof. intros cfg i m ctx st eff H. unfold ns_refusal_eff. rewrite H. reflexivity. Qed.

(** More families allowed to fail filter fewer answers. *)
Lemma ns_refusal_off_b_mono : forall cfg1 cfg2 i ret,
  cfg_le cfg1 cfg2 -> ns_refusal_off_b cfg2 i ret = true -> ns_refusal_off_b cfg1 i ret = true.
Proof.
  intros cfg1 cfg2 i ret Hle. unfold ns_refusal_off_b.
  destruct (ns_matching i ret) as [|p ps]; [intros Hc; discriminate Hc|].
  intros H. apply forallb_forall. intros q Hq.
  pose proof (proj1 (forallb_forall _ _) H q Hq) as Hq2. cbv beta in Hq2 |- *.
  apply negb_true_iff in Hq2. apply negb_true_iff.
  destruct (family_may_fail cfg1 (snd q)) eqn:E1; [|reflexivity].
  rewrite (Hle _ E1) in Hq2. discriminate Hq2.
Qed.

Lemma ns_refusal_eff_mono : forall cfg1 cfg2 i m ctx st eff,
  cfg_le cfg1 cfg2 -> ns_refusal_eff cfg2 i m ctx st eff -> ns_refusal_eff cfg1 i m ctx st eff.
Proof.
  intros cfg1 cfg2 i m ctx st eff Hle. unfold ns_refusal_eff.
  destruct (flat_view ctx st || existsb (Z.eqb (ns_sysno i)) pass_numbers || released_fd_call i m st).
  - unfold spurious_refusal_cfg, injected_family_off.
    destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|]; [|intros [Hc _]; discriminate Hc].
    intros [Hoff Hrest]. split; [|exact Hrest].
    apply negb_true_iff in Hoff. apply negb_true_iff.
    destruct (family_may_fail cfg1 (ia_family a)) eqn:E1; [|reflexivity].
    rewrite (Hle _ E1) in Hoff. discriminate Hoff.
  - intros [Hoff Hrest]. split; [exact (ns_refusal_off_b_mono cfg1 cfg2 i (eff_ret eff) Hle Hoff)
                                | exact Hrest].
Qed.

Lemma ns_spurious_refusal_cfg_mono : forall cfg1 cfg2 i m ctx st o,
  cfg_le cfg1 cfg2 -> ns_refusal cfg2 i m ctx st o -> ns_refusal cfg1 i m ctx st o.
Proof.
  intros cfg1 cfg2 i m ctx st [eff m' ctx' st' evs|] Hle.
  - intros [H | [Hb Hw]].
    + left. exact (ns_refusal_eff_mono cfg1 cfg2 i m ctx st eff Hle H).
    + right. split; [|exact Hw].
      apply andb_prop in Hb as [Hb HN]. apply andb_prop in Hb as [Hb HF].
      assert (HF1 : negb (family_may_fail cfg1 FamAlloc) = true).
      { apply negb_true_iff in HF. apply negb_true_iff.
        destruct (family_may_fail cfg1 FamAlloc) eqn:E1; [|reflexivity].
        rewrite (Hle _ E1) in HF. discriminate HF. }
      rewrite Hb, HF1, HN. reflexivity.
  - intros H. exact (False_ind _ H).
Qed.

(** With one pair for a number, the filter is the released single-family
    one: the errno is in the pair and its family is off. *)
Lemma ns_refusal_off_b_single : forall cfg i ret (P : Z -> bool) F,
  ns_matching i ret = (if P (Z.opp (bv_signed ret)) then [(P, F)] else []) ->
  ns_refusal_off_b cfg i ret = P (Z.opp (bv_signed ret)) && negb (family_may_fail cfg F).
Proof.
  intros cfg i ret P F H. unfold ns_refusal_off_b. rewrite H.
  destruct (P (Z.opp (bv_signed ret))); cbn; [rewrite andb_true_r; reflexivity | reflexivity].
Qed.

(** THE CALLS A TASK OUTSIDE THE RELEASED WORLD MAKES WHILE ANOTHER PROCESS
    LIVES.  A core admits a claimed call in a system of several processes
    only when it is one of the core's own numbers or this guard admits it;
    a task in the released world gets the core's class list alone
    ([ns_multiproc_coherent]).  This guard admits exactly the calls the
    setup child of a sandbox makes while its parent lives -- bubblewrap
    0.13.1's child from its [raw_clone] to its exec, as three re-traced
    launches record them, the checks a harness runs there, and the stderr
    message of a setup that dies -- and each only where its answer reads
    and writes state that a live peer either shares as the model shares
    it or cannot reach:
    - the namespace state [NsState], which the core keeps once, in its
      shared part, as Linux keeps one copy of every namespace, mount,
      dentry, inode, socket and open file of the namespace model;
    - the caller's [NsCtx] and its released [Model]'s task fields (ids,
      capabilities, umask, root, cwd, signal mask, parent-death signal):
      per task in Linux after a [clone] without CLONE_FS, CLONE_FILES,
      CLONE_SIGHAND or CLONE_THREAD (kernel/fork.c [copy_fs],
      [copy_files], [copy_sighand]), and per process in the core;
    - the caller's descriptor table, per task after a clone without
      CLONE_FILES, and the start a directory descriptor names, which no
      peer can change ([ns_mp_any_fd]).
    What a descriptor's OPEN FILE holds is shared by every holder: an
    offset, status flags, a socket's queue, an eventfd's counter.  The
    namespace model keeps that state for its own descriptors ([ONsFile])
    in [NsState], so it is shared ([ns_mp_nsfile_calls]); the released
    model keeps it per process, so a call that reads or moves it on a
    released descriptor is not admitted, except where the arm reads none
    of it:
    - [read] (63) of an eventfd: the arm admits every value Linux can
      return and keeps no counter ([FsOps.eventfd_read_arm]);
    - [read] (63) of an inherited file that holds its offset
      ([State.OInherited] with [Some]): Linux keeps one [f_pos] for the
      description, which every table that names it shares ([dup_fd],
      fs/file.c; [ksys_read], fs/read_write.c; v6.18.46).  The model
      holds that offset live in ONE entry of the configuration: a clone
      of either word leaves it with the child and the caller keeps
      [OInherited None] ([Kernel.Fork.forfeit_inherited]), on which every
      call that reads or moves the offset declines; [dup] and [F_DUPFD]
      decline on it.  So no modeled peer moves it,
      and SCOPE.md assumes that no process outside the model does;
    - [writev] (66) of a standard channel: the answer depends only on the
      launch fact [State.m_channel_reader], and what it writes is the
      trace's [WriteEv];
    - [close] (57) of an opaque descriptor (an O_PATH or /proc/sys file,
      an eventfd, a namespace file, an inherited file): Linux's close of
      these drops a reference and nothing a peer observes; a namespace
      file another process still names is freed early
      ([Arm.release_handle]), and that process's later use declines; an
      inherited file's close clears this table's slot (the table is a
      copy after a clone without CLONE_FILES), and the description's
      offset, which only this entry holds live, is read by no other
      modeled holder;
    - [fcntl] (25) F_GETFD (1) and F_SETFD (2): the close-on-exec bit is
      the caller's descriptor table's.
    THE INODES AND DENTRIES of the namespace model are in [NsState] too,
    one copy for every process, as Linux keeps one:
    - [fchmod] (52) of a namespace file writes the inode's mode there
      ([FsOps.set_inode_perm], [FsOps.set_inode_perm_frame]), so a peer
      that reads the inode afterwards reads the new mode, as in Linux; a
      peer in the released world reads no inode of the namespace model,
      and [FsOps.fchmod_fn] declines every file but a tmpfs one;
    - [unlinkat] (35) marks the dentry unlinked there
      ([FsOps.set_unlinked], [FsOps.set_unlinked_frame]) and returns the
      caller's model as it was.  This guard does not list it: it is one
      of the core's gated numbers ([Procs.multiproc_gated_sysnos]), which
      [Procs.multiproc_base] admits.
    THE ADDRESS SPACE is per process in Linux after a clone without
    CLONE_VM ([dup_mm], kernel/fork.c) and per process in the core, so the
    memory calls are admitted: [brk] 214, [munmap] 215, [mremap] 216,
    [mprotect] 226, [madvise] 233 (the harness's checks allocate, and
    musl's allocator may map or unmap a group), and [mmap] 222 only with
    MAP_ANONYMOUS: a file mapping reads the file, and the released file
    system is kept per process.  [capget] 90 reads the task's own sets.
    [sethostname] 161 (bubblewrap's child setting a host name) reads the caller's
    context, its own memory and the UTS namespace, and writes that
    namespace's name, which [NsState] keeps once for every process in it,
    as Linux keeps one [uts_namespace].  [setsid] 157 (bubblewrap's child
    making a new session) reads the caller's pid and its process's leader
    bit, per process in the core, and tests whether a live task's process
    group is the caller's pid: in a pid namespace the tables made no
    modelled process makes such a group, a peer's included, because
    [setpgid] has no arm, and a process outside the model can only when
    the caller is the namespace's pid 1 and its modelled parent exits,
    which the launch value [Tables.env_foreign_pgroups] names
    ([Task.setsid_arm]); in the host's
    pid namespace, or under that value, the arm admits EPERM beside the
    success.  Linux also sets the caller's session and group ids; the
    model records the leader bit only, and no call of a peer the model
    answers reads those ids.
    Every other claimed call is not admitted while another process lives:
    the core makes it a model error, never a wrong answer.  That covers
    the released file system, pipes and sockets of the released model,
    and every call this child does not make.  Time is not among them:
    [clock_gettime] 113 is one of the core's synced numbers
    ([Procs.multiproc_synced_sysnos]), which [Procs.multiproc_base]
    admits, and the core brings the caller's clock up to every peer's
    before it answers ([Procs.pstep_sync]).  Widening the list is one
    more row of this argument. *)
Definition ns_mp_any_fd : list Z :=
  [17; 34; 36; 39; 40; 41; 43; 48; 49; 50; 56; 78; 79; 90; 91; 97; 135; 157; 161; 166; 167; 172;
   198; 214; 215; 216; 226; 233; 437; 442]%Z.

(** [ioctl], [getdents64], [fchmod], [read], [write], [fstat], [bind],
    [sendto] and [recvfrom], admitted on a descriptor of the namespace
    model only. *)
Definition ns_mp_nsfile_calls : list Z := [29; 52; 61; 63; 64; 80; 200; 206; 207]%Z.

Definition ns_multiproc_call (i : SyscallInput) (m : Model) : bool :=
  let n := ns_sysno i in
  let fd := fd_word (in_arg i 0) in
  let e := fd_lookup (m_fds m) fd in
  let nsfile := match e with
                | Some x => match fd_entry_handle x with Some _ => true | None => false end
                | None => false
                end in
  let evfd := match eventfd_flags_of m fd with Some _ => true | None => false end in
  let opaque := match e with Some x => fd_entry_opaque x | None => false end in
  let chan := match e with Some (FdChannel _) => true | _ => false end in
  let inh := match e with Some x => Fork.inherited_live_b x | None => false end in
  let cmd := Z.land (bv_unsigned (in_arg i 1)) 4294967295 in
  existsb (Z.eqb n) ns_mp_any_fd
  || (existsb (Z.eqb n) ns_mp_nsfile_calls && nsfile)
  || (Z.eqb n 63 && evfd)
  || (Z.eqb n 63 && inh)
  || (Z.eqb n 66 && chan)
  || (Z.eqb n 57 && opaque)
  || (Z.eqb n 25 && (nsfile || Z.eqb cmd 1 || Z.eqb cmd 2))
  || (Z.eqb n 222 && Z.testbit (bv_unsigned (in_arg i 3)) 5).    (* MAP_ANONYMOUS, 0x20 *)

Definition ns_multiproc (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : bool :=
  negb (flat_view ctx st) && ns_multiproc_call i m.

Lemma ns_multiproc_coherent : forall i m ctx st,
  flat_view ctx st = true -> ns_multiproc i m ctx st = false.
Proof. intros i m ctx st H. unfold ns_multiproc. rewrite H. reflexivity. Qed.

Definition ns_ext : ExtSpec :=
  mkExtSpec ns_claims ns_spec ns_refusal clone_ns ns_multiproc ns_coherent ns_refusal_coherent
            clone_ns_coherent ns_multiproc_coherent.

(** For a task in the released world [ns_ext] answers exactly as the
    released model does, Unmodeled included. *)
Lemma ns_spec_flat : forall i m ctx st o,
  flat_view ctx st = true -> ns_spec i m ctx st o <-> released i m ctx st o.
Proof. intros i m ctx st o H. unfold ns_spec. rewrite H. reflexivity. Qed.

(** No call number has two arms, and none has two injected-refusal
    entries, so the first match is the only one. *)
Lemma ns_table_nodup : List.NoDup (map fst ns_table).
Proof.
  vm_compute.
  repeat (apply List.NoDup_cons; [intros Hin; vm_compute in Hin; intuition discriminate|]).
  apply List.NoDup_nil.
Qed.

Lemma ns_injected_nodup : List.NoDup (map ni_no ns_injected_table).
Proof.
  vm_compute.
  repeat (apply List.NoDup_cons; [intros Hin; vm_compute in Hin; intuition discriminate|]).
  apply List.NoDup_nil.
Qed.

(** THE RULE [ns_witness] NEEDS, CHECKED OF EVERY ROW: each row's
    [ni_forced] is exactly the errnos of its [ni_answers] that a pair
    matches ([Arm.ni_forced_ok]); today ENOSPC for [unshare] and [mount],
    ENOMEM for [write], EPERM for [setsid].  A row whose tables answer an
    errno a pair matches without listing it in [ni_forced] fails this
    computation, and the file does not compile
    ([Checks.Cases.Ns.SpecCases.bad_row_fails] shows the check refusing
    such a row). *)
Lemma ns_injected_forced : forallb ni_forced_ok ns_injected_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lookup_ns_injected_in : forall t n r, lookup_ns_injected t n = Some r -> In r t.
Proof.
  induction t as [|r0 t IH]; intros n r; cbn [lookup_ns_injected]; [intros H; discriminate H|].
  destruct (Z.eqb (ni_no r0) n); intros H.
  - injection H as <-. apply in_eq.
  - apply in_cons. exact (IH n r H).
Qed.

(** The rule as a lemma: an errno the tables answer for call [n] that a
    pair of [n]'s row matches is in that row's [ni_forced]. *)
Lemma ns_forced_rule : forall n r e,
  lookup_ns_injected ns_injected_table n = Some r ->
  In e (ni_answers r) -> ni_errno r e = true -> In e (ni_forced r).
Proof.
  intros n r e Hr Ha He.
  pose proof (proj1 (forallb_forall _ _) ns_injected_forced r (lookup_ns_injected_in _ _ _ Hr)) as Hok.
  unfold ni_forced_ok in Hok. apply andb_true_iff in Hok. destruct Hok as [Hok _].
  pose proof (proj1 (forallb_forall _ _) Hok e Ha) as He'. cbv beta in He'.
  rewrite He in He'. cbn [negb orb] in He'.
  unfold errno_in in He'. apply existsb_exists in He'. destruct He' as (x & Hx & Hxe).
  apply Z.eqb_eq in Hxe. subst x. exact Hx.
Qed.

(** The calls the core answers ([core_sysnos]: clone, wait4, clone3) are
    not claimed, so no arm is listed for them. *)
Lemma ns_table_not_core : forall n, In n core_sysnos -> ~ In n (map fst ns_table).
Proof.
  intros n Hn. cbn [core_sysnos In] in Hn.
  destruct Hn as [<-|[<-|[<-|[]]]]; vm_compute; intuition discriminate.
Qed.

(* =========================================================================
   Where the namespace model answers as the released model does
   ========================================================================= *)

Lemma lookup_read : lookup_ns_arm ns_table 63%Z = Some read_arm.
Proof. reflexivity. Qed.

Lemma lookup_write : lookup_ns_arm ns_table 64%Z = Some write_arm.
Proof. reflexivity. Qed.

(** A READ ON A DESCRIPTOR THE RELEASED MODEL OWNS HAS EXACTLY THE RELEASED
    ANSWERS in every world: in the released world by [ns_spec_flat], in a
    world with a mount tree by [FsOps.read_arm_released]. *)
Theorem ns_spec_read_released : forall i m ctx st o,
  ns_sysno i = 63%Z -> released_owned m st (fd_word (in_arg i 0)) ->
  (ns_spec i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o Hn Hr. unfold ns_spec. destruct (flat_view ctx st); [reflexivity|].
  rewrite Hn, lookup_read. apply read_arm_released. exact Hr.
Qed.

(** The same for write, on every descriptor that is not one of the
    namespace model's own files. *)
Theorem ns_spec_write_released : forall i m ctx st o,
  ns_sysno i = 64%Z -> ns_file_of m st (fd_word (in_arg i 0)) = None ->
  (ns_spec i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o Hn Hr. unfold ns_spec. destruct (flat_view ctx st); [reflexivity|].
  rewrite Hn, lookup_write. apply write_arm_released. exact Hr.
Qed.

Lemma lookup_getdents64 : lookup_ns_arm ns_table 61%Z = Some getdents64_arm.
Proof. reflexivity. Qed.

(** The same for getdents64, on an open descriptor that is not one of the
    namespace model's own files. *)
Theorem ns_spec_getdents64_released : forall i m ctx st o,
  ns_sysno i = 61%Z -> fd_lookup (m_fds m) (fd_word (in_arg i 0)) <> None ->
  ns_file_of m st (fd_word (in_arg i 0)) = None ->
  (ns_spec i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o Hn Hfd Hr. unfold ns_spec. destruct (flat_view ctx st); [reflexivity|].
  rewrite Hn, lookup_getdents64. apply getdents64_arm_released; [exact Hfd | exact Hr].
Qed.

(** So [released_fd_call] names calls whose answers are exactly the
    released ones, in every world: the released filter asks of them the
    question it asks in the released world. *)
Theorem released_fd_call_released : forall i m ctx st o,
  released_fd_call i m st = true -> (ns_spec i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o. unfold released_fd_call.
  destruct (Z.eqb (ns_sysno i) 64) eqn:E64.
  - destruct (ns_file_of m st (fd_word (in_arg i 0))) eqn:Ens; intros H; [discriminate H|].
    apply ns_spec_write_released; [apply Z.eqb_eq; exact E64 | exact Ens].
  - destruct (Z.eqb (ns_sysno i) 61) eqn:E61; [|intros H; discriminate H].
    destruct (fd_lookup (m_fds m) (fd_word (in_arg i 0))) eqn:Efd; [|intros H; discriminate H].
    destruct (ns_file_of m st (fd_word (in_arg i 0))) eqn:Ens; intros H; [discriminate H|].
    apply ns_spec_getdents64_released.
    + apply Z.eqb_eq. exact E61.
    + rewrite Efd. discriminate.
    + exact Ens.
Qed.

(** Each pass-through number ([Ns.Pass]) has exactly the released answers
    in every world. *)
Theorem ns_spec_pass_released : forall i m ctx st o,
  In (ns_sysno i) pass_numbers -> (ns_spec i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o Hn. unfold ns_spec. destruct (flat_view ctx st); [reflexivity|].
  assert (H : lookup_ns_arm ns_table (ns_sysno i) = Some released).
  { remember (ns_sysno i) as n eqn:En. clear En. cbn [pass_numbers In] in Hn.
    repeat (destruct Hn as [<- | Hn]; [reflexivity |]). destruct Hn. }
  rewrite H. reflexivity.
Qed.
