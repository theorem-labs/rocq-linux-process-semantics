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

    Every arm's header names the Linux 6.18.44 functions it follows and
    its kind: exact (every Linux outcome for the accepted shape, and no
    other), over (every Linux outcome, plus outcomes the model does not
    decide), or declines. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Task Clone Files UserArms MountArms Net FsOps Pass.
Import ListNotations.

(** The arms, by call number: the task's own state ([Ns.Task]), files and
    paths ([Ns.Files], [Ns.FsOps]), user namespaces ([Ns.UserArms]), mounts
    ([Ns.MountArms]), NETLINK_ROUTE and SIOCGIFINDEX ([Ns.Net]), and the
    calls a namespace does not change ([Ns.Pass]).  A number not listed
    fails closed; no number is listed twice ([ns_table_nodup]). *)
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

(** The injected refusals of the arms [ns_table] holds.  An answer of an
    arm whose refusals are not listed is never filtered; the pass-through
    calls list none, so none of their answers is filtered outside the
    released world. *)
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

(** [ret] is an injected refusal every family of which [cfg] switches off:
    it matches some pair, and every pair it matches is of a family that may
    not fail.  A refusal one enabled family can produce is never filtered. *)
Definition ns_refusal_off_b (cfg : SpuriousCfg) (i : SyscallInput) (ret : word) : bool :=
  match ns_matching i ret with
  | [] => false
  | ps => forallb (fun p => negb (family_may_fail cfg (snd p))) ps
  end.

(** The forced-only filter of [ns_ext]: the released filter for a task in
    the released world; elsewhere, a refusal of switched-off families where the model
    also admits an answer that is no refusal at all (the state did not
    force the refusal). *)
Definition ns_refusal (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (ctx : NsCtx)
    (st : NsState) (eff : SyscallEffect) : Prop :=
  if flat_view ctx st then spurious_refusal_cfg cfg i m eff
  else ns_refusal_off_b cfg i (eff_ret eff) = true
       /\ exists eff' m' ctx' st' evs',
            ns_spec i m ctx st (EOk eff' m' ctx' st' evs') /\ ns_matching i (eff_ret eff') = [].

Lemma ns_refusal_coherent : forall cfg i m ctx st eff,
  flat_view ctx st = true -> ns_claims i = true ->
  (ns_refusal cfg i m ctx st eff <-> spurious_refusal_cfg cfg i m eff).
Proof. intros cfg i m ctx st eff H _. unfold ns_refusal. rewrite H. reflexivity. Qed.

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

Lemma ns_spurious_refusal_cfg_mono : forall cfg1 cfg2 i m ctx st eff,
  cfg_le cfg1 cfg2 -> ns_refusal cfg2 i m ctx st eff -> ns_refusal cfg1 i m ctx st eff.
Proof.
  intros cfg1 cfg2 i m ctx st eff Hle. unfold ns_refusal.
  destruct (flat_view ctx st).
  - unfold spurious_refusal_cfg, injected_family_off.
    destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|]; [|intros [Hc _]; discriminate Hc].
    intros [Hoff Hrest]. split; [|exact Hrest].
    apply negb_true_iff in Hoff. apply negb_true_iff.
    destruct (family_may_fail cfg1 (ia_family a)) eqn:E1; [|reflexivity].
    rewrite (Hle _ E1) in Hoff. discriminate Hoff.
  - intros [Hoff Hrest]. split; [exact (ns_refusal_off_b_mono cfg1 cfg2 i (eff_ret eff) Hle Hoff)
                                | exact Hrest].
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
    - [writev] (66) of a standard channel: the answer depends only on the
      launch fact [State.m_channel_reader], and what it writes is the
      trace's [WriteEv];
    - [close] (57) of an opaque descriptor (an O_PATH or /proc/sys file,
      an eventfd, a namespace file): Linux's close of these drops a
      reference and nothing a peer observes; a namespace file another
      process still names is freed early ([Arm.release_handle]), and that
      process's later use declines;
    - [fcntl] (25) F_GETFD (1) and F_SETFD (2): the close-on-exec bit is
      the caller's descriptor table's.
    THE ADDRESS SPACE is per process in Linux after a clone without
    CLONE_VM ([dup_mm], kernel/fork.c) and per process in the core, so the
    memory calls are admitted: [brk] 214, [munmap] 215, [mremap] 216,
    [mprotect] 226, [madvise] 233 (the harness's checks allocate, and
    musl's allocator may map or unmap a group), and [mmap] 222 only with
    MAP_ANONYMOUS: a file mapping reads the file, and the released file
    system is kept per process.  [capget] 90 reads the task's own sets.
    Every other claimed call is not admitted while another process lives:
    the core makes it a model error, never a wrong answer.  That covers
    time ([clock_gettime] 113: the core keeps a clock per process), the
    released file system, pipes and sockets of the released model, and
    every call this child does not make.  Widening the list is one more
    row of this argument. *)
Definition ns_mp_any_fd : list Z :=
  [17; 34; 36; 39; 40; 41; 43; 48; 49; 50; 56; 78; 79; 90; 91; 97; 135; 166; 167; 172; 198;
   214; 215; 216; 226; 233; 437; 442]%Z.

(** [ioctl], [getdents64], [read], [write], [fstat], [bind], [sendto] and
    [recvfrom], admitted on a descriptor of the namespace model only. *)
Definition ns_mp_nsfile_calls : list Z := [29; 61; 63; 64; 80; 200; 206; 207]%Z.

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
  let cmd := Z.land (bv_unsigned (in_arg i 1)) 4294967295 in
  existsb (Z.eqb n) ns_mp_any_fd
  || (existsb (Z.eqb n) ns_mp_nsfile_calls && nsfile)
  || (Z.eqb n 63 && evfd)
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
