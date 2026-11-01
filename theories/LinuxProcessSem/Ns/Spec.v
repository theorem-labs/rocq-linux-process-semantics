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
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Task Clone.
Import ListNotations.

(** The arms, by call number.  A number not listed fails closed. *)
Definition ns_table : list (Z * NsArm) := task_arms.

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
    arm whose refusals are not listed is never filtered. *)
Definition ns_injected_table : list NsInjected := task_injected.

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

(** The descriptor calls whose released answer reads or moves a
    descriptor's private state (an offset, a pipe's or socket's buffer, a
    directory position, status flags): fcntl, ioctl, close, getdents64,
    lseek, read, write, readv, writev, pread64, pwrite64, sendto,
    recvfrom, sendmsg, recvmsg. *)
Definition private_fd_calls : list Z :=
  [25; 29; 57; 61; 62; 63; 64; 65; 66; 67; 68; 206; 207; 211; 212]%Z.

(** The call reaches the released answer on such a descriptor of the
    released model: a file, a pipe, a socket or a directory. *)
Definition released_private_fd (i : SyscallInput) (m : Model) : bool :=
  existsb (Z.eqb (ns_sysno i)) private_fd_calls
  && match fd_lookup (m_fds m) (in_arg i 0) with
     | Some (FdFile _ _) | Some (FdFileW _ _) | Some (FdFileA _ _) | Some (FdFileRW _ _)
     | Some (FdPipe _ _) | Some (FdSocket _) | Some FdDir => true
     | _ => false
     end.

(** The claimed calls [ns_ext] answers soundly while other processes are
    live: a task outside the released world, whose arms read the shared
    namespace state, except a call that falls back to the released answer
    on a descriptor whose state a multi-process core keeps per process.
    A task in the released world gets the core's own guard. *)
Definition ns_multiproc (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : bool :=
  negb (flat_view ctx st) && negb (released_private_fd i m).

Lemma ns_multiproc_coherent : forall i m ctx st,
  flat_view ctx st = true -> ns_multiproc i m ctx st = false.
Proof. intros i m ctx st H. unfold ns_multiproc. rewrite H. reflexivity. Qed.

Definition ns_ext : ExtSpec :=
  mkExtSpec ns_claims ns_spec ns_refusal clone_ns clone_ns_refusal ns_multiproc ns_coherent
            ns_refusal_coherent clone_ns_coherent clone_ns_refusal_coherent ns_multiproc_coherent.

(** For a task in the released world [ns_ext] answers exactly as the
    released model does, Unmodeled included. *)
Lemma ns_spec_flat : forall i m ctx st o,
  flat_view ctx st = true -> ns_spec i m ctx st o <-> released i m ctx st o.
Proof. intros i m ctx st o H. unfold ns_spec. rewrite H. reflexivity. Qed.
