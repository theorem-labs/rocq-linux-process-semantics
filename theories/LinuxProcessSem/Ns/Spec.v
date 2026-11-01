(** * LinuxProcessSem.Ns.Spec — the namespace model's answers, as a step extension

    [ns_ext] is the namespace and mount model as an [Ns.Ext.ExtSpec]: a
    core that takes it answers every system call but [clone] (220) and
    [wait4] (260), which stay the core's own, through [ns_spec].

    [ns_spec] has two regimes.
    - In the released world ([flat_view]: no mount tree is known) it is the
      released [Specs.syscall_spec], with the namespace context and state
      unchanged ([released]).  That is [ns_coherent], the obligation
      [ExtSpec] carries, and it holds by construction.
    - In a world with a mount tree, the call's arm in [ns_table] answers;
      a number with no arm is [EUnmodeled]: the model fails closed, it
      never falls back to the released arm, whose path walks read the flat
      file system.  An arm that answers some shapes as the released arm
      does says so in its header and calls [released] for them.

    Every arm's header names the Linux 6.18.44 functions it follows and
    its kind: exact (every Linux outcome for the accepted shape, and no
    other), over (every Linux outcome, plus outcomes the model does not
    decide), or declines. *)

From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
Import ListNotations.

(** One call number's answer in a world with a mount tree. *)
Definition NsArm : Type := SyscallInput -> Model -> NsCtx -> NsState -> ext_outcome -> Prop.

(** The released answer, with the namespace context and state unchanged. *)
Definition released : NsArm := fun i m ctx st o =>
  match o with
  | EOk eff m' ctx' st' evs => ctx' = ctx /\ st' = st /\ syscall_spec i m (Ok eff m' evs)
  | EUnmodeled => syscall_spec i m Unmodeled
  end.

(* =========================================================================
   What arms share
   ========================================================================= *)

(** An answer that sets the return register and changes nothing else. *)
Definition ns_ret (r : word) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  EOk (mkEffect r [] []) m ctx st [].

Definition ns_errno (e : Z) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  ns_ret (errno_ret e) m ctx st.

Fixpoint lookup_file (fs : list (N * NsFile)) (h : N) : option NsFile :=
  match fs with
  | [] => None
  | (k, f) :: r => if N.eqb k h then Some f else lookup_file r h
  end.

(** The open file of the namespace model that descriptor [fd] names, with
    its handle; [None] for a descriptor of another kind or no descriptor. *)
Definition ns_file_of (m : Model) (st : NsState) (fd : word) : option (N * NsFile) :=
  match fd_lookup (m_fds m) fd with
  | Some (FdOpaque (ONsFile h)) => option_map (fun f => (h, f)) (lookup_file (ns_files st) h)
  | _ => None
  end.

(** A handle no open file has. *)
Definition fresh_handle (st : NsState) : N :=
  N.succ (fold_left N.max (map fst (ns_files st)) 0%N).

(** The task's pid in a pid namespace, and in its own. *)
Fixpoint pid_in (ps : list (positive * Z)) (n : positive) : option Z :=
  match ps with
  | [] => None
  | (k, p) :: r => if Pos.eqb k n then Some p else pid_in r n
  end.

Definition task_pid (ctx : NsCtx) : option Z := pid_in (cx_pids ctx) (cx_pidns ctx).

Definition with_umask (ctx : NsCtx) (u : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) u (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

(* =========================================================================
   Arms on the task's own state
   ========================================================================= *)

(** [umask] (166): [SYSCALL_DEFINE1(umask)], kernel/sys.c: the mask's
    permission bits are stored and the old mask returned.  Kind: exact. *)
Definition umask_arm : NsArm := fun i m ctx st o =>
  o = ns_ret (Z_to_bv 64 (cx_umask ctx)) m
             (with_umask ctx (Z.land (bv_unsigned (in_arg i 0)) 511)) st.

(** [getpid] (172) and [gettid] (178): [task_tgid_vnr] and
    [task_pid_vnr] (kernel/sys.c), the pid in the task's active pid
    namespace; one thread per process, so both are the same.  Kind: exact;
    a task with no pid in its own namespace is not one the model holds,
    and declines. *)
Definition getpid_arm : NsArm := fun i m ctx st o =>
  match task_pid ctx with
  | Some p => o = ns_ret (Z_to_bv 64 p) m ctx st
  | None => o = EUnmodeled
  end.

(** The arms, by call number.  A number not listed fails closed. *)
Definition ns_table : list (Z * NsArm) :=
  [(166%Z, umask_arm); (172%Z, getpid_arm); (178%Z, getpid_arm)].

Fixpoint lookup_ns_arm (t : list (Z * NsArm)) (n : Z) : option NsArm :=
  match t with
  | [] => None
  | (k, a) :: r => if Z.eqb k n then Some a else lookup_ns_arm r n
  end.

Definition ns_sysno (i : SyscallInput) : Z := bv_unsigned (in_sysno i).

(** Every call but [clone] and [wait4], which the core answers. *)
Definition ns_claims (i : SyscallInput) : bool :=
  negb (Z.eqb (ns_sysno i) 220 || Z.eqb (ns_sysno i) 260).

Definition ns_spec : NsArm := fun i m ctx st o =>
  if flat_view st then released i m ctx st o
  else match lookup_ns_arm ns_table (ns_sysno i) with
       | Some a => a i m ctx st o
       | None => o = EUnmodeled
       end.

Lemma ns_coherent : forall i m ctx st,
  flat_view st = true -> ns_claims i = true -> ~ syscall_spec i m Unmodeled ->
  forall o, ns_spec i m ctx st o <->
            exists eff m' evs, o = EOk eff m' ctx st evs /\ syscall_spec i m (Ok eff m' evs).
Proof.
  intros i m ctx st Hflat _ Hans o. unfold ns_spec. rewrite Hflat.
  destruct o as [eff m' ctx' st' evs|]; cbn [released]; split.
  - intros (-> & -> & H). exists eff, m', evs. split; [reflexivity | exact H].
  - intros (eff0 & m0 & evs0 & Heq & H). injection Heq as -> -> -> -> ->.
    split; [reflexivity | split; [reflexivity | exact H]].
  - intros H. contradiction.
  - intros (eff0 & m0 & evs0 & Heq & _). discriminate Heq.
Qed.

Definition ns_ext : ExtSpec := mkExtSpec ns_claims ns_spec ns_coherent.

(** In the released world [ns_ext] answers exactly as the released model
    does, Unmodeled included. *)
Lemma ns_spec_flat : forall i m ctx st o,
  flat_view st = true -> ns_spec i m ctx st o <-> released i m ctx st o.
Proof. intros i m ctx st o H. unfold ns_spec. rewrite H. reflexivity. Qed.
