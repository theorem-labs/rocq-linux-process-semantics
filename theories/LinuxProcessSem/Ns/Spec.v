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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Task.
Import ListNotations.

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
