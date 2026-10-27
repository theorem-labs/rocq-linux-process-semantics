(** * LinuxProcessSem.Checks.Witness.Kernel.Fork — the set_tid_address (96), clone (220) and clone3 (435) witnesses, and their proofs

    Mirrors [Sys/Kernel/Fork.v], which answers to Linux [kernel/fork.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

Definition set_tid_address_witness (m : Model) : outcome SyscallEffect :=
  match m_tid m with
  | Some tid => ret_outcome tid m
  | None => ret_outcome (Z_to_bv 64 1) (with_tid (Z_to_bv 64 1) m)
  end.

Lemma set_tid_address_witness_ok : forall i m,
  set_tid_address_spec i m (set_tid_address_witness m).
Proof.
  intros. unfold set_tid_address_spec, set_tid_address_witness.
  destruct (m_tid m) as [tid|] eqn:Htid.
  - eapply bind_step; [apply get_model_ok|]. cbv beta.
    rewrite Htid; cbv iota. apply pure_ok.
  - eapply bind_step; [apply get_model_ok|]. cbv beta.
    rewrite Htid; cbv iota.
    eapply bind_step.
    { apply (choose_ok _ (Z_to_bv 64 1)).
      unfold PID_MAX_ENVELOPE. change (0 < 1 < 4194304)%Z. lia. }
    eapply bind_step; [apply modify_ok|].
    apply pure_ok.
Qed.

(** clone / clone3 witness: the -EAGAIN arm, whose choice is a member of
    a list literal rather than a value to construct, and which leaves
    the model alone — so it is available whenever the argument gates let
    the call through.  The pid arm would have to invent an id inside an
    envelope, and is never needed to show the spec is receptive. *)
Definition clone_resolve_witness (m : Model) : outcome SyscallEffect :=
  if negb (clone_no_shared_file_b (m_fds m)) then Unmodeled
  else ret_outcome (errno_ret EAGAIN) m.

Lemma clone_resolve_witness_ok : forall i m,
  clone_resolve i m (clone_resolve_witness m).
Proof.
  intros. unfold clone_resolve, clone_resolve_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (m_fds m))); cbv iota;
    [apply unmodeled_intro|].
  apply alt_l. eapply bind_step; [apply (choose_ok _ EAGAIN); cbn; auto|].
  apply pure_ok.
Qed.

Definition clone_witness (flags : word) (m : Model) : outcome SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve_witness m else Unmodeled.

Lemma clone_witness_ok : forall flags i m,
  clone_spec flags i m (clone_witness flags m).
Proof.
  intros. unfold clone_spec, clone_witness.
  destruct (clone_fork_flags_b flags);
    [apply clone_resolve_witness_ok | apply unmodeled_intro].
Qed.

(** The same witness, carrying the copy-in ledger the [clone3] resolution
    records.  [clone_resolve_witness] answers with [mkEffect], whose
    [eff_copyins] is [], so [record_copyins_ok_empty] applies directly. *)
Definition clone3_resolve_witness (uargs : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (clone_no_shared_file_b (m_fds m)) then Unmodeled
  else Ok (with_copyins [(uargs, CLONE_ARGS_SIZE_nat)]
             (mkEffect (errno_ret EAGAIN) [] [])) m [].

Lemma clone3_resolve_witness_ok : forall i uargs m,
  clone3_resolve uargs i m (clone3_resolve_witness uargs m).
Proof.
  intros. unfold clone3_resolve, clone3_resolve_witness.
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg.
  - apply record_copyins_unmodeled.
    unfold clone_resolve. eapply bind_unmodeled2; [apply get_model_ok|].
    cbv beta. rewrite Hg. cbv iota. apply unmodeled_intro.
  - apply record_copyins_ok_empty; [reflexivity|].
    pose proof (clone_resolve_witness_ok i m) as H.
    unfold clone_resolve_witness in H. rewrite Hg in H. exact H.
Qed.

Definition clone3_witness (i : SyscallInput) (uargs size : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then Unmodeled
  else match user_read i m uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
       | UFault | USpecial => Unmodeled        (* unreadable clone_args *)
       | UOk bs =>
           if clone3_fork_args_b bs then clone3_resolve_witness uargs m
           else Unmodeled
       end.

Lemma clone3_witness_ok : forall i uargs size m,
  clone3_spec uargs size i m (clone3_witness i uargs size m).
Proof.
  intros. unfold clone3_spec, clone3_witness.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))); cbv iota;
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (user_read i m uargs (Z_to_bv 64 CLONE_ARGS_SIZE))
    as [bs| |]; [|apply unmodeled_intro|apply unmodeled_intro].
  destruct (clone3_fork_args_b bs);
    [apply clone3_resolve_witness_ok | apply unmodeled_intro].
Qed.
