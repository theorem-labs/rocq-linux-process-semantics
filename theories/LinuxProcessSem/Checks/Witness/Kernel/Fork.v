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
    envelope, and is never needed to show the spec is receptive.  The
    gate is the one both words ask of the table the caller keeps
    ([Kernel.Fork.forfeit_inherited]). *)
Definition clone_resolve_witness (m : Model) : outcome SyscallEffect :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then Unmodeled
  else ret_outcome (errno_ret EAGAIN) m.

Lemma clone_resolve_witness_ok : forall i m,
  clone_resolve i m (clone_resolve_witness m).
Proof.
  intros. unfold clone_resolve, clone_resolve_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota;
    [apply unmodeled_intro|].
  apply alt_l. eapply bind_step; [apply (choose_ok _ EAGAIN); cbn; auto|].
  apply pure_ok.
Qed.

(** The namespace word's resolution admits every errno but -EINTR behind
    the same gate, so the same -EAGAIN outcome witnesses it. *)
Lemma clone_ns_resolve_witness_ok : forall i m,
  clone_ns_resolve i m (clone_resolve_witness m).
Proof.
  intros. unfold clone_ns_resolve, clone_resolve_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota;
    [apply unmodeled_intro|].
  apply alt_l. eapply bind_step.
  { apply (choose_ok _ EAGAIN). cbv beta. unfold EAGAIN, EINTR. lia. }
  apply pure_ok.
Qed.

(** A word the argument checks refuse: -EINVAL behind the descriptor
    gate ([Kernel.Fork.clone_einval]). *)
Definition clone_einval_witness (m : Model) : outcome SyscallEffect :=
  if clone_no_shared_file_b (forfeit_inherited (m_fds m))
  then ret_outcome (errno_ret EINVAL) m
  else Unmodeled.

Lemma clone_einval_witness_ok : forall i m,
  clone_einval i m (clone_einval_witness m).
Proof.
  intros. unfold clone_einval, clone_einval_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m))); cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok | apply unmodeled_intro].
Qed.

(** [CLONE_NEWIPC] with [CLONE_SYSVSEM] admits every errno but -EINTR
    behind the gate, so the same -EAGAIN outcome witnesses it. *)
Lemma clone_ns_refused_witness_ok : forall i m,
  clone_ns_refused i m (clone_resolve_witness m).
Proof.
  intros. unfold clone_ns_refused, clone_resolve_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota;
    [apply unmodeled_intro|].
  unfold errno_any. eapply bind_step.
  { apply (choose_ok _ EAGAIN). cbv beta. unfold EAGAIN, EINTR. lia. }
  apply pure_ok.
Qed.

(** A word with stores: the body's witness when the stores are ones the
    model states.  The -EAGAIN answer is an errno, so it stores
    nothing. *)
Definition clone_stores_witness (i : SyscallInput) (r : CloneArgs) (m : Model)
    : outcome SyscallEffect :=
  if clone_stores_ok i m r then clone_resolve_witness m else Unmodeled.

Lemma clone_stores_witness_ok : forall (body : Sys SyscallEffect) i r m,
  body i m (clone_resolve_witness m) ->
  clone_with_stores r body i m (clone_stores_witness i r m).
Proof.
  intros body i r m Hb. apply clone_with_stores_iff. unfold clone_stores_witness.
  destruct (clone_stores_ok i m r) eqn:Hok; cbv iota.
  - left. split; [reflexivity|].
    unfold clone_resolve_witness in *.
    destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota in Hb |- *;
      [exact Hb|].
    unfold ret_outcome in *. cbv iota.
    exists (mkEffect (errno_ret EAGAIN) [] []). split; [exact Hb|].
    unfold tid_store_effect. cbn [eff_ret].
    replace (addr_is_error_b (errno_ret EAGAIN)) with true by (vm_compute; reflexivity).
    reflexivity.
  - right. split; reflexivity.
Qed.

Definition clone_witness (i : SyscallInput) (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve_witness m
  else if clone_ns_flags_b flags then clone_resolve_witness m
  else match clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) with
       | Some r =>
           if clone_arg_checks r then clone_einval_witness m
           else match clone_class r with
                | CcFork | CcNs => clone_stores_witness i r m
                | CcNsRefused => clone_resolve_witness m
                | CcNone => Unmodeled
                end
       | None => Unmodeled
       end.

Lemma clone_witness_ok : forall i flags m,
  clone_spec flags i m (clone_witness i flags m).
Proof.
  intros. unfold clone_spec, clone_witness.
  destruct (clone_fork_flags_b flags); cbv iota;
    [apply clone_resolve_witness_ok|].
  destruct (clone_ns_flags_b flags); cbv iota;
    [apply clone_ns_resolve_witness_ok|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota; [|apply unmodeled_intro].
  destruct (clone_arg_checks r); cbv iota; [apply clone_einval_witness_ok|].
  destruct (clone_class r); cbv iota.
  - apply clone_stores_witness_ok, clone_resolve_witness_ok.
  - apply clone_stores_witness_ok, clone_ns_resolve_witness_ok.
  - apply clone_ns_refused_witness_ok.
  - apply unmodeled_intro.
Qed.

(** The same witness, carrying the copy-in ledger the [clone3] resolution
    records.  [clone_resolve_witness] answers with [mkEffect], whose
    [eff_copyins] is [], so [record_copyins_ok_empty] applies directly. *)
Definition clone3_resolve_witness (reads : list (word * nat)) (m : Model)
    : outcome SyscallEffect :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then Unmodeled
  else Ok (with_copyins reads (mkEffect (errno_ret EAGAIN) [] [])) m [].

Lemma clone3_resolve_witness_ok : forall i reads m,
  clone3_resolve reads i m (clone3_resolve_witness reads m).
Proof.
  intros. unfold clone3_resolve, clone3_resolve_witness.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg.
  - apply record_copyins_unmodeled.
    unfold clone_resolve. eapply bind_unmodeled2; [apply get_model_ok|].
    cbv beta. rewrite Hg. cbv iota. apply unmodeled_intro.
  - apply record_copyins_ok_empty; [reflexivity|].
    pose proof (clone_resolve_witness_ok i m) as H.
    unfold clone_resolve_witness in H. rewrite Hg in H. exact H.
Qed.

(** A [clone3] record with stores ([Kernel.Fork.clone3_with_stores]):
    the copy's ledger around the same witness. *)
Definition clone3_stores_witness (i : SyscallInput) (reads : list (word * nat))
    (r : CloneArgs) (m : Model) : outcome SyscallEffect :=
  if clone_stores_ok i m r
  then clone3_resolve_witness reads m else Unmodeled.

Lemma clone3_stores_witness_ok : forall i reads r m,
  clone3_with_stores reads r i m (clone3_stores_witness i reads r m).
Proof.
  intros i reads r m. unfold clone3_with_stores, clone3_stores_witness.
  destruct (clone_stores_ok i m r) eqn:Hok; cbv iota.
  - unfold clone3_resolve_witness.
    destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg; cbv iota.
    + apply record_copyins_unmodeled. apply clone_with_stores_iff. left.
      split; [exact Hok|]. cbv iota.
      unfold clone_resolve. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta. rewrite Hg. cbv iota. apply unmodeled_intro.
    + apply record_copyins_ok_empty with (eff := mkEffect (errno_ret EAGAIN) [] []);
        [reflexivity|].
      apply clone_with_stores_iff. left. split; [exact Hok|]. cbv iota.
      exists (mkEffect (errno_ret EAGAIN) [] []). split.
      * pose proof (clone_resolve_witness_ok i m) as H.
        unfold clone_resolve_witness in H. rewrite Hg in H. exact H.
      * unfold tid_store_effect. cbn [eff_ret].
        replace (addr_is_error_b (errno_ret EAGAIN)) with true by (vm_compute; reflexivity).
        reflexivity.
  - apply record_copyins_unmodeled. apply clone_with_stores_iff. right.
    split; [exact Hok | reflexivity].
Qed.

(** [Kernel.Fork.clone3_on_struct]'s witness. *)
Definition clone3_on_struct_witness (i : SyscallInput) (reads : list (word * nat))
    (short : bool) (bs : list byte) (m : Model) : outcome SyscallEffect :=
  if clone3_fork_args_b bs then clone3_resolve_witness reads m
  else if clone3_einval_sz short bs
  then Ok (with_copyins reads (mkEffect (errno_ret EINVAL) [] [])) m []
  else match clone3_pre_sz short bs with
       | CdArgs r =>
           match clone_class r with
           | CcFork => clone3_stores_witness i reads r m
           | _ => Unmodeled
           end
       | _ => Unmodeled
       end.

Lemma clone3_on_struct_witness_ok : forall i reads short bs m,
  clone3_on_struct reads short bs i m (clone3_on_struct_witness i reads short bs m).
Proof.
  intros. unfold clone3_on_struct, clone3_on_struct_witness.
  destruct (clone3_fork_args_b bs); cbv iota; [apply clone3_resolve_witness_ok|].
  destruct (clone3_einval_sz short bs); cbv iota.
  { unfold clone3_einval. apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (clone3_pre_sz short bs) as [| |r]; cbv iota;
    [apply unmodeled_intro | apply unmodeled_intro|].
  destruct (clone_class r); cbv iota;
    [apply clone3_stores_witness_ok | apply unmodeled_intro | apply unmodeled_intro
    | apply unmodeled_intro].
Qed.

Definition clone3_witness (i : SyscallInput) (uargs size : word) (m : Model)
    : outcome SyscallEffect :=
  match clone3_copy (in_mem i) uargs (bv_unsigned size) with
  | C3Err reads en => Ok (with_copyins reads (mkEffect (errno_ret en) [] [])) m []
  | C3Decline => Unmodeled
  | C3Struct reads short bs => clone3_on_struct_witness i reads short bs m
  end.

Lemma clone3_witness_ok : forall i uargs size m,
  clone3_spec uargs size i m (clone3_witness i uargs size m).
Proof.
  intros. unfold clone3_spec, clone3_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (clone3_copy (in_mem i) uargs (bv_unsigned size)) as [reads en| |reads short bs];
    cbv iota.
  - unfold clone3_fail. apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok.
  - apply unmodeled_intro.
  - apply clone3_on_struct_witness_ok.
Qed.
