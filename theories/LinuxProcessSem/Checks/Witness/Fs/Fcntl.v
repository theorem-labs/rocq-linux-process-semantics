(** * LinuxProcessSem.Checks.Witness.Fs.Fcntl — the fcntl (25) witness, and its proof

    Mirrors [Sys/Fs/Fcntl.v], which answers to Linux [fs/fcntl.c]: this
    file holds the witnesses for the syscalls defined there, and no
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
  Prelude Fs.ReadWrite.

(** Mirrors [Fcntl.stream_setfl]: 0 with the end's O_NONBLOCK recorded
    for an [arg] carrying no [setfl_acted_on] bit but O_NONBLOCK, and
    [Unmodeled] for any other [arg]. *)
Definition stream_setfl_witness (fd id : word) (side : bool) (st : StreamEnd)
    (arg : word) (m : Model) : outcome SyscallEffect :=
  if Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0
  then ret_outcome (Z_to_bv 64 0)
         (with_fds (fd_insert (m_fds m) fd
                      (FdStream id side
                         (se_set_nonblock st (Z.testbit (bv_unsigned arg) 11)))) m)
  else Unmodeled.

Lemma stream_setfl_witness_ok : forall fd id side st arg i m,
  stream_setfl fd id side st arg m i m (stream_setfl_witness fd id side st arg m).
Proof.
  intros. unfold stream_setfl, stream_setfl_witness.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota.
  - eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - apply unmodeled_intro.
Qed.

(** Mirrors [Fcntl.eventfd_setfl]: [stream_setfl_witness]'s answer,
    with the bit recorded in the context's [ef_nonblock]. *)
Definition eventfd_setfl_witness (fd : word) (ctx : EventfdCtx) (arg : word)
    (m : Model) : outcome SyscallEffect :=
  if Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0
  then ret_outcome (Z_to_bv 64 0)
         (with_fds (fd_insert (m_fds m) fd
                      (FdEventfd (ef_set_nonblock ctx (Z.testbit (bv_unsigned arg) 11)))) m)
  else Unmodeled.

Lemma eventfd_setfl_witness_ok : forall fd ctx arg i m,
  eventfd_setfl fd ctx arg m i m (eventfd_setfl_witness fd ctx arg m).
Proof.
  intros. unfold eventfd_setfl, eventfd_setfl_witness.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota.
  - eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - apply unmodeled_intro.
Qed.

(** fcntl witness: -EBADF on a closed fd, 0 for F_SETFD and for F_GETFD
    (the first of its two admitted answers), [stream_setfl_witness] or
    [eventfd_setfl_witness] for an F_SETFL on a stream-pair end or an
    eventfd, 0 for an F_SETFL on any other kind that provably changes
    nothing, the derived flag word for an F_GETFL on an fd kind
    [Fcntl.getfl_f_flags] answers for, and [Unmodeled] on every other
    command. *)
Definition fcntl_witness (fd cmd arg : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      if bv_eqb cmd F_SETFD then ret_outcome (Z_to_bv 64 0) m
      else if bv_eqb cmd F_GETFD then ret_outcome (Z_to_bv 64 0) m
      else if bv_eqb cmd F_SETFL then
        match e with
        | FdStream id side st => stream_setfl_witness fd id side st arg m
        | FdEventfd ctx => eventfd_setfl_witness fd ctx arg m
        | _ => if setfl_noop_on e arg then ret_outcome (Z_to_bv 64 0) m
               else Unmodeled
        end
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | Some fl => ret_outcome fl m
        | None => Unmodeled
        end
      else Unmodeled
  end.

Lemma fcntl_witness_ok : forall fd cmd arg i m,
  fcntl_spec fd cmd arg i m (fcntl_witness fd cmd arg m).
Proof.
  intros. unfold fcntl_spec, fcntl_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - destruct (bv_eqb cmd F_SETFD) eqn:Hd.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd. apply pure_ok.
    + destruct (bv_eqb cmd F_GETFD) eqn:Hgd.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd. apply alt_l. apply pure_ok.
      * destruct (bv_eqb cmd F_SETFL) eqn:Hs.
        -- (* one arm per fd kind: the stream-pair end's [stream_setfl],
              the eventfd's [eventfd_setfl], every other kind's
              [setfl_noop_on] *)
           destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |id side st|ctx|fam];
             (eapply bind_step; [apply get_model_ok|]); cbv beta iota; srw Hfd;
             [ .. | apply stream_setfl_witness_ok | apply eventfd_setfl_witness_ok | idtac ];
             match goal with
             | |- context [setfl_noop_on ?e arg] =>
                 destruct (setfl_noop_on e arg); cbv beta iota;
                 [apply pure_ok | apply unmodeled_intro]
             end.
        -- destruct (bv_eqb cmd F_GETFL) eqn:Hg.
           ++ destruct (getfl_f_flags e) as [fl|] eqn:Hgf.
              ** eapply bind_step; [apply get_model_ok|].
                 cbv beta iota; srw Hfd; srw Hgf. apply pure_ok.
              ** eapply bind_step; [apply get_model_ok|].
                 cbv beta iota; srw Hfd; srw Hgf. apply unmodeled_intro.
           ++ eapply bind_step; [apply get_model_ok|].
              cbv beta iota; srw Hfd. apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
Qed.
