(** * LinuxProcessSem.Checks.Witness.Fs.Locks — the flock (32) witness, and its proof

    Mirrors [Sys/Fs/Locks.v], which answers to Linux [fs/locks.c]: this
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

(** flock witness: every modeled arm is deterministic — the spec draws
    no errno and chooses nothing — so the witness is the answer itself,
    and [Unmodeled] on the shapes the spec declines. *)
Definition flock_witness (fd cmd : word) (m : Model) : outcome SyscallEffect :=
  if flock_mand_b cmd then ret_outcome (Z_to_bv 64 0) m
  else if negb (flock_cmd_ok_b cmd) then ret_outcome (errno_ret EINVAL) m
  else
    match fd_lookup (m_fds m) fd with
    | None => ret_outcome (errno_ret EBADF) m
    | Some e =>
        if flock_unlock_b cmd then ret_outcome (Z_to_bv 64 0) m
        else
          match e with
          | FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (Z_to_bv 64 0) m else Unmodeled
          | FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (Z_to_bv 64 0) m else Unmodeled
          | FdFileA p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (Z_to_bv 64 0) m else Unmodeled
          | FdFileRW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (Z_to_bv 64 0) m
              else Unmodeled
          | FdChannel _ => Unmodeled
          | FdDir       => Unmodeled
          | FdSocket _  => Unmodeled
          | FdPipe _ _  => Unmodeled
          | FdDevNull _ _ => Unmodeled
          | FdUrandom => Unmodeled
          | FdStream _ _ _ => Unmodeled
          end
    end.

Lemma flock_witness_ok : forall fd cmd i m,
  flock_spec fd cmd i m (flock_witness fd cmd m).
Proof.
  intros. unfold flock_spec, flock_witness.
  destruct (flock_mand_b cmd) eqn:Hmand.
  { eapply bind_step; [apply get_model_ok|]. cbv beta iota. apply pure_ok. }
  destruct (negb (flock_cmd_ok_b cmd)) eqn:Hok.
  { eapply bind_step; [apply get_model_ok|]. cbv beta iota. apply pure_ok. }
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    [| eapply bind_step; [apply get_model_ok|];
       cbv beta iota; srw Hfd; apply pure_ok ].
  destruct (flock_unlock_b cmd) eqn:Hun.
  { eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok. }
  destruct e as [c|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd sst].
  - eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; srw Hsole; [apply pure_ok | apply unmodeled_intro].
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; srw Hsole; [apply pure_ok | apply unmodeled_intro].
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; srw Hsole; [apply pure_ok | apply unmodeled_intro].
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; srw Hsole; [apply pure_ok | apply unmodeled_intro].
  - eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* /dev/null: declined *)
    eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* /dev/urandom: declined *)
    eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* a stream-pair end: declined, the [FdSocket] case *)
    eapply bind_step; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
Qed.
