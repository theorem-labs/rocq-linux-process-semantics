(** * LinuxProcessSem.Checks.Witness.Fs.Pipe — the pipe2 (59) witness, and its proof

    Mirrors [Sys/Fs/Pipe.v], which answers to Linux [fs/pipe.c]: this
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

Definition pipe2_witness (fildes flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask) 0)
  then ret_outcome (errno_ret EINVAL) m
  else if negb (Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags) 0)
  then Unmodeled
  else
  match pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
  | Some _ => Unmodeled
  | None =>
      if negb (access_okb fildes 8) then ret_outcome (errno_ret EMFILE) m
      else
      match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8) with
      | Some _ => ret_outcome (errno_ret EMFILE) m
      | None =>
          match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1) with
          | None => ret_outcome (errno_ret EMFILE) m
          | Some _ => Unmodeled
          end
      end
  end.

Lemma pipe2_witness_ok : forall fildes flags i m,
  pipe2_spec fildes flags i m (pipe2_witness fildes flags i m).
Proof.
  intros. unfold pipe2_spec, pipe2_witness.
  (* every scrutinee here is closed over the quantified variables, so
     [destruct] substitutes it on both sides at once and the [rewrite]s
     below are only there for the occurrences it could not reach *)
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask =? 0)%Z)
    eqn:Hbad.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    rewrite ?Hbad; cbv beta iota zeta. apply pure_ok. }
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags =? 0)%Z)
    eqn:Hnz.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz; cbv beta iota zeta. apply unmodeled_intro. }
  destruct (pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m))) as [st|]
    eqn:Hid.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz, ?Hid; cbv beta iota zeta. apply unmodeled_intro. }
  destruct (negb (access_okb fildes 8)) eqn:Hak.
  { (* [access_ok] refuses the range: the spec offers the injected errno
       beside -EFAULT, and the witness takes the injected head *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz, ?Hid, ?Hak; cbv beta iota zeta.
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8)) as [w8|] eqn:H8.
  - (* the whole destination is writable: the injectable errno is the
       witness, since it is admissible whatever the fd table holds *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz, ?Hid, ?Hak, ?H8; cbv beta iota zeta.
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1)) as [w1|] eqn:H1.
    + (* a writable prefix and an unwritable tail: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|].
      rewrite ?Hbad, ?Hnz, ?Hid, ?Hak, ?H8, ?H1; cbv beta iota zeta.
      apply unmodeled_intro.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      rewrite ?Hbad, ?Hnz, ?Hid, ?Hak, ?H8, ?H1; cbv beta iota zeta.
      apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
Qed.
