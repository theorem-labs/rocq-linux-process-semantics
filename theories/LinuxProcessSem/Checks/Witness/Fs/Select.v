(** * LinuxProcessSem.Checks.Witness.Fs.Select — the pselect6 (72) and ppoll (73) witnesses, and their proofs

    Mirrors [Sys/Fs/Select.v], which answers to Linux [fs/select.c]: this
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
  Prelude.

(** pselect6 witness: the single outcome [Select.pselect6_outcome] names,
    or [Unmodeled] where it declines (fail closed, but never stuck). *)
Definition pselect6_witness (i : SyscallInput) (m : Model)
    (n32 inp outp exp tsp sig : word) : outcome SyscallEffect :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | None => Unmodeled
  | Some (r, ws) =>
      Ok (with_copyins (pselect6_reads i m n32 inp outp exp tsp sig)
            (mkEffect r ws [])) m []
  end.

Lemma pselect6_witness_ok : forall n32 inp outp exp tsp sig i m,
  pselect6_spec n32 inp outp exp tsp sig i m (pselect6_witness i m n32 inp outp exp tsp sig).
Proof.
  intros. unfold pselect6_spec, pselect6_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|];
    cbv iota; [apply pure_ok | apply unmodeled_intro].
Qed.

(** ppoll witness: the single outcome [Select.ppoll_outcome] names, or
    [Unmodeled] where it declines (fail closed, but never stuck). *)
Definition ppoll_witness (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : outcome SyscallEffect :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | None => Unmodeled
  | Some (r, ws) =>
      Ok (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
            (mkEffect r ws [])) m []
  end.

Lemma ppoll_witness_ok : forall ufds nfds tsp sig sigsetsize i m,
  ppoll_spec ufds nfds tsp sig sigsetsize i m
    (ppoll_witness i m ufds nfds tsp sig sigsetsize).
Proof.
  intros. unfold ppoll_spec, ppoll_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [[r ws]|];
    cbv iota; [apply pure_ok | apply unmodeled_intro].
Qed.
