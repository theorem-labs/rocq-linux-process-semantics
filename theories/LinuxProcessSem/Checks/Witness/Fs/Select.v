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

(** The remaining time {0,0} is in every range: it is what the clamp
    writes. *)
Lemma pselect_remaining_ok_zero : forall sec nsec : word,
  pselect_remaining_ok sec nsec pselect_timespec_zero = true.
Proof.
  intros sec nsec. unfold pselect_remaining_ok.
  change (Nat.eqb (length pselect_timespec_zero) 16) with true.
  change (tv_frac_of pselect_timespec_zero <? NSEC_PER_SEC)%Z with true.
  change (timespec_ns pselect_timespec_zero) with 0%Z.
  cbn [andb]. apply Z.leb_le.
  pose proof (bv_unsigned_in_range _ sec). pose proof (bv_unsigned_in_range _ nsec).
  unfold NSEC_PER_SEC. lia.
Qed.

(** One answer of [Select.pselect_answer]: the choice 0 -- every
    undecided pair end reports its smaller mask -- and, where a remaining
    time is chosen, {0,0}. *)
Definition pselect_answer_witness (reads : list (word * nat)) (pa : PselectAnswers)
    (m : Model) : outcome SyscallEffect :=
  match pa_ans pa 0%Z with
  | (r, ws, None) => Ok (with_copyins reads (mkEffect r ws [])) m []
  | (r, ws, Some (tsp, _)) =>
      Ok (with_copyins reads (mkEffect r (ws ++ [(tsp, pselect_timespec_zero)]) [])) m []
  end.

Lemma pselect_answer_witness_ok : forall reads pa i m,
  pselect_answer reads pa i m (pselect_answer_witness reads pa m).
Proof.
  intros reads pa i m. unfold pselect_answer, pselect_answer_witness.
  eapply bind_step; [apply (choose_ok _ 0%Z); apply Z.land_0_r|]. cbv beta.
  destruct (pa_ans pa 0%Z) as [[r ws] [[tsp [sec nsec]]|]]; cbv beta iota.
  - eapply bind_step;
      [apply (choose_ok _ pselect_timespec_zero); apply pselect_remaining_ok_zero|].
    cbv beta. apply pure_ok.
  - apply pure_ok.
Qed.

(** pselect6 witness: an answer [Select.pselect6_outcome] admits, or
    [Unmodeled] where it declines (fail closed, but never stuck). *)
Definition pselect6_witness (i : SyscallInput) (m : Model)
    (n32 inp outp exp tsp sig : word) : outcome SyscallEffect :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | None => Unmodeled
  | Some pa => pselect_answer_witness (pselect6_reads i n32 inp outp exp tsp sig) pa m
  end.

Lemma pselect6_witness_ok : forall n32 inp outp exp tsp sig i m,
  pselect6_spec n32 inp outp exp tsp sig i m (pselect6_witness i m n32 inp outp exp tsp sig).
Proof.
  intros. unfold pselect6_spec, pselect6_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|];
    cbv beta iota; [apply pselect_answer_witness_ok | apply unmodeled_intro].
Qed.

(** ppoll witness: an answer [Select.ppoll_outcome] admits, or
    [Unmodeled] where it declines (fail closed, but never stuck). *)
Definition ppoll_witness (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : outcome SyscallEffect :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | None => Unmodeled
  | Some pa => pselect_answer_witness (ppoll_reads i m ufds nfds tsp sig sigsetsize) pa m
  end.

Lemma ppoll_witness_ok : forall ufds nfds tsp sig sigsetsize i m,
  ppoll_spec ufds nfds tsp sig sigsetsize i m
    (ppoll_witness i m ufds nfds tsp sig sigsetsize).
Proof.
  intros. unfold ppoll_spec, ppoll_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|];
    cbv beta iota; [apply pselect_answer_witness_ok | apply unmodeled_intro].
Qed.
