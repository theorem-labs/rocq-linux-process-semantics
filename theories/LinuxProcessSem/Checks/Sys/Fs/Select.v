(** * LinuxProcessSem.Checks.Sys.Fs.Select — the pselect6 (72) and ppoll (73) checkers, and their proofs

    Mirrors [Sys/Fs/Select.v], which answers to Linux [fs/select.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** pselect6: deterministic throughout the modeled band, so the acceptor
    is the spec's own computation plus one equality, on the return, the
    writes and the copy-from-user ledger [Select.pselect6_reads].
    Everything that makes this syscall hard -- readiness, the timeout
    write-back, the [fdt->max_fds] clamp, a real signal mask -- is decided
    by [Select.pselect6_outcome] answering [None], which is
    [CheckUnmodeled] here. *)
Definition check_pselect6 (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | None => CheckUnmodeled
  | Some (r, ws) =>
      match eff with
      | mkEffectU r' ws' [] [] [] ks =>
          if bv_eqb r' r && writes_eqb ws' ws
             && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig)
          then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_pselect6_sound_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs).
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    cbv iota; [|discriminate].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig))
    eqn:Hg; [|discriminate].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hg Hk].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hr Hw].
  apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw.
  apply access_ranges_eqb_eq in Hk. subst r' ws' ks.
  injection H as <- <-. apply pure_ok.
Qed.

Lemma check_pselect6_sound_unmodeled :
  forall i n32 inp outp exp tsp sig eff m,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled ->
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled.
Proof.
  intros i n32 inp outp exp tsp sig eff m H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    cbv iota; [|apply unmodeled_intro].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig));
    discriminate.
Qed.

Lemma check_pselect6_complete_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs) ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold pselect6_spec in H. unfold check_pselect6. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
    access_ranges_eqb_refl.
  reflexivity.
Qed.

Lemma check_pselect6_complete_unmodeled :
  forall i n32 inp outp exp tsp sig m eff,
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled.
Proof.
  intros i n32 inp outp exp tsp sig m eff H.
  unfold pselect6_spec in H. unfold check_pselect6. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok; reflexivity.
Qed.

(** ppoll: deterministic throughout the modeled band, exactly as
    pselect6 is above, so the acceptor is the spec's own computation
    plus one equality, the ledger [Select.ppoll_reads] included.
    Everything that makes this syscall hard -- readiness for a descriptor
    whose answer is a schedule, the timeout write-back, the [kmalloc]
    above [N_STACK_PPS], a real signal mask -- is decided by
    [Select.ppoll_outcome] answering [None], which is [CheckUnmodeled]
    here. *)
Definition check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | None => CheckUnmodeled
  | Some (r, ws) =>
      match eff with
      | mkEffectU r' ws' [] [] [] ks =>
          if bv_eqb r' r && writes_eqb ws' ws
             && access_ranges_eqb ks (ppoll_reads i m ufds nfds tsp sig sigsetsize)
          then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_ppoll_sound_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs).
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. unfold ppoll_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [[r ws]|] eqn:Ho;
    cbv iota; [|discriminate].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (ppoll_reads i m ufds nfds tsp sig sigsetsize))
    eqn:Hg; [|discriminate].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hg Hk].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hr Hw].
  apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw.
  apply access_ranges_eqb_eq in Hk. subst r' ws' ks.
  injection H as <- <-. apply pure_ok.
Qed.

Lemma check_ppoll_sound_unmodeled :
  forall i ufds nfds tsp sig sigsetsize eff m,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m H.
  unfold check_ppoll in H. unfold ppoll_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [[r ws]|] eqn:Ho;
    cbv iota; [|apply unmodeled_intro].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (ppoll_reads i m ufds nfds tsp sig sigsetsize));
    discriminate.
Qed.

Lemma check_ppoll_complete_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold ppoll_spec in H. unfold check_ppoll. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
    access_ranges_eqb_refl.
  reflexivity.
Qed.

Lemma check_ppoll_complete_unmodeled :
  forall i ufds nfds tsp sig sigsetsize m eff,
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize m eff H.
  unfold ppoll_spec in H. unfold check_ppoll. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok; reflexivity.
Qed.
