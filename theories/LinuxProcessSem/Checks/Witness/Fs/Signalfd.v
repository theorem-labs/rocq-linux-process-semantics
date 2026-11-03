(** * LinuxProcessSem.Checks.Witness.Fs.Signalfd — the signalfd4 (74) witness, and its proof

    Mirrors [Sys/Fs/Signalfd.v], which answers to Linux [fs/signalfd.c]:
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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** A new signalfd exhibits the FIRST of [signalfd4_errnos], the
    allocation failure, which the spec admits whatever the descriptor
    table holds; [Checks.Cases.Fs.Signalfd] pins that the descriptor is
    admitted too. *)
Definition signalfd4_witness (ufd mask sizemask flags : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES) then ret_outcome (errno_ret EINVAL) m
  else
    match sigset_at (in_mem i) mask with
    | None => ret_outcome (errno_ret EFAULT) m
    | Some _ =>
        if negb (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0)
        then Ok (with_copyins [(mask, Z.to_nat NSIG_BYTES)]
                   (mkEffect (errno_ret EINVAL) [] [])) m []
        else if negb (bv_eqb ufd signalfd_new_ufd) then Unmodeled
        else Ok (with_copyins [(mask, Z.to_nat NSIG_BYTES)]
                   (mkEffect (errno_ret ENOMEM) [] [])) m []
    end.

Lemma signalfd4_witness_ok : forall ufd mask sizemask flags i m,
  signalfd4_spec ufd mask sizemask flags i m (signalfd4_witness ufd mask sizemask flags i m).
Proof.
  intros ufd mask sizemask flags i m.
  unfold signalfd4_spec, signalfd4_einval_b, signalfd4_witness.
  destruct (negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)); cbv iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) mask) as [raw|]; cbv iota.
  2:{ unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0); cbn [negb]; cbv iota.
  2:{ apply record_copyins_ok_empty; [reflexivity|]. unfold err_ret, ret_only. apply pure_ok. }
  destruct (bv_eqb ufd signalfd_new_ufd); cbn [negb]; cbv iota.
  - apply record_copyins_ok_empty; [reflexivity|].
    eapply bind_step; [apply get_model_ok|]. cbv beta.
    apply alt_l. eapply bind_step; [apply (choose_ok _ ENOMEM); cbn; auto|].
    apply pure_ok.
  - unfold record_copyins. apply bind_unmodeled1. apply unmodeled_intro.
Qed.
