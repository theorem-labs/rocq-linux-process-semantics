(** * LinuxProcessSem.Checks.Witness.Kernel.Time.Hrtimer — the nanosleep (101) witness, and its proof

    Mirrors [Sys/Kernel/Time/Hrtimer.v], which answers to Linux
    [kernel/time/hrtimer.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

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

(** nanosleep: the witness always takes the COMPLETED-SLEEP arm.  That
    arm needs nothing chosen — no remainder is written — so it is
    available for every model state the guards let through, and the
    interrupted arm, whose remainder would have to be constructed, is
    never needed to show the spec is receptive.

    It reads the model only to compute the new clock: there is no gate
    on [m_clock] to re-play, [Kernel.Time.Hrtimer.nanosleep_clock]
    clamping a saturating deadline rather than the spec declining it,
    and none on the request's seconds field either — a [tv_sec] at or
    above [Uapi.KTIME_SEC_MAX] is a sleep toward [Uapi.KTIME_MAX] and
    the completed arm exhibits it like any other.

    Every outcome it exhibits is reached through a successful read of
    the request, so every one of them carries that read in its ledger:
    [nanosleep_spec] wraps the whole arm in [record_copyins], and a
    witness that left the ledger empty would no longer be an outcome
    the spec admits. *)
Definition nanosleep_witness (rqtp rmtp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match user_read i m rqtp (Z_to_bv 64 16) with
  | UFault => Unmodeled                        (* unreadable request *)
  | USpecial => Unmodeled                      (* request in the vDSO pair *)
  | UOk req =>
      if negb (timespec_valid_b req)
      then Ok (with_copyins [(rqtp, 16%nat)] (mkEffect (errno_ret EINVAL) [] []))
             m []
      else
        let done :=
          Ok (with_copyins [(rqtp, 16%nat)] (mkEffect (Z_to_bv 64 0) [] []))
             (with_clock (nanosleep_clock (m_clock m) req []) m) [] in
        if w_is0 rmtp then done
        else match read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16) with
             | None => Unmodeled               (* unwritable remainder *)
             | Some _ => done
             end
  end.

Lemma nanosleep_witness_ok : forall i rqtp rmtp m,
  nanosleep_spec rqtp rmtp i m (nanosleep_witness rqtp rmtp i m).
Proof.
  intros. unfold nanosleep_spec, nanosleep_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    [|apply unmodeled_intro|apply unmodeled_intro].
  destruct (negb (timespec_valid_b req)) eqn:Hv;
    [apply record_copyins_ok_empty; [reflexivity|apply pure_ok]|].
  cbv zeta.
  destruct (w_is0 rmtp) eqn:Hrm.
  - apply record_copyins_ok_empty; [reflexivity|]. cbv iota zeta.
    apply alt_l. eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2.
    + apply record_copyins_ok_empty; [reflexivity|]. cbv iota zeta.
      apply alt_l. eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + apply record_copyins_unmodeled. cbv iota zeta. apply unmodeled_intro.
Qed.
