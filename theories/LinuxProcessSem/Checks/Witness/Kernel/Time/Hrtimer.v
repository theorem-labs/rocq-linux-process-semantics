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

    Every outcome it exhibits past a successful read of the request
    carries that read in its ledger: [nanosleep_spec] wraps the whole
    arm in [record_copyins], and a witness that left the ledger empty
    would no longer be an outcome the spec admits.  A request
    [access_ok] refuses is the one -EFAULT it exhibits with an EMPTY
    ledger, since nothing was copied.  An [rmtp] [access_ok] refuses
    still lets the completed sleep through, so the witness takes it
    there as everywhere else. *)
Definition nanosleep_witness (rqtp rmtp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match copy_bytes_map (in_mem i) rqtp 16 with
  | None =>
      if negb (access_okb rqtp 16) then ret_outcome (errno_ret EFAULT) m
      else Unmodeled                           (* unreadable request *)
  | Some req =>
      if negb (timespec_valid_b req)
      then Ok (with_copyins [(rqtp, 16%nat)] (mkEffect (errno_ret EINVAL) [] []))
             m []
      else
        let done :=
          Ok (with_copyins [(rqtp, 16%nat)] (mkEffect (Z_to_bv 64 0) [] []))
             (with_clock (nanosleep_clock (m_clock m) req []) m) [] in
        if w_is0 rmtp then done
        else match copy_bytes_map (in_wmem i) rmtp 16 with
             | None =>
                 if negb (access_okb rmtp 16) then done
                 else Unmodeled                (* unwritable remainder *)
             | Some _ => done
             end
  end.

Lemma nanosleep_witness_ok : forall i rqtp rmtp m,
  nanosleep_spec rqtp rmtp i m (nanosleep_witness rqtp rmtp i m).
Proof.
  intros. unfold nanosleep_spec, nanosleep_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_mem i) rqtp 16) as [req|] eqn:Hrq.
  2:{ cbv iota. destruct (negb (access_okb rqtp 16)) eqn:Ho; cbv iota;
        [|apply unmodeled_intro].
      unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (timespec_valid_b req)) eqn:Hv;
    [apply record_copyins_ok_empty; [reflexivity|apply pure_ok]|].
  cbv zeta.
  destruct (w_is0 rmtp) eqn:Hrm.
  - apply record_copyins_ok_empty; [reflexivity|].
    eapply bind_step; [apply get_model_ok|]. cbv beta. cbv iota zeta.
    apply alt_l. eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - destruct (copy_bytes_map (in_wmem i) rmtp 16) eqn:Hrm2.
    + apply record_copyins_ok_empty; [reflexivity|].
      eapply bind_step; [apply get_model_ok|]. cbv beta. cbv iota zeta.
      apply alt_l. eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb rmtp 16)) eqn:Ho.
      * apply record_copyins_ok_empty; [reflexivity|].
        eapply bind_step; [apply get_model_ok|]. cbv beta. cbv iota zeta.
        apply alt_l. eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * apply record_copyins_unmodeled.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
        cbv iota zeta. apply unmodeled_intro.
Qed.
