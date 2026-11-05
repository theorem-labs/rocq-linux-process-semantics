(** * LinuxProcessSem.Checks.Witness.Kernel.Exit — the exit (93), exit_group (94), wait4 (260) witnesses, and their proofs

    Mirrors [Sys/Kernel/Exit.v], which answers to Linux [kernel/exit.c]:
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

Definition exit_witness (code : word) (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) (with_halted (bv_and code (Z_to_bv 64 255)) m).

Lemma exit_witness_ok : forall code i m, exit_spec code i m (exit_witness code m).
Proof.
  intros. unfold exit_spec, exit_witness.
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(* =========================================================================
   set_tid_address (96) / ioctl (29)
   ========================================================================= *)

(** set_tid_address witness: the pinned tid if one is recorded; on the
    first call the environment pins the valid identity 1. *)

(* =========================================================================
   wait4 (260) — witness: -ECHILD for a caller with no child, 0 for a
   caller with a recorded child after its SIGCHLD SIG_DFL install.
   ========================================================================= *)

(** The bare 0 is always admissible where the reap is, so it is the
    witness there: it needs no choice of pid or status word. *)
Definition wait4_witness (upid stat_addr options rusage : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned upid) WAIT_ANY32) then Unmodeled
  else if negb (Z.eqb (bv_unsigned options) WNOHANG) then Unmodeled
  else if negb (w_is0 rusage) then Unmodeled
  else if m_has_children m then
    match m_child_pids m with
    | [] => Unmodeled
    | _ :: _ =>
        if negb (m_sigchld_dfl m) then Unmodeled
        else if negb (wait4_stat_ok_b (in_wmem i) stat_addr) then Unmodeled
        else ret_outcome (Z_to_bv 64 0) m
    end
  else ret_outcome (errno_ret ECHILD) m.

Lemma wait4_witness_ok : forall upid stat_addr options rusage i m,
  wait4_spec upid stat_addr options rusage i m
    (wait4_witness upid stat_addr options rusage i m).
Proof.
  intros upid stat_addr options rusage i m.
  unfold wait4_spec, wait4_witness.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [apply unmodeled_intro|].
  destruct (negb (w_is0 rusage)); [apply unmodeled_intro|].
  destruct (m_has_children m) eqn:Hc.
  - destruct (m_child_pids m) as [|q0 l0] eqn:Hl.
    + eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta. rewrite Hc, Hl. cbv iota. apply unmodeled_intro.
    + destruct (negb (m_sigchld_dfl m)) eqn:Hd.
      { eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta. rewrite Hc, Hl. cbv iota. rewrite Hd. cbv iota.
        apply unmodeled_intro. }
      destruct (negb (wait4_stat_ok_b (in_wmem i) stat_addr)) eqn:Hw.
      * eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta. rewrite Hc, Hl. cbv iota. rewrite Hd. cbv iota.
        eapply bind_unmodeled2; [apply input_ok|].
        cbv beta. rewrite Hw. cbv iota. apply unmodeled_intro.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta. rewrite Hc, Hl. cbv iota. rewrite Hd. cbv iota.
        eapply bind_step; [apply input_ok|].
        cbv beta. rewrite Hw. cbv iota.
        apply alt_l. unfold ret_only, ret_outcome. apply pure_ok.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta. rewrite Hc. cbv iota.
    unfold err_ret, ret_only. apply pure_ok.
Qed.
