(** * LinuxProcessSem.Checks.Cases.Kernel.Fork — worked examples over set_tid_address (96) and clone (220)

    Mirrors [Sys/Kernel/Fork.v], which answers to Linux [kernel/fork.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Lemma set_tid_address_first_choice_is_within_modeled_envelope :
  forall i m eff m' evs,
  m_tid m = None ->
  set_tid_address_spec i m (Ok eff m' evs) ->
  exists tid,
    (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z /\
    eff = mkEffect tid [] [] /\
    m' = with_tid tid m /\
    evs = [].
Proof.
  intros i m eff m' evs Htid Hspec.
  apply check_set_tid_address_complete_ok in Hspec.
  unfold check_set_tid_address in Hspec.
  destruct eff as [ret ws zs us cs copyins].
  destruct ws as [|w ws]; [|discriminate].
  destruct zs as [|z zs]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  rewrite Htid in Hspec.
  destruct ((0 <? bv_unsigned ret)%Z &&
            (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Hvalid;
    [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hvalid as [Hlo Hhi].
  apply Z.ltb_lt in Hlo. apply Z.ltb_lt in Hhi.
  exists ret. repeat split; try reflexivity; assumption.
Qed.

(* -------------------------------------------------------------------------
   clone (220) with namespace flags: the parent's view

   PAIRED TEST.  Before [Kernel.Fork.clone_ns_flags_b], [clone_spec]
   answered the single word SIGCHLD and declined every other, so the
   namespace word below was [CheckUnmodeled].  The case is that word,
   now answered with a pid (the child recorded) or any errno.  The
   controls are words the old text and the new one treat alike: the
   plain fork word answers in both, and a CLONE_VM word declines in
   both.
   ------------------------------------------------------------------------- *)

Definition clone_in (flags : word) : SyscallInput :=
  mkInput 220 [flags; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** No descriptor at all, so [Kernel.Fork.clone_no_shared_file_b] lets
    every call through. *)
Definition clone_case_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** bubblewrap 0.13.1's flag word: SIGCHLD | CLONE_NEWNS | CLONE_NEWUSER
    | CLONE_NEWPID | CLONE_NEWNET | CLONE_NEWIPC | CLONE_NEWUTS. *)
Definition bwrap_clone_flags : word :=
  Z_to_bv 64 (SIGCHLD + CLONE_NEWNS + CLONE_NEWUSER + CLONE_NEWPID
              + CLONE_NEWNET + CLONE_NEWIPC + CLONE_NEWUTS).

(** The case: a pid, recorded with [with_children]; -EPERM (which is not
    in [Fork.clone_errnos]) and -ENOSPC, with the model unchanged; and
    0, the child's own return, refused. *)
Example clone_namespace_word_answers_a_pid :
  check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
    clone_case_model = CheckOk (with_children clone_case_model) []
  /\ check_syscall (clone_in bwrap_clone_flags)
       (mkEffect (errno_ret EPERM) [] []) clone_case_model
       = CheckOk clone_case_model []
  /\ check_syscall (clone_in bwrap_clone_flags)
       (mkEffect (errno_ret 28) [] []) clone_case_model
       = CheckOk clone_case_model []
  /\ check_syscall (clone_in bwrap_clone_flags) (mkEffect 0 [] [])
       clone_case_model = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** The controls.  [clone(SIGCHLD)] answers a pid in both texts, and
    keeps its four errnos (-EPERM is not one of them); [clone(CLONE_VM
    | SIGCHLD)] declines in both, and so does the namespace word with
    CLONE_VM added, and a namespace bit without SIGCHLD. *)
Example clone_controls_fork_word_and_clone_vm :
  check_syscall (clone_in (Z_to_bv 64 SIGCHLD)) (mkEffect 4242 [] [])
    clone_case_model = CheckOk (with_children clone_case_model) []
  /\ check_syscall (clone_in (Z_to_bv 64 SIGCHLD))
       (mkEffect (errno_ret EPERM) [] []) clone_case_model = CheckReject
  /\ check_syscall (clone_in (Z_to_bv 64 (CLONE_VM + SIGCHLD)))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (bwrap_clone_flags + Z_to_bv 64 CLONE_VM))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled
  /\ check_syscall (clone_in (Z_to_bv 64 CLONE_NEWUSER))
       (mkEffect 4242 [] []) clone_case_model = CheckUnmodeled.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** The descriptor gate is the fork word's: a regular file open declines
    the namespace word too. *)
Example clone_namespace_word_keeps_the_descriptor_gate :
  check_syscall (clone_in bwrap_clone_flags) (mkEffect 4242 [] [])
    (with_fds [(3, FdFile [] 0)] clone_case_model) = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.
