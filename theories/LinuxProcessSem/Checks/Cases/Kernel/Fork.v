(** * LinuxProcessSem.Checks.Cases.Kernel.Fork — worked examples over set_tid_address (96) and clone3 (435)

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

(* =========================================================================
   clone3 (435): THE ARGUMENT BLOCK THAT WALKED OFF THE TOP OF THE
   ADDRESS SPACE

   [Fork.clone3_spec] read its 88-byte [struct clone_args] with
   [State.read_bytes_map] bare, a walk that wraps at 2^64 (see
   [State.copy_bytes_map]'s note), so a [uargs] in the last bytes of the
   address space whose range was backed at both ends was RESOLVED: the
   fields were judged and the call answered with the struct in the
   ledger.  Linux refuses the range before a byte moves:
   [copy_clone_args_from_user] (kernel/fork.c) reads the struct with
   [copy_struct_from_user], whose [copy_from_user] tests [access_ok] in
   [_inline_copy_from_user] (include/linux/uaccess.h).  The arm now asks
   the same through [State.copy_bytes_map] and answers -EFAULT with an
   empty ledger.

   The group is the refusal, the control that the bare walk really would
   have passed — and read a fork-shaped struct — and a neighbour at the
   top of what [State.access_okb] accepts that is still resolved.  The
   memories map exactly their own range.
   ========================================================================= *)

Definition clone3_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Definition clone3_wrap_uargs : word := Z_to_bv 64 (2 ^ 64 - 8).

(** Eight bytes below the top and eighty from 0: the 88-byte walk covers
    both halves.  Every byte is zero but the one at address 24, which is
    offset 32 of the struct — [exit_signal] — and holds SIGCHLD, so what
    the bare walk reads back is the ONE struct [Fork.clone3_fork_args_b]
    admits. *)
Definition clone3_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 80)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 24) then Z_to_bv 8 SIGCHLD
                      else Z_to_bv 8 0)
           else None.

Definition clone3_wrap_call : SyscallInput :=
  mkInput 435 [clone3_wrap_uargs; Z_to_bv 64 CLONE_ARGS_SIZE; 0; 0; 0; 0]
    clone3_wrap_mem (fun _ => None).

Example clone3_wrap_would_pass_the_bare_walk :
  read_bytes_map clone3_wrap_mem clone3_wrap_uargs (Z_to_bv 64 CLONE_ARGS_SIZE)
    <> None
  (* ...and what it reads back is the fork-shaped struct *)
  /\ option_map clone3_fork_args_b
       (read_bytes_map clone3_wrap_mem clone3_wrap_uargs
          (Z_to_bv 64 CLONE_ARGS_SIZE))
     = Some true.
Proof. split; vm_compute; [discriminate | reflexivity]. Qed.

Example clone3_wrap_args_are_not_copyable :
  copy_bytes_map clone3_wrap_mem clone3_wrap_uargs CLONE_ARGS_SIZE = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with an EMPTY ledger is the answer.  The -EAGAIN resolution
    the bare walk reached, with the struct in its ledger, is refused, and
    so is an -EFAULT that claims the struct was read. *)
Example clone3_wrapping_args_is_efault :
  check_syscall clone3_wrap_call (mkEffect (errno_ret EFAULT) [] []) clone3_model
  = CheckOk clone3_model []
  /\ check_syscall clone3_wrap_call
       (mkEffectU (errno_ret EAGAIN) [] [] [] []
                  [(clone3_wrap_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckReject
  /\ check_syscall clone3_wrap_call
       (mkEffectU (errno_ret EFAULT) [] [] [] []
                  [(clone3_wrap_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE NEIGHBOUR, and the half that says the arm still works: the last
    88 bytes [State.access_okb] accepts, mapped end to end, holding the
    same fork-shaped struct.  The call is still resolved — the -EAGAIN
    [kernel_clone] can always answer and a pid, each with the 88-byte
    ledger, the pid recording the child — and -EFAULT is refused there. *)
Definition clone3_top_uargs : word := Z_to_bv 64 (TASK_SIZE - CLONE_ARGS_SIZE).

Definition clone3_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - CLONE_ARGS_SIZE <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if bv_eqb a (clone3_top_uargs + Z_to_bv 64 32)
                      then Z_to_bv 8 SIGCHLD else Z_to_bv 8 0)
           else None.

Definition clone3_top_call : SyscallInput :=
  mkInput 435 [clone3_top_uargs; Z_to_bv 64 CLONE_ARGS_SIZE; 0; 0; 0; 0]
    clone3_top_mem (fun _ => None).

Example clone3_at_the_top_still_resolves :
  check_syscall clone3_top_call
    (mkEffectU (errno_ret EAGAIN) [] [] [] []
               [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
    clone3_model
  = CheckOk clone3_model []
  /\ check_syscall clone3_top_call
       (mkEffectU (Z_to_bv 64 4242) [] [] [] []
                  [(clone3_top_uargs, CLONE_ARGS_SIZE_nat)])
       clone3_model
     = CheckOk (with_children clone3_model) []
  /\ check_syscall clone3_top_call (mkEffect (errno_ret EFAULT) [] []) clone3_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A range [State.access_okb] ADMITS with nothing behind it is declined,
    not answered -EFAULT: the house rule [Kernel.Sys.prlimit64_spec]'s
    note states, which keeps -EFAULT for the ranges [access_ok] refuses. *)
Example clone3_admitted_but_unbacked_declines :
  check_syscall (mkInput 435 [clone3_top_uargs; Z_to_bv 64 CLONE_ARGS_SIZE;
                              0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) clone3_model
  = CheckUnmodeled.
Proof. check_eq. Qed.
