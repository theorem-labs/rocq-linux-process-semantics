(** * LinuxProcessSem.Checks.Cases.Kernel.Exit — worked examples over wait4 (260)

    Mirrors [Sys/Kernel/Exit.v], which answers to Linux [kernel/exit.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(* =========================================================================
   wait4 (260): A CALLER WITH A RECORDED CHILD

   PAIRED TEST.  Before [Kernel.Exit.wait4_spec] answered a caller with a
   recorded child, every call below at [wait4_one_child] was
   [CheckUnmodeled]: the arm declined any caller whose child bit was set.
   The call is bubblewrap 0.13.1's [monitor_child] loop through musl:
   [wait4(-1, st, WNOHANG, 0)], after one [clone] returned 4242.  Each
   example ends with a CONTROL the earlier text and this one answer
   alike.
   ========================================================================= *)

(** No descriptor, no mapping: nothing here reads either. *)
Definition wait4_case_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** The model after one clone that returned 4242: the child bit set and
    the pid recorded ([State.with_child], as [Kernel.Fork.clone_resolve]
    leaves it). *)
Definition wait4_one_child : Model :=
  with_child (Z_to_bv 64 4242) wait4_case_model.

(** The same model after the reap of 4242: the list is empty, and the
    child bit stays set. *)
Definition wait4_reaped : Model := with_child_pids [] wait4_one_child.

(** The status slot: four writable bytes at 0x3000, and nothing else. *)
Definition wait4_st : word := Z_to_bv 64 0x3000.
Definition wait4_st_wmem : word -> option byte :=
  fun a => if bv_leu 0x3000 a && bv_ltu a 0x3004 then Some 0 else None.

(** [wait4(-1, st, WNOHANG, 0)]: the pid word is the 64-bit -1, which
    [Syscall.pid32] truncates to [Exit.WAIT_ANY32]. *)
Definition wait4_in (st : word) (wmem : word -> option byte) : SyscallInput :=
  mkInput 260 [Z_to_bv 64 (-1); st; 1; 0; 0; 0] (fun _ => None) wmem.

(** The call with the writable slot. *)
Definition wait4_call : SyscallInput := wait4_in wait4_st wait4_st_wmem.

(** The reap of 4242 with status word [s] stored at the slot. *)
Definition wait4_reap_eff (s : Z) : SyscallEffect :=
  mkEffect 4242 [(wait4_st, Z_to_le_bytes 4 s)] [].

(** THE CASE, ACCEPTED.  0 with nothing stored, the model unchanged: the
    child lives and has nothing to report.  The pid 4242 with an exit
    status 0 (0x0000) or 1 (0x0100), a death by SIGKILL (0x0009), and a
    death by SIGABRT with a core (0x0086), each stored at the slot, and
    4242 removed from the list.  With a NULL slot, 4242 and no store.
    THE CONTROL: a caller with no child gets -ECHILD in both texts. *)
Example wait4_one_child_answers :
  check_syscall wait4_call (mkEffect 0 [] []) wait4_one_child
    = CheckOk wait4_one_child []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0000) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0100) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0009) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0086) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall (wait4_in 0 (fun _ => None)) (mkEffect 4242 [] [])
       wait4_one_child = CheckOk wait4_reaped []
  (* the control *)
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_case_model = CheckOk wait4_case_model [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** What the reap leaves: the list empty, the child bit still set. *)
Example wait4_reap_empties_the_list :
  m_child_pids wait4_one_child = [Z_to_bv 64 4242]
  /\ m_child_pids wait4_reaped = []
  /\ m_has_children wait4_reaped = true.
Proof. repeat match goal with |- _ /\ _ => split end; reflexivity. Qed.

(** THE CASE, REJECTED.  A pid the model did not record (4243); a
    stopped child's report (0x137f, SIGSTOP, which needs WUNTRACED);
    -ECHILD, which Linux never gives a caller with a child; a reap with
    nothing stored at a non-NULL slot; a store at another address; a
    store of two bytes; and 0 with a store.  THE CONTROL: a caller with
    no child rejects the bare 0 in both texts. *)
Example wait4_one_child_rejects :
  check_syscall wait4_call
    (mkEffect 4243 [(wait4_st, Z_to_le_bytes 4 0x0100)] []) wait4_one_child
    = CheckReject
  /\ check_syscall wait4_call (wait4_reap_eff 0x137f) wait4_one_child
     = CheckReject
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_one_child = CheckReject
  /\ check_syscall wait4_call (mkEffect 4242 [] []) wait4_one_child
     = CheckReject
  /\ check_syscall wait4_call
       (mkEffect 4242 [(Z_to_bv 64 0x3004, Z_to_le_bytes 4 0x0100)] [])
       wait4_one_child = CheckReject
  /\ check_syscall wait4_call
       (mkEffect 4242 [(wait4_st, Z_to_le_bytes 2 0x0100)] [])
       wait4_one_child = CheckReject
  /\ check_syscall wait4_call
       (mkEffect 0 [(wait4_st, Z_to_le_bytes 4 0x0000)] []) wait4_one_child
     = CheckReject
  (* the control *)
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_case_model
     = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

(** THE CASE, DECLINED.  A slot the model cannot see as four writable
    bytes declines the whole call, the bare 0 included: Linux would reap
    and then answer -EFAULT, which loses the child's status.  After the
    reap the bit is set and the list is empty, so whether a child remains
    is not known.  THE CONTROLS are these same two calls, which the
    earlier text declined too, and a caller with no child, which answers
    -ECHILD in both texts whatever the slot is. *)
Example wait4_one_child_declines :
  check_syscall (wait4_in wait4_st (fun _ => None)) (mkEffect 0 [] [])
    wait4_one_child = CheckUnmodeled
  /\ check_syscall (wait4_in wait4_st (fun _ => None))
       (mkEffect 4242 [(wait4_st, Z_to_le_bytes 4 0x0100)] [])
       wait4_one_child = CheckUnmodeled
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_reaped
     = CheckUnmodeled
  /\ check_syscall wait4_call (wait4_reap_eff 0x0100) wait4_reaped
     = CheckUnmodeled
  (* the control: no child, an unwritable slot, -ECHILD *)
  /\ check_syscall (wait4_in wait4_st (fun _ => None))
       (mkEffect (errno_ret ECHILD) [] []) wait4_case_model
     = CheckOk wait4_case_model [].
Proof.
  repeat match goal with |- _ /\ _ => split end;
    first [vm_compute; reflexivity | check_eq].
Qed.
