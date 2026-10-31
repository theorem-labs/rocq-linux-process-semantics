(** * LinuxProcessSem.Checks.Cases.Fs.EventPoll — worked examples over epoll_ctl (21)

    Mirrors [Sys/Fs/EventPoll.v], which answers to Linux [fs/eventpoll.c]:
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
  Prelude.

(** stdin at fd 0 and the regular file "f" open read-only at fd 3.  A
    regular file has no [->poll], so [epoll_ctl(3, op, 3, event)] answers
    -EPERM at step 4 of [EventPoll.epoll_ctl_outcome] once the event
    struct is past. *)
Definition epoll_model : Model :=
  mkModel [(0, FdChannel 0); (3, FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

(** Sixteen readable bytes at 4096: one [struct epoll_event] (riscv64
    does not pack it). *)
Definition ep_event_mem : word -> option byte :=
  bytes_at 4096 (repeat (Z_to_bv 8 0) 16).

(** THE COPY IS IN THE LEDGER.  [SYSCALL_DEFINE4(epoll_ctl)] copies the
    event struct before [do_epoll_ctl] looks at a descriptor, so the
    -EPERM for a target with no [->poll] comes after the 16 bytes at
    [event] were read, and the effect carries them.  The same answer
    claiming no read is rejected. *)
Example epoll_ctl_add_records_the_event_copy :
  check_syscall (mkInput 21 [3; 1; 3; 4096; 0; 0] ep_event_mem (fun _ => None))
    (with_copyins [(4096, 16%nat)] (mkEffect (errno_ret EPERM) [] [])) epoll_model
  = CheckOk epoll_model []
  /\ check_syscall (mkInput 21 [3; 1; 3; 4096; 0; 0] ep_event_mem (fun _ => None))
       (mkEffect (errno_ret EPERM) [] []) epoll_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** [EPOLL_CTL_DEL] copies nothing: [ep_op_has_event] is false, the
    event pointer is never dereferenced however wild it is, and the
    ledger is empty.  A ledger that names the event struct is
    rejected. *)
Example epoll_ctl_del_reads_no_event :
  check_syscall (mkInput 21 [3; 2; 3; 65536; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EPERM) [] []) epoll_model
  = CheckOk epoll_model []
  /\ check_syscall (mkInput 21 [3; 2; 3; 65536; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(65536, 16%nat)] (mkEffect (errno_ret EPERM) [] [])) epoll_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A copy that FAILS records nothing: an unreadable event struct is
    -EFAULT with an empty ledger, the convention
    [Kernel.Signal.rt_sigprocmask_spec] states, and a ledger that claims
    the read is rejected. *)
Example epoll_ctl_efault_records_nothing :
  check_syscall (mkInput 21 [3; 1; 3; 65536; 0; 0] ep_event_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) epoll_model
  = CheckOk epoll_model []
  /\ check_syscall (mkInput 21 [3; 1; 3; 65536; 0; 0] ep_event_mem (fun _ => None))
       (with_copyins [(65536, 16%nat)] (mkEffect (errno_ret EFAULT) [] [])) epoll_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.
