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
   [wait4(-1, st, WNOHANG, 0)], after bubblewrap's SIGCHLD install and
   one [clone] that returned 4242.  Each example ends with a CONTROL the
   earlier text and this one answer alike.
   ========================================================================= *)

(** No descriptor, no mapping: nothing here reads either. *)
Definition wait4_case_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** bubblewrap 0.13.1's first call in [main] (bubblewrap.c:2910-2914):
    "Reset SIGCHILD to SIG_DFL allowing signalfd working properly if the
    parent process had set SIGCHLD to SIG_IGN" -- [sigaction(SIGCHLD,
    &sa, NULL)] with [sa_handler] SIG_DFL, an empty mask and flags 0,
    which musl passes as [rt_sigaction(17, act, NULL, 8)] over 24 zero
    bytes. *)
Definition wait4_sigaction_mem : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24) then Some 0 else None.
Definition wait4_sigaction_call : SyscallInput :=
  mkInput 134 [17; 4096; 0; 8; 0; 0] wait4_sigaction_mem (fun _ => None).

(** The model after that install: [State.procst_sigchld_dfl] set. *)
Definition wait4_installed : Model := with_sigchld_dfl true wait4_case_model.

Example wait4_install_first :
  check_syscall wait4_sigaction_call
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] [])) wait4_case_model
  = CheckOk wait4_installed [].
Proof. vm_compute. reflexivity. Qed.

(** The model after the install and one clone that returned 4242: the
    child bit set and the pid recorded ([State.with_child], as
    [Kernel.Fork.clone_resolve] leaves it). *)
Definition wait4_one_child : Model :=
  with_child (Z_to_bv 64 4242) wait4_installed.

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

(** The returned pid is checked even when a raw model records an errno
    word or a value outside the kernel pid envelope.  The valid recorded
    pid remains answerable through the same NULL-status call. *)
Example wait4_reap_bounds_raw_recorded_pids :
  check_syscall (wait4_in 0 (fun _ => None))
    (mkEffect (errno_ret ECHILD) [] [])
    (with_child (errno_ret ECHILD) wait4_installed) = CheckReject
  /\ check_syscall (wait4_in 0 (fun _ => None))
       (mkEffect (Z_to_bv 64 PID_MAX_ENVELOPE) [] [])
       (with_child (Z_to_bv 64 PID_MAX_ENVELOPE) wait4_installed) = CheckReject
  /\ check_syscall (wait4_in 0 (fun _ => None)) (mkEffect 4242 [] [])
       wait4_one_child = CheckOk wait4_reaped [].
Proof. repeat split; check_eq. Qed.

(** THE CASE, AT THE PRESENT VALUE OF THE INSTALL BIT: a clone that
    returned 4242 in a process that has made no SIGCHLD install.  Its
    disposition is the launcher's, which may be SIG_IGN ([execve] keeps
    one), and under SIG_IGN Linux reaps the child at its exit
    ([do_notify_parent], kernel/signal.c) and answers 0 and then
    -ECHILD, never 4242.  So every call declines: the bare 0, the reap
    with a status and with a NULL slot, and -ECHILD.  The text before
    the install bit answered the first three, which is the review
    finding this case closes.  THE CONTROLS: the same calls after the
    install ([wait4_one_child]) are answered, and a caller with no child
    gets -ECHILD with no install. *)
Definition wait4_no_install_child : Model :=
  with_child (Z_to_bv 64 4242) wait4_case_model.

Example wait4_no_sigchld_install_unmodeled :
  m_sigchld_dfl wait4_no_install_child = false
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_no_install_child
     = CheckUnmodeled
  /\ check_syscall wait4_call (wait4_reap_eff 0x0000) wait4_no_install_child
     = CheckUnmodeled
  /\ check_syscall (wait4_in 0 (fun _ => None)) (mkEffect 4242 [] [])
       wait4_no_install_child = CheckUnmodeled
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_no_install_child = CheckUnmodeled
  (* the controls *)
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_one_child
     = CheckOk wait4_one_child []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0000) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_case_model = CheckOk wait4_case_model [].
Proof.
  repeat match goal with |- _ /\ _ => split end;
    first [vm_compute; reflexivity | check_eq].
Qed.

(* =========================================================================
   THE ORDER OF THE CLONE AND THE INSTALL

   PAIRED TEST.  The bit is set only if every child the process has was
   cloned while SIGCHLD was SIG_DFL.  Linux decides whether to reap a
   child itself when that child exits, from the parent's disposition
   then ([do_notify_parent], kernel/signal.c:2241-2259, v6.18.46), so a
   child cloned under a launcher's SIG_IGN can be gone before a later
   SIG_DFL install, and [wait4] then answers 0 and -ECHILD, never its
   pid.  The text before [Kernel.Signal.sigchld_install_model] set the
   bit at that install too, and then answered 0 and the reap of 4242
   and rejected -ECHILD: the review finding these cases close.
   ========================================================================= *)

(** [clone(SIGCHLD, 0, 0, 0, 0)]: musl's [fork] word. *)
Definition wait4_clone_call : SyscallInput :=
  mkInput 220 [17; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** THE CASE: CLONE, THEN INSTALL, THEN [wait4].  The clone records
    4242 in a process that has made no install.  The install is still
    answered 0 with the 24 bytes of [act] in the ledger, as Linux
    answers it, but it leaves the model as it is: the bit stays clear,
    because 4242 was cloned under the launch's disposition.  So every
    [wait4] declines: the bare 0, the reap with a status and with a NULL
    slot, and -ECHILD. *)
Example wait4_clone_then_install_unmodeled :
  check_syscall wait4_clone_call (mkEffect 4242 [] []) wait4_case_model
    = CheckOk wait4_no_install_child []
  /\ check_syscall wait4_sigaction_call
       (with_copyins [(4096, 24%nat)] (mkEffect 0 [] [])) wait4_no_install_child
     = CheckOk wait4_no_install_child []
  /\ m_sigchld_dfl wait4_no_install_child = false
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_no_install_child
     = CheckUnmodeled
  /\ check_syscall wait4_call (wait4_reap_eff 0x0000) wait4_no_install_child
     = CheckUnmodeled
  /\ check_syscall (wait4_in 0 (fun _ => None)) (mkEffect 4242 [] [])
       wait4_no_install_child = CheckUnmodeled
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_no_install_child = CheckUnmodeled.
Proof.
  repeat match goal with |- _ /\ _ => split end;
    first [vm_compute; reflexivity | check_eq].
Qed.

(** THE CONTROL: INSTALL BEFORE ANY CLONE, bubblewrap's order (the
    install at bubblewrap.c:2910-2914, before any clone).  The install
    sets the bit, the clone records 4242 under SIG_DFL, and [wait4] is
    answered: 0 with the model unchanged, or the reap of 4242 with a
    status and with a NULL slot; -ECHILD is rejected. *)
Example wait4_install_then_clone_answered :
  check_syscall wait4_sigaction_call
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] [])) wait4_case_model
    = CheckOk wait4_installed []
  /\ check_syscall wait4_clone_call (mkEffect 4242 [] []) wait4_installed
     = CheckOk wait4_one_child []
  /\ m_sigchld_dfl wait4_one_child = true
  /\ check_syscall wait4_call (mkEffect 0 [] []) wait4_one_child
     = CheckOk wait4_one_child []
  /\ check_syscall wait4_call (wait4_reap_eff 0x0000) wait4_one_child
     = CheckOk wait4_reaped []
  /\ check_syscall (wait4_in 0 (fun _ => None)) (mkEffect 4242 [] [])
       wait4_one_child = CheckOk wait4_reaped []
  /\ check_syscall wait4_call (mkEffect (errno_ret ECHILD) [] [])
       wait4_one_child = CheckReject.
Proof.
  repeat match goal with |- _ /\ _ => split end;
    first [vm_compute; reflexivity | check_eq].
Qed.
