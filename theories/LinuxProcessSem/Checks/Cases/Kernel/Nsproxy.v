(** * LinuxProcessSem.Checks.Cases.Kernel.Nsproxy — worked examples over setns (268)

    Mirrors [Sys/Kernel/Nsproxy.v], which answers to Linux
    [kernel/nsproxy.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    THE PAIRED TESTS.  Before [Kernel.Nsproxy], 268 had no entry in
    [Sys.SyscallTable.spec_table], so [check_syscall] answered
    [CheckUnmodeled] for every input of it.  Each positive below is a
    case that model declined and this one answers, and its control is
    the 0 of a join, which the arm never gives. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** fds 0-2 the launch's channels; 3 an O_PATH descriptor on "/proc";
    4 a non-blocking eventfd; 5 the read end of an empty pipe; 6 a
    descriptor of the namespace and mount model. *)
Definition setns_model : Model :=
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  with_pipes [(0, (@nil byte, 0%Z))]
    (with_fds (fd_insert (fd_insert (fd_insert (fd_insert (m_fds m)
                3 (FdOpaque (OProcPath [47; 112; 114; 111; 99])))
                4 (FdOpaque (OEventFd (Z_to_bv 64 0x80800))))
                5 (FdPipe 0 false))
                6 (FdOpaque (ONsFile 7))) m).

(** [setns(fd, nstype)]. *)
Definition setns_in (fd nstype : word) : SyscallInput :=
  mkInput 268 [fd; nstype; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** S1.  A number that names no descriptor is -EBADF (kernel/nsproxy.c:543-544),
    a negative one too ([fdget] reads it as [unsigned int]), and the
    model is unchanged.  CONTROL: the 0 of a join. *)
Example setns_no_descriptor_ebadf :
  check_syscall (setns_in 9 0) (mkEffect (errno_ret EBADF) [] []) setns_model
  = CheckOk setns_model []
  /\ check_syscall (setns_in (Z_to_bv 64 (-1)) 0) (mkEffect (errno_ret EBADF) [] [])
       setns_model
     = CheckOk setns_model []
  (* the control *)
  /\ check_syscall (setns_in 9 0) (mkEffect 0 [] []) setns_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** S2.  An O_PATH descriptor is the same -EBADF: [fdget] refuses
    FMODE_PATH (fs/file.c:1169-1170).  CONTROLS: the 0 of a join, and
    the -EINVAL of a file [fdget] takes. *)
Example setns_o_path_ebadf :
  check_syscall (setns_in 3 0) (mkEffect (errno_ret EBADF) [] []) setns_model
  = CheckOk setns_model []
  (* the controls *)
  /\ check_syscall (setns_in 3 0) (mkEffect 0 [] []) setns_model = CheckReject
  /\ check_syscall (setns_in 3 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** S3.  An eventfd is neither a namespace file nor a pidfd, so -EINVAL
    whatever [nstype] holds: 0 (any type) and CLONE_NEWNET alike
    (kernel/nsproxy.c:553-555).  CONTROL: the 0 of a join. *)
Example setns_eventfd_einval :
  check_syscall (setns_in 4 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
  = CheckOk setns_model []
  /\ check_syscall (setns_in 4 (Z_to_bv 64 CLONE_NEWNET)) (mkEffect (errno_ret EINVAL) [] [])
       setns_model
     = CheckOk setns_model []
  (* the control *)
  /\ check_syscall (setns_in 4 (Z_to_bv 64 CLONE_NEWNET)) (mkEffect 0 [] []) setns_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** S4.  A standard channel is -EINVAL, on the model's assumption that
    fds 0, 1 and 2 are pipes, sockets or terminals ([State.FdChannel]);
    2^32 names fd 0 ([Syscall.fd32]).  CONTROL: the 0 of a join. *)
Example setns_channel_einval :
  check_syscall (setns_in 0 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
  = CheckOk setns_model []
  /\ check_syscall (setns_in 2 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
     = CheckOk setns_model []
  /\ check_syscall (setns_in (Z_to_bv 64 (2 ^ 32)) 0) (mkEffect (errno_ret EINVAL) [] [])
       setns_model
     = CheckOk setns_model []
  (* the control *)
  /\ check_syscall (setns_in 0 0) (mkEffect 0 [] []) setns_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** S5.  A pipe end is -EINVAL.  CONTROL: the 0 of a join. *)
Example setns_pipe_einval :
  check_syscall (setns_in 5 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
  = CheckOk setns_model []
  (* the control *)
  /\ check_syscall (setns_in 5 0) (mkEffect 0 [] []) setns_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** U2, UNCHANGED.  A descriptor of the namespace and mount model may be
    a namespace file, so the call may join: declined, for the 0 and for
    the -EINVAL alike.  CONTROL: the eventfd beside it is answered. *)
Example setns_ns_file_declines :
  check_syscall (setns_in 6 0) (mkEffect 0 [] []) setns_model = CheckUnmodeled
  /\ check_syscall (setns_in 6 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
     = CheckUnmodeled
  (* the control *)
  /\ check_syscall (setns_in 4 0) (mkEffect (errno_ret EINVAL) [] []) setns_model
     = CheckOk setns_model [].
Proof. repeat split; check_eq. Qed.
