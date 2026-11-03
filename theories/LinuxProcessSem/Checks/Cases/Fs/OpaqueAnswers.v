(** * LinuxProcessSem.Checks.Cases.Fs.OpaqueAnswers — read (63) and write (64) on the opaque descriptors

    NOT a mirror of one [Sys] file: worked examples over the errno rows
    of [Fs.ReadWrite.read_opaque_spec] and [Fs.ReadWrite.write_opaque_spec]
    (fs/read_write.c), kept apart from [Checks.Cases.Fs.ReadWrite] so that
    each row has its positive and its control side by side.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers, read off without running a binary.

    THE PAIRED TESTS.  Before these rows the model declined each
    positive below.  Each control is an answer the kernel does not give
    on the same input: the success a broken row would accept, or the
    errno of a test the kernel runs LATER, which pins the order of
    [ksys_read]/[ksys_write]'s descriptor test, [vfs_read]/[vfs_write]'s
    mode tests and [access_ok] (fs/read_write.c:704-709, :727-732,
    :556-561, :670-675, Linux v6.18.46). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** fds 0-2 the launch's channels; 3 an O_PATH descriptor on "/proc";
    4 a /proc/sys leaf open read-only; 5 the /proc/self/fd directory at
    position 0, opened with the word 0x98900; 6 a non-blocking signalfd;
    7 a blocking eventfd; 8 a descriptor of the namespace and mount
    model. *)
Definition opq_model : Model :=
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  with_fds (fd_insert (fd_insert (fd_insert (fd_insert (fd_insert (fd_insert (m_fds m)
              3 (FdOpaque (OProcPath [47; 112; 114; 111; 99])))
              4 (FdOpaque (OProcFile proc_sys_overflowuid_path)))
              5 (FdOpaque (OProcFdDir (Z_to_bv 64 0x98900) (Some (Z_to_bv 64 0)))))
              6 (FdOpaque (OSignalFd (Z_to_bv 64 0x10000) (Z_to_bv 64 0x80800))))
              7 (FdOpaque (OEventFd (Z_to_bv 64 0x80000))))
              8 (FdOpaque (ONsFile 7))) m.

(** 4096 bytes at 0x10000, readable and writable, all zero. *)
Definition opq_mem : word -> option byte :=
  fun a => if bv_leu 0x10000 a && bv_ltu a 0x11000 then Some 0 else None.

(** An address [access_ok] refuses for any count: past [State.TASK_SIZE]. *)
Definition opq_bad : word := Z_to_bv 64 (2 ^ 63).

(** [write(fd, buf, count)] from [opq_mem]. *)
Definition opq_write_in (fd buf count : word) : SyscallInput :=
  mkInput 64 [fd; buf; count; 0; 0; 0] opq_mem (fun _ => None).

(** [read(fd, buf, count)] into [opq_mem]. *)
Definition opq_read_in (fd buf count : word) : SyscallInput :=
  mkInput 63 [fd; buf; count; 0; 0; 0] (fun _ => None) opq_mem.

(** W1, W2.  [write] on the O_PATH descriptor is -EBADF, and the model
    is unchanged: [fdget_pos] refuses the file (fs/file.c:1169-1170,
    :1225-1227).  It stays -EBADF for a buffer [access_ok] refuses,
    because the descriptor test comes first.  CONTROLS: the 1 byte a
    write that went through would answer, and the -EFAULT [vfs_write]'s
    [access_ok] would give if the descriptor were taken. *)
Example write_o_path_ebadf :
  check_syscall (opq_write_in 3 0x10000 1) (mkEffect (errno_ret EBADF) [] []) opq_model
  = CheckOk opq_model []
  /\ check_syscall (opq_write_in 3 opq_bad 1) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckOk opq_model []
  (* the controls *)
  /\ check_syscall (opq_write_in 3 0x10000 1)
       (with_copyins [(0x10000, 1%nat)] (mkEffect 1 [] [])) opq_model
     = CheckReject
  /\ check_syscall (opq_write_in 3 opq_bad 1) (mkEffect (errno_ret EFAULT) [] []) opq_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** W3, W4.  [write] on the /proc/sys leaf and on the /proc/self/fd
    directory is [vfs_write]'s FMODE_WRITE -EBADF (fs/read_write.c:670-671):
    both are open with the O_RDONLY access mode only.  The test comes
    before [access_ok], so a refused buffer is -EBADF too.  CONTROLS: the
    1 byte of a write that went through, and the later -EFAULT. *)
Example write_read_only_opaque_ebadf :
  check_syscall (opq_write_in 4 0x10000 1) (mkEffect (errno_ret EBADF) [] []) opq_model
  = CheckOk opq_model []
  /\ check_syscall (opq_write_in 4 opq_bad 1) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckOk opq_model []
  /\ check_syscall (opq_write_in 5 0x10000 1) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckOk opq_model []
  (* the controls *)
  /\ check_syscall (opq_write_in 4 0x10000 1)
       (with_copyins [(0x10000, 1%nat)] (mkEffect 1 [] [])) opq_model
     = CheckReject
  /\ check_syscall (opq_write_in 4 opq_bad 1) (mkEffect (errno_ret EFAULT) [] []) opq_model
     = CheckReject
  /\ check_syscall (opq_write_in 5 0x10000 1)
       (with_copyins [(0x10000, 1%nat)] (mkEffect 1 [] [])) opq_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** W5.  [write] on the signalfd is -EINVAL: the file is O_RDWR, so
    FMODE_WRITE passes, but [signalfd_fops] has no write operation, so
    FMODE_CAN_WRITE is clear (fs/signalfd.c:241-249, :280-282;
    fs/file_table.c:369-371; fs/read_write.c:672-673).  That test also
    comes before [access_ok].  CONTROLS: the -EBADF of a read-only file,
    and the later -EFAULT. *)
Example write_signalfd_einval :
  check_syscall (opq_write_in 6 0x10000 8) (mkEffect (errno_ret EINVAL) [] []) opq_model
  = CheckOk opq_model []
  /\ check_syscall (opq_write_in 6 opq_bad 8) (mkEffect (errno_ret EINVAL) [] []) opq_model
     = CheckOk opq_model []
  (* the controls *)
  /\ check_syscall (opq_write_in 6 0x10000 8) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckReject
  /\ check_syscall (opq_write_in 6 opq_bad 8) (mkEffect (errno_ret EFAULT) [] []) opq_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** R1.  [read] on the O_PATH descriptor is -EBADF, for a writable
    buffer and for one [access_ok] refuses ([ksys_read]'s descriptor
    test, fs/read_write.c:704-709).  CONTROL: the later -EFAULT. *)
Example read_o_path_ebadf :
  check_syscall (opq_read_in 3 0x10000 8) (mkEffect (errno_ret EBADF) [] []) opq_model
  = CheckOk opq_model []
  /\ check_syscall (opq_read_in 3 opq_bad 8) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckOk opq_model []
  (* the control *)
  /\ check_syscall (opq_read_in 3 opq_bad 8) (mkEffect (errno_ret EFAULT) [] []) opq_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** R2.  [read] on the /proc/self/fd directory: -EFAULT for a buffer
    [access_ok] refuses (fs/read_write.c:560-561), and otherwise
    [generic_read_dir]'s -EISDIR (fs/proc/fd.c:310-311;
    fs/libfs.c:224-227), for a zero count too.  The directory position is
    unchanged.  CONTROLS: -EISDIR for the refused buffer (the order), and
    a read that delivered 8 bytes. *)
Example read_procfd_dir_efault_eisdir :
  check_syscall (opq_read_in 5 0x10000 8) (mkEffect (errno_ret EISDIR) [] []) opq_model
  = CheckOk opq_model []
  /\ check_syscall (opq_read_in 5 0x10000 0) (mkEffect (errno_ret EISDIR) [] []) opq_model
     = CheckOk opq_model []
  /\ check_syscall (opq_read_in 5 opq_bad 8) (mkEffect (errno_ret EFAULT) [] []) opq_model
     = CheckOk opq_model []
  (* the controls *)
  /\ check_syscall (opq_read_in 5 opq_bad 8) (mkEffect (errno_ret EISDIR) [] []) opq_model
     = CheckReject
  /\ check_syscall (opq_read_in 5 0x10000 8)
       (mkEffect 8 [(0x10000, [0; 0; 0; 0; 0; 0; 0; 0])] []) opq_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** U1, UNCHANGED.  The eventfd's write still answers 8, with the 8
    bytes read on the copy-in ledger ([Fs.ReadWrite.write_eventfd_spec]).
    CONTROLS, declined before and after: [write] on the namespace model's
    descriptor, whose object may be of any type, and [read] on the
    signalfd and on that descriptor. *)
Example opaque_rows_unchanged :
  check_syscall (opq_write_in 7 0x10000 8)
    (with_copyins [(0x10000, 8%nat)] (mkEffect 8 [] [])) opq_model
  = CheckOk opq_model []
  (* the controls *)
  /\ check_syscall (opq_write_in 8 0x10000 8) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckUnmodeled
  /\ check_syscall (opq_read_in 6 0x10000 128) (mkEffect (errno_ret EAGAIN) [] []) opq_model
     = CheckUnmodeled
  /\ check_syscall (opq_read_in 8 0x10000 8) (mkEffect (errno_ret EBADF) [] []) opq_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.
