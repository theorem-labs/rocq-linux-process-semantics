(** * LinuxProcessSem.Sys.Kernel.Nsproxy — setns (268)

    This file answers to Linux [kernel/nsproxy.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs
    in is therefore not a judgement call — look up where the kernel
    defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** [setns fd nstype] (riscv64 nr 268: include/uapi/asm-generic/unistd.h:653,
    scripts/syscall.tbl:318, Linux v6.18.46).

    THE KERNEL ORDER ([SYSCALL_DEFINE2(setns)], kernel/nsproxy.c:536-574,
    v6.18.46).  [CLASS(fd, f)] is [fdget] (include/linux/file.h:83), and
    an empty [struct fd] returns -EBADF (:543-544).  [fdget] is
    [__fget_light(fd, FMODE_PATH)] (fs/file.c:1179-1182), which gives an
    empty [struct fd] both for a number that names no file and for an
    O_PATH file (:1169-1170; with a shared table [__fget_files_rcu],
    :1052-1055).  Then a namespace file ([proc_ns_file]: its [f_op] is
    [ns_file_operations], fs/nsfs.c:391-394) or a pidfd ([pidfd_pid],
    fs/pidfs.c:583-586) goes on to the join, and every other file is
    -EINVAL whatever [nstype] holds (:553-555).  The error returns before
    [prepare_nsset] (:556-557), so the call changes nothing.

    WHAT THE MODEL HOLDS.  No descriptor this model makes is a pidfd, and
    the only kind that may be a namespace file is [State.ONsFile], whose
    object is of a type the model does not know.  So the arm answers only
    errors, never joins a namespace, and declines [ONsFile].  No answer it
    gives reads [nstype], so [nstype] is not an argument.

    EVERY OTHER KIND IS -EINVAL, in one row, because the kernel's test is
    one else-branch: a regular file of the image, an inherited regular
    file ([State.OInherited], either form), a directory, a socket, a pipe
    end, /dev/null, /dev/urandom, a /proc/sys leaf, an eventfd, the
    /proc/self/fd directory, a signalfd and a regular-file alias
    ([State.OAlias]) are each neither a namespace file nor a pidfd.
    The standard channels are in that row on
    the assumption the model already makes for fds 0, 1 and 2, that they
    are pipes, sockets or terminals ([State.FdChannel]; [Fs.Sync.fsync_spec]'s
    -EINVAL and [Fs.ReadWrite.lseek_spec]'s -ESPIPE rest on it as well).
    A new [FdEntry] or [OpaqueFd] kind that can be a namespace file or a
    pidfd needs its own row here, ahead of the wildcard.

    [fd] arrives truncated to 32 bits ([Syscall.fd32]): the kernel
    declares it [int] and [fdget] reads it as [unsigned int], so a
    negative number names no file and is -EBADF. *)
Definition setns_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* no file: the empty [struct fd] *)
  | Some (FdOpaque (OProcPath _)) => err_ret EBADF
      (* an O_PATH file: [fdget] refuses FMODE_PATH, the same -EBADF *)
  | Some (FdOpaque (ONsFile _)) => unmodeled
      (* FAIL-CLOSED: the object may be a namespace file, and then the
         call may join its namespace ([State.ONsFile]) *)
  | Some _ => err_ret EINVAL
      (* neither a namespace file nor a pidfd: see above *)
  end.
