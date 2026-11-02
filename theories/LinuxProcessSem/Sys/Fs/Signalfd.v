(** * LinuxProcessSem.Sys.Fs.Signalfd — signalfd4 (74)

    This file answers to Linux [fs/signalfd.c]: it holds what the kernel
    defines there, and nothing else.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import
  Fs.File Kernel.Signal.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** The flag test of [do_signalfd4]: [flags & ~(SFD_CLOEXEC | SFD_NONBLOCK)]
    used as a truth value, so any residue is -EINVAL.  [flags] is [int],
    narrowed to its low 32 bits at the arm ([Syscall.flag32]).
      fs/signalfd.c [do_signalfd4]: read at v6.18.44; identical at v6.18.46. *)
Definition signalfd4_einval_b (flags : word) : bool :=
  negb (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0).

(** The errnos a new signalfd can still meet past the gates: [kmalloc]'s
    -ENOMEM for the context, [get_unused_fd_flags]'s -EMFILE (and
    [expand_files]'s -ENOMEM), and [anon_inode_getfile_fmode]'s -ENOMEM
    and -ENFILE ([alloc_file_pseudo]) — the same set as
    [EventFd.eventfd2_errnos], for the same functions.
      fs/signalfd.c [do_signalfd4], fs/file.c [alloc_fd], fs/anon_inodes.c
      [anon_inode_getfile_fmode]: read at v6.18.44; identical at v6.18.46. *)
Definition signalfd4_errnos : list Z := [ENOMEM; EMFILE; ENFILE].

(** The [ufd] that asks for a new descriptor: [-1] as an [int], which is
    the low 32 bits all set once the arm has narrowed it ([Syscall.fd32]). *)
Definition signalfd_new_ufd : word := Z_to_bv 64 (2 ^ 32 - 1).

(** [signalfd4 ufd user_mask sizemask flags].

    In [SYSCALL_DEFINE4(signalfd4)]'s order:
    - [sizemask] is [size_t] and compared full-width with
      [sizeof(sigset_t)], 8: anything else is -EINVAL, nothing read.
    - [copy_from_user] of the 8-byte mask: a range it cannot read is
      -EFAULT, nothing recorded ([Kernel.Signal.sigset_at]).  The bytes
      read go in the copy-in ledger on every later answer.
    - [do_signalfd4]: a flag word outside SFD_CLOEXEC | SFD_NONBLOCK is
      -EINVAL.
    - [ufd = -1]: a new descriptor at the lowest free fd holding
      [State.OSignalFd] with the mask SIGKILL and SIGSTOP removed
      ([Kernel.Signal.sigmask_strip], the [sigdelsetmask] the kernel
      applies before [signotset]) and the flag word, or an errno from
      [signalfd4_errnos].
    - any other [ufd] would update an existing signalfd's mask (or answer
      -EBADF / -EINVAL); that is declined.
      fs/signalfd.c [SYSCALL_DEFINE4(signalfd4)], [do_signalfd4]: read at v6.18.44; identical at v6.18.46. *)
Definition signalfd4_spec (ufd mask sizemask flags : word) : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES) then err_ret EINVAL
  else
    i <- input ;;
    match sigset_at (in_mem i) mask with
    | None => err_ret EFAULT
    | Some raw =>
        record_copyins [(mask, Z.to_nat NSIG_BYTES)]
          (if signalfd4_einval_b flags then err_ret EINVAL
           else if negb (bv_eqb ufd signalfd_new_ufd) then unmodeled
           else
             m <- get_model ;;
             alt (e <- errno_from signalfd4_errnos ;; err_ret e)
                 (fd <- lowest_fd (m_fds m) ;;
                  modify (with_fds (fd_insert (m_fds m) fd
                                     (FdOpaque (OSignalFd (sigmask_strip raw) flags)))) ;;
                  ret_only fd))
    end.
