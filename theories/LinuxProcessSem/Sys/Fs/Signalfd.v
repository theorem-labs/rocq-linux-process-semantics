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
  Fs.File Kernel.Signal Kernel.Fork.
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

(** * What a signalfd can hand back

    A signalfd answers from the signals PENDING for its process: a read
    dequeues them ([signalfd_read_iter], [signalfd_dequeue], which calls
    [dequeue_signal] against the descriptor's own mask) and a poll
    reports EPOLLIN when one in that mask is pending ([signalfd_poll],
    which asks [next_signal] of [current->pending] and of
    [signal->shared_pending]).  The model holds no pending set, so the
    arms that answer on a signalfd ([ReadWrite.read_signalfd_spec],
    [Select.ppoll_opaque_revents]) ask the two questions below instead,
    both about state the model does hold exactly.
      fs/signalfd.c [signalfd_poll], [signalfd_dequeue],
        [signalfd_read_iter], [signalfd_copyinfo]: read at v6.18.44; identical at v6.18.46.
      kernel/signal.c [sig_ignored], [sig_task_ignored],
        [sig_handler_ignored], [do_notify_parent]: read at v6.18.44; identical at v6.18.46. *)

(** Signal [sig] (1 to 64) is in the set [w]: bit [sig - 1], as
    [sigismember] (include/linux/signal.h) reads a one-word set. *)
Definition sigset_has (w : word) (sig : Z) : bool :=
  Z.testbit (bv_unsigned w) (sig - 1)%Z.

(** Can a SIGCHLD be pending for the signalfd with mask [mask]?

    Under SCOPE.md's assumption that nothing outside the process makes a
    signal pending for it, a SIGCHLD comes only from the process's own
    child, so the process must have one ([State.m_has_children]).  The
    signal must be BLOCKED ([State.m_sigmask]) to stay pending: SIG_DFL
    is the only SIGCHLD disposition the model admits
    ([Kernel.Signal.sigchld_dfl_install]), and at SIG_DFL an unblocked
    SIGCHLD is discarded when it is generated ([sig_ignored] returns
    false for a blocked signal only).  And the descriptor's mask must
    hold it.  When all three hold, whether one IS pending is the
    child's schedule, which is the environment's. *)
Definition signalfd_sigchld_may_pend (mask : word) (m : Model) : bool :=
  (sigset_has mask SIGCHLD && sigset_has (m_sigmask m) SIGCHLD
   && m_has_children m)%bool.

(** Does the descriptor's mask select a signal OTHER than SIGCHLD that
    the process may hold pending?  The process raises two signals itself,
    and a blocked one stays pending:
    - SIGABRT, from [Kernel.Signal.tkill_spec] with SIGABRT blocked;
      [State.m_sigabrt_pending] records it exactly.
    - SIGPIPE, from [ReadWrite.raise_sigpipe] with SIGPIPE blocked.
      Under SIG_DFL [State.m_sigpipe_pending] records it exactly.  Under
      a launch's SIG_IGN the model discards it, but Linux queues a
      blocked signal whatever its handler ([sig_ignored]), so while
      SIGPIPE is blocked and ignored the model cannot tell.
    When this holds the arms DECLINE: [dequeue_signal] would hand back
    that signal first (or as well), and [signalfd_poll] would report it,
    and neither is something the model can say. *)
Definition signalfd_other_may_pend (mask : word) (m : Model) : bool :=
  ((sigset_has mask SIGABRT && m_sigabrt_pending m)
   || (sigset_has mask SIGPIPE
       && (m_sigpipe_pending m
           || (negb (m_sigpipe_default m) && sigpipe_blocked (m_sigmask m)))))%bool.

(** One [struct signalfd_siginfo] the model admits for a dequeued
    SIGCHLD: 128 bytes whose [ssi_signo], the little-endian [__u32] at
    offset 0, is 17.  Every other byte is the environment's: [ssi_pid],
    [ssi_uid], [ssi_status], [ssi_utime] and [ssi_stime] describe the
    child, and [ssi_code] how it changed ([signalfd_copyinfo]'s
    [SIL_CHLD] case). *)
Definition signalfd_record_ok (bs : list byte) : bool :=
  (Nat.eqb (length bs) (Z.to_nat SIGNALFD_SIGINFO_BYTES)
   && Z.eqb (bytes_le_to_Z (firstn 4 bs)) SIGCHLD)%bool.

(** [bs] is between 1 and [n] such records, one after another, as
    [signalfd_read_iter] copies them out: it dequeues and copies until
    the count is used up or [signalfd_dequeue] finds nothing more. *)
Fixpoint signalfd_records_b (n : nat) (bs : list byte) : bool :=
  match n with
  | O => false
  | S n' =>
      (signalfd_record_ok (firstn (Z.to_nat SIGNALFD_SIGINFO_BYTES) bs)
       && match skipn (Z.to_nat SIGNALFD_SIGINFO_BYTES) bs with
          | [] => true
          | rest => signalfd_records_b n' rest
          end)%bool
  end.

(** How many records a [read] of [count] bytes can return:
    [signalfd_read_iter] divides the iterator's count, which [vfs_read]
    has already clamped to [MAX_RW_COUNT] ([State.rw_count_clamp]), by
    the record size. *)
Definition signalfd_read_max (count : word) : Z :=
  (rw_count_clamp count / SIGNALFD_SIGINFO_BYTES)%Z.
