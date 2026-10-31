(** * LinuxProcessSem.Checks.Cases.LinuxOnly — the model answers Linux's, and not QEMU user mode's

    Mirrors no single [Sys] module.  This file holds one worked example
    for each place where Linux v6.18.46 (commit 1f99e9ab748f) and QEMU
    user mode for riscv64 (QEMU 10.0.11) give different answers, and the
    model answers Linux's.  SCOPE.md's list "Where QEMU user mode
    differs" is the prose of the same list, with the file and the
    function on each side; the examples here are the executable half.

    EACH EXAMPLE HAS TWO CONJUNCTS and the second is the point: the
    first pins Linux's answer, and the second REJECTS QEMU's.  A
    [CheckReject] is the thing no truthful run can show, so it has to be
    written down rather than observed.

    [Checks/Examples.v] keeps what is not per-syscall and re-exports this
    module. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(* =========================================================================
   THE MACHINE: the LR/SC reservation across a system call

   Linux clears the reservation on each return to user mode.
   [ret_from_exception] (arch/riscv/kernel/entry.S, v6.18.46) ends with
   [REG_SC x0, a2, PT_EPC(sp)], and the unprivileged specification makes
   an SC fail when another SC stands between the LR and it.  QEMU user
   mode keeps it: [cpu_loop] (linux-user/riscv/cpu_loop.c, QEMU 10.0.11)
   never writes [env->load_res].
   ========================================================================= *)

(** [lrsc_ecall_clears]: after a system call the reservation is gone, so
    the [sc] of [lr; ecall; sc] fails whatever the memory holds.  Stated
    for EVERY machine state, which is what makes it the rule rather than
    one trace. *)
Lemma lrsc_ecall_clears : forall ms, ms_resv (advance_past_svc ms) = None.
Proof. reflexivity. Qed.

(** The same through the effect the syscall applies, which is the shape
    [Run.sstep_syscall] builds. *)
Lemma lrsc_ecall_clears_after_effect : forall ms eff,
  ms_resv (advance_past_svc (apply_effect ms eff)) = None.
Proof. reflexivity. Qed.

(** And it is NOT the identity on the field: a state carrying a
    reservation loses it, so the lemma above is a change rather than a
    restatement of the initial value. *)
Lemma lrsc_ecall_clears_a_live_reservation : forall ms a,
  ms_resv ms = Some a -> ms_resv (advance_past_svc ms) <> ms_resv ms.
Proof. intros ms a H. rewrite H. cbn. discriminate. Qed.

(* =========================================================================
   THE FIXTURES
   ========================================================================= *)

(** Three standard descriptors, a readable file on 3, a writable file on
    4, and NOTHING on 9 — the closed descriptor every "the fd is
    resolved first" example below uses. *)
Definition lo_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdFile [102] 0); (4, FdFileW [103] 0)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105]); ([103], [])] None None None.

(** The same table with one 8 KiB mapping at 65536, for mremap. *)
Definition lo_mapped_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 demo_limit) lo_model.

(* =========================================================================
   Q1 — mremap(MREMAP_MAYMOVE) at an EQUAL size

   Linux answers the old address and moves nothing: [mremap_to]
   (mm/mremap.c, v6.18.46) reaches no relocation when [new_len] equals
   [old_len].  QEMU user mode reserves a fresh range with
   [mmap_find_vma] before the host [mremap] ([target_mremap],
   linux-user/mmap.c, QEMU 10.0.11), so it RELOCATES the call.
   ========================================================================= *)

Example q1_mremap_equal_size_is_linux_answer_only :
  check_syscall (mkInput 216 [65536; 8192; 8192; MREMAP_MAYMOVE; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] []) lo_mapped_model = CheckOk lo_mapped_model []
  /\ check_syscall (mkInput 216 [65536; 8192; 8192; MREMAP_MAYMOVE; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 131072 [] []) lo_mapped_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q2 — ioctl, a tty-only request and a closed fd

   Linux resolves the descriptor first ([SYSCALL_DEFINE3(ioctl)],
   fs/ioctl.c: [CLASS(fd, f)(fd); if (fd_empty(f)) return -EBADF;]) and
   then answers -ENOTTY for a file, because [vfs_ioctl] returns it when
   [f_op->unlocked_ioctl] is NULL.  QEMU user mode answers before the
   descriptor: [do_ioctl] (linux-user/syscall.c) returns
   -TARGET_ENOTTY for a request it does not know.
   ========================================================================= *)

Example q2_ioctl_resolves_the_fd_first :
  check_syscall (mkInput 29 [9; TCGETS; 4096; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 29 [3; TCGETS; 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTTY) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 29 [9; TCGETS; 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTTY) [] []) lo_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   Q3 — readv and writev on a CLOSED fd

   Linux validates the unsigned 32-bit count and resolves the descriptor
   before it imports the vector (fs/read_write.c, [do_readv] and
   [do_writev]).  QEMU user mode locks the vector in [lock_iovec]
   (linux-user/syscall.c) before the fd, so it answers -EFAULT or
   -EINVAL there.
   ========================================================================= *)

Example q3_readv_writev_closed_fd_is_ebadf :
  check_syscall (mkInput 66 [9; 8192; 1; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 65 [9; 8192; 1; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 66 [9; 8192; 1; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) lo_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   Q4 — writev with a RAW count over IOV_MAX whose low 32 bits are in range

   Linux takes the unsigned 32-bit count (commits bc917be8 and 0504c074,
   first released in v4.1; fs/read_write.c, [do_writev]), so the call is
   the transfer that count names.  qemu-user's [lock_iovec] validates
   the raw 64-bit count instead and answers -EINVAL.  The same wide
   count on a CLOSED fd is still -EBADF, which is the half this example
   pins, because it needs no readable vector.
   ========================================================================= *)

Example q4_writev_wide_count_is_not_einval :
  check_syscall (mkInput 66 [9; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 66 [9; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q5 — sendto with a CLOSED fd beside a fault

   Linux resolves the descriptor before it touches the buffer
   ([__sys_sendto], net/socket.c), so a closed fd beside an unreadable
   buffer is -EBADF.  QEMU user mode locks the whole buffer first
   ([do_sendto], linux-user/syscall.c) and answers -EFAULT.
   ========================================================================= *)

Example q5_sendto_closed_fd_beside_a_fault_is_ebadf :
  check_syscall (mkInput 206 [9; 4096; 4; MSG_NOSIGNAL; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 206 [9; 4096; 4; MSG_NOSIGNAL; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q6 — socket with a type at or above SOCK_MAX

   [__sock_create] (net/socket.c) rejects [family < 0 || family >=
   NPROTO] with -EAFNOSUPPORT and only then [type >= SOCK_MAX] with
   -EINVAL, so an in-range family with an out-of-range type is -EINVAL.
   ========================================================================= *)

Example q6_socket_type_at_sock_max_is_einval :
  check_syscall (mkInput 198 [44; 11; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 198 [44; 11; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q7 — socket with an UNKNOWN FLAG BIT in the type word

   [__sys_socket_create] (net/socket.c) answers -EINVAL for
   [(type & ~SOCK_TYPE_MASK) & ~(SOCK_CLOEXEC | SOCK_NONBLOCK)] before
   anything else.  QEMU user mode drops the unknown bits in
   [target_to_host_sock_type] (linux-user/syscall.c), so the call can
   SUCCEED there.
   ========================================================================= *)

Example q7_socket_unknown_flag_bit_is_einval :
  check_syscall (mkInput 198 [AF_INET; Z_to_bv 64 (1 + 4096); 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 198 [AF_INET; Z_to_bv 64 (1 + 4096); 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q8 — eventfd2 with a refused flag word

   [SYSCALL_DEFINE2(eventfd2)] (fs/eventfd.c) answers -EINVAL for a word
   outside {EFD_CLOEXEC, EFD_NONBLOCK, EFD_SEMAPHORE}.  A qemu-user host
   whose target is sparc64, mips or parisc accepts some of those words,
   because its TARGET_O_NONBLOCK and TARGET_O_CLOEXEC differ
   (linux-user/syscall_defs.h).  CONFIG_EVENTFD=y is an assumption of
   the Linux system, named in SCOPE.md, which is why -ENOSYS is not an
   answer here either.
   ========================================================================= *)

Example q8_eventfd2_refused_flags_is_einval_only :
  check_syscall (mkInput 19 [0; 4; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 19 [0; 4; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOSYS) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q9 — epoll_pwait with a CLOSED epfd and a bad maxevents

   v6.18.46 resolves the descriptor first ([do_epoll_wait],
   fs/eventpoll.c), so the answer is -EBADF.  QEMU user mode checks the
   count and locks the buffer first ([TARGET_NR_epoll_pwait],
   linux-user/syscall.c).
   ========================================================================= *)

Example q9_epoll_pwait_closed_epfd_is_ebadf :
  check_syscall (mkInput 22 [9; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 22 [9; 4096; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   Q10 — accept4 with a CLOSED fd beside unknown flags

   [__sys_accept4] (net/socket.c) at v6.18.46 resolves the descriptor
   before it looks at the flags, so the answer is -EBADF.  QEMU user
   mode checks the flags first ([do_accept4], linux-user/syscall.c).
   ========================================================================= *)

Example q10_accept4_closed_fd_beside_bad_flags_is_ebadf :
  check_syscall (mkInput 242 [9; 0; 0; 4096; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 242 [9; 0; 0; 4096; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   THE RULES THIS REVISION CHANGED, beyond Q1-Q10

   Each of these answered QEMU user mode's outcome, or declined because
   of it, before this revision.
   ========================================================================= *)

(** [set_robust_list]: Linux's two answers, and no -ENOSYS.  The full
    pins are [Cases.Kernel.Futex.Syscalls.set_robust_list_lengths_and_head]
    and its [_linux_answer_only] neighbour. *)
Example set_robust_list_has_no_enosys :
  check_syscall (mkInput 99 [0; 24; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 99 [0; 24; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOSYS) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(** [mmap] with a MISALIGNED OFFSET: -EINVAL for every length, the
    wrapping one included.  [riscv_sys_mmap]
    (arch/riscv/kernel/sys_riscv.c) tests the offset before
    [ksys_mmap_pgoff] reads the length; [target_mmap]
    (linux-user/mmap.c) rounds and tests the length first and answers
    -ENOMEM. *)
Example mmap_misaligned_off_is_einval_at_every_length :
  check_syscall (mkInput 222 [0; Z_to_bv 64 (2 ^ 64 - 1); 1; 2; 999; 1]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 222 [0; Z_to_bv 64 (2 ^ 64 - 1); 1; 2; 999; 1]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) lo_model = CheckReject.
Proof. split; check_eq. Qed.

(** [mmap] of a FILE on a descriptor the process does not hold: -EBADF,
    because [ksys_mmap_pgoff] (mm/mmap.c) runs [fget] before [do_mmap].
    A LIVE descriptor still declines, for the two model reasons the arm
    states. *)
Example mmap_file_backed_closed_fd_is_ebadf :
  check_syscall (mkInput 222 [0; 4096; 1; 2; 9; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lo_model = CheckOk lo_model []
  /\ check_syscall (mkInput 222 [0; 4096; 1; 2; 9; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lo_model = CheckReject
  /\ check_syscall (mkInput 222 [0; 4096; 1; 2; 3; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) lo_model = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.
