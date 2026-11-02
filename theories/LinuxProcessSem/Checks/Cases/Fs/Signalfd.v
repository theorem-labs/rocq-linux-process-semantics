(** * LinuxProcessSem.Checks.Cases.Fs.Signalfd — worked examples over signalfd4 (74)

    Mirrors [Sys/Fs/Signalfd.v], which answers to Linux [fs/signalfd.c]:
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
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** The launch's three channels: the lowest free descriptor is 3. *)
Definition sfd_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** [signalfd4(ufd, 0x2000, sizemask, flags)] with the 8 mask bytes [ms]
    at 0x2000. *)
Definition sfd_in (ufd : Z) (sizemask flags : Z) (ms : list byte) : SyscallInput :=
  mkInput 74 [Z_to_bv 64 ufd; 0x2000; Z_to_bv 64 sizemask; Z_to_bv 64 flags; 0; 0]
    (bytes_at 0x2000 ms) (fun _ => None).

(** SIGCHLD (17) alone: bit 16. *)
Definition sfd_sigchld : list byte := [0; 0; 1; 0; 0; 0; 0; 0].
(** SIGCHLD and SIGKILL (9, bit 8). *)
Definition sfd_sigchld_kill : list byte := [0; 1; 1; 0; 0; 0; 0; 0].

Definition sfd_minted (mask : Z) (flags : Z) : Model :=
  with_fds (fd_insert (m_fds sfd_model) 3
              (FdOpaque (OSignalFd (Z_to_bv 64 mask) (Z_to_bv 64 flags)))) sfd_model.

(** bubblewrap's monitor process makes its signalfd with
    [signalfd(-1, {SIGCHLD}, SFD_CLOEXEC|SFD_NONBLOCK)], which musl issues
    as [signalfd4(-1, mask, 8, 0x80800)].  The answer is the lowest free
    descriptor holding [State.OSignalFd] with that mask and word, or an
    allocation errno; the 8 mask bytes are on the ledger either way.
    SIGKILL in the mask is dropped before it is stored, as
    [do_signalfd4]'s [sigdelsetmask] drops it.  -EINTR is not an answer.
    Before this arm the model had no row for 74 and declined every call.

    THE CONTROL is declined by the old text and the new: a [ufd] that
    names an existing descriptor, which would update a signalfd's mask. *)
Example signalfd4_bwrap_monitor :
  check_syscall (sfd_in (-1) 8 0x80800 sfd_sigchld)
    (with_copyins [(0x2000, 8%nat)] (mkEffect 3 [] [])) sfd_model
  = CheckOk (sfd_minted 0x10000 0x80800) []
  /\ check_syscall (sfd_in (-1) 8 0x80800 sfd_sigchld_kill)
       (with_copyins [(0x2000, 8%nat)] (mkEffect 3 [] [])) sfd_model
     = CheckOk (sfd_minted 0x10000 0x80800) []
  /\ check_syscall (sfd_in (-1) 8 0x80800 sfd_sigchld)
       (with_copyins [(0x2000, 8%nat)] (mkEffect (errno_ret EMFILE) [] [])) sfd_model
     = CheckOk sfd_model []
  /\ check_syscall (sfd_in (-1) 8 0x80800 sfd_sigchld)
       (with_copyins [(0x2000, 8%nat)] (mkEffect (errno_ret EINTR) [] [])) sfd_model
     = CheckReject
  (* a descriptor other than the lowest free one *)
  /\ check_syscall (sfd_in (-1) 8 0x80800 sfd_sigchld)
       (with_copyins [(0x2000, 8%nat)] (mkEffect 4 [] [])) sfd_model
     = CheckReject
  (* the control *)
  /\ check_syscall (sfd_in 5 8 0x80800 sfd_sigchld)
       (with_copyins [(0x2000, 8%nat)] (mkEffect 5 [] [])) sfd_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** THE GATES, in [SYSCALL_DEFINE4(signalfd4)]'s order: a [sizemask]
    other than 8 is -EINVAL with nothing read; a mask [copy_from_user]
    cannot read is -EFAULT with nothing recorded; a flag outside
    SFD_CLOEXEC|SFD_NONBLOCK is -EINVAL after the mask is read, so the
    8 bytes are on the ledger.  None of them mints a descriptor. *)
Example signalfd4_gates :
  check_syscall (sfd_in (-1) 16 0x80800 sfd_sigchld) (mkEffect (errno_ret EINVAL) [] [])
    sfd_model
  = CheckOk sfd_model []
  /\ check_syscall
       (mkInput 74 [Z_to_bv 64 (-1); 0x5000; 8; Z_to_bv 64 0x80800; 0; 0]
          (bytes_at 0x2000 sfd_sigchld) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sfd_model
     = CheckOk sfd_model []
  /\ check_syscall (sfd_in (-1) 8 1 sfd_sigchld)
       (with_copyins [(0x2000, 8%nat)] (mkEffect (errno_ret EINVAL) [] [])) sfd_model
     = CheckOk sfd_model []
  /\ check_syscall (sfd_in (-1) 8 1 sfd_sigchld) (mkEffect (errno_ret EINVAL) [] [])
       sfd_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   read (63) on a signalfd ([ReadWrite.read_signalfd_spec])

   Before this arm the model declined every read of a signalfd.
   bubblewrap's monitor process, after its [clone], blocks SIGCHLD and
   reads 128 bytes from the signalfd it made for SIGCHLD with
   SFD_CLOEXEC|SFD_NONBLOCK.
   ========================================================================= *)

(** That state: fd 3 the signalfd for SIGCHLD with SFD_CLOEXEC|SFD_NONBLOCK,
    SIGCHLD blocked, and a child recorded. *)
Definition sfd_ready_model : Model :=
  with_children (with_sigmask (Z_to_bv 64 0x10000) (sfd_minted 0x10000 0x80800)).

(** The same with SIGCHLD NOT blocked. *)
Definition sfd_unblocked_model : Model :=
  with_children (sfd_minted 0x10000 0x80800).

(** The ready state on a BLOCKING signalfd (SFD_CLOEXEC alone). *)
Definition sfd_blocking_model : Model :=
  with_children (with_sigmask (Z_to_bv 64 0x10000) (sfd_minted 0x10000 0x80000)).

(** [read(fd, 0x10000, count)] into the 256 writable bytes at 0x10000. *)
Definition sfd_read_in (fd count : Z) : SyscallInput :=
  mkInput 63 [Z_to_bv 64 fd; 0x10000; Z_to_bv 64 count; 0; 0; 0] (fun _ => None)
    (bytes_at 0x10000 (repeat (Z_to_bv 8 0) 256)).

(** One [struct signalfd_siginfo] whose [ssi_signo] is [signo], the other
    124 bytes 0. *)
Definition sfd_record (signo : Z) : list byte :=
  word_le4 (Z_to_bv 64 signo) ++ repeat (Z_to_bv 8 0) 124.

(** bubblewrap's [read(signal_fd, &fdsi, 128)] with SIGCHLD blocked and a
    child recorded: -EAGAIN (no child has changed state yet), or 128 with
    one record whose [ssi_signo] is 17.  A record for signal 2 is
    rejected: SIGCHLD is the only signal that can be pending.  A second
    record does not fit in 128 bytes, and 64 bytes hold no record, which
    is -EINVAL.

    THE CONTROL, answered alike by the old text and the new: the same
    read on a BLOCKING signalfd is declined, because it may wait. *)
Example read_signalfd_bwrap_monitor :
  check_syscall (sfd_read_in 3 128) (mkEffect (errno_ret EAGAIN) [] []) sfd_ready_model
  = CheckOk sfd_ready_model []
  /\ check_syscall (sfd_read_in 3 128) (mkEffect 128 [(0x10000, sfd_record 17)] [])
       sfd_ready_model
     = CheckOk sfd_ready_model []
  /\ check_syscall (sfd_read_in 3 128) (mkEffect 128 [(0x10000, sfd_record 2)] [])
       sfd_ready_model
     = CheckReject
  /\ check_syscall (sfd_read_in 3 128)
       (mkEffect 256 [(0x10000, sfd_record 17 ++ sfd_record 17)] []) sfd_ready_model
     = CheckReject
  /\ check_syscall (sfd_read_in 3 64) (mkEffect (errno_ret EINVAL) [] []) sfd_ready_model
     = CheckOk sfd_ready_model []
  (* the control *)
  /\ check_syscall (sfd_read_in 3 128) (mkEffect (errno_ret EAGAIN) [] [])
       sfd_blocking_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** WITH SIGCHLD NOT BLOCKED nothing can be pending: at SIG_DFL an
    unblocked SIGCHLD is discarded when the child's exit generates it.
    So the record is rejected and -EAGAIN is the one answer.  A read of
    256 bytes may return two records where both fit.

    THE CONTROL, answered alike by the old text and the new: a read of
    the same blocking signalfd, declined. *)
Example read_signalfd_sigchld_unblocked :
  check_syscall (sfd_read_in 3 128) (mkEffect 128 [(0x10000, sfd_record 17)] [])
    sfd_unblocked_model
  = CheckReject
  /\ check_syscall (sfd_read_in 3 128) (mkEffect (errno_ret EAGAIN) [] [])
       sfd_unblocked_model
     = CheckOk sfd_unblocked_model []
  /\ check_syscall (sfd_read_in 3 256)
       (mkEffect 256 [(0x10000, sfd_record 17 ++ sfd_record 17)] []) sfd_ready_model
     = CheckOk sfd_ready_model []
  (* the control *)
  /\ check_syscall (sfd_read_in 3 256) (mkEffect (errno_ret EAGAIN) [] [])
       sfd_blocking_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** A SIGPIPE THE PROCESS HOLDS PENDING, selected by the descriptor's
    mask, makes the read decline: [dequeue_signal] would hand back that
    record, which the model does not describe.  The same mask with
    nothing pending answers. *)
Example read_signalfd_pending_sigpipe_declined :
  let mk := with_sigmask (Z_to_bv 64 0x11000) (sfd_minted 0x11000 0x80800) in
  check_syscall (sfd_read_in 3 128) (mkEffect (errno_ret EAGAIN) [] [])
    (with_sigpipe_pending mk)
  = CheckUnmodeled
  /\ check_syscall (sfd_read_in 3 128) (mkEffect (errno_ret EAGAIN) [] []) mk
     = CheckOk mk [].
Proof. cbv zeta. split; check_eq. Qed.
