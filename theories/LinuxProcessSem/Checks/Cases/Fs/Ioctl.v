(** * LinuxProcessSem.Checks.Cases.Fs.Ioctl — worked examples over ioctl (29)

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Example ioctl_tiocgwinsz_enotty :
  check_syscall (mkInput 29 [1; TIOCGWINSZ; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)) [].
Proof. check_eq. Qed.

Example ioctl_tty_only_requests_all_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof))
    = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)) [])
    [TCGETS; TCSETS; TIOCSCTTY; TIOCGWINSZ;
     TIOCSWINSZ; TIOCNOTTY; TIOCGPTN; TIOCSPTLCK].
Proof. split_forall; split_conj; check_eq. Qed.

Example ioctl_other_request_is_error :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof))
    = CheckUnmodeled)
    [Z_to_bv 64 21531; Z_to_bv 64 21537].   (* FIONREAD 0x541B, FIONBIO 0x5421 *)
Proof. split_forall; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   THE NULL DEVICE

   [State.FdDevNull] is the descriptor [Open.open_devnull] mints, and
   the reason this kind needs its own examples is that the two above run
   on fd 1, which [init_model] makes an [FdChannel] -- a different
   constructor, so nothing they prove reaches this arm.

   The model below keeps the three standard descriptors and adds the
   null device on 3, which is the shape a program that [fopen]s
   "/dev/null" for writing is in: musl's [__fdopen] issues TIOCGWINSZ on
   the fresh stream to pick a buffering mode, and that is the call these
   examples are about.
   ------------------------------------------------------------------------- *)

Definition ioctl_devnull_model : Model :=
  with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)))
              3 (FdDevNull false true))
    (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)).

Example ioctl_devnull_tiocgwinsz_enotty :
  check_syscall (mkInput 29 [3; TIOCGWINSZ; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOTTY) [] []) ioctl_devnull_model
  = CheckOk ioctl_devnull_model [].
Proof. check_eq. Qed.

Example ioctl_devnull_tty_only_requests_all_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_devnull_model
    = CheckOk ioctl_devnull_model [])
    [TCGETS; TCSETS; TIOCSCTTY; TIOCGWINSZ;
     TIOCSWINSZ; TIOCNOTTY; TIOCGPTN; TIOCSPTLCK].
Proof. split_forall; check_eq. Qed.

(** FAIL-CLOSED beside the conforming answer: a request outside
    [Sys.Fs.Ioctl.tty_only_request] is still declined ON THIS KIND, so
    the arm answers the requests of [tty_only_request] rather than
    answering the descriptor.  The two here are the ones
    [do_vfs_ioctl] claims before the device is ever reached -- FIONBIO
    really succeeds and sets O_NONBLOCK, which this model does not
    carry, and FIONREAD on a character device is handed back to
    [vfs_ioctl] and so is -ENOTTY, an answer the model could give but
    has not written down.  Either way the model stops. *)
Example ioctl_devnull_other_request_is_unmodeled :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect 0 [] []) ioctl_devnull_model
    = CheckUnmodeled)
    [Z_to_bv 64 21537; Z_to_bv 64 21531].   (* FIONBIO 0x5421, FIONREAD 0x541B *)
Proof. split_forall; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   MUSL'S OTHER TERMIOS REQUESTS: TCSETSW, TCSETSF, TCSBRK, TCFLSH and
   TIOCGPGRP, which [tcsetattr] (TCSADRAIN, TCSAFLUSH), [tcdrain],
   [tcflush] and [tcgetpgrp] issue.  [Sys.Fs.Ioctl.tty_only_request]
   holds them with the eight above, for the reason its comment gives:
   [do_vfs_ioctl] (fs/ioctl.c:492-580, Linux v6.18.46) names none of
   them, and no table a non-terminal kind installs answers them, so
   [vfs_ioctl] (:44-53) answers -ENOTTY.
   ------------------------------------------------------------------------- *)

Definition musl_termios_requests : list word :=
  [TCSETSW; TCSETSF; TCSBRK; TCFLSH; TIOCGPGRP].

(** A regular file at fd 3, beside the three standard descriptors: the
    shape [ioctl_spec.c] probes. *)
Definition ioctl_file_model : Model :=
  with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)))
              3 (FdFile 1 0))
    (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)).

(** POSITIVE: -ENOTTY on stdout (a channel), on a regular file and on
    the null device, with no memory written. *)
Example ioctl_musl_termios_requests_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof))
    = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)) []
    /\ check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret ENOTTY) [] []) ioctl_file_model
       = CheckOk ioctl_file_model []
    /\ check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret ENOTTY) [] []) ioctl_devnull_model
       = CheckOk ioctl_devnull_model [])
    musl_termios_requests.
Proof. unfold musl_termios_requests; split_forall; split_conj; check_eq. Qed.

(** NEGATIVE: no longer declined, and nothing but -ENOTTY: a success (a
    terminal's answer) and -EINVAL (/dev/urandom's) are refused, where
    the old arm answered [CheckUnmodeled] to both. *)
Example ioctl_musl_termios_requests_refuse_success_and_einval :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof))
    = CheckReject
    /\ check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret EINVAL) [] []) ioctl_file_model
       = CheckReject)
    musl_termios_requests.
Proof. unfold musl_termios_requests; split_forall; split_conj; check_eq. Qed.

(* -------------------------------------------------------------------------
   /dev/urandom ANSWERS THE TERMINAL REQUESTS -EINVAL

   [urandom_fops] (drivers/char/random.c:1572-1581, Linux v6.18.46)
   installs [random_ioctl] (drivers/char/random.c:1492-1553), whose
   switch names the RND* requests only and whose default arm is -EINVAL
   (:1550-1551); [do_vfs_ioctl] names no request of [tty_only_request],
   and [vfs_ioctl] passes the -EINVAL through.
   The model below is a program that [fopen]ed "/dev/urandom" for
   writing: musl's [__fdopen] then issues TIOCGWINSZ on fd 3.
   ------------------------------------------------------------------------- *)

Definition ioctl_urandom_model : Model :=
  with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)))
              3 (FdUrandom false true))
    (init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof)).

Definition urandom_tty_requests : list word :=
  [TCGETS; TCSETS; TIOCSCTTY; TIOCGWINSZ; TIOCSWINSZ; TIOCNOTTY; TIOCGPTN;
   TIOCSPTLCK; TCSETSW; TCSETSF; TCSBRK; TCFLSH; TIOCGPGRP].

(** POSITIVE: -EINVAL, no memory written. *)
Example ioctl_urandom_tty_requests_einval :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EINVAL) [] []) ioctl_urandom_model
    = CheckOk ioctl_urandom_model [])
    urandom_tty_requests.
Proof. unfold urandom_tty_requests; split_forall; check_eq. Qed.

(** NEGATIVE: the -ENOTTY every other kind gives, and a success, are
    refused, where the old arm declined every request. *)
Example ioctl_urandom_tty_requests_refuse_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_urandom_model
    = CheckReject
    /\ check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
         (mkEffect 0 [] []) ioctl_urandom_model
       = CheckReject)
    urandom_tty_requests.
Proof. unfold urandom_tty_requests; split_forall; split_conj; check_eq. Qed.

(** FAIL-CLOSED beside it: RNDGETENTCNT reads the pool's entropy count,
    and FIONBIO and FIONREAD are [do_vfs_ioctl]'s own, so all three stay
    declined on this kind. *)
Example ioctl_urandom_other_request_is_unmodeled :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EINVAL) [] []) ioctl_urandom_model
    = CheckUnmodeled)
    [Z_to_bv 64 2147766784; Z_to_bv 64 21537; Z_to_bv 64 21531].
    (* RNDGETENTCNT 0x80045200, FIONBIO 0x5421, FIONREAD 0x541B *)
Proof. split_forall; vm_compute; reflexivity. Qed.
