(** * LinuxProcessSem.Checks.Cases.Fs.Ioctl — worked examples over ioctl (29)

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

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
  Prelude Fs.ReadWrite.

Example ioctl_tiocgwinsz_enotty :
  check_syscall (mkInput 29 [1; TIOCGWINSZ; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof)) [].
Proof. check_eq. Qed.

Example ioctl_tty_only_requests_all_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof))
    = CheckOk (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof)) [])
    [TCGETS; TCSETS; TIOCSCTTY; TIOCGWINSZ;
     TIOCSWINSZ; TIOCNOTTY; TIOCGPTN; TIOCSPTLCK].
Proof. repeat constructor; check_eq. Qed.

Example ioctl_other_request_is_error :
  Forall (fun req =>
    check_syscall (mkInput 29 [1; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof))
    = CheckUnmodeled)
    [Z_to_bv 64 21531; Z_to_bv 64 21537].   (* FIONREAD 0x541B, FIONBIO 0x5421 *)
Proof. repeat constructor; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   THE NULL DEVICE

   [State.FdDevNull] is the descriptor [openat_devnull_spec] mints, and
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
  with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof)))
              3 (FdDevNull false true))
    (init_model [] 0 0 demo_sp demo_ed_top demo_limit (demo_input [] IEof)).

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
Proof. repeat constructor; check_eq. Qed.

(** FAIL-CLOSED beside the conforming answer: a request outside the
    eight is still declined ON THIS KIND, so the arm answers the eight
    rather than answering the descriptor.  The two here are the ones
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
Proof. repeat constructor; vm_compute; reflexivity. Qed.
