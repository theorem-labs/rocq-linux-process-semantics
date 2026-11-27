(** * LinuxProcessSem.Checks.Cases.Fs.DPath — worked examples over getcwd (17)

    Mirrors [Sys/Fs/DPath.v], which answers to Linux [fs/d_path.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    Split out of [Checks/Examples.v], which keeps what is not
    per-syscall and re-exports this module. These are worked examples
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
  Prelude.

(** THE WORKING DIRECTORY THESE PINS READ.  [Fs.default_cwd] is "/work",
    five bytes, so the string [getcwd] delivers is six bytes long with
    its terminating NUL and six is the value the call returns.  Every
    pin below is a computation on that one number, which is what makes
    them a check on the arm rather than on a literal: change
    [Fs.default_cwd] and each of these recomputes. *)
Definition getcwd_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (Fs.standard_root Fs.default_cwd) None None None.

(** A writable landing zone at 4096, wide enough for the whole string. *)
Definition cwd_out : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4112 then Some 0 else None.

(** The zone one byte SHY of what the delivery needs, which is the shape
    that separates a partial [copy_to_user] from a whole one. *)
Definition cwd_out_short : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4101 then Some 0 else None.

(** THE SUCCESS ARM, which R22 is what made reachable: the declared
    working directory's bytes and one NUL land at [buf], and the call
    returns the length INCLUDING that NUL.

    The second conjunct is what makes the first non-vacuous: a kernel
    that returned the length WITHOUT the NUL — the off-by-one every
    reader of getcwd(2) has to get right — is rejected on the return
    value, with the same bytes delivered. *)
Example getcwd_answers_the_declared_directory :
  check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out)
    (mkEffect (Z_to_bv 64 6)
       [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
    getcwd_model
  = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out)
       (mkEffect (Z_to_bv 64 5)
          [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
       getcwd_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** A BUFFER EXACTLY BIG ENOUGH still succeeds, and one byte smaller is
    -ERANGE.  [len > size] is the kernel's own test, so the boundary is
    at [size = len] and not at [size = len - 1]; pinning both sides is
    what says which way the comparison runs. *)
Example getcwd_size_boundary_is_the_whole_string :
  check_syscall (mkInput 17 [4096; 6; 0; 0; 0; 0] (fun _ => None) cwd_out)
    (mkEffect (Z_to_bv 64 6)
       [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
    getcwd_model
  = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [4096; 5; 0; 0; 0; 0] (fun _ => None) cwd_out)
       (mkEffect (errno_ret ERANGE) [] []) getcwd_model
     = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [4096; 5; 0; 0; 0; 0] (fun _ => None) cwd_out)
       (mkEffect (Z_to_bv 64 6)
          [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
       getcwd_model
     = CheckReject.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** A ZERO SIZE IS -ERANGE AND NOT -EFAULT, with a null [buf].  The
    kernel builds the path into a kernel page and compares before it
    looks at the destination at all, so [getcwd(NULL, 0)] never reaches
    [copy_to_user].  This is the pin that would catch a spec which
    probed [buf] first. *)
Example getcwd_null_buffer_zero_size_is_erange :
  check_syscall (mkInput 17 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ERANGE) [] []) getcwd_model
  = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) getcwd_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** THE -ENOMEM IS INJECTABLE ON EVERY BRANCH, because [__getname()]
    runs before all of them.  It is admitted beside the -ERANGE above
    and beside the success. *)
Example getcwd_enomem_is_injectable_everywhere :
  check_syscall (mkInput 17 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) getcwd_model
  = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out)
       (mkEffect (errno_ret ENOMEM) [] []) getcwd_model
     = CheckOk getcwd_model []
  (* and the two errnos R22 removed are NOT injectable any more: the cwd
     always exists and always fits *)
  /\ check_syscall (mkInput 17 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOENT) [] []) getcwd_model
     = CheckReject
  /\ check_syscall (mkInput 17 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENAMETOOLONG) [] []) getcwd_model
     = CheckReject.
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.

(** A DESTINATION THAT FAULTS MID-COPY IS DECLINED, not answered.  The
    range passes [access_ok] — it is inside the user address space —
    and then one of its bytes is not writable, which is the partially
    written buffer the model has no vocabulary for. *)
Example getcwd_partial_destination_is_declined :
  check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out_short)
    (mkEffect (Z_to_bv 64 6)
       [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
    getcwd_model
  = CheckUnmodeled.
Proof. vm_compute; reflexivity. Qed.

(** A DESTINATION OUTSIDE THE USER ADDRESS SPACE IS -EFAULT with nothing
    written, which is what [copy_to_user]'s own range test does before a
    byte moves. *)
Example getcwd_unusable_destination_is_efault :
  check_syscall (mkInput 17 [Z_to_bv 64 (2 ^ 63); 64; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) getcwd_model
  = CheckOk getcwd_model []
  /\ check_syscall (mkInput 17 [Z_to_bv 64 (2 ^ 63); 64; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (Z_to_bv 64 6)
          [(Z_to_bv 64 (2 ^ 63), Fs.default_cwd ++ [Fs.path_nul_byte])] [])
       getcwd_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** THE ANSWER FOLLOWS THE DECLARED DIRECTORY rather than a literal.
    The same call on a model whose working directory is the ROOT
    delivers two bytes, and the pin recomputes rather than repeating
    "/work". *)
Definition getcwd_root_model : Model :=
  with_cwd Fs.root getcwd_model.

Example getcwd_follows_the_model_not_a_literal :
  check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out)
    (mkEffect (Z_to_bv 64 2) [(4096, Fs.root ++ [Fs.path_nul_byte])] [])
    getcwd_root_model
  = CheckOk getcwd_root_model []
  /\ check_syscall (mkInput 17 [4096; 64; 0; 0; 0; 0] (fun _ => None) cwd_out)
       (mkEffect (Z_to_bv 64 6)
          [(4096, Fs.default_cwd ++ [Fs.path_nul_byte])] [])
       getcwd_root_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.
