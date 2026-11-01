(** * LinuxProcessSem.Checks.Cases.ParentTrace — bubblewrap parent's calls before clone

    A sequential replay, through the executable checker, of the 35 system
    calls that bubblewrap's parent makes before its namespace clone in a
    full-system trace on Linux 6.18.44.  Each call is written with the
    traced argument words and the traced return value.

    THE STATES ARE THE CHECKER'S, NOT HAND-WRITTEN.  [parent_trace_s00] is
    the parent after start-up; every later state [parent_trace_sNN] is
    [parent_trace_next] of the call before it, that is, the model the
    checker's [CheckOk] answer carries.  Each per-call Example states that
    the call is answered [CheckOk] with no events and that the answer's
    model is the next state, so a call the model refused, declined or
    answered with another value makes that Example (and the closing
    lemma [parent_trace_replays_to_the_clone]) false. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import
  Capability Fork Signal Sys.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs Require Import
  EventFd File Ioctl Open ReadWrite.

(* =========================================================================
   The replay machinery
   ========================================================================= *)

(** One traced call: the input the parent passes and the effect the
    kernel answered with. *)
Definition parent_trace_check (c : SyscallInput * SyscallEffect) (m : Model)
    : check_result :=
  check_syscall (fst c) (snd c) m.

(** The model after call [c]: the one the checker's [CheckOk] carries.
    The fallback is never taken on the replay below, because each
    per-call Example proves the answer is [CheckOk]. *)
Definition parent_trace_next (c : SyscallInput * SyscallEffect) (m : Model)
    : Model :=
  match parent_trace_check c m with
  | CheckOk m' _ => m'
  | _ => m
  end.

(** A list of calls, run in order: the final model, or [None] at the
    first call not answered [CheckOk] with no events. *)
Fixpoint parent_trace_run (cs : list (SyscallInput * SyscallEffect)) (m : Model)
    : option Model :=
  match cs with
  | [] => Some m
  | c :: rest =>
      match parent_trace_check c m with
      | CheckOk m' [] => parent_trace_run rest m'
      | _ => None
      end
  end.

Lemma parent_trace_run_step : forall c rest m m' r,
  parent_trace_check c m = CheckOk m' [] ->
  parent_trace_run rest m' = r ->
  parent_trace_run (c :: rest) m = r.
Proof. intros c rest m m' r Hc Hr. cbn [parent_trace_run]. rewrite Hc. exact Hr. Qed.

Definition parent_trace_call (no a0 a1 a2 a3 a4 a5 : word) : SyscallInput :=
  mkInput no [a0; a1; a2; a3; a4; a5] (fun _ => None) (fun _ => None).

(** The traced -1: mmap's descriptor word and wait4's pid. *)
Definition parent_trace_minus1 : word := Z_to_bv 64 (-1).

(** [sigmask(SIGCHLD)] is bit 16: the eight-byte set rt_sigprocmask reads. *)
Definition parent_trace_sigchld_set : word -> option byte :=
  bytes_at 0x3000 [0; 0; 1; 0; 0; 0; 0; 0].

(* =========================================================================
   The parent after start-up
   ========================================================================= *)

(** uid and gid 65534, descriptors 0-2, the traced initial break 0x51000
    and a stack pointer near the top of the window.

    THE MMAP BASE IS NOT IN THE TRACE; THE TWO TRACED ADDRESSES FIX IT.
    The model places the vDSO pair (four vvar pages and two text pages,
    24576 bytes, [State.vdso_reserved]) directly under the base, and a
    plain anonymous mapping at the highest free range below it
    ([Checks.Placement.linux_place_b]).  The traced 16384-byte mapping at
    0x7fff9428a000 therefore puts the pair at [0x7fff9428e000,
    0x7fff94294000) and the base at 0x7fff94294000; the same base gives the
    traced 4096-byte mapping at 0x7fff9428d000 after the munmap.  No
    image reservation is listed: the parent's own segments end below the
    break, and no traced call reaches them. *)
Definition parent_trace_s00 : Model :=
  with_creds (mkCreds 65534 65534 65534 65534 65534 65534 [])
    (init_model [] 0x51000 0x7fff94294000 0x7ffffffffdf0 demo_limit
       (demo_input [] IEof)).

(* =========================================================================
   The 35 traced calls, in trace order
   ========================================================================= *)

(** set_tid_address(0x4fd20) = 319 *)
Definition parent_trace_c01 : SyscallInput * SyscallEffect :=
  (parent_trace_call 96 0x4fd20 0 0 0 0 0, mkEffect 319 [] []).
(** prctl(PR_CAPBSET_READ, 0x20) = 1 *)
Definition parent_trace_c02 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x20 0 0 0, mkEffect 1 [] []).
(** prctl(PR_CAPBSET_READ, 0x30) = -EINVAL *)
Definition parent_trace_c03 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x30 0 0 0, mkEffect (errno_ret EINVAL) [] []).
(** prctl(PR_CAPBSET_READ, 0x28) = 1 *)
Definition parent_trace_c04 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x28 0 0 0, mkEffect 1 [] []).
(** prctl(PR_CAPBSET_READ, 0x2c) = -EINVAL *)
Definition parent_trace_c05 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x2c 0 0 0, mkEffect (errno_ret EINVAL) [] []).
(** prctl(PR_CAPBSET_READ, 0x2a) = -EINVAL *)
Definition parent_trace_c06 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x2a 0 0 0, mkEffect (errno_ret EINVAL) [] []).
(** prctl(PR_CAPBSET_READ, 0x29) = -EINVAL *)
Definition parent_trace_c07 : SyscallInput * SyscallEffect :=
  (prctl_in 23 0x29 0 0 0, mkEffect (errno_ret EINVAL) [] []).
(** rt_sigaction(17, {SIG_DFL, mask 0, flags 0}, NULL, 8) = 0; the call
    reads the 24-byte action. *)
Definition parent_trace_c08 : SyscallInput * SyscallEffect :=
  (mkInput 134 [17; 4096; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None),
   with_copyins [(4096, 24%nat)] (mkEffect 0 [] [])).
(** getuid() = 65534 *)
Definition parent_trace_c09 : SyscallInput * SyscallEffect :=
  (parent_trace_call 174 0 0 0 0 0 0, mkEffect 65534 [] []).
(** getgid() = 65534 *)
Definition parent_trace_c10 : SyscallInput * SyscallEffect :=
  (parent_trace_call 176 0 0 0 0 0 0, mkEffect 65534 [] []).
(** geteuid() = 65534 *)
Definition parent_trace_c11 : SyscallInput * SyscallEffect :=
  (parent_trace_call 175 0 0 0 0 0 0, mkEffect 65534 [] []).
(** capget({0x20080522, 0}, data) = 0, with 24 zero bytes stored. *)
Definition parent_trace_c12 : SyscallInput * SyscallEffect :=
  (capget_input LINUX_CAPABILITY_VERSION_3 cap_dataptr,
   mkEffectU 0 [(cap_dataptr, cap_image 0 0 0 0 0 0)] [] [] [] cap_ledger2).
(** prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) = 0 *)
Definition parent_trace_c13 : SyscallInput * SyscallEffect :=
  (prctl_in 38 1 0 0 0, mkEffect 0 [] []).
(** openat(-100, "/proc/sys/kernel/overflowuid", 0x88000) = 3 *)
Definition parent_trace_c14 : SyscallInput * SyscallEffect :=
  (proc_open_in AT_FDCWD s_overflowuid 0x88000,
   with_copyins [(8192, 29%nat)] (mkEffect 3 [] [])).
(** brk(NULL) = 0x51000 *)
Definition parent_trace_c15 : SyscallInput * SyscallEffect :=
  (parent_trace_call 214 0 0 0 0 0 0, mkEffect 0x51000 [] []).
(** brk(0x53000) = 0x53000; the two new pages are zero-filled. *)
Definition parent_trace_c16 : SyscallInput * SyscallEffect :=
  (parent_trace_call 214 0x53000 0 0 0 0 0,
   mkEffect 0x53000 [] [(0x51000, 8192)]).
(** mmap(0x51000, 4096, PROT_NONE, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS,
    -1, 0) = 0x51000; the page becomes inaccessible. *)
Definition parent_trace_c17 : SyscallInput * SyscallEffect :=
  (parent_trace_call 222 0x51000 4096 0 0x32 parent_trace_minus1 0,
   mkEffectU 0x51000 [] [] [(0x51000, 4096)] [] []).
(** mmap(NULL, 16384, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS,
    -1, 0) = 0x7fff9428a000; the mapping is zero-filled. *)
Definition parent_trace_c18 : SyscallInput * SyscallEffect :=
  (parent_trace_call 222 0 16384 3 0x22 parent_trace_minus1 0,
   mkEffect 0x7fff9428a000 [] [(0x7fff9428a000, 16384)]).
(** read(3, buf, 4079) = 6, storing "65534\n" *)
Definition parent_trace_c19 : SyscallInput * SyscallEffect :=
  (sysctl_read_in 3 4079, mkEffect 6 [(0x10000, [54; 53; 53; 51; 52; 10])] []).
(** read(3, buf, 4073) = 0 *)
Definition parent_trace_c20 : SyscallInput * SyscallEffect :=
  (sysctl_read_in 3 4073, mkEffect 0 [] []).
(** close(3) = 0 *)
Definition parent_trace_c21 : SyscallInput * SyscallEffect :=
  (parent_trace_call 57 3 0 0 0 0 0, mkEffect 0 [] []).
(** openat(-100, "/proc/sys/kernel/overflowgid", 0x88000) = 3 *)
Definition parent_trace_c22 : SyscallInput * SyscallEffect :=
  (proc_open_in AT_FDCWD s_overflowgid 0x88000,
   with_copyins [(8192, 29%nat)] (mkEffect 3 [] [])).
(** read(3, buf, 4079) = 6, storing "65534\n" *)
Definition parent_trace_c23 : SyscallInput * SyscallEffect :=
  (sysctl_read_in 3 4079, mkEffect 6 [(0x10000, [54; 53; 53; 51; 52; 10])] []).
(** read(3, buf, 4073) = 0 *)
Definition parent_trace_c24 : SyscallInput * SyscallEffect :=
  (sysctl_read_in 3 4073, mkEffect 0 [] []).
(** close(3) = 0 *)
Definition parent_trace_c25 : SyscallInput * SyscallEffect :=
  (parent_trace_call 57 3 0 0 0 0 0, mkEffect 0 [] []).
(** munmap(0x7fff9428a000, 16384) = 0; the range becomes inaccessible. *)
Definition parent_trace_c26 : SyscallInput * SyscallEffect :=
  (parent_trace_call 215 0x7fff9428a000 16384 0 0 0 0,
   mkEffectU 0 [] [] [(0x7fff9428a000, 16384)] [] []).
(** ioctl(1, TIOCGWINSZ, 0x7ffffe5dcc70) = -ENOTTY *)
Definition parent_trace_c27 : SyscallInput * SyscallEffect :=
  (parent_trace_call 29 1 0x5413 0x7ffffe5dcc70 0 0 0,
   mkEffect (errno_ret ENOTTY) [] []).
(** mmap(NULL, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS,
    -1, 0) = 0x7fff9428d000; the page is zero-filled. *)
Definition parent_trace_c28 : SyscallInput * SyscallEffect :=
  (parent_trace_call 222 0 4096 3 0x22 parent_trace_minus1 0,
   mkEffect 0x7fff9428d000 [] [(0x7fff9428d000, 4096)]).
(** getuid() = 65534 *)
Definition parent_trace_c29 : SyscallInput * SyscallEffect :=
  (parent_trace_call 174 0 0 0 0 0 0, mkEffect 65534 [] []).
(** openat(-100, "/proc", O_RDONLY|O_LARGEFILE|O_PATH) = 3 *)
Definition parent_trace_c30 : SyscallInput * SyscallEffect :=
  (proc_open_in AT_FDCWD s_proc 0x208000,
   with_copyins [(8192, 6%nat)] (mkEffect 3 [] [])).
(** eventfd2(0, EFD_CLOEXEC|EFD_NONBLOCK) = 4 *)
Definition parent_trace_c31 : SyscallInput * SyscallEffect :=
  (parent_trace_call 19 0 0x80800 0 0 0 0, mkEffect 4 [] []).
(** rt_sigprocmask(SIG_BLOCK, [SIGCHLD], NULL, 8) = 0; the call reads the
    eight-byte set. *)
Definition parent_trace_c32 : SyscallInput * SyscallEffect :=
  (mkInput 135 [0; 0x3000; 0; 8; 0; 0] parent_trace_sigchld_set (fun _ => None),
   with_copyins [(0x3000, 8%nat)] (mkEffect 0 [] [])).
(** wait4(-1, 0x7ffffe5ddeb0, WNOHANG, NULL) = -ECHILD *)
Definition parent_trace_c33 : SyscallInput * SyscallEffect :=
  (parent_trace_call 260 parent_trace_minus1 0x7ffffe5ddeb0 1 0 0 0,
   mkEffect (errno_ret ECHILD) [] []).
(** eventfd2(0, EFD_CLOEXEC) = 5 *)
Definition parent_trace_c34 : SyscallInput * SyscallEffect :=
  (parent_trace_call 19 0 0x80000 0 0 0 0, mkEffect 5 [] []).
(** clone(CLONE_NEWNS|CLONE_NEWUTS|CLONE_NEWIPC|CLONE_NEWUSER|CLONE_NEWPID
    |CLONE_NEWNET|SIGCHLD, NULL) = 320 *)
Definition parent_trace_c35 : SyscallInput * SyscallEffect :=
  (parent_trace_call 220 bwrap_clone_flags 0 0 0 0 0, mkEffect 320 [] []).

Definition parent_trace_calls : list (SyscallInput * SyscallEffect) :=
  [ parent_trace_c01; parent_trace_c02; parent_trace_c03; parent_trace_c04;
    parent_trace_c05; parent_trace_c06; parent_trace_c07; parent_trace_c08;
    parent_trace_c09; parent_trace_c10; parent_trace_c11; parent_trace_c12;
    parent_trace_c13; parent_trace_c14; parent_trace_c15; parent_trace_c16;
    parent_trace_c17; parent_trace_c18; parent_trace_c19; parent_trace_c20;
    parent_trace_c21; parent_trace_c22; parent_trace_c23; parent_trace_c24;
    parent_trace_c25; parent_trace_c26; parent_trace_c27; parent_trace_c28;
    parent_trace_c29; parent_trace_c30; parent_trace_c31; parent_trace_c32;
    parent_trace_c33; parent_trace_c34; parent_trace_c35 ].

Example parent_trace_has_35_calls : length parent_trace_calls = 35%nat.
Proof. reflexivity. Qed.

(* =========================================================================
   The states: each is the checker's successor of the one before
   ========================================================================= *)

Definition parent_trace_s01 : Model := parent_trace_next parent_trace_c01 parent_trace_s00.
Definition parent_trace_s02 : Model := parent_trace_next parent_trace_c02 parent_trace_s01.
Definition parent_trace_s03 : Model := parent_trace_next parent_trace_c03 parent_trace_s02.
Definition parent_trace_s04 : Model := parent_trace_next parent_trace_c04 parent_trace_s03.
Definition parent_trace_s05 : Model := parent_trace_next parent_trace_c05 parent_trace_s04.
Definition parent_trace_s06 : Model := parent_trace_next parent_trace_c06 parent_trace_s05.
Definition parent_trace_s07 : Model := parent_trace_next parent_trace_c07 parent_trace_s06.
Definition parent_trace_s08 : Model := parent_trace_next parent_trace_c08 parent_trace_s07.
Definition parent_trace_s09 : Model := parent_trace_next parent_trace_c09 parent_trace_s08.
Definition parent_trace_s10 : Model := parent_trace_next parent_trace_c10 parent_trace_s09.
Definition parent_trace_s11 : Model := parent_trace_next parent_trace_c11 parent_trace_s10.
Definition parent_trace_s12 : Model := parent_trace_next parent_trace_c12 parent_trace_s11.
Definition parent_trace_s13 : Model := parent_trace_next parent_trace_c13 parent_trace_s12.
Definition parent_trace_s14 : Model := parent_trace_next parent_trace_c14 parent_trace_s13.
Definition parent_trace_s15 : Model := parent_trace_next parent_trace_c15 parent_trace_s14.
Definition parent_trace_s16 : Model := parent_trace_next parent_trace_c16 parent_trace_s15.
Definition parent_trace_s17 : Model := parent_trace_next parent_trace_c17 parent_trace_s16.
Definition parent_trace_s18 : Model := parent_trace_next parent_trace_c18 parent_trace_s17.
Definition parent_trace_s19 : Model := parent_trace_next parent_trace_c19 parent_trace_s18.
Definition parent_trace_s20 : Model := parent_trace_next parent_trace_c20 parent_trace_s19.
Definition parent_trace_s21 : Model := parent_trace_next parent_trace_c21 parent_trace_s20.
Definition parent_trace_s22 : Model := parent_trace_next parent_trace_c22 parent_trace_s21.
Definition parent_trace_s23 : Model := parent_trace_next parent_trace_c23 parent_trace_s22.
Definition parent_trace_s24 : Model := parent_trace_next parent_trace_c24 parent_trace_s23.
Definition parent_trace_s25 : Model := parent_trace_next parent_trace_c25 parent_trace_s24.
Definition parent_trace_s26 : Model := parent_trace_next parent_trace_c26 parent_trace_s25.
Definition parent_trace_s27 : Model := parent_trace_next parent_trace_c27 parent_trace_s26.
Definition parent_trace_s28 : Model := parent_trace_next parent_trace_c28 parent_trace_s27.
Definition parent_trace_s29 : Model := parent_trace_next parent_trace_c29 parent_trace_s28.
Definition parent_trace_s30 : Model := parent_trace_next parent_trace_c30 parent_trace_s29.
Definition parent_trace_s31 : Model := parent_trace_next parent_trace_c31 parent_trace_s30.
Definition parent_trace_s32 : Model := parent_trace_next parent_trace_c32 parent_trace_s31.
Definition parent_trace_s33 : Model := parent_trace_next parent_trace_c33 parent_trace_s32.
Definition parent_trace_s34 : Model := parent_trace_next parent_trace_c34 parent_trace_s33.
Definition parent_trace_s35 : Model := parent_trace_next parent_trace_c35 parent_trace_s34.


(* =========================================================================
   One Example per traced call: answered, with the next state
   ========================================================================= *)

Example parent_trace_set_tid_address :
  parent_trace_check parent_trace_c01 parent_trace_s00 = CheckOk parent_trace_s01 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_20 :
  parent_trace_check parent_trace_c02 parent_trace_s01 = CheckOk parent_trace_s02 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_30 :
  parent_trace_check parent_trace_c03 parent_trace_s02 = CheckOk parent_trace_s03 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_28 :
  parent_trace_check parent_trace_c04 parent_trace_s03 = CheckOk parent_trace_s04 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_2c :
  parent_trace_check parent_trace_c05 parent_trace_s04 = CheckOk parent_trace_s05 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_2a :
  parent_trace_check parent_trace_c06 parent_trace_s05 = CheckOk parent_trace_s06 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capbset_read_29 :
  parent_trace_check parent_trace_c07 parent_trace_s06 = CheckOk parent_trace_s07 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_sigaction_sigchld :
  parent_trace_check parent_trace_c08 parent_trace_s07 = CheckOk parent_trace_s08 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_getuid :
  parent_trace_check parent_trace_c09 parent_trace_s08 = CheckOk parent_trace_s09 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_getgid :
  parent_trace_check parent_trace_c10 parent_trace_s09 = CheckOk parent_trace_s10 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_geteuid :
  parent_trace_check parent_trace_c11 parent_trace_s10 = CheckOk parent_trace_s11 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_capget :
  parent_trace_check parent_trace_c12 parent_trace_s11 = CheckOk parent_trace_s12 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_no_new_privs :
  parent_trace_check parent_trace_c13 parent_trace_s12 = CheckOk parent_trace_s13 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_open_overflowuid :
  parent_trace_check parent_trace_c14 parent_trace_s13 = CheckOk parent_trace_s14 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_brk_query :
  parent_trace_check parent_trace_c15 parent_trace_s14 = CheckOk parent_trace_s15 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_brk_grow :
  parent_trace_check parent_trace_c16 parent_trace_s15 = CheckOk parent_trace_s16 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_mmap_brk_guard :
  parent_trace_check parent_trace_c17 parent_trace_s16 = CheckOk parent_trace_s17 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_mmap_16384 :
  parent_trace_check parent_trace_c18 parent_trace_s17 = CheckOk parent_trace_s18 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_read_overflowuid :
  parent_trace_check parent_trace_c19 parent_trace_s18 = CheckOk parent_trace_s19 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_read_overflowuid_eof :
  parent_trace_check parent_trace_c20 parent_trace_s19 = CheckOk parent_trace_s20 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_close_overflowuid :
  parent_trace_check parent_trace_c21 parent_trace_s20 = CheckOk parent_trace_s21 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_open_overflowgid :
  parent_trace_check parent_trace_c22 parent_trace_s21 = CheckOk parent_trace_s22 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_read_overflowgid :
  parent_trace_check parent_trace_c23 parent_trace_s22 = CheckOk parent_trace_s23 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_read_overflowgid_eof :
  parent_trace_check parent_trace_c24 parent_trace_s23 = CheckOk parent_trace_s24 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_close_overflowgid :
  parent_trace_check parent_trace_c25 parent_trace_s24 = CheckOk parent_trace_s25 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_munmap_16384 :
  parent_trace_check parent_trace_c26 parent_trace_s25 = CheckOk parent_trace_s26 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_ioctl_tiocgwinsz :
  parent_trace_check parent_trace_c27 parent_trace_s26 = CheckOk parent_trace_s27 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_mmap_page :
  parent_trace_check parent_trace_c28 parent_trace_s27 = CheckOk parent_trace_s28 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_getuid_after_mmap :
  parent_trace_check parent_trace_c29 parent_trace_s28 = CheckOk parent_trace_s29 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_open_proc :
  parent_trace_check parent_trace_c30 parent_trace_s29 = CheckOk parent_trace_s30 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_eventfd_nonblock :
  parent_trace_check parent_trace_c31 parent_trace_s30 = CheckOk parent_trace_s31 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_sigprocmask_block_sigchld :
  parent_trace_check parent_trace_c32 parent_trace_s31 = CheckOk parent_trace_s32 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_wait4_no_child :
  parent_trace_check parent_trace_c33 parent_trace_s32 = CheckOk parent_trace_s33 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_eventfd_cloexec :
  parent_trace_check parent_trace_c34 parent_trace_s33 = CheckOk parent_trace_s34 [].
Proof. vm_compute. reflexivity. Qed.

Example parent_trace_namespace_clone :
  parent_trace_check parent_trace_c35 parent_trace_s34 = CheckOk parent_trace_s35 [].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   What the computed states hold
   ========================================================================= *)

(** The clone's answer is the pid with the child recorded, and nothing
    else of the model moves. *)
Example parent_trace_clone_records_the_child :
  parent_trace_s35 = with_children parent_trace_s34.
Proof. vm_compute. reflexivity. Qed.

(** The clone runs with the descriptors the trace has open then: the
    O_PATH descriptor on "/proc" at 3 and the two eventfds at 4 and 5,
    beside channels 0-2, so the namespace word passes the clone's
    descriptor gate with them. *)
Example parent_trace_clone_descriptors :
  fd_lookup (m_fds parent_trace_s34) 3 = Some (FdOpaque (OProcPath s_proc))
  /\ fd_lookup (m_fds parent_trace_s34) 4
     = Some (FdOpaque (OEventFd (Z_to_bv 64 0x80800)))
  /\ fd_lookup (m_fds parent_trace_s34) 5
     = Some (FdOpaque (OEventFd (Z_to_bv 64 0x80000)))
  /\ fd_lookup (m_fds parent_trace_s34) 6 = None.
Proof. repeat split; check_eq. Qed.

(** After the last mapping: the break is 0x53000, the brk pages and the
    final page are mapped, the 16384-byte mapping is gone, and the guard
    page is inaccessible.  SIGCHLD is blocked once rt_sigprocmask has
    run. *)
Example parent_trace_address_space_after_mmaps :
  bv_unsigned (vm_brk (m_vmmaps parent_trace_s28)) = 0x53000%Z
  /\ map_has (vm_maps (m_vmmaps parent_trace_s28)) 0x51000 8192 = true
  /\ map_has (vm_maps (m_vmmaps parent_trace_s28)) 0x7fff9428d000 4096 = true
  /\ map_has (vm_maps (m_vmmaps parent_trace_s28)) 0x7fff9428a000 16384 = false
  /\ map_contains (vm_noaccess (m_vmmaps parent_trace_s28)) 0x51000 4096 = true
  /\ bv_unsigned (m_sigmask parent_trace_s32) = 65536%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* =========================================================================
   The whole replay, composed call by call
   ========================================================================= *)

(** From the parent after start-up, the 35 traced calls run in order, each
    answered [CheckOk] with no events by its Example above, and the run
    ends in the clone's answer: the model with the child recorded. *)
Lemma parent_trace_replays_to_the_clone :
  parent_trace_run parent_trace_calls parent_trace_s00
  = Some (with_children parent_trace_s34).
Proof.
  rewrite <- parent_trace_clone_records_the_child.
  unfold parent_trace_calls.
  eapply parent_trace_run_step; [exact parent_trace_set_tid_address|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_20|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_30|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_28|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_2c|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_2a|].
  eapply parent_trace_run_step; [exact parent_trace_capbset_read_29|].
  eapply parent_trace_run_step; [exact parent_trace_sigaction_sigchld|].
  eapply parent_trace_run_step; [exact parent_trace_getuid|].
  eapply parent_trace_run_step; [exact parent_trace_getgid|].
  eapply parent_trace_run_step; [exact parent_trace_geteuid|].
  eapply parent_trace_run_step; [exact parent_trace_capget|].
  eapply parent_trace_run_step; [exact parent_trace_no_new_privs|].
  eapply parent_trace_run_step; [exact parent_trace_open_overflowuid|].
  eapply parent_trace_run_step; [exact parent_trace_brk_query|].
  eapply parent_trace_run_step; [exact parent_trace_brk_grow|].
  eapply parent_trace_run_step; [exact parent_trace_mmap_brk_guard|].
  eapply parent_trace_run_step; [exact parent_trace_mmap_16384|].
  eapply parent_trace_run_step; [exact parent_trace_read_overflowuid|].
  eapply parent_trace_run_step; [exact parent_trace_read_overflowuid_eof|].
  eapply parent_trace_run_step; [exact parent_trace_close_overflowuid|].
  eapply parent_trace_run_step; [exact parent_trace_open_overflowgid|].
  eapply parent_trace_run_step; [exact parent_trace_read_overflowgid|].
  eapply parent_trace_run_step; [exact parent_trace_read_overflowgid_eof|].
  eapply parent_trace_run_step; [exact parent_trace_close_overflowgid|].
  eapply parent_trace_run_step; [exact parent_trace_munmap_16384|].
  eapply parent_trace_run_step; [exact parent_trace_ioctl_tiocgwinsz|].
  eapply parent_trace_run_step; [exact parent_trace_mmap_page|].
  eapply parent_trace_run_step; [exact parent_trace_getuid_after_mmap|].
  eapply parent_trace_run_step; [exact parent_trace_open_proc|].
  eapply parent_trace_run_step; [exact parent_trace_eventfd_nonblock|].
  eapply parent_trace_run_step; [exact parent_trace_sigprocmask_block_sigchld|].
  eapply parent_trace_run_step; [exact parent_trace_wait4_no_child|].
  eapply parent_trace_run_step; [exact parent_trace_eventfd_cloexec|].
  eapply parent_trace_run_step; [exact parent_trace_namespace_clone|].
  reflexivity.
Qed.

(** Trace-call index, 35 calls, in order (call [cNN] runs from state
    [s(NN-1)] to [sNN]):

    01 set_tid_address: [parent_trace_set_tid_address].
    02-07 prctl(PR_CAPBSET_READ, 0x20/0x30/0x28/0x2c/0x2a/0x29):
       [parent_trace_capbset_read_20], [parent_trace_capbset_read_30],
       [parent_trace_capbset_read_28], [parent_trace_capbset_read_2c],
       [parent_trace_capbset_read_2a], [parent_trace_capbset_read_29].
    08 rt_sigaction: [parent_trace_sigaction_sigchld].
    09-11 getuid, getgid, geteuid: [parent_trace_getuid],
       [parent_trace_getgid], [parent_trace_geteuid].
    12 capget: [parent_trace_capget].
    13 prctl(PR_SET_NO_NEW_PRIVS): [parent_trace_no_new_privs].
    14 openat overflowuid: [parent_trace_open_overflowuid].
    15-16 brk(NULL), brk(0x53000): [parent_trace_brk_query],
       [parent_trace_brk_grow].
    17-18 mmap guard page, mmap 16384: [parent_trace_mmap_brk_guard],
       [parent_trace_mmap_16384].
    19-21 read, read, close: [parent_trace_read_overflowuid],
       [parent_trace_read_overflowuid_eof], [parent_trace_close_overflowuid].
    22 openat overflowgid: [parent_trace_open_overflowgid].
    23-25 read, read, close: [parent_trace_read_overflowgid],
       [parent_trace_read_overflowgid_eof], [parent_trace_close_overflowgid].
    26 munmap: [parent_trace_munmap_16384].
    27 ioctl(TIOCGWINSZ): [parent_trace_ioctl_tiocgwinsz].
    28 mmap 4096: [parent_trace_mmap_page].
    29 getuid: [parent_trace_getuid_after_mmap].
    30 openat "/proc": [parent_trace_open_proc].
    31 eventfd2(0, 0x80800): [parent_trace_eventfd_nonblock].
    32 rt_sigprocmask: [parent_trace_sigprocmask_block_sigchld].
    33 wait4: [parent_trace_wait4_no_child].
    34 eventfd2(0, 0x80000): [parent_trace_eventfd_cloexec].
    35 clone: [parent_trace_namespace_clone], with
       [parent_trace_clone_records_the_child] and
       [parent_trace_clone_descriptors].

    [parent_trace_replays_to_the_clone] composes all 35. *)
