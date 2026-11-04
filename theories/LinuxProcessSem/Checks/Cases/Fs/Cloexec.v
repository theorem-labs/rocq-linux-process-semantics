(** * LinuxProcessSem.Checks.Cases.Fs.Cloexec — worked examples over the recorded close-on-exec bit

    Mirrors the close-on-exec parts of [Sys/Fs/Fcntl.v], [Sys/Fs/Open.v]
    and [Sys/Fs/File.v], which answer to Linux [fs/fcntl.c], [fs/open.c]
    and [fs/file.c]: [State.m_cloexec], the bits the model KNOWS, and
    what [fcntl]'s [F_GETFD] and [F_SETFD], [openat], [dup3],
    [close_range], [close] and the descriptor creators do with it.

    [Checks/Examples.v] keeps what is not per-syscall and re-exports this
    module.  These cases pin model-internal state (which bit is known)
    and name rejected answers, which no run can show.

    Each example pairs the recorded bit's answer with a CONTROL that the
    text before the bit was recorded answers the same way: there no arm
    recorded a bit, and [F_GETFD] admitted both 0 and FD_CLOEXEC on every
    open descriptor.  Together they are a launcher's key setup read back:
    open a file with O_CLOEXEC, clear the bit with [F_SETFD(fd, 0)] or
    [dup3(fd, k, 0)], and see [F_GETFD] answer 0 alone.  The invariant
    that keeps an unknown bit sound, every key an open descriptor, is
    [Checks.CloexecKeys.cloexec_keys_open]. *)

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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import
  Fs.ReadWrite Fs.Pipe.

Definition getfd_in (fd : word) : SyscallInput :=
  mkInput 25 [fd; F_GETFD; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Definition setfd_in (fd arg : word) : SyscallInput :=
  mkInput 25 [fd; F_SETFD; arg; 0; 0; 0] (fun _ => None) (fun _ => None).

Definition dup3_in (oldfd newfd flags : word) : SyscallInput :=
  mkInput 24 [oldfd; newfd; flags; 0; 0; 0] (fun _ => None) (fun _ => None).

Definition close_range_call (lo hi : word) : SyscallInput :=
  mkInput 436 [lo; hi; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** The second call of a two-call run: [i] answering [eff] on the model
    the first answer [r] left, or [r] itself where the first call did not
    answer. *)
Definition then_call (r : check_result) (i : SyscallInput) (eff : SyscallEffect)
    : check_result :=
  match r with
  | CheckOk m _ => check_syscall i eff m
  | other => other
  end.

Definition answered (r : check_result) : bool :=
  match r with CheckOk _ _ => true | _ => false end.

(** The descriptor table an answer leaves, for the controls that compare
    two answers' tables. *)
Definition table_of (r : check_result) : list (word * FdEntry) :=
  match r with CheckOk m _ => m_fds m | _ => [] end.

(** Three channels, "f" = "hi" read-only at 3, a directory at 4 and a
    socket at 6; the lowest free descriptor is 5.  A [State.mkModel]
    fixture knows no bit; [cl_known] knows 3's as SET and 4's as CLEAR,
    and nothing of 6's or of the channels'. *)
Definition cl_base : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdFile [102] 0); (4, FdDir); (6, FdSocket SkFresh)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None
    None.

Definition cl_known : Model := with_cloexec [(3, true); (4, false)] cl_base.

(** A launch whose file system holds "f" = "hi": descriptors 0 to 2 are
    the channels, known clear ([State.launch_cloexec]). *)
Definition cl_launch : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [([102], [104; 105])] IEof).

(** F_GETFD ANSWERS ONLY THE STORED BIT: FD_CLOEXEC on 3, 0 on 4, and
    the other answer is rejected on each ([Fcntl.fcntl_spec]'s known arm;
    fs/fcntl.c [do_fcntl] answers [get_close_on_exec(fd) ? FD_CLOEXEC :
    0], read at v6.18.44, identical at v6.18.46).

    THE CONTROLS, answered alike before the bit was recorded: on 6, whose
    bit is unknown, both 0 and FD_CLOEXEC and nothing else; on 5, which is
    not open, -EBADF. *)
Example getfd_answers_only_the_stored_bit :
  check_syscall (getfd_in 3) (mkEffect FD_CLOEXEC [] []) cl_known = CheckOk cl_known []
  /\ check_syscall (getfd_in 3) (mkEffect 0 [] []) cl_known = CheckReject
  /\ check_syscall (getfd_in 4) (mkEffect 0 [] []) cl_known = CheckOk cl_known []
  /\ check_syscall (getfd_in 4) (mkEffect FD_CLOEXEC [] []) cl_known = CheckReject
  (* the controls *)
  /\ check_syscall (getfd_in 6) (mkEffect 0 [] []) cl_known = CheckOk cl_known []
  /\ check_syscall (getfd_in 6) (mkEffect FD_CLOEXEC [] []) cl_known
     = CheckOk cl_known []
  /\ check_syscall (getfd_in 6) (mkEffect 2 [] []) cl_known = CheckReject
  /\ check_syscall (getfd_in 5) (mkEffect (errno_ret EBADF) [] []) cl_known
     = CheckOk cl_known [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** F_GETFD ON AN UNKNOWN BIT STILL ADMITS BOTH ANSWERS, which is the
    control here: [cl_base] knows no bit, and descriptor 3 answers 0 or
    FD_CLOEXEC, and not 2, as it always did.  The pair is the same
    descriptor once its bit is known: [cl_known]'s 3 refuses the 0. *)
Example getfd_unknown_bit_admits_both :
  check_syscall (getfd_in 3) (mkEffect 0 [] []) cl_base = CheckOk cl_base []
  /\ check_syscall (getfd_in 3) (mkEffect FD_CLOEXEC [] []) cl_base = CheckOk cl_base []
  /\ check_syscall (getfd_in 3) (mkEffect 2 [] []) cl_base = CheckReject
  (* the pair *)
  /\ check_syscall (getfd_in 3) (mkEffect 0 [] []) cl_known = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** F_SETFD SETS OR CLEARS THE BIT, from bit 0 of [arg] alone
    ([Fcntl.setfd_cloexec_b]; fs/fcntl.c [do_fcntl], [set_close_on_exec],
    read at v6.18.44, identical at v6.18.46): arg 1 sets it on 6, whose
    bit was unknown; arg 0 clears it on 3, where it was set; and arg 2
    clears it too, bit 1 being no flag.  [F_GETFD] then reads back
    exactly what was written.

    THE CONTROLS, answered alike before: F_SETFD's return is 0 and
    nothing else on an open descriptor, and -EBADF on a closed one. *)
Example setfd_sets_or_clears_the_bit :
  check_syscall (setfd_in 6 1) (mkEffect 0 [] []) cl_known
  = CheckOk (with_cloexec [(6, true); (3, true); (4, false)] cl_base) []
  /\ check_syscall (setfd_in 3 0) (mkEffect 0 [] []) cl_known
     = CheckOk (with_cloexec [(3, false); (4, false)] cl_base) []
  /\ check_syscall (setfd_in 3 2) (mkEffect 0 [] []) cl_known
     = CheckOk (with_cloexec [(3, false); (4, false)] cl_base) []
  (* read back *)
  /\ answered (then_call (check_syscall (setfd_in 6 1) (mkEffect 0 [] []) cl_known)
                 (getfd_in 6) (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (check_syscall (setfd_in 6 1) (mkEffect 0 [] []) cl_known)
       (getfd_in 6) (mkEffect 0 [] []) = CheckReject
  /\ answered (then_call (check_syscall (setfd_in 3 0) (mkEffect 0 [] []) cl_known)
                 (getfd_in 3) (mkEffect 0 [] [])) = true
  /\ then_call (check_syscall (setfd_in 3 0) (mkEffect 0 [] []) cl_known)
       (getfd_in 3) (mkEffect FD_CLOEXEC [] []) = CheckReject
  /\ then_call (check_syscall (setfd_in 3 2) (mkEffect 0 [] []) cl_known)
       (getfd_in 3) (mkEffect FD_CLOEXEC [] []) = CheckReject
  (* the controls *)
  /\ check_syscall (setfd_in 3 1) (mkEffect 1 [] []) cl_known = CheckReject
  /\ check_syscall (setfd_in 5 1) (mkEffect (errno_ret EBADF) [] []) cl_known
     = CheckOk cl_known [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** [openat(AT_FDCWD, "f", fl)] answering 3 on [cl_launch]. *)
Definition open_f (fl : Z) : check_result :=
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 0; 0; 0] mem_open_write (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] [])) cl_launch.

(** OPENAT WITH O_CLOEXEC SETS THE BIT AND WITHOUT IT CLEARS IT
    ([Open.open_cloexec_model]; [get_unused_fd_flags] hands
    [flags & O_CLOEXEC] to [__set_open_fd], fs/open.c and fs/file.c,
    read at v6.18.44, identical at v6.18.46): after the open, [F_GETFD]
    on 3 answers FD_CLOEXEC alone, or 0 alone.  The word with
    O_LARGEFILE added, as a 64-bit libc issues it, answers the same.

    THE CONTROL, answered alike before: both opens answer 3 and leave the
    same descriptor table; only the bit differs. *)
Example openat_records_o_cloexec :
  answered (then_call (open_f O_CLOEXEC) (getfd_in 3) (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (open_f O_CLOEXEC) (getfd_in 3) (mkEffect 0 [] []) = CheckReject
  /\ answered (then_call (open_f (O_CLOEXEC + O_LARGEFILE)%Z) (getfd_in 3)
                 (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (open_f (O_CLOEXEC + O_LARGEFILE)%Z) (getfd_in 3) (mkEffect 0 [] [])
     = CheckReject
  /\ answered (then_call (open_f 0%Z) (getfd_in 3) (mkEffect 0 [] [])) = true
  /\ then_call (open_f 0%Z) (getfd_in 3) (mkEffect FD_CLOEXEC [] []) = CheckReject
  (* the control *)
  /\ answered (open_f O_CLOEXEC) = true
  /\ answered (open_f 0%Z) = true
  /\ table_of (open_f O_CLOEXEC) = table_of (open_f 0%Z).
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** DUP3(OLD, NEW, 0) CLEARS THE BIT ON NEW AND WITH O_CLOEXEC SETS IT
    ([File.dup3_spec]; [do_dup2] ends in [__set_open_fd(fd, fdt, flags &
    O_CLOEXEC)], fs/file.c, read at v6.18.44, identical at v6.18.46).
    The directory at 4 goes onto 3, whose bit was SET, with flags 0: 3's
    bit is now known clear.  With O_CLOEXEC onto the free 7: 7's is known
    set.  [F_GETFD] reads each back, and 4 keeps its own.

    THE CONTROL, answered alike before: the two flag words leave the same
    descriptor table and the same return. *)
Example dup3_writes_the_bit_on_newfd :
  check_syscall (dup3_in 4 3 0) (mkEffect 3 [] []) cl_known
  = CheckOk (with_cloexec [(3, false); (4, false)]
               (with_fds (fd_insert (m_fds cl_base) 3 FdDir) cl_base)) []
  /\ check_syscall (dup3_in 4 7 (Z_to_bv 64 O_CLOEXEC)) (mkEffect 7 [] []) cl_known
     = CheckOk (with_cloexec [(7, true); (3, true); (4, false)]
                  (with_fds (fd_insert (m_fds cl_base) 7 FdDir) cl_base)) []
  (* read back *)
  /\ answered (then_call (check_syscall (dup3_in 4 3 0) (mkEffect 3 [] []) cl_known)
                 (getfd_in 3) (mkEffect 0 [] [])) = true
  /\ then_call (check_syscall (dup3_in 4 3 0) (mkEffect 3 [] []) cl_known)
       (getfd_in 3) (mkEffect FD_CLOEXEC [] []) = CheckReject
  /\ answered (then_call (check_syscall (dup3_in 4 7 (Z_to_bv 64 O_CLOEXEC))
                            (mkEffect 7 [] []) cl_known)
                 (getfd_in 7) (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (check_syscall (dup3_in 4 7 (Z_to_bv 64 O_CLOEXEC)) (mkEffect 7 [] []) cl_known)
       (getfd_in 7) (mkEffect 0 [] []) = CheckReject
  /\ then_call (check_syscall (dup3_in 4 7 (Z_to_bv 64 O_CLOEXEC)) (mkEffect 7 [] []) cl_known)
       (getfd_in 4) (mkEffect FD_CLOEXEC [] []) = CheckReject
  (* the control *)
  /\ table_of (check_syscall (dup3_in 4 7 0) (mkEffect 7 [] []) cl_known)
     = table_of (check_syscall (dup3_in 4 7 (Z_to_bv 64 O_CLOEXEC)) (mkEffect 7 [] []) cl_known)
  /\ answered (check_syscall (dup3_in 4 7 0) (mkEffect 7 [] []) cl_known) = true.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** [cl_known] with 6's bit known set too. *)
Definition cl_three : Model := with_cloexec [(3, true); (4, false); (6, true)] cl_base.

(** CLOSE_RANGE KEEPS THE BIT OF EVERY DESCRIPTOR IT DOES NOT CLOSE
    ([File.close_range_cloexec] forgets exactly the keys
    [File.close_range_fds] closes; fs/file.c [__range_close], read at
    v6.18.44, identical at v6.18.46).  [close_range(4, 5, 0)] closes 4
    and keeps 3's and 6's set bits; the launcher's
    [close_range(5, ~0U, 0)] closes 6 and keeps 3's set bit and 4's clear
    one.

    THE CONTROLS, answered alike before: the closed descriptor is -EBADF
    to F_GETFD and admits no bit. *)
Example close_range_keeps_every_other_bit :
  check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three
  = CheckOk (with_cloexec [(3, true); (6, true)]
               (with_fds (fd_remove (m_fds cl_base) 4) cl_base)) []
  /\ answered (then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
                 (getfd_in 3) (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
       (getfd_in 3) (mkEffect 0 [] []) = CheckReject
  /\ answered (then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
                 (getfd_in 6) (mkEffect FD_CLOEXEC [] [])) = true
  /\ then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
       (getfd_in 6) (mkEffect 0 [] []) = CheckReject
  /\ answered (then_call
                 (check_syscall (close_range_call 5 4294967295) (mkEffect 0 [] []) cl_three)
                 (getfd_in 4) (mkEffect 0 [] [])) = true
  /\ then_call (check_syscall (close_range_call 5 4294967295) (mkEffect 0 [] []) cl_three)
       (getfd_in 4) (mkEffect FD_CLOEXEC [] []) = CheckReject
  /\ then_call (check_syscall (close_range_call 5 4294967295) (mkEffect 0 [] []) cl_three)
       (getfd_in 3) (mkEffect 0 [] []) = CheckReject
  (* the controls *)
  /\ answered (then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
                 (getfd_in 4) (mkEffect (errno_ret EBADF) [] [])) = true
  /\ then_call (check_syscall (close_range_call 4 5) (mkEffect 0 [] []) cl_three)
       (getfd_in 4) (mkEffect 0 [] []) = CheckReject
  /\ then_call (check_syscall (close_range_call 5 4294967295) (mkEffect 0 [] []) cl_three)
       (getfd_in 6) (mkEffect FD_CLOEXEC [] []) = CheckReject.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** DESCRIPTORS 0 TO 2 START CLEAR: [init_model] knows each one's bit as
    clear ([State.launch_cloexec]), because [execve]'s [begin_new_exec]
    calls [do_close_on_exec] (fs/exec.c, fs/file.c, read at v6.18.44,
    identical at v6.18.46), which closes every descriptor whose bit is
    set; so F_GETFD on each answers 0 alone.

    THE CONTROL, answered alike before: 3 is not open at launch and is
    -EBADF. *)
Example launch_descriptors_start_clear :
  check_syscall (getfd_in 0) (mkEffect 0 [] []) cl_launch = CheckOk cl_launch []
  /\ check_syscall (getfd_in 0) (mkEffect FD_CLOEXEC [] []) cl_launch = CheckReject
  /\ check_syscall (getfd_in 1) (mkEffect 0 [] []) cl_launch = CheckOk cl_launch []
  /\ check_syscall (getfd_in 1) (mkEffect FD_CLOEXEC [] []) cl_launch = CheckReject
  /\ check_syscall (getfd_in 2) (mkEffect 0 [] []) cl_launch = CheckOk cl_launch []
  /\ check_syscall (getfd_in 2) (mkEffect FD_CLOEXEC [] []) cl_launch = CheckReject
  (* the control *)
  /\ check_syscall (getfd_in 3) (mkEffect (errno_ret EBADF) [] []) cl_launch
     = CheckOk cl_launch [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** Inherited descriptors survived the same exec as the standard channels,
    so their close-on-exec bits are clear too.  A gap in the inherited
    list is still a closed descriptor, not an unknown bit. *)
Definition cl_inherited_launch : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (with_inherited_fds [(3, [107]); (5, [101])]
      (demo_input [] IEof)).

Example inherited_launch_descriptors_start_clear :
  check_syscall (getfd_in 3) (mkEffect 0 [] []) cl_inherited_launch
    = CheckOk cl_inherited_launch []
  /\ check_syscall (getfd_in 3) (mkEffect FD_CLOEXEC [] []) cl_inherited_launch
       = CheckReject
  /\ check_syscall (getfd_in 5) (mkEffect 0 [] []) cl_inherited_launch
       = CheckOk cl_inherited_launch []
  /\ check_syscall (getfd_in 5) (mkEffect FD_CLOEXEC [] []) cl_inherited_launch
       = CheckReject
  /\ check_syscall (getfd_in 4) (mkEffect (errno_ret EBADF) [] [])
       cl_inherited_launch = CheckOk cl_inherited_launch [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** [close(4)] on [cl_known], then [eventfd2(0, EFD_CLOEXEC)], which
    takes the lowest free descriptor: 4 again. *)
Definition closed_then_eventfd : check_result :=
  then_call
    (check_syscall (mkInput 57 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) cl_known)
    (mkInput 19 [0; Z_to_bv 64 O_CLOEXEC; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 4 [] []).

(** PIPE2 AND EVENTFD2 WITH THEIR *_CLOEXEC FLAG ARE NEVER KNOWN CLEAR.
    The creators record no bit: they install at a free number, and
    [Checks.CloexecKeys.cloexec_keys_open] says no key survives there, so
    F_GETFD admits FD_CLOEXEC.  The sharp case is a REUSED number: 4's
    bit is known CLEAR in [cl_known] (the pair: FD_CLOEXEC is refused
    there), [close(4)] forgets that key, and [eventfd2] with EFD_CLOEXEC
    at 4 then admits FD_CLOEXEC, as Linux answers.  Had the key survived,
    the model would answer 0 alone, which Linux does not.  [pipe2] with
    O_CLOEXEC declines, so it claims no bit at all.

    THE CONTROLS, answered alike before: F_GETFD admits FD_CLOEXEC on the
    eventfd and on both ends of a [pipe2] with flags 0, and [pipe2] with
    O_CLOEXEC declines. *)
Example creators_with_cloexec_are_never_known_clear :
  check_syscall (getfd_in 4) (mkEffect FD_CLOEXEC [] []) cl_known = CheckReject
  /\ answered closed_then_eventfd = true
  /\ answered (then_call closed_then_eventfd (getfd_in 4) (mkEffect FD_CLOEXEC [] [])) = true
  /\ answered (then_call closed_then_eventfd (getfd_in 4) (mkEffect 0 [] [])) = true
  (* beside a pipe's two ends, the launch's descriptor 0 is still known clear *)
  /\ check_syscall (getfd_in 0) (mkEffect FD_CLOEXEC [] []) one_pipe_model = CheckReject
  (* the controls *)
  /\ check_syscall
       (mkInput 59 [pipe2_flat_fildes; Z_to_bv 64 O_CLOEXEC; 0; 0; 0; 0]
          (fun _ => None) pipe2_flat_mem)
       (mkEffect (Z_to_bv 64 0) [(pipe2_flat_fildes, [3;0;0;0;4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ answered (check_syscall (getfd_in 3) (mkEffect FD_CLOEXEC [] []) one_pipe_model) = true
  /\ answered (check_syscall (getfd_in 4) (mkEffect FD_CLOEXEC [] []) one_pipe_model) = true.
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.
