(** * LinuxProcessSem.Checks.Cases.Fs.EventFd — worked examples over eventfd2 (19)

    Mirrors [Sys/Fs/EventFd.v], which answers to Linux [fs/eventfd.c]:
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
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** Past its gate [eventfd2] reads one field of the model, the fd table,
    to find the lowest free descriptor.  Three channels and nothing else,
    as [timerfd_model] is, so that descriptor is 3. *)
Definition eventfd_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** The counter comes FIRST and the flag word second, which is the one
    thing about this call's shape a reader is likely to get backwards.
    [efd_in] is written to make that visible at every use site. *)
Definition efd_in (count flags : Z) : SyscallInput :=
  mkInput 19 [Z_to_bv 64 count; Z_to_bv 64 flags; 0; 0; 0; 0]
    (fun _ => None) (fun _ => None).

(** The model after a successful [eventfd2] on [eventfd_model]: a new
    [State.FdEventfd] at descriptor 3 holding the counter and the two
    bits, and nothing else changed.  Spelled out so that every case below
    names the counter and the bits it expects rather than "a descriptor". *)
Definition efd_after (count : Z) (sem nb : bool) : Model :=
  with_fds (fd_insert (m_fds eventfd_model) 3
              (FdEventfd (mkEventfdCtx count sem nb))) eventfd_model.

(** THE FLAG BITS, ONE AT A TIME.
    These examples walk single bits, and carry what a return value
    alone cannot show — the second conjunct below.

    Linux answers -EINVAL for ANY bit outside
    [EFD_CLOEXEC|EFD_NONBLOCK|EFD_SEMAPHORE] (fs/eventfd.c,
    [do_eventfd], v6.18.46), and the spec follows.

    The second conjunct of each pair is what stops the first being
    vacuous: a kernel handing back a DESCRIPTOR for these words is
    rejected, so this pins -EINVAL rather than merely admitting it.
    Together they also pin that the answer is inert — the returned model
    is the SAME model and the event list is empty, neither of which the
    return value reveals. *)

Example eventfd2_dropped_flag_bits_are_einval :
  (* bit 1, the bit immediately above EFD_SEMAPHORE: the likeliest
     off-by-one when a reader remembers "eventfd2 takes a low bit" *)
  check_syscall (efd_in 0 (2 ^ 1)) (mkEffect (errno_ret EINVAL) [] [])
    eventfd_model
  = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 (2 ^ 1)) (mkEffect 3 [] []) eventfd_model
     = CheckReject
  (* bit 10, just below O_NONBLOCK's bit 11 *)
  /\ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect 3 [] []) eventfd_model
     = CheckReject
  (* bit 15, O_LARGEFILE's bit, which musl ORs into every open it issues
     and which this call does NOT accept *)
  /\ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect 3 [] []) eventfd_model
     = CheckReject
  (* bit 20, just above O_CLOEXEC's bit 19 *)
  /\ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect 3 [] []) eventfd_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE ACCEPTED MASK ANSWERS WITH A DESCRIPTOR, one bit at a time and
    all together, and each bit lands in the new context.
    ADMISSION REASON: model-internal -- a run shows the descriptor
    number Linux returns, not which of the context's fields the model
    set from which bit.

    THIS IS THE PASS-AFTER HALF OF A PAIR.  The fail-before half was
    [eventfd2_accepted_flag_words_decline], the same calls judged
    [CheckUnmodeled] while the model had no descriptor kind for an
    eventfd; it is false by design now that [State.FdEventfd] exists and
    [Sys.Fs.EventFd.eventfd2_spec] answers past the gate.

    THE SEPARATION FROM [timerfd_create] IS THE POINT OF THE FIRST PAIR.
    [EFD_FLAGS_SET] and [TFD_CREATE_FLAGS] differ in exactly one bit,
    bit 0: it is [EFD_SEMAPHORE] here and belongs to
    [timerfd_settime]'s mask there, so [eventfd2(0, 1)] hands back a
    descriptor while [timerfd_create(CLOCK_MONOTONIC, 1)] is -EINVAL
    ([Uapi.EFD_FLAGS_SET] carries the derivation).  A model that spelled
    one gate with the other's mask would answer -EINVAL here, so the
    conjunct refusing that -EINVAL is what makes the two masks two
    rather than one.  EFD_CLOEXEC is accepted and stored nowhere, as the
    spec states.

    The words bubblewrap 0.13.1's parent issues are among them: 0x80800
    ([EFD_CLOEXEC|EFD_NONBLOCK]) and 0x80000 ([EFD_CLOEXEC]), from its
    QEMU trace on Linux 6.18.44. *)

Example eventfd2_accepted_flag_words_answer :
  (* EFD_SEMAPHORE alone: accepted by eventfd2, refused by timerfd_create *)
  check_syscall (efd_in 0 EFD_SEMAPHORE) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_after 0 true false) []
  (* ...and the -EINVAL a timerfd-shaped mask would have produced for it
     is NOT accepted *)
  /\ check_syscall (efd_in 0 EFD_SEMAPHORE)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* the empty flag word, which is what glibc's and musl's eventfd(0, 0)
     compiles to *)
  /\ check_syscall (efd_in 0 0) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 false false) []
  /\ check_syscall (efd_in 0 O_CLOEXEC) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 false false) []
  /\ check_syscall (efd_in 0 O_NONBLOCK) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 false true) []
  (* every accepted bit at once *)
  /\ check_syscall (efd_in 0 EFD_FLAGS_SET) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 true true) []
  (* bubblewrap's two words *)
  /\ check_syscall (efd_in 0 0x80800) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 false true) []
  /\ check_syscall (efd_in 0 0x80000) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 false false) []
  (* the lowest free descriptor and no other: 4 is refused *)
  /\ check_syscall (efd_in 0 0) (mkEffect 4 [] []) eventfd_model
     = CheckReject
  (* AND ONE BIT OUTSIDE IT, STILL -EINVAL.  The bit above the mask's top
     bit is the sharpest witness that the mask is still a mask. *)
  /\ check_syscall (efd_in 0 (2 * O_CLOEXEC))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** THE ERRNOS PAST THE GATE ARE EXACTLY [eventfd2_errnos]: the
    [kmalloc]'s -ENOMEM, [get_unused_fd_flags]' -EMFILE and
    [alloc_file_pseudo]'s -ENFILE are admitted with the model unchanged,
    and an errno outside the set -- -EAGAIN here -- is refused.  The
    failures have to stay live, or a target could delete the source's
    error handling and remain equivalent. *)

Example eventfd2_injected_errnos :
  check_syscall (efd_in 0 0) (mkEffect (errno_ret ENOMEM) [] []) eventfd_model
  = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 0) (mkEffect (errno_ret EMFILE) [] []) eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 0) (mkEffect (errno_ret ENFILE) [] []) eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 0) (mkEffect (errno_ret EAGAIN) [] []) eventfd_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE COUNTER IS NOT JUDGED, IT IS STORED, AND THE FLAG WORD IS
    ARGUMENT 1.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which argument the model read to
    produce it.

    Three mistakes are ruled out here, and none is visible from the
    accepted-mask cases above, where the counter is 0 throughout.

    FIRST, that the counter is judged at all.  [count] is stored by
    [ctx->count = count] BELOW the gate, so no value of it can be
    refused: the first pairs offer a wild counter with an accepted flag
    word and require the descriptor, and refuse the -EINVAL a spec that
    masked the counter would produce.

    SECOND, that the counter is stored wrong.  It is an [unsigned int],
    so the low 32 bits of the register are what lands in the context: a
    register of 2^32 + 5 stores 5.

    THIRD, that the two arguments are read in the wrong ORDER.  An arm
    reading [in_arg i 0] as the flag word would judge the COUNTER
    against [EFD_FLAGS_SET].  [eventfd2(2^20, 0)] is a legal call Linux
    answers with a descriptor, and a swapped arm would answer -EINVAL
    for it. *)

Example eventfd2_counter_is_not_judged :
  (* a counter with bits far outside any flag mask, flags accepted *)
  check_syscall (efd_in (2 ^ 20) 0) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_after (2 ^ 20) false false) []
  /\ check_syscall (efd_in (2 ^ 20) 0) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = CheckReject
  (* the largest counter an unsigned int can carry *)
  /\ check_syscall (efd_in (2 ^ 32 - 1) 0) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after (2 ^ 32 - 1) false false) []
  /\ check_syscall (efd_in (2 ^ 32 - 1) 0)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* a register above 32 bits stores its low half *)
  /\ check_syscall (efd_in (2 ^ 32 + 5) 0) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 5 false false) []
  (* a wild counter does not rescue a BAD flag word either *)
  /\ check_syscall (efd_in (2 ^ 32 - 1) (2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** THE FLAG WORD NARROWS TO 32 BITS, and the two halves are pinned
    together because only their conjunction says what narrowing means.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which comparison the model made.

    A high half on the flag word aliases onto a clean flag word and is
    answered with a descriptor.  A spec comparing the whole 64-bit
    register would have answered -EINVAL, so the second conjunct — that
    the -EINVAL is REFUSED — is the half that discriminates.

    No real run can show the refusal of the -EINVAL, because a kernel
    that returned one for this word does not exist. *)

Example eventfd2_narrows_the_flag_word :
  check_syscall (efd_in 0 (2 ^ 32)) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_after 0 false false) []
  /\ check_syscall (efd_in 0 (2 ^ 32))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* an accepted low half with a high half set is still accepted, and
     its bit is still stored *)
  /\ check_syscall (efd_in 0 (2 ^ 32 + EFD_SEMAPHORE))
       (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_after 0 true false) []
  (* and the high half does not rescue a BAD low half: aliasing is not a
     second chance *)
  /\ check_syscall (efd_in 0 (2 ^ 32 + 2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** BUBBLEWRAP'S SEQUENCE, PAIRED.  bubblewrap 0.13.1's parent holds
    "/proc" as an O_PATH descriptor at fd 3 when it makes its two
    eventfds, and its QEMU trace on Linux 6.18.44 reads
    [eventfd2(0, 0x80800) = 4] then [eventfd2(0, 0x80000) = 5].  Each
    lands at the lowest free descriptor past the O_PATH one, and the
    clone gate ([Kernel.Fork.clone_no_shared_file_b]) passes all three:
    the clone itself turns the two eventfds into the shared kind (the
    examples below).

    THE CONTROL is the refused word: -EINVAL with the table untouched. *)
Definition efd_bwrap_model : Model :=
  with_fds (fd_insert (m_fds eventfd_model) 3
              (FdOpaque (OProcPath proc_root_path))) eventfd_model.

Example eventfd2_bwrap_parent_words :
  let after4 := with_fds (fd_insert (m_fds efd_bwrap_model) 4
                  (FdEventfd (mkEventfdCtx 0 false true))) efd_bwrap_model in
  let after5 := with_fds (fd_insert (m_fds after4) 5
                  (FdEventfd (mkEventfdCtx 0 false false))) after4 in
  check_syscall (efd_in 0 0x80800) (mkEffect 4 [] []) efd_bwrap_model
  = CheckOk after4 []
  /\ check_syscall (efd_in 0 0x80000) (mkEffect 5 [] []) after4
     = CheckOk after5 []
  /\ clone_no_shared_file_b (m_fds after5) = true
  (* the control: a refused bit is -EINVAL, and mints nothing *)
  /\ check_syscall (efd_in 0 (2 ^ 1)) (mkEffect (errno_ret EINVAL) [] [])
       efd_bwrap_model
     = CheckOk efd_bwrap_model []
  /\ check_syscall (efd_in 0 (2 ^ 1)) (mkEffect 4 [] []) efd_bwrap_model
     = CheckReject.
Proof. cbv zeta. repeat split; check_eq. Qed.

(** A CLONE SHARES THE COUNTER, SO THE COUNTER CALLS DECLINE AFTER IT.
    ADMISSION REASON: model-internal -- a run shows the answers, not which
    descriptor kind the model holds.

    [efd_live_model] holds a non-blocking eventfd at fd 3 whose counter is
    5.  Before a clone, read(3, buf, 8) is answered from the counter: 8,
    and the value 5 stored at [buf].  A successful clone
    ([Kernel.Fork.clone_child_made]) turns the entry into
    [State.FdOpaque (State.OEventFd w)], with w the O_NONBLOCK bit
    ([Kernel.Fork.share_eventfds]): after the clone the description is
    shared by two tasks, so the same read declines; a decline is never a
    wrong answer.  F_GETFL still answers exactly from w (O_RDWR |
    O_NONBLOCK, 2050), F_SETFL records a change of O_NONBLOCK in w, and
    close answers. *)
(** Eight writable bytes at 0x9000, the read's destination. *)
Definition efd_wmem : word -> option byte :=
  fun a => if bv_leu 0x9000 a && bv_ltu a 0x9008 then Some 0 else None.

Definition efd_read_in : SyscallInput :=
  mkInput 63 [3; 0x9000; 8; 0; 0; 0] (fun _ => None) efd_wmem.

(** The answer: 8, and the counter's value 5 as eight little-endian
    bytes ([ReadWrite.eventfd_read]). *)
Definition efd_read_5 : SyscallEffect :=
  mkEffect 8 [(0x9000, word_le8 (Z_to_bv 64 5))] [].

Definition efd_live_model : Model :=
  with_fds (fd_insert (m_fds eventfd_model) 3
              (FdEventfd (mkEventfdCtx 5 false true))) eventfd_model.

Definition efd_clone_in : SyscallInput :=
  mkInput 220 [Z_to_bv 64 SIGCHLD; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Definition efd_fcntl_in (cmd arg : word) : SyscallInput :=
  mkInput 25 [3; cmd; arg; 0; 0; 0] (fun _ => None) (fun _ => None).

Example eventfd_read_answers_before_a_clone_and_declines_after :
  let shared := clone_child_made (Z_to_bv 64 4242) efd_live_model in
  (* before the clone: the counter's value, 5 *)
  match check_syscall efd_read_in efd_read_5 efd_live_model with
  | CheckOk _ [] => true
  | _ => false
  end = true
  (* the clone is answered, and the entry is the shared kind *)
  /\ check_syscall efd_clone_in (mkEffect 4242 [] []) efd_live_model
     = CheckOk shared []
  /\ fd_lookup (m_fds shared) 3 = Some (FdOpaque (OEventFd (Z_to_bv 64 O_NONBLOCK)))
  (* after the clone: the same read declines *)
  /\ check_syscall efd_read_in efd_read_5 shared = CheckUnmodeled
  (* F_GETFL answers from w: O_RDWR | O_NONBLOCK *)
  /\ check_syscall (efd_fcntl_in F_GETFL 0) (mkEffect 2050 [] []) shared
     = CheckOk shared []
  (* F_SETFL clears O_NONBLOCK in w *)
  /\ check_syscall (efd_fcntl_in F_SETFL 0) (mkEffect 0 [] []) shared
     = CheckOk (with_fds (fd_insert (m_fds shared) 3
                            (FdOpaque (OEventFd (Z_to_bv 64 0)))) shared) []
  (* close answers *)
  /\ check_syscall (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) shared
     = CheckOk (with_fds (fd_remove (m_fds shared) 3) shared) [].
Proof. cbv zeta. repeat split; check_eq. Qed.

(** F_GETFD ON A SHARED EVENTFD DECLINES.  ADMISSION REASON:
    model-internal -- the decline is the model's; Linux answers one of
    the two values.

    The descriptor's close-on-exec bit came from the EFD_CLOEXEC bit of
    the [eventfd2] word ([do_eventfd], fs/eventfd.c), and a clone keeps
    the table's bit as it was ([dup_fd], fs/file.c), but the word the
    shared kind keeps does not carry it ([Fcntl.getfd_declines]).  So
    after the clone F_GETFD ([do_fcntl], fs/fcntl.c) declines, for
    either claimed answer.  THE CONTROLS: before the clone the same call
    on the same descriptor admits both answers, and after it F_SETFD
    still answers 0.  fs/eventfd.c, fs/file.c, fs/fcntl.c: read at
    v6.18.44; identical at v6.18.46. *)
Example eventfd_getfd_declines_after_a_clone :
  let shared := clone_child_made (Z_to_bv 64 4242) efd_live_model in
  check_syscall (efd_fcntl_in F_GETFD 0) (mkEffect 0 [] []) shared = CheckUnmodeled
  /\ check_syscall (efd_fcntl_in F_GETFD 0) (mkEffect FD_CLOEXEC [] []) shared
     = CheckUnmodeled
  (* the controls *)
  /\ check_syscall (efd_fcntl_in F_GETFD 0) (mkEffect 0 [] []) efd_live_model
     = CheckOk efd_live_model []
  /\ check_syscall (efd_fcntl_in F_GETFD 0) (mkEffect FD_CLOEXEC [] []) efd_live_model
     = CheckOk efd_live_model []
  /\ check_syscall (efd_fcntl_in F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) shared
     = CheckOk shared [].
Proof. cbv zeta. repeat split; check_eq. Qed.

(** BIT 31 ALONE, WHICH IS THE SIGN BIT OF THE [int] LINUX COMPARES.
    ADMISSION REASON: the REFUSAL of a descriptor for it is the
    environment-cannot-produce-it reason, since no kernel hands one out
    here.

    [flags & ~EFD_FLAGS_SET] is used directly as an [if] condition, so a
    residue of 0x80000000 is truthy exactly as 1 is.  A spec that read
    the residue as a signed [int] and asked whether it was POSITIVE would
    admit this word. *)

Example eventfd2_sign_bit_is_still_a_bad_bit :
  check_syscall (efd_in 0 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
    eventfd_model
  = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 (2 ^ 31)) (mkEffect 3 [] []) eventfd_model
     = CheckReject
  (* and beside an accepted bit, so the sign bit is not excused by
     company it keeps *)
  /\ check_syscall (efd_in 0 (2 ^ 31 + EFD_SEMAPHORE))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.
