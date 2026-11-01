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
    spec states. *)

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
