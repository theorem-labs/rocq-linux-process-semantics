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

(** [eventfd2] reads no field of the model but the descriptor table, so
    the state here only has to exist.  Three channels and nothing else,
    as [timerfd_model] is: the lowest free descriptor is 3. *)
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

(** The model an accepted [eventfd2] leaves behind: fd 3 holds an
    eventfd made with the (32-bit) flag word [fl], and nothing else
    moved.  [Fs.EventFd.eventfd2_spec] records the word as the call
    passed it, so the stored word is part of what is pinned. *)
Definition efd_minted (fl : Z) : Model :=
  with_fds (fd_insert (m_fds eventfd_model) 3
              (FdOpaque (OEventFd (Z_to_bv 64 fl)))) eventfd_model.

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

(** THE ACCEPTED MASK MINTS A DESCRIPTOR, one bit at a time and all
    together.  Until the eventfd descriptor kind ([State.OEventFd]) the
    model declined every one of these words; it now answers the lowest
    free descriptor holding the eventfd, or an allocation errno
    ([Fs.EventFd.eventfd2_errnos]), and nothing else.

    THE SEPARATION FROM [timerfd_create] IS THE POINT OF THE FIRST PAIR.
    [EFD_FLAGS_SET] and [TFD_CREATE_FLAGS] differ in exactly one bit,
    bit 0: it is [EFD_SEMAPHORE] here and belongs to
    [timerfd_settime]'s mask there, so [eventfd2(0, 1)] hands back a
    descriptor while [timerfd_create(CLOCK_MONOTONIC, 1)] is -EINVAL
    ([Uapi.EFD_FLAGS_SET] carries the derivation).  A model that spelled
    one gate with the other's mask would answer -EINVAL here, so the
    conjunct REJECTING that -EINVAL is what makes the two masks two
    rather than one.

    The words bubblewrap 0.13.1's parent issues are among them: 0x80800
    ([EFD_CLOEXEC|EFD_NONBLOCK]) and 0x80000 ([EFD_CLOEXEC]), from its
    QEMU trace on Linux 6.18.44. *)

Example eventfd2_accepted_flag_words_mint :
  (* EFD_SEMAPHORE alone: accepted by eventfd2, refused by timerfd_create *)
  check_syscall (efd_in 0 EFD_SEMAPHORE) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_minted EFD_SEMAPHORE) []
  (* ...and the -EINVAL a timerfd-shaped mask would have produced for it
     is REJECTED *)
  /\ check_syscall (efd_in 0 EFD_SEMAPHORE)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* the empty flag word, which is what glibc's and musl's eventfd(0, 0)
     compiles to *)
  /\ check_syscall (efd_in 0 0) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted 0) []
  /\ check_syscall (efd_in 0 O_CLOEXEC) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted O_CLOEXEC) []
  /\ check_syscall (efd_in 0 O_NONBLOCK) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted O_NONBLOCK) []
  (* bubblewrap's two words *)
  /\ check_syscall (efd_in 0 0x80800) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted 0x80800) []
  /\ check_syscall (efd_in 0 0x80000) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted 0x80000) []
  (* every accepted bit at once *)
  /\ check_syscall (efd_in 0 EFD_FLAGS_SET) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted EFD_FLAGS_SET) []
  (* the allocation errnos stand, with the model untouched *)
  /\ check_syscall (efd_in 0 0x80800) (mkEffect (errno_ret ENOMEM) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 0x80800) (mkEffect (errno_ret EMFILE) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  /\ check_syscall (efd_in 0 0x80800) (mkEffect (errno_ret ENFILE) [] [])
       eventfd_model
     = CheckOk eventfd_model []
  (* NOT ANY descriptor: the lowest free one, which is 3 *)
  /\ check_syscall (efd_in 0 0x80800) (mkEffect 4 [] []) eventfd_model
     = CheckReject
  (* AND ONE BIT OUTSIDE IT, STILL -EINVAL.  The bit above the mask's
     top bit is the sharpest witness that the mask is still a mask. *)
  /\ check_syscall (efd_in 0 (2 * O_CLOEXEC))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** THE COUNTER IS NOT JUDGED, AND THE FLAG WORD IS ARGUMENT 1.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which argument the model read to
    produce it.

    Two mistakes are ruled out here, and neither is visible from the
    accepted-mask cases above, where the counter is 0 throughout.

    FIRST, that the counter is judged at all.  [count] is stored by
    [ctx->count = count] BELOW the gate, so no value of it can be
    refused: the first two pairs offer a wild counter with an accepted
    flag word and require the descriptor, and reject the -EINVAL a spec
    that masked the counter would produce.

    SECOND, that the two arguments are read in the wrong ORDER.  An arm
    reading [in_arg i 0] as the flag word would judge the COUNTER
    against [EFD_FLAGS_SET].  The first pair is what catches it:
    [eventfd2(2^20, 0)] is a legal call Linux answers with a descriptor,
    and a swapped arm would answer -EINVAL for it. *)

Example eventfd2_counter_is_not_judged :
  (* a counter with bits far outside any flag mask, flags accepted *)
  check_syscall (efd_in (2 ^ 20) 0) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_minted 0) []
  /\ check_syscall (efd_in (2 ^ 20) 0) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = CheckReject
  (* the largest counter an unsigned int can carry *)
  /\ check_syscall (efd_in (2 ^ 32 - 1) 0) (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted 0) []
  /\ check_syscall (efd_in (2 ^ 32 - 1) 0)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* a wild counter does not rescue a BAD flag word either *)
  /\ check_syscall (efd_in (2 ^ 32 - 1) (2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** THE FLAG WORD NARROWS TO 32 BITS, and the two halves are pinned
    together because only their conjunction says what narrowing means.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which comparison the model made.

    A high half on the flag word aliases onto a clean flag word and
    mints a descriptor, which records the NARROWED word.  A spec
    comparing the whole 64-bit register would have answered -EINVAL, so
    the second conjunct — that the -EINVAL is REJECTED — is the half that
    discriminates.

    No real run can show the rejection of the -EINVAL, because a kernel
    that returned one for this word does not exist. *)

Example eventfd2_narrows_the_flag_word :
  check_syscall (efd_in 0 (2 ^ 32)) (mkEffect 3 [] []) eventfd_model
  = CheckOk (efd_minted 0) []
  /\ check_syscall (efd_in 0 (2 ^ 32))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckReject
  (* an accepted low half with a high half set is still accepted, and
     the descriptor carries the low half alone *)
  /\ check_syscall (efd_in 0 (2 ^ 32 + EFD_SEMAPHORE))
       (mkEffect 3 [] []) eventfd_model
     = CheckOk (efd_minted EFD_SEMAPHORE) []
  (* and the high half does not rescue a BAD low half: aliasing is not a
     second chance *)
  /\ check_syscall (efd_in 0 (2 ^ 32 + 2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = CheckOk eventfd_model [].
Proof. repeat split; check_eq. Qed.

(** BUBBLEWRAP'S SEQUENCE, PAIRED.  bubblewrap 0.13.1's parent holds
    "/proc" as an O_PATH descriptor at fd 3 when it makes its two
    eventfds, and its QEMU trace on Linux 6.18.44 reads
    [eventfd2(0, 0x80800) = 4] then [eventfd2(0, 0x80000) = 5].  Before
    [State.OEventFd] the model declined both (the old
    [eventfd2_accepted_flag_words_decline] pinned that); now each lands
    at the lowest free descriptor past the O_PATH one, and the clone
    gate ([Kernel.Fork.clone_no_shared_file_b]) passes all three.

    THE CONTROL is the refused word, answered alike by the old text and
    the new: -EINVAL with the table untouched. *)
Definition efd_bwrap_model : Model :=
  with_fds (fd_insert (m_fds eventfd_model) 3
              (FdOpaque (OProcPath proc_root_path))) eventfd_model.

Example eventfd2_bwrap_parent_words :
  let after4 := with_fds (fd_insert (m_fds efd_bwrap_model) 4
                  (FdOpaque (OEventFd (Z_to_bv 64 0x80800)))) efd_bwrap_model in
  let after5 := with_fds (fd_insert (m_fds after4) 5
                  (FdOpaque (OEventFd (Z_to_bv 64 0x80000)))) after4 in
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
