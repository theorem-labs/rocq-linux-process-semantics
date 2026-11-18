(** * LinuxProcessSem.Checks.Cases.Fs.Timerfd — worked examples over timerfd_create (85)

    Mirrors [Sys/Fs/Timerfd.v], which answers to Linux [fs/timerfd.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

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
  Prelude.

(** [timerfd_create] reads no field of the model, so the state here only
    has to exist.  Three channels and nothing else. *)
Definition timerfd_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

Definition tfd_in (clkid flags : Z) : SyscallInput :=
  mkInput 85 [Z_to_bv 64 clkid; Z_to_bv 64 flags; 0; 0; 0; 0]
    (fun _ => None) (fun _ => None).

(** THE FLAG BITS, ONE AT A TIME.
    These examples walk single bits, and carry what a return value alone
    cannot show — the second conjunct below.

    Linux answers -EINVAL for ANY bit outside [TFD_CLOEXEC|TFD_NONBLOCK]
    (fs/timerfd.c, [SYSCALL_DEFINE2(timerfd_create)], v6.18.46), and the
    spec follows.

    The second conjunct of each pair is what stops the first being
    vacuous: a kernel handing back a DESCRIPTOR for these words is
    rejected, so this pins -EINVAL rather than merely admitting it.
    Together they also pin that the answer is inert — the returned model
    is the SAME model and the event list is empty, neither of which the
    return value reveals. *)

Example timerfd_create_dropped_flag_bits_are_einval :
  (* bit 22, an ordinary swallowed bit *)
  check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22))
    (mkEffect (errno_ret EINVAL) [] []) timerfd_model
  = CheckOk timerfd_model []
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22))
       (mkEffect 3 [] []) timerfd_model
     = CheckReject
  (* bit 15, a swallowed bit in the other run of them *)
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckOk timerfd_model []
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15))
       (mkEffect 3 [] []) timerfd_model
     = CheckReject
  (* bit 20, the third run of them *)
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckOk timerfd_model []
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20))
       (mkEffect 3 [] []) timerfd_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE ADMITTED CLOCK IDS DECLINE RATHER THAN ANSWER, including the two
    alarm ids the model can never resolve.  ADMISSION REASON: it is
    universally quantified in spirit and model-internal in fact — a
    run that fails closed shows that SOME call left the surface, and
    which syscall it was, but not that the decline is keyed on the clock
    id rather than on something else.

    The point of the alarm pair is stated in [Sys/Fs/Timerfd.v]: keeping
    [CLOCK_REALTIME_ALARM] and [CLOCK_BOOTTIME_ALARM] in the admitted set
    costs nothing and dropping them would answer -EINVAL where Linux
    answers -EPERM or a descriptor.  The two conjuncts that offer
    -EINVAL on the alarm ids are what make that concrete — the errno a
    shortened whitelist would produce is offered there and must NOT be
    accepted. *)

Example timerfd_create_admitted_clocks_decline :
  check_syscall (tfd_in CLOCK_REALTIME 0) (mkEffect 3 [] []) timerfd_model
  = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_MONOTONIC 0) (mkEffect 3 [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_BOOTTIME 0) (mkEffect 3 [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0) (mkEffect 3 [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0) (mkEffect 3 [] []) timerfd_model
     = CheckUnmodeled
  (* the alarm ids decline the -EPERM a real kernel gives an unprivileged
     caller too: declining is not "it happens to answer the right errno" *)
  /\ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0)
       (mkEffect (errno_ret EPERM) [] []) timerfd_model
     = CheckUnmodeled
  (* and a shortened whitelist's -EINVAL is not accepted for them *)
  /\ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckUnmodeled
  (* AND A CLOCK ID IN THE ADMITTED SET'S OWN GAP, STILL ANSWERED.
     Every conjunct above is [CheckUnmodeled], so on their own they stay
     green under any change that declines MORE -- the membership test
     widening, or the arm going unmodeled outright -- which is the change
     this lemma exists to notice.

     The admitted ids are 0, 1, 7, 8 and 9, so they are not an interval,
     and the likeliest way to widen the test is to read them as one:
     [0 <= clockid <= CLOCK_BOOTTIME_ALARM] swallows 2 through 6 and no
     conjunct above would notice.  [CLOCK_PROCESS_CPUTIME_ID] (2) sits in
     that gap and takes the gate's -EINVAL, so pinning it here is what
     makes the admitted set a SET rather than a range. *)
  /\ check_syscall (tfd_in CLOCK_PROCESS_CPUTIME_ID 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckOk timerfd_model [].
Proof. split_conj; check_eq. Qed.

(** THE ARGUMENTS NARROW TO 32 BITS, and the two halves are pinned
    together because only their conjunction says what narrowing means.
    ADMISSION REASON: model-internal — a run shows the answer the kernel
    returns and cannot show which comparison the model made to decline.

    A high half on the CLOCK ID aliases onto the admitted id and
    declines; a high half on the FLAGS aliases onto a clean flag word and
    declines.  A spec comparing the whole 64-bit register would have
    answered -EINVAL to both, so the second conjunct of each pair —
    that the -EINVAL is REFUSED — is the half that discriminates.

    No real run can show the refusal of the -EINVAL, because a kernel
    that returned one for these words does not exist. *)

Example timerfd_create_narrows_both_arguments :
  check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0)
    (mkEffect 3 [] []) timerfd_model
  = CheckUnmodeled
  /\ check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32))
       (mkEffect 3 [] []) timerfd_model
     = CheckUnmodeled
  /\ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckUnmodeled
  (* the high half does not rescue a BAD low half either: aliasing is not
     a second chance *)
  /\ check_syscall (tfd_in (2 ^ 32 + 11) 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = CheckOk timerfd_model [].
Proof. split_conj; check_eq. Qed.
