(** * LinuxProcessSem.Checks.Cases.Kernel.Sched.Syscalls — worked examples over sched_getaffinity (123), sched_setscheduler (119), sched_yield (124)

    Mirrors [Sys/Kernel/Sched/Syscalls.v], which answers to Linux
    [kernel/sched/syscalls.c]: this file holds the worked examples for
    the syscalls defined there, and no others.

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
(* [demo_model] is the shared fixture; it is defined beside the id calls
   that mutate it and shared rather than redefined — [Checks/Examples.v]
   re-exports every Cases module into one namespace, so two definitions of
   a name would shadow each other.  Nothing here depends on what is IN it:
   [sched_getaffinity_spec] reads no model state. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Kernel.Sys.

(* -------------------------------------------------------------------------
   sched_getaffinity (123)

   Every example below is here for the LAST of the four reasons listed
   at the top of [Checks/Examples.v]: a [CheckReject] needs a kernel
   answering something no kernel answers, and a [CheckUnmodeled] on a
   length Linux ANSWERS is a claim about the model alone.  The wrapping
   lengths themselves are issuable — [SYSCALL_DEFINE3(sched_getaffinity)]
   computes [(len * BITS_PER_BYTE) < nr_cpu_ids] on an [unsigned int
   len] and touches neither the pid nor the pointer before either gate
   (kernel/sched/syscalls.c, v6.18.46) — and the wrapping set and the
   compat-aligned lengths are walked here.
   ------------------------------------------------------------------------- *)

Definition sched_getaffinity_in (pid len user_mask_ptr : word) : SyscallInput :=
  mkInput 123 [pid; len; user_mask_ptr; 0; 0; 0] (fun _ => None) (fun _ => None).

(** THE WRAPPING LENGTHS.  [len] is an [unsigned int] and
    [BITS_PER_BYTE] is a plain [8], so [len * BITS_PER_BYTE] is computed
    in 32 bits.  The product is zero exactly on the multiples of 2^29,
    and [nr_cpu_ids] is at least 1, so every one of them is -EINVAL —
    the large ones included, which read as obviously-big-enough to a
    model that did the multiplication over the integers.  The pid and
    the mask pointer are garbage throughout: both gates run before
    either is looked at. *)
Example sched_getaffinity_wrapping_lengths_are_einval :
  let einval := mkEffect (errno_ret EINVAL) [] [] in
  check_syscall (sched_getaffinity_in 0 0 3735928559) einval demo_model
    = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 536870912 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 1073741824 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 1610612736 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 2147483648 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 2684354560 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 3221225472 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 3758096384 3735928559) einval demo_model
       = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE LENGTHS CONGRUENT TO 4 MOD 8 are what tell the native gate's
    [& 7] from the compat gate's [& 3], and they are the sharpest
    available mistake: a spec written from kernel/compat.c's
    [COMPAT_SYSCALL_DEFINE3(sched_getaffinity)] instead of
    kernel/sched/syscalls.c's would call these MODELED-OUT and still
    answer -EINVAL for every other length in this file.  They are
    -EINVAL for an LP64 caller, which is the only kind this model
    loads. *)
Example sched_getaffinity_compat_aligned_lengths_are_einval :
  let einval := mkEffect (errno_ret EINVAL) [] [] in
  check_syscall (sched_getaffinity_in 0 4 3735928559) einval demo_model
    = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 12 3735928559) einval demo_model
       = CheckOk demo_model []
  /\ check_syscall (sched_getaffinity_in 0 4294967292 3735928559) einval demo_model
       = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** …and the boundary is exactly where the wrap puts it.  The two
    neighbours of 2^29 are eight-aligned like it, differ from it by one
    machine word, and are NOT refused: their bit counts are 2^32 - 64
    and 64, neither of which is below every [nr_cpu_ids].  So the model
    declines them rather than guess, and that is the discrimination this
    file exists for — an arm that refused every large length, or every
    length above some cap, would answer -EINVAL here too, and only these
    cases tell it apart. *)
Example sched_getaffinity_wrap_neighbours_are_unmodeled :
  let einval := mkEffect (errno_ret EINVAL) [] [] in
  check_syscall (sched_getaffinity_in 0 536870904 3735928559) einval demo_model
    = CheckUnmodeled
  /\ check_syscall (sched_getaffinity_in 0 536870920 3735928559) einval demo_model
       = CheckUnmodeled
  (* AND THE WRAP ITSELF, STILL ANSWERED, between them.  The two
     declines are both [CheckUnmodeled], so on their own they stay green
     under any change that declines MORE -- the wrapping-length arm
     going unmodeled along with its neighbours, which erases the very
     discrimination the paragraph above claims.  2^29 is the point the
     two neighbours are neighbours OF; pinning it here is what makes
     this lemma fail when the boundary moves rather than merely say
     where it is. *)
  /\ check_syscall (sched_getaffinity_in 0 536870912 3735928559) einval demo_model
       = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE NEGATIVE DIRECTION, which no real run can produce: a kernel
    that answered a wrapping length with a plausible byte count, with
    the -EFAULT its untouched pointer cannot produce, or with the errno 3
    (-ESRCH) its unreached task lookup cannot produce, is REJECTED.  So is
    one that answered -EINVAL and wrote to the mask anyway: nothing is
    stored before either gate.  -ESRCH is spelled as the number because
    [State.v] has no constant for it. *)
Example sched_getaffinity_wrapping_length_lies_rejected :
  check_syscall (sched_getaffinity_in 0 536870912 3735928559)
    (mkEffect 8 [] []) demo_model = CheckReject
  /\ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
  /\ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret 3) [] []) demo_model = CheckReject
  /\ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret EINVAL) [(3735928559, [Z_to_bv 8 0])] []) demo_model
       = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   sched_setscheduler (119)

   These are here for the FOURTH of the four reasons listed at the top of
   [Checks/Examples.v] for the [CheckReject]s — a lying kernel is the only
   thing that produces them — and for the SECOND for the pairs below that
   separate two -EINVALs a real run cannot tell apart.  The kernel
   answers -EINVAL by four different routes and by the same number, so
   a real run cannot say WHICH route a model took; the discriminations that need saying are
   made here, against the checker.
   ------------------------------------------------------------------------- *)

Definition sched_setscheduler_in (pid policy param : word)
    (mem : word -> option byte) : SyscallInput :=
  mkInput 119 [pid; policy; param; 0; 0; 0] mem (fun _ => None).

(** Four readable bytes at address 4096 holding a little-endian [int],
    which is the whole of a [struct sched_param].  Nothing else in the
    address space is readable, which is what makes the -EFAULT and
    decline cases below reachable at all. *)
Definition sched_param_mem (v : Z) : word -> option byte :=
  fun a =>
    let off := (bv_unsigned a - 4096)%Z in
    if ((0 <=? off)%Z && (off <? 4)%Z)%bool
    then Some (Z_to_bv 8 ((v / 2 ^ (8 * off)) mod 256))
    else None.

Definition sched_param_ptr : word := Z_to_bv 64 4096.

(** THE PRIORITY IS A [__u32] AT THE RANGE GATE, and this is the pair
    that says so.  [struct sched_param] holds an [int], and
    [_sched_setscheduler] copies it into [struct sched_attr]'s [__u32
    sched_priority], so -1 meets [attr->sched_priority > MAX_RT_PRIO-1]
    as 4294967295 and is refused THERE — by the same gate that refuses
    100, and before the [rt_policy(policy) != (sched_priority != 0)]
    comparison ever runs.  Both answers are -EINVAL, so no real run can
    separate them; what CAN be separated is 99, which the range gate
    admits, from -1, which it does not.  A model that read the field
    signed would put -1 on the far side of the range gate and reach the
    same -EINVAL through the RT-agreement test for SCHED_IDLE — and
    would then have to answer SCHED_FIFO at priority -1 with a success,
    which is the case that fails here. *)
Example sched_setscheduler_negative_priority_is_out_of_range :
  let einval := mkEffect (errno_ret EINVAL)
                  [] [] in
  let einval_c := with_copyins [(sched_param_ptr, 4%nat)] einval in
  (* -1 as a signed int, 4294967295 as the u32 the gate compares *)
  check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                   (sched_param_mem 4294967295)) einval_c demo_model
    = CheckOk demo_model []
  (* ...and 99 is admitted by that gate, so SCHED_FIFO at 99 is not an
     -EINVAL at all: it is the RT request the model declines *)
  /\ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                      (sched_param_mem 99)) einval_c demo_model
       = CheckUnmodeled
  (* ...while 100 is refused, one past MAX_RT_PRIO-1 *)
  /\ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                      (sched_param_mem 100)) einval_c demo_model
       = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE ORDER OF THE TWO PRE-COPY -EINVALS, on a call that is wrong in
    three ways at once.  [policy < 0] is decided in
    [SYSCALL_DEFINE3(sched_setscheduler)] itself, before
    [do_sched_setscheduler] is entered, so a negative policy beats the
    null [param] and the negative pid beside it — and beats the -EFAULT
    an unreadable [param] would raise, which is the discrimination the
    unreadable pointer here makes.  A model that tested the pointer
    first would answer -EFAULT to the second of these. *)
Example sched_setscheduler_negative_policy_wins :
  let einval := mkEffect (errno_ret EINVAL) [] [] in
  check_syscall (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => None))
    einval demo_model = CheckOk demo_model []
  /\ check_syscall (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1))
                      (Z_to_bv 64 (2 ^ 63)) (fun _ => None))
       einval demo_model = CheckOk demo_model []
  (* and the truncation is real: 2^32 | SCHED_IDLE is a [pid_t]-width 5
     and not a negative number, so the same register value with the low
     half changed is answered rather than refused *)
  /\ check_syscall (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 32 + 5))
                      sched_param_ptr (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4%nat)] (mkEffect (Z_to_bv 64 0) [] []))
       demo_model = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** -EFAULT IS THE RANGE VERDICT AND NOTHING ELSE, and it records no
    copy-in.  [access_ok] refuses four bytes whose last one is at
    [State.TASK_SIZE], and refuses them before a load, so the answer
    carries an empty ledger; a range [access_ok] ADMITS that memory does
    not back is declined instead, because Linux answers -EFAULT there
    too and the ledger cannot say which bytes it read first.  The two
    addresses below are three bytes apart and land on opposite sides of
    that line. *)
Example sched_setscheduler_fault_is_the_range_verdict :
  let efault := mkEffect (errno_ret EFAULT) [] [] in
  check_syscall (sched_setscheduler_in 0 5
                   (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => None))
    efault demo_model = CheckOk demo_model []
  (* the last four bytes wholly under TASK_SIZE: the range passes, and
     the model declines rather than reporting the fault *)
  /\ check_syscall (sched_setscheduler_in 0 5
                      (Z_to_bv 64 (TASK_SIZE - 4)) (fun _ => None))
       efault demo_model = CheckUnmodeled
  (* ...and the -EFAULT it does answer carries no ledger *)
  /\ check_syscall (sched_setscheduler_in 0 5
                      (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => None))
       (with_copyins [(Z_to_bv 64 (TASK_SIZE - 3), 4%nat)] efault) demo_model
       = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE DECLINES, each on the exact argument that makes it one.  Every
    call here is one Linux ANSWERS — SCHED_FIFO at priority 1 and
    SCHED_NORMAL at 0 are ordinary requests, and SCHED_IDLE with
    SCHED_RESET_ON_FORK is a 0 — so each is a claim about the model
    alone, which is why they are here. *)
Example sched_setscheduler_declines :
  let ok := with_copyins [(sched_param_ptr, 4%nat)]
              (mkEffect (Z_to_bv 64 0) [] []) in
  (* RLIMIT_RTPRIO and CAP_SYS_NICE decide this one *)
  check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                   (sched_param_mem 1)) ok demo_model = CheckUnmodeled
  (* whether the task is ALREADY SCHED_IDLE decides this one *)
  /\ check_syscall (sched_setscheduler_in 0 0 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = CheckUnmodeled
  (* ...and this one, for the same reason *)
  /\ check_syscall (sched_setscheduler_in 0 3 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = CheckUnmodeled
  (* CONFIG_SCHED_CLASS_EXT decides whether 7 is a policy at all *)
  /\ check_syscall (sched_setscheduler_in 0 7 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = CheckUnmodeled
  (* the SCHED_RESET_ON_FORK bit is a state change nothing records *)
  /\ check_syscall (sched_setscheduler_in 0
                      (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = CheckUnmodeled
  (* a positive pid, with no tid pinned: the model cannot say whether
     the number names this task *)
  /\ check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE ONE ANSWER PAST THE TASK LOOKUP, and the lies a kernel would
    have to tell to make it something else.  -EPERM is the sharpest of
    them: it is what the call really returns when
    [p->sched_reset_on_fork] is set or when a capability is missing, so
    a model that had made the SCHED_IDLE answer depend on a credential
    it does not carry would ACCEPT it here and agree with this file
    everywhere else. *)
Example sched_setscheduler_idle_is_zero :
  let ok := with_copyins [(sched_param_ptr, 4%nat)]
              (mkEffect (Z_to_bv 64 0) [] []) in
  check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                   (sched_param_mem 0)) ok demo_model = CheckOk demo_model []
  /\ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4%nat)]
          (mkEffect (errno_ret EPERM) [] [])) demo_model = CheckReject
  /\ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4%nat)]
          (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
  (* nor does the success write anything back: the call has no output
     parameter at all *)
  /\ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4%nat)]
          (mkEffect (Z_to_bv 64 0) [(sched_param_ptr, [Z_to_bv 8 0])] []))
       demo_model = CheckReject
  (* ...and it does record the four bytes it read *)
  /\ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE PID THE PINNED TID NAMES, against one it does not, on the SAME
    model.  This is the shape musl's [pthread_setschedparam] issues — it
    passes [t->tid], never 0 — so the pair matters: an arm that answered
    only pid 0 leaves every real caller outside the modeled surface, and
    an arm that answered any positive pid would be claiming to know
    about a task it has no representation of. *)
Example sched_setscheduler_pid_is_the_pinned_tid :
  let m := with_tid (Z_to_bv 64 4096) demo_model in
  let ok := with_copyins [(sched_param_ptr, 4%nat)]
              (mkEffect (Z_to_bv 64 0) [] []) in
  check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr
                   (sched_param_mem 0)) ok m = CheckOk m []
  (* the same register with its high half set: [pid_t] is an [int], so
     this IS the pinned tid *)
  /\ check_syscall (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 + 4096)) 5
                      sched_param_ptr (sched_param_mem 0)) ok m = CheckOk m []
  (* the neighbouring pid is a different task, and declined *)
  /\ check_syscall (sched_setscheduler_in 4097 5 sched_param_ptr
                      (sched_param_mem 0)) ok m = CheckUnmodeled
  (* ...and pid 0 is [current] whatever the tid is *)
  /\ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0)) ok m = CheckOk m [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE FOUR BYTES THAT WALKED OFF THE TOP.  [param] is read through
    [State.copy_bytes_map], which asks [State.access_okb] before the
    walk; [Kernel.Sched.Syscalls.sched_setscheduler_spec]'s note says
    why, and [State.copy_bytes_map]'s note carries the wrap argument.
    The group has the shape of [Checks.Cases.Net.Socket]'s wrapping-read
    groups: the wrapping call refused, a NEIGHBOURING ordinary call at
    the top of what [State.access_okb] accepts still answered, and the
    control that the bare walk really would have passed.  Both memories
    map exactly their own four bytes.

    Two readable bytes below the top and two from 0, all zero: the
    bare walk reads priority 0, and SCHED_IDLE at priority 0 on the
    calling task is the one call this arm answers 0 to — so before the
    guard this call was answered, with the four bytes in the ledger. *)
Definition sched_setscheduler_wrap_param : word := Z_to_bv 64 (2 ^ 64 - 2).

Definition sched_setscheduler_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 2)%Z || (2 ^ 64 - 2 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example sched_setscheduler_wrap_would_pass_the_bare_walk :
  read_bytes_map sched_setscheduler_wrap_mem sched_setscheduler_wrap_param
    (Z_to_bv 64 4) <> None.
Proof. vm_compute. discriminate. Qed.

Example sched_setscheduler_wrap_param_is_not_copyable :
  copy_bytes_map sched_setscheduler_wrap_mem sched_setscheduler_wrap_param 4
    = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with an empty ledger.  [do_sched_setscheduler]'s
    [copy_from_user] of [struct sched_param] (kernel/sched/syscalls.c)
    refuses this range in [access_ok] before it loads a byte.  The 0 the
    bare walk admitted is refused, and so is an -EFAULT claiming the
    copy-in. *)
Example sched_setscheduler_wrapping_param_is_efault :
  check_syscall (sched_setscheduler_in 0 5 sched_setscheduler_wrap_param
                   sched_setscheduler_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) demo_model
  = CheckOk demo_model []
  /\ check_syscall (sched_setscheduler_in 0 5 sched_setscheduler_wrap_param
                      sched_setscheduler_wrap_mem)
       (with_copyins [(sched_setscheduler_wrap_param, 4%nat)]
          (mkEffect (Z_to_bv 64 0) [] [])) demo_model
     = CheckReject
  /\ check_syscall (sched_setscheduler_in 0 5 sched_setscheduler_wrap_param
                      sched_setscheduler_wrap_mem)
       (with_copyins [(sched_setscheduler_wrap_param, 4%nat)]
          (mkEffect (errno_ret EFAULT) [] [])) demo_model
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** THE NEIGHBOUR: the last four bytes [State.access_okb] accepts,
    readable and zero.  The same SCHED_IDLE call is still answered 0
    with the copy-in recorded, and -EFAULT is refused.  This is the
    address [sched_setscheduler_fault_is_the_range_verdict] declines on
    with nothing mapped; mapped, it is answered. *)
Definition sched_setscheduler_top_param : word := Z_to_bv 64 (TASK_SIZE - 4).

Definition sched_setscheduler_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 4 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example sched_setscheduler_param_at_the_top_still_answers :
  check_syscall (sched_setscheduler_in 0 5 sched_setscheduler_top_param
                   sched_setscheduler_top_mem)
    (with_copyins [(sched_setscheduler_top_param, 4%nat)]
       (mkEffect (Z_to_bv 64 0) [] [])) demo_model
  = CheckOk demo_model []
  /\ check_syscall (sched_setscheduler_in 0 5 sched_setscheduler_top_param
                      sched_setscheduler_top_mem)
       (mkEffect (errno_ret EFAULT) [] []) demo_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* -------------------------------------------------------------------------
   sched_yield (124)

   These are here for the last of the four reasons at the top of
   [Checks/Examples.v]: a [CheckReject] needs a kernel answering
   something no kernel answers.  The accepting half is reachable by a
   real run.  What no real run can show at all is the refusing
   half: that the model rejects the answers Linux never gives, and that
   it accepts 0 for every argument word rather than for the ones a run
   happened to pass.
   ------------------------------------------------------------------------- *)

Definition sched_yield_in (a0 a1 a2 a3 a4 a5 : word) : SyscallInput :=
  mkInput 124 [a0; a1; a2; a3; a4; a5] (fun _ => None) (fun _ => None).

Definition sched_yield_zeros : SyscallInput := sched_yield_in 0 0 0 0 0 0.

(** 124 is dispatched at all: without an arm, a target that called it
    would reach the error transition. *)
Example sched_yield_is_modeled : In 124%Z modeled_sysnos.
Proof. vm_compute. tauto. Qed.

(** THE ANSWER IS 0 AND NOTHING ELSE MOVES.  [SYSCALL_DEFINE0(sched_yield)]
    is [do_sched_yield(); return 0;] (kernel/sched/syscalls.c, Linux
    v6.12.1), and everything [do_sched_yield] touches is per-run-queue
    scheduler bookkeeping this model has no representation of. *)
Example sched_yield_answers_zero :
  check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 0) [] []) demo_model
  = CheckOk demo_model [].
Proof. vm_compute. reflexivity. Qed.

(** EVERY ARGUMENT WORD IS IGNORED, and that is the kernel's own shape
    rather than this spec's convenience: riscv64's [SYSCALL_DEFINE0]
    (arch/riscv/include/asm/syscall_wrapper.h) takes
    [const struct pt_regs *__unused] and expands without
    [SC_RISCV_REGS_TO_ARGS], so no argument register reaches the body.
    A spec that refused some argument shape would decline a call Linux
    answers 0.  Three shapes a typical caller would not pass: all bits
    set, a mix of addresses and errno-looking words, and the all-ones
    word in the last register alone. *)
Example sched_yield_ignores_every_argument_word :
  let ok := mkEffect (Z_to_bv 64 0) [] [] in
  check_syscall (sched_yield_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)))
    ok demo_model = CheckOk demo_model []
  /\ check_syscall (sched_yield_in 4096 (errno_ret EINVAL) (Z_to_bv 64 0x7fff80000000)
                     (Z_to_bv 64 (2 ^ 32)) 1 0) ok demo_model = CheckOk demo_model []
  /\ check_syscall (sched_yield_in 0 0 0 0 0 (Z_to_bv 64 (2 ^ 64 - 1)))
       ok demo_model = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE REFUSALS.  No kernel answers this call anything but 0, so each
    of these is an answer the checker must reject rather than record:
    the two nearest integers, an errno, and the -EPERM
    [ALLOW_ERROR_INJECTION] would make reachable on a kernel running a
    [bpf_override_return] program — which [Kernel.Sched.Syscalls.sched_yield_spec]
    names as the residual this model does not describe.  A
    [CheckUnmodeled] is impossible here and no case asserts one: the arm
    has no fail-closed branch at all. *)
Example sched_yield_nonzero_answers_rejected :
  check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 1) [] []) demo_model
    = CheckReject
  /\ check_syscall sched_yield_zeros
       (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) demo_model = CheckReject
  /\ check_syscall sched_yield_zeros
       (mkEffect (errno_ret EINTR) [] []) demo_model = CheckReject
  /\ check_syscall sched_yield_zeros
       (mkEffect (errno_ret EPERM) [] []) demo_model = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ...and a 0 that claims to have written user memory, freed a
    mapping, or read one is rejected too: the call has no output
    parameter, no argument to fetch, and nothing to unmap. *)
Example sched_yield_effect_shape_is_bare :
  check_syscall sched_yield_zeros
    (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) demo_model
    = CheckReject
  /\ check_syscall sched_yield_zeros
       (with_copyins [(Z_to_bv 64 4096, 4%nat)] (mkEffect (Z_to_bv 64 0) [] []))
       demo_model = CheckReject
  /\ check_syscall sched_yield_zeros
       (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
       demo_model = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.
