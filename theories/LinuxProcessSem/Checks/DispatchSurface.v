(** * LinuxProcessSem.Checks.DispatchSurface — the modeled syscall list is exactly the dispatched set

    [Specs.modeled_sysnos] is the list that documents which syscall
    numbers this model covers.  Nothing in the trace semantics consults
    it, so on its own it is a comment that happens to be typed, and
    [Checks/ProcessCreation.v] says so where it names this file.

    WHAT IS ALREADY IMPOSSIBLE, and therefore not what this file is for.
    The list and the dispatcher are read off ONE table:
    [modeled_sysnos = arm_numbers spec_table] and
    [syscall_spec = dispatch spec_table].  A number cannot be in
    one and missing from the other, whatever anybody edits.  What this
    file adds is
    two facts the shared table does not give, and one that it does but
    that nothing else states.

    - EXCLUSION, which the table gives cheaply but nothing else states.
      [Sys/Dispatch.v]'s [dispatch_unmodeled] is stated over
      [lookup_arm t n = None], not over [~ In n (arm_numbers t)], so it
      does not bridge "absent from the LIST" and "declined".
      [syscall_spec_number_modeled] is that bridge, and it holds for ANY
      table rather than for one dispatcher: the work is in
      [lookup_arm_in], seven lines by induction.

    - THE CONVERSE, which the table does NOT give: every number the list
      names is answered on SOME input ([modeled_sysnos_dispatched]).  An
      arm can sit in [spec_table] and be [unmodeled] on every input, and
      the table identity cannot see it — [dispatch_arm] says the
      dispatcher equals that arm's spec and nothing about the spec
      answering anything.  This is proved by running the computable
      witness of [Progress.syscall_spec_witness] on one probe input per
      number and checking by [vm_compute] that none falls through;
      [Progress.receptive] carries that back to [syscall_spec].  READ IT
      AS A FLOOR, NOT AS COVERAGE: it says each number has an answer
      somewhere, not that it answers the argument shape any particular
      program uses.  A listed number still declines the shapes its own
      spec rejects, which is the whole point of [Monad.unmodeled].

    - NO REPEATS, which the table does not give either.  [lookup_arm] is
      first-match-wins, so a number listed twice silently shadows the
      second arm, and exactness — stated with [In] — is blind to it.
      [modeled_sysnos_nodup] rules it out separately, and it is the only
      mechanism anywhere in the tree that would: there is no [NoDup], no
      length and no sortedness lemma over either table.  Two changes
      that each add the same arm merge clean, build green, and leave a
      second arm that nothing will ever reach.

    Both checked facts fail the BUILD rather than a linter.  Adding a
    syscall means adding the arm and, if the number needs arguments the
    default probe does not supply, a [probe_args] entry; get either out
    of step and this file does not compile. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Progress.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   Small helpers
   ========================================================================= *)

(** Membership decided by computation, so the side conditions below can be
    discharged by [vm_compute] against whatever [modeled_sysnos] currently
    holds — no proof edit when an entry is added. *)
Lemma forallb_In : forall (f : Z -> bool) (l : list Z) (x : Z),
  forallb f l = true -> In x l -> f x = true.
Proof. intros f l x H Hin. rewrite forallb_forall in H. now apply H. Qed.

Lemma in_of_existsb_eqb : forall (n : Z) (l : list Z),
  existsb (Z.eqb n) l = true -> In n l.
Proof.
  intros n l H. apply existsb_exists in H. destruct H as [x [Hx Heq]].
  apply Z.eqb_eq in Heq. subst. exact Hx.
Qed.


(* =========================================================================
   Direction 1: nothing outside [modeled_sysnos] is dispatched
   ========================================================================= *)

(** The whole of it, and it is a fact about [lookup_arm] rather than about
    any particular table: if the lookup finds an arm, the number it was
    given is one of the table's own.  The [if] that decides each step is
    exactly the equality the conclusion needs. *)
Lemma lookup_arm_in : forall t n a,
  lookup_arm t n = Some a -> In n (arm_numbers t).
Proof.
  induction t as [|b r IH]; intros n a H; cbn in H; [discriminate|].
  destruct (Z.eqb (sa_no b) n) eqn:E.
  - apply Z.eqb_eq in E. left. exact E.
  - right. exact (IH n a H).
Qed.

(** An [Ok] outcome pins the syscall number into the list.  A number with
    no arm reaches [Monad.unmodeled], which admits no [Ok] at all. *)
Theorem syscall_spec_number_modeled : forall i m x m' evs,
  syscall_spec i m (Ok x m' evs) ->
  In (bv_unsigned (in_sysno i)) modeled_sysnos.
Proof.
  intros i m x m' evs H.
  unfold syscall_spec, dispatch, modeled_sysnos in *.
  destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - exact (lookup_arm_in _ _ _ E).
  - unfold unmodeled in H. discriminate H.
Qed.

(** The same fact read as fail-closed behaviour. *)
Corollary syscall_spec_unmodeled_outside : forall i m o,
  ~ In (bv_unsigned (in_sysno i)) modeled_sysnos ->
  syscall_spec i m o ->
  o = Unmodeled.
Proof.
  intros i m o Hnin H. destruct o as [x m' evs|]; [|reflexivity].
  exfalso. apply Hnin. exact (syscall_spec_number_modeled _ _ _ _ _ H).
Qed.

(** The fail-closed direction stated as an INTRODUCTION lemma: outside the
    list, [Unmodeled] is an admissible outcome.  That is a strictly weaker
    claim than [syscall_spec_unmodeled_outside] — it says the dispatcher
    ADMITS [Unmodeled], not that it admits nothing else, and [Sys] is a
    relation, so a spec can admit both — but it is the shape a proof that
    needs to CONSTRUCT the declined outcome wants.  It follows from the
    exclusion direction and [Progress.receptive] (which supplies an
    admissible outcome for every input) in two steps, so there is no reason
    for anything else in the tree to prove it separately. *)
Corollary syscall_spec_declines_outside : forall i m,
  ~ In (bv_unsigned (in_sysno i)) modeled_sysnos ->
  syscall_spec i m Unmodeled.
Proof.
  intros i m Hnin.
  rewrite <- (syscall_spec_unmodeled_outside i m _ Hnin (receptive i m)).
  apply receptive.
Qed.

(* =========================================================================
   Direction 2: every number in [modeled_sysnos] is answered somewhere
   ========================================================================= *)
(** A model with no files, no mappings and only the three standard fds, so a
    probe fd of AT_FDCWD (which is not a valid fd) reliably answers -EBADF. *)
Definition probe_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo)
    0x40000000%Z
    (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                 net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48).

(** THE ONE EXCEPTION TO ONE MODEL FOR EVERY NUMBER, and it is worth
    reading before the table below rather than after.

    [tkill] (130) and [tgkill] (131) answer only where the task DECLARED
    the abort path ([State.in_abort_terminal]) and only for the caller's
    own tid, so no choice of argument registers reaches an answer from
    [probe_model]: the declaration is a property of the run, not of the
    call.  That is the arms' whole design — with the declaration clear
    they decline every shape, which is what the numbers did when they had
    no arm — so the probe for those two numbers runs against a model that
    declares it and pins a tid, and every other number keeps
    [probe_model].

    What this check therefore says about 130 and 131 is "answers under a
    declaration", which is the strongest true statement about them.  The
    other half — that they decline WITHOUT one — is
    [Checks.Cases.Kernel.Signal]'s [tkill_off_declined], which runs the
    answering shape against a model with the declaration clear. *)
Definition probe_tid : word := Z_to_bv 64 4242.

Definition probe_model_abort : Model :=
  with_tid probe_tid
    (init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo)
       0x40000000%Z
       (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc
                    true Sv48)).

(** The model a probe of [n] runs against. *)
Definition probe_model_for (n : Z) : Model :=
  if (Z.eqb n 130 || Z.eqb n 131)%bool then probe_model_abort else probe_model.

(** Where [clone3]'s probe finds a FORK-SHAPED [struct clone_args].  Far
    from 0 and from AT_FDCWD, the two addresses every other probe uses. *)
Definition clone3_probe_uargs : word := Z_to_bv 64 0x10000.

(** Every address readable and writable, holding a NUL byte -- openat's
    probe path is then the empty string (-ENOENT) and no buffer is
    unreadable -- EXCEPT the one byte that makes [clone3]'s struct
    fork-shaped.

    [clone3_spec] declines every size but [CLONE_ARGS_SIZE] and then every
    struct but the one [Fork.clone3_fork_args_b] admits: all eleven fields
    zero except [exit_signal] = SIGCHLD, which [Fork.clone_args_field]
    reads from offset 32.  An all-NUL memory therefore gives
    [exit_signal = 0] and the arm declines, so unlike every other entry
    below this one cannot be fixed by choosing arguments -- the fixture
    has to carry the struct.  Only that byte changes; every other address
    still reads NUL. *)
Definition probe_mem : word -> option byte :=
  fun a => Some (if bv_eqb a (clone3_probe_uargs + Z_to_bv 64 32)
                 then Z_to_bv 8 SIGCHLD
                 else Z_to_bv 8 0).

(** Arguments for the probe of syscall number [n].

    The default answers every modeled number except the ones listed
    below.  Deliberately not a COUNT: a number here is checked by
    nobody and goes stale when the next arm is added, while the list
    below is at least read by whoever adds an arm.

    [a0] is AT_FDCWD, which is
    three useful things at once: the dirfd that openat and readlinkat
    model, an fd that no open-file table holds (so fd-taking arms answer
    -EBADF), and — as an address, [2^64 - 100] — a value no page boundary
    can equal, so the arms that gate on alignment answer -EINVAL there.
    The remaining registers are zero, which is a modeled flag word for
    openat and getrandom and a zero length for munmap and the transfer
    calls.

    mprotect is one of the alignment-gated arms: [mprotect_spec] reaches
    [addr mod page_size] before it consults [mprotect_modeled_b prot],
    and the one gate ahead of the alignment test reads only [prot]'s two
    grows bits, which answers -EINVAL rather than declining.  So the
    default probe answers 226 whatever [prot] holds and it needs no entry
    here.

    The exceptions are the arms that DECLINE what the default registers
    hold rather than answering with it, so none of them reaches an error
    gate without help:

    - mmap (222) and mremap (216) decline the default FLAG WORD.
      [mmap_spec] at zero length answers only for an anonymous mapping
      and is [unmodeled] otherwise, and [mremap_spec] models only
      MREMAP_MAYMOVE.
    - prlimit64 (261) declines the default PID: [Specs.prlimit64_spec]
      answers only for pid 0 (no other task exists), only for
      RLIMIT_CORE, and only when exactly one of the two rlimit pointers
      is NULL — three gates the default registers fail at the first.
    - clock_gettime (113) declines the default CLOCKID: [a0] is a clock
      id here rather than an fd, and AT_FDCWD truncated to 32 bits is no
      modeled clock, so the arm declines before it reaches an answer.
    - clock_getres (114) also needs a valid CLOCKID.  Its [tp] must be
      non-NULL in this probe because [probe_mem] makes address zero
      writable, and QEMU could copy the result there.
    - clone (220) declines the default FLAG WORD: [clone_fork_flags_b]
      admits the single word SIGCHLD and nothing else.
    - clone3 (435) declines the default SIZE and the default STRUCT: it
      answers only [CLONE_ARGS_SIZE] bytes at a readable address holding
      the fork-shaped [struct clone_args], which is why [probe_mem] above
      carries one.
    - wait4 (260) declines the default ARGUMENT WORDS, before anything
      else: [Kernel.Exit.wait4_spec] answers only when [upid] is the
      32-bit -1 [Kernel.Exit.WAIT_ANY32] and [options] is exactly
      [WNOHANG].
    - sendto (206) and sendmsg (211) decline the default FLAG WORD, and
      for a stricter reason than mmap's: [Net.Socket.send_flags_modeled]
      is a [Z.eqb] against MSG_NOSIGNAL, not a mask test, so zero is not
      a permissive default here but a value the arm refuses.  The flag
      sits in a DIFFERENT REGISTER for the two: sendto's arguments are
      (fd, buf, count, flags, addr, addrlen) so it is [a3], and
      sendmsg's are (fd, msg, flags) so it is [a2].

      THIS COUNT AND THESE BULLETS ARE HAND-MAINTAINED AND NOTHING
      CHECKS THEM.  [probe_args] below is gated by
      [modeled_sysnos_probes_answer], which fails the build if an entry
      is missing; the sentence and the list up here are gated by nobody,
      so adding another entry without editing them leaves a paragraph
      that is wrong by one and compiles clean.
    - socketpair (199) declines the default FAMILY.  [a0] IS the family,
      so there is no -EBADF to fall back on the way recvfrom (207) and
      recvmsg (212) have one, and [Net.Socket.socketpair_modeled_b]
      admits only AF_INET.  That is the general rule the entries above
      follow — an arm that resolves an fd first answers -EBADF before the
      gated argument matters, and an arm that gates on an ARGUMENT VALUE
      declines and needs an entry.

    THE RULE HAS AN EXCEPTION, and it is worth naming so that the next
    arm-that-reads-a0-as-a-value is not given an entry it does not need.
    getgroups (158) reads [a0] as a value too — it is [gidsetsize], not
    an fd — and it needs no entry, because AT_FDCWD is -100 and
    [Kernel.Groups.getgroups_spec]'s FIRST test is [gidsetsize < 0].  The
    default probe therefore reaches its -EINVAL rather than declining.
    What decides the question is not whether [a0] is an fd but whether
    the arm has an ERROR GATE the default value trips, which is the same
    thing mprotect's paragraph above says about alignment.

    Add an entry when a newly listed syscall needs something else;
    leaving it out makes [modeled_sysnos_probes_answer] below fail to
    compute to [true], which fails the build. *)
Definition probe_args (n : Z) : list word :=
  let z := Z_to_bv 64 0 in
  if Z.eqb n 19 then
    (* eventfd2 reads a1 as the FLAG WORD and a0 as an initial counter it
       never judges, so the default probe -- whose a1 is 0 -- hands it an
       ACCEPTED flag word and the arm declines the descriptor it would
       have to mint.  [O_LARGEFILE] is a bit outside [EFD_FLAGS_SET], so
       the arm reaches the -EINVAL that is its only answer.  a0 stays 0
       because no [count] changes the verdict. *)
    [z; Z_to_bv 64 O_LARGEFILE; z; z; z; z]
  else if Z.eqb n 222 then
    (* mmap answers -EINVAL on a zero length only for an anonymous mapping *)
    [AT_FDCWD; z; z; Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS); z; z]
  else if Z.eqb n 216 then
    (* mremap models only MREMAP_MAYMOVE; the misaligned a0 is then -EINVAL *)
    [AT_FDCWD; z; z; Z_to_bv 64 MREMAP_MAYMOVE; z; z]
  else if Z.eqb n 261 then
    (* prlimit64 READING RLIMIT_CORE: pid 0, and exactly one of the two
       rlimit pointers NULL -- new_rlim = 0 with old_rlim writable is
       the read path, and [probe_mem] makes a3 writable *)
    [z; Z_to_bv 64 RLIMIT_CORE; z; Z_to_bv 64 4096; z; z]
  else if Z.eqb n 199 then
    (* socketpair gates on the FAMILY and has no descriptor to resolve
       first, so the default [AT_FDCWD] in a0 is read as a family no
       [Net.Socket.socketpair_modeled_b] accepts and the arm declines.
       With AF_INET/SOCK_STREAM at protocol 0 it reaches [socketpair_fds]
       and then the [usockvec] store, which [probe_mem] makes writable at
       0, so it answers.  a3 stays 0 for that reason. *)
    [Z_to_bv 64 AF_INET; Z_to_bv 64 SOCK_STREAM; z; z; z; z]
  else if Z.eqb n 113 then
    (* clock_gettime dispatches on a CLOCKID, not an fd: AT_FDCWD truncated
       to 32 bits is no modeled clock, so the arm declines before it reaches
       an answer.  [CLOCK_REALTIME] is 0, so this reads like the default --
       named anyway, because a bare [z] in the one position that carries the
       entry is indistinguishable from a don't-care.  Chosen over
       [CLOCK_MONOTONIC] because that arm also gates on
       [m_clock m <? CLOCK_NS_ENVELOPE], which would make whether the probe
       answers depend on [probe_model]'s clock; the realtime arm gates only
       on the destination, which [probe_mem] makes writable. *)
    [Z_to_bv 64 CLOCK_REALTIME; z; z; z; z; z]
  else if Z.eqb n 114 then
    (* The probe memory is writable at zero, so use a non-NULL [tp]. *)
    [Z_to_bv 64 CLOCK_MONOTONIC; Z_to_bv 64 4096; z; z; z; z]
  else if Z.eqb n 98 then
    (* futex dispatches on the OP WORD, and the default a1 of 0 is
       [FUTEX_WAIT] without [FUTEX_PRIVATE_FLAG] -- a shared wait, which
       [Kernel.Futex.Syscalls.futex_spec] declines.  The private wake is
       the arm with an answer that needs nothing of the model: a0 of 0 is
       4-byte aligned and passes [access_okb], so the arm returns 0
       waiters woken.  a0 is named rather than left at [AT_FDCWD]
       because that address is aligned too and would answer -EFAULT --
       an answer, so the probe would pass, but on the gate rather than
       on the operation. *)
    [z; Z_to_bv 64 FUTEX_WAKE_PRIVATE; z; z; z; z]
  else if Z.eqb n 167 then
    (* prctl dispatches on an OPTION, not an fd: [AT_FDCWD] narrowed to 32
       bits is 0xffffff9c, which is no prctl option, so the arm declines
       before it reaches an answer.  [PR_CAPBSET_READ] is the one option
       [Kernel.Sys.prctl_modeled_options] carries, and a1 is the capability
       number -- 0 is a capability at or below [CAP_LAST_CAP], so the arm
       answers 1 rather than -EINVAL.  Which of the two answers this probe
       reaches does not matter to the check, only that it reaches one. *)
    [Z_to_bv 64 PR_CAPBSET_READ; z; z; z; z; z]
  else if Z.eqb n 220 then
    (* clone declines the default FLAG WORD: [clone_fork_flags_b] admits
       the single word SIGCHLD and nothing else, so [AT_FDCWD] there is
       [unmodeled] rather than an answer. *)
    [Z_to_bv 64 SIGCHLD; z; z; z; z; z]
  else if Z.eqb n 435 then
    (* clone3 reaches [kernel_clone] through a struct in user memory
       rather than through registers, and declines every size but
       [CLONE_ARGS_SIZE] and every struct but the fork-shaped one.  No
       choice of registers alone reaches an answer; the struct lives in
       [probe_mem] at [clone3_probe_uargs]. *)
    [clone3_probe_uargs; Z_to_bv 64 CLONE_ARGS_SIZE; z; z; z; z]
  else if Z.eqb n 260 then
    (* wait4 decides on the ARGUMENT WORDS before it decides anything else:
       [Kernel.Exit.wait4_spec] declines unless [upid] is the 32-bit -1
       [Kernel.Exit.WAIT_ANY32], [options] is exactly [WNOHANG], and
       [rusage] is NULL.  The default probe's a0 is [AT_FDCWD] = -100,
       which is not -1, so the arm would fail closed before reaching the
       -ECHILD that is its only answer.  a1 ([stat_addr]) is left at the
       default: at a negative return [kernel_wait4] never dereferences it,
       so no property of it changes the verdict. *)
    [Z_to_bv 64 WAIT_ANY32; z; Z_to_bv 64 WNOHANG; z; z; z]
  else if Z.eqb n 132 then
    (* sigaltstack reads its [stack_t] out of user memory, and [probe_mem]
       is all-NUL, so the default probe's a0 ([AT_FDCWD] read as an
       address) presents a struct whose [ss_sp] and [ss_size] are both
       zero under a mode of 0 -- the one shape
       [Kernel.Signal.sigaltstack_spec] declines, because there the
       kernel's answer turns on the [sas_ss_flags] word execve did not
       reset.  Unlike clone3, no struct is needed to get past it: BOTH
       pointers NULL is a real call that [do_sigaltstack] answers 0 for,
       having done nothing, so zeros in a0 and a1 reach an answer. *)
    [z; z; z; z; z; z]
  else if Z.eqb n 206 then
    (* sendto gates on the FLAG WORD BEING EXACTLY [MSG_NOSIGNAL] --
       [Net.Socket.send_flags_modeled] is a [Z.eqb], not a mask test -- so
       the default probe's flags 0 declines before the arm reaches any
       answer.  With the flag set the order is the spec's own: the flag
       word, then [import_ubuf]'s range verdict on a zero-length buffer at
       0, then the descriptor -- and [AT_FDCWD] is not an open fd, so the
       arm answers -EBADF.  a4 stays 0 because a non-NULL destination
       address is [unmodeled]. *)
    [AT_FDCWD; z; z; Z_to_bv 64 MSG_NOSIGNAL; z; z]
  else if Z.eqb n 73 then
    (* ppoll's default probe would be an INFINITE WAIT: a0 is unread at
       [nfds = 0], and a NULL [tsp] with a zero count is the one shape
       [poll_select_finish] cannot describe, since [do_poll]'s
       [timed_out] flag is never set and the call never returns.  So the
       probe passes a non-NULL [tsp] instead, and [probe_mem]'s all-zero
       bytes make it a requested {0,0} — [poll_select_set_timeout]'s own
       zero-timeout case, which polls once, returns 0 and writes nothing
       back.  Any address serves; AT_FDCWD is reused so the entry names
       no new constant.  a1 stays 0, so [ufds] is never dereferenced. *)
    [AT_FDCWD; z; AT_FDCWD; z; z; z]
  else if Z.eqb n 130 then
    (* tkill answers only for the caller's own tid, which
       [probe_model_abort] pins; the signal is SIGABRT, the only one any
       arm sends.  The default [AT_FDCWD] in a0 is negative and would
       reach the -EINVAL gate, so the entry is what makes the probe
       measure the DELIVERY rather than the argument check. *)
    [probe_tid; Z_to_bv 64 SIGABRT; z; z; z; z]
  else if Z.eqb n 131 then
    (* tgkill, the same call with the thread-group id in front. *)
    [probe_tid; probe_tid; Z_to_bv 64 SIGABRT; z; z; z]
  else if Z.eqb n 211 then
    (* sendmsg, for the same reason and with the flag in a different
       position: its arguments are (fd, msg, flags), so the flag word is a2
       where sendto's is a3.  Unlike sendto, sendmsg resolves the
       descriptor BEFORE it copies the 56-byte header, so [AT_FDCWD]
       answers -EBADF without [probe_mem] needing to hold a readable
       [struct user_msghdr] at 0. *)
    [AT_FDCWD; z; Z_to_bv 64 MSG_NOSIGNAL; z; z; z]
  else [AT_FDCWD; z; z; z; z; z].

Definition probe_input (n : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (probe_args n) probe_mem probe_mem.

(** Does the dispatcher answer number [n] at all? *)
Definition probe_answers (n : Z) : bool :=
  match syscall_spec_witness (probe_input n) (probe_model_for n) with
  | Ok _ _ _ => true
  | Unmodeled => false
  end.

(** THE CHECK.  Every listed number has an arm that answers.  A number added
    to [modeled_sysnos] without a dispatch arm falls through to the final
    [unmodeled] and turns this into [false = true]. *)
Lemma modeled_sysnos_probes_answer : forallb probe_answers modeled_sysnos = true.
Proof.
  lazymatch eval vm_compute in (forallb probe_answers modeled_sysnos) with
  | true => vm_compute; reflexivity
  | _ => fail "a number in Specs.modeled_sysnos has no answering dispatch arm -- add the arm, or give the number a probe_args entry if the default probe cannot reach its answer"
  end.
Qed.

(** The list holds genuine unsigned 64-bit syscall numbers, so a probe input
    really does carry the number it was built from. *)
Lemma modeled_sysnos_in_range :
  forallb (fun n => (0 <=? n)%Z && (n <? 2 ^ 64)%Z) modeled_sysnos = true.
Proof. vm_compute. reflexivity. Qed.

Theorem modeled_sysnos_dispatched : forall n, In n modeled_sysnos ->
  exists i m o,
    bv_unsigned (in_sysno i) = n /\ syscall_spec i m o /\ o <> Unmodeled.
Proof.
  intros n Hin.
  exists (probe_input n), (probe_model_for n),
         (syscall_spec_witness (probe_input n) (probe_model_for n)).
  split; [|split].
  - (* the probe carries the number it was built from *)
    pose proof (forallb_In _ _ _ modeled_sysnos_in_range Hin) as Hr.
    apply andb_prop in Hr. destruct Hr as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    replace (in_sysno (probe_input n)) with (Z_to_bv 64 n) by reflexivity.
    apply Z_to_bv_small. change (bv_modulus 64) with (2 ^ 64)%Z. lia.
  - apply receptive.
  - pose proof (forallb_In _ _ _ modeled_sysnos_probes_answer Hin) as Ha.
    unfold probe_answers in Ha.
    destruct (syscall_spec_witness (probe_input n) (probe_model_for n));
      [discriminate|].
    discriminate Ha.
Qed.

(** Both directions in one statement: [modeled_sysnos] is EXACTLY the set of
    syscall numbers the dispatcher answers. *)
Theorem modeled_sysnos_exact : forall n,
  In n modeled_sysnos <->
  (exists i m o, bv_unsigned (in_sysno i) = n /\ syscall_spec i m o /\ o <> Unmodeled).
Proof.
  intro n. split; [apply modeled_sysnos_dispatched|].
  intros (i & m & o & Hn & Hspec & Ho).
  destruct o as [x m' evs|]; [|contradiction Ho; reflexivity].
  rewrite <- Hn. exact (syscall_spec_number_modeled _ _ _ _ _ Hspec).
Qed.

(* =========================================================================
   The list itself: no number listed twice

   Exactness above is stated with [In], which cannot see a repeat: a list
   holding 62 twice satisfies both directions exactly as one holding it
   once, and every proof in this file still closes.  Nor does the shared
   table help, because the repeat is IN the table: [modeled_sysnos] is
   [arm_numbers spec_table], so a duplicated arm duplicates the number
   too, and [Sys.Dispatch.lookup_arm] then resolves it first-match-wins —
   the second arm is dead and nothing says so.  [checked_table_arms] does
   not see it either: it compares the two tables to each other, and a
   merge that duplicates an arm in [spec_table] and its mirror in
   [checked_table] keeps them equal.  That pair is exactly what two
   independent additions at the same sorted position produce.  State the
   absence of repeats as its own checked fact rather than leave it to a
   reader counting entries.
   ========================================================================= *)

(** [n] occurs exactly once in [l].  Counted with [Z.eqb] rather than
    with the [count_occ Z.eq_dec] that [NoDup_count_occ'] wants, because
    [Z.eq_dec] returns a [sumbool] carrying equality PROOFS and the
    computation below would normalize those too.
    [count_occ_filter_eqb] bridges the two once, symbolically. *)
Definition listed_once (l : list Z) (n : Z) : bool :=
  Nat.eqb (List.length (List.filter (Z.eqb n) l)) 1.

Lemma count_occ_filter_eqb : forall (l : list Z) (n : Z),
  count_occ Z.eq_dec l n = List.length (List.filter (Z.eqb n) l).
Proof.
  induction l as [|a l IH]; intro n; [reflexivity|].
  cbn [count_occ List.filter]. destruct (Z.eqb n a) eqn:E.
  - apply Z.eqb_eq in E. subst a.
    destruct (Z.eq_dec n n) as [_|Hne]; [|congruence].
    cbn [List.length]. f_equal. apply IH.
  - apply Z.eqb_neq in E.
    destruct (Z.eq_dec a n) as [Heq|_]; [congruence|]. apply IH.
Qed.

(** Stated over an ABSTRACT [l]: proved directly about [modeled_sysnos]
    instead, its [Qed] spends seconds unfolding every entry of the list
    through [count_occ]'s decider, and the cost grows with the list.  With
    [l] a variable the kernel has nothing to unfold, and the instance below
    is free at any length.

    [List.NoDup] is qualified because stdpp, in scope here through
    [BvBase], shadows it with a [NoDup] of its own. *)
Lemma nodup_of_listed_once : forall l : list Z,
  forallb (listed_once l) l = true -> List.NoDup l.
Proof.
  intros l H. apply (proj2 (NoDup_count_occ' Z.eq_dec l)).
  intros n Hin. pose proof (forallb_In _ _ _ H Hin) as Hn.
  unfold listed_once in Hn. apply Nat.eqb_eq in Hn.
  now rewrite count_occ_filter_eqb.
Qed.

(** THE CHECK. *)
Lemma modeled_sysnos_listed_once :
  forallb (listed_once modeled_sysnos) modeled_sysnos = true.
Proof.
  lazymatch eval vm_compute in (forallb (listed_once modeled_sysnos)
                                        modeled_sysnos) with
  | true => vm_compute; reflexivity
  | _ => fail "a number appears more than once in Specs.modeled_sysnos -- a merge or a replay duplicated an entry; delete the repeat"
  end.
Qed.

Theorem modeled_sysnos_nodup : List.NoDup modeled_sysnos.
Proof. exact (nodup_of_listed_once _ modeled_sysnos_listed_once). Qed.
