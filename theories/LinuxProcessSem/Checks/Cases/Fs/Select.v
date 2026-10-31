(** * LinuxProcessSem.Checks.Cases.Fs.Select — worked examples over pselect6 (72) and ppoll (73)

    Mirrors [Sys/Fs/Select.v], which answers to Linux [fs/select.c]:
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

(** [bytes_at] is [Cases/Prelude]'s: the unlinkat examples lay a pathname
    out the same way, so the two share one definition rather than each
    spelling the bound out.

    The left map where it answers, the right one otherwise. *)
Definition mem_join (m1 m2 : word -> option byte) : word -> option byte :=
  fun a => match m1 a with Some b => Some b | None => m2 a end.

(** The three descriptor-set bitmaps are placed CONTIGUOUSLY, so one
    [bytes_at] carrying up to three little-endian words describes all of
    them: [readfds] at [ps_inp], [writefds] eight bytes later, [exceptfds]
    eight after that.  The timespec and the {[sigset_t *], [size_t]} pack
    each get their own 16 bytes. *)
Definition ps_inp  : word := 4096.

Definition ps_outp : word := 4104.

Definition ps_exp  : word := 4112.

Definition ps_tsp  : word := 4128.

Definition ps_sig  : word := 4160.

(** Everything the examples name is writable, except where an example
    passes [fun _ => None] on purpose. *)
Definition ps_wmem : word -> option byte :=
  bytes_at ps_inp (repeat (Z_to_bv 8 0) 128).

(** stdin (channel) at fd 0 and file "f" = "hi" open read-only at fd 3, so
    both descriptor kinds the model has are present: a file, whose
    readiness [vfs_poll] answers with the constant [DEFAULT_POLLMASK], and
    a channel, whose readiness is a schedule the model does not
    represent. *)
Definition pselect_model : Model :=
  mkModel [(0, FdChannel 0); (3, FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

(** The return value is a BIT count, not a descriptor count: [do_select]
    has three independent [retval++], one per result mask, so fd 3 named
    in both [readfds] and [writefds] contributes twice and the call
    returns 2.  Both sets come back with the bit still set, because
    [DEFAULT_POLLMASK] meets [POLLIN_SET] and [POLLOUT_SET].  A kernel
    answering 1 — the number of ready descriptors — is inadmissible. *)
Example pselect_a_file_counts_once_per_set :
  check_syscall
    (mkInput 72 [4; ps_inp; ps_outp; 0; 0; 0]
       (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat); (ps_outp, 8%nat)]
       (mkEffect 2 [(ps_inp, word_le8 8); (ps_outp, word_le8 8)] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 72 [4; ps_inp; ps_outp; 0; 0; 0]
          (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat); (ps_outp, 8%nat)]
          (mkEffect 1 [(ps_inp, word_le8 8); (ps_outp, word_le8 8)] [])) pselect_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** [exceptfds] is requested, so it IS copied back — as a zero word — and
    it adds nothing to the count.  [DEFAULT_POLLMASK] is
    [EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM], which misses [POLLEX_SET]
    entirely, so no file is ever exceptional and the third [retval++]
    never fires for one. *)
Example pselect_exceptfds_comes_back_zeroed :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; ps_exp; 0; 0]
       (bytes_at ps_inp (word_le8 8 ++ word_le8 0 ++ word_le8 8)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat); (ps_exp, 8%nat)]
       (mkEffect 1 [(ps_inp, word_le8 8); (ps_exp, word_le8 0)] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** A bit at or above [n] is INVISIBLE and comes back CLEARED.  The word
    here names fd 3 and fd 9, and fd 9 is not open — but with [n = 4],
    [max_select_fd]'s partial-word mask
    [~(~0UL << (n & (BITS_PER_LONG-1)))] hides bit 9 from the -EBADF test
    and from the scan, and the result word starts zeroed and is assigned
    wholesale, so the write-back drops it. *)
Example pselect_bits_at_or_above_n_are_invisible :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 520)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat)] (mkEffect 1 [(ps_inp, word_le8 8)] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** Raise [n] past that bit and the SAME word is -EBADF, with nothing
    copied back at all.  [max_select_fd] runs its [set & ~*open_fds] test
    over the union of the three requested sets before a single descriptor
    is polled, so one closed descriptor decides the whole call. *)
Example pselect_a_closed_descriptor_below_n_is_ebadf :
  check_syscall
    (mkInput 72 [10; ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 520)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat)] (mkEffect (errno_ret EBADF) [] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** A CHANNEL is declined.  A pipe's readiness is a function of what its
    peer has written so far — wall-clock arrival — and [m_stdin] records
    which bytes will eventually arrive, not which have.  Either answer
    would be a claim the model cannot support, so it fails closed. *)
Example pselect_a_channel_is_declined :
  check_syscall
    (mkInput 72 [1; ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 1)) ps_wmem)
    (mkEffect 1 [(ps_inp, word_le8 1)] []) pselect_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** An [n] above [NR_OPEN_DEFAULT] is declined.  [core_sys_select] clamps
    [n] to [fdt->max_fds], which is a property of the fd table's
    ALLOCATION HISTORY and not of which descriptors are open; the model
    tracks the latter only, so above the [NR_OPEN_DEFAULT] floor it cannot
    say how many bytes are read and written back. *)
Example pselect_n_above_nr_open_default_is_declined :
  check_syscall
    (mkInput 72 [65; ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 8)) ps_wmem)
    (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A real signal mask is declined — the model has no signals — while the
    SAME 16-byte pack with a wrong [sigsetsize] is -EINVAL.  The kernel's
    [sigset_t] is 8 bytes ([_NSIG] = 64), so 8 is the only size
    [set_user_sigmask] accepts; 4 is glibc's business, not the kernel's. *)
Example pselect_a_real_sigmask_is_declined_but_a_bad_size_is_einval :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; 0; ps_sig]
       (mem_join (bytes_at ps_inp (word_le8 8))
                (bytes_at ps_sig (word_le8 1 ++ word_le8 8))) ps_wmem)
    (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 0; 0; 0; ps_sig]
          (mem_join (bytes_at ps_inp (word_le8 8))
                   (bytes_at ps_sig (word_le8 1 ++ word_le8 4))) ps_wmem)
       (with_copyins [(ps_sig, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
     = CheckOk pselect_model [].
Proof. split; [vm_compute; reflexivity | check_eq]. Qed.

(** THE ERRNO-ORDER PAIR.  [set_user_sigmask] runs
    in the syscall entry, before [do_pselect] calls [core_sys_select], so a
    call carrying BOTH an unreadable descriptor set and a bad [sigsetsize]
    is -EINVAL: the set is never copied in and its -EFAULT never happens.
    The second conjunct states the -EFAULT as a rejection: it is
    inadmissible for the kernel the model describes. *)
Example pselect_a_bad_sigsetsize_beats_an_unreadable_set :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; 0; ps_sig]
       (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
    (with_copyins [(ps_sig, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 0; 0; 0; ps_sig]
          (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
       (with_copyins [(ps_sig, 16%nat)] (mkEffect (errno_ret EFAULT) [] [])) pselect_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** {NULL, 999} is NO MASK, not a bad size: [set_user_sigmask] returns 0
    on a NULL mask BEFORE it looks at [sigsetsize], so the second word is
    never read.  That is what makes musl's plain [select] — which always
    passes the constant pair {NULL, 8} rather than a NULL sixth argument —
    an ordinary call rather than a declined one. *)
Example pselect_null_mask_ignores_the_size :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; 0; ps_sig]
       (mem_join (bytes_at ps_inp (word_le8 8))
                (bytes_at ps_sig (word_le8 0 ++ word_le8 999))) ps_wmem)
    (with_copyins [(ps_sig, 16%nat); (ps_inp, 8%nat)]
       (mkEffect 1 [(ps_inp, word_le8 8)] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** A real deadline plus a bit requested below [n] in [readfds] or
    [writefds] is declined; drop the deadline and the same call answers.
    Every return passes through [poll_select_finish], which writes
    [end_time - ktime_get_ts64()] back to [*tsp] — a live clock reading,
    sampled after the work is done.  With [tsp] NULL that write does not
    happen, so the answer is forced. *)
Example pselect_a_deadline_with_a_request_is_declined :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; ps_tsp; 0]
       (mem_join (bytes_at ps_inp (word_le8 8))
                (bytes_at ps_tsp (word_le8 5 ++ word_le8 0))) ps_wmem)
    (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 0; 0; 0; 0]
          (bytes_at ps_inp (word_le8 8)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat)] (mkEffect 1 [(ps_inp, word_le8 8)] [])) pselect_model
     = CheckOk pselect_model [].
Proof. split; [vm_compute; reflexivity | check_eq]. Qed.

(** A real deadline with an EMPTY request runs to expiry and writes 16
    ZERO bytes.  [end_time] is in the past by then, so
    [if (rts.tv_sec < 0) rts.tv_sec = rts.tv_nsec = 0] fires and the
    written value is forced rather than sampled — the hrtimer range slack
    only ever fires LATE, so the remaining time can never be positive.
    This is [select(0, NULL, NULL, NULL, &tv)], the portable sleep — one
    of the two modeled shapes in which this syscall waits; the other is
    just below. *)
Example pselect_an_empty_request_sleeps_and_writes_zeros :
  check_syscall
    (mkInput 72 [0; 0; 0; 0; ps_tsp; 0]
       (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) ps_wmem)
    (with_copyins [(ps_tsp, 16%nat)]
       (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** AND THE EMPTY REQUEST IS NOT THE ONLY SHAPE THAT WAITS.
    [DEFAULT_POLLMASK] misses [POLLEX_SET] entirely, so an [exceptfds] bit
    can never fire the third [retval++] and the set always comes back
    zeroed.  A request naming an open file in [exceptfds] ALONE therefore
    still returns 0, and still runs to expiry — the same forced 16 zero
    bytes over [*tsp], plus the zeroed [exceptfds] word.  Real Linux blocks
    here too: [select] on a regular file for exceptions waits out the
    timeout. *)
Example pselect_an_exceptfds_only_request_still_sleeps :
  check_syscall
    (mkInput 72 [4; 0; 0; ps_exp; ps_tsp; 0]
       (mem_join (bytes_at ps_exp (word_le8 8))
                (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000))) ps_wmem)
    (with_copyins [(ps_tsp, 16%nat); (ps_exp, 8%nat)]
       (mkEffect 0 [(ps_exp, word_le8 0); (ps_tsp, word_le8 0 ++ word_le8 0)] []))
    pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** The same empty request under a NULL timeout is DECLINED, and not
    answered 0.  [schedule_hrtimeout_range_clock] treats a NULL expiry as
    infinite, so [do_select]'s [timed_out] flag is never set and the loop
    cannot exit with a zero count: [pselect6(0, NULL, NULL, NULL, NULL,
    NULL) == 0] is unreachable because the call never returns. *)
Example pselect_a_null_timeout_with_nothing_requested_is_declined :
  check_syscall
    (mkInput 72 [0; 0; 0; 0; 0; 0] (fun _ => None) ps_wmem)
    (mkEffect 0 [] []) pselect_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** Where an errno comes FROM decides whether it survives the timeout
    write-back, and this trio is the whole distinction.

    [n = -1] (the register holds 0xFFFFFFFF; [SYSCALL_DEFINE6] casts it to
    [int]) is -EINVAL out of [core_sys_select].  With no deadline that is
    the answer.  With a real deadline it is DECLINED — the error still
    passes through [poll_select_finish], which writes a live clock reading
    to [*tsp] on its way out.

    The third case separates the two mechanisms rather than the two
    errnos: a wrong [sigsetsize] is also -EINVAL, but it comes out of
    [set_user_sigmask], which returns from [do_pselect] directly and never
    reaches the write-back — so it is answered even with the deadline in
    place, and even though [n] is also invalid. *)
Example pselect_where_an_errno_comes_from_decides_the_writeback :
  check_syscall
    (mkInput 72 [Z_to_bv 64 (2 ^ 32 - 1); ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 8)) ps_wmem)
    (mkEffect (errno_ret EINVAL) [] []) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 72 [Z_to_bv 64 (2 ^ 32 - 1); ps_inp; 0; 0; ps_tsp; 0]
          (mem_join (bytes_at ps_inp (word_le8 8))
                   (bytes_at ps_tsp (word_le8 5 ++ word_le8 0))) ps_wmem)
       (mkEffect (errno_ret EINVAL) [] []) pselect_model
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 72 [Z_to_bv 64 (2 ^ 32 - 1); ps_inp; 0; 0; ps_tsp; ps_sig]
          (mem_join (bytes_at ps_inp (word_le8 8))
                   (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0))
                            (bytes_at ps_sig (word_le8 1 ++ word_le8 4)))) ps_wmem)
       (with_copyins [(ps_sig, 16%nat); (ps_tsp, 16%nat)]
          (mkEffect (errno_ret EINVAL) [] [])) pselect_model
     = CheckOk pselect_model [].
Proof.
  split; [check_eq | split; [vm_compute; reflexivity | check_eq]].
Qed.

(** The WRITE-BACK gate.  The set is readable, so the import succeeds and
    the call has an answer — but the bitmap is not WRITABLE, and
    [set_fd_set] is a [copy_to_user], which lands an unspecified PREFIX
    and then faults.  The model has no representation for "some number of
    bytes landed", so it declines the shape rather than assert a byte
    count it cannot derive.  The band is narrow — an unreadable set
    already answered -EFAULT at import — so what is left is a set in
    .rodata.

    This example is the only statement of the gate. *)
Example pselect_a_set_that_is_readable_but_not_writable_is_declined :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; 0; 0; 0]
       (bytes_at ps_inp (word_le8 8)) (fun _ => None))
    (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** [n = 0] never DEREFERENCES a set pointer.  [FDS_BYTES(0)] is 0, so
    [get_fd_set] and [set_fd_set] both copy zero bytes and a wild pointer
    is never touched — no -EFAULT, and nothing written back.  The timeout
    here is a requested {0,0} rather than NULL, because a NULL timeout
    with nothing requested is the unreachable shape above; {0,0} polls
    once and returns, and [poll_select_finish] writes nothing for it
    either. *)
Example pselect_n_zero_never_dereferences_a_set_pointer :
  check_syscall
    (mkInput 72 [0; 65536; 65536; 65536; ps_tsp; 0]
       (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem)
    (with_copyins [(ps_tsp, 16%nat)] (mkEffect 0 [] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** THE TIMESPEC IS JUDGED RAW.  [do_pselect] hands
    [poll_select_set_timeout] the fields exactly as the program wrote
    them, and [get_timespec64] normalizes nothing, so [timespec64_valid]
    rejects a [tv_sec] below zero and a [tv_nsec] at or above
    [NSEC_PER_SEC] read as [unsigned long] — which every negative
    [tv_nsec] is.  A [tv_nsec] of 1000000000 is therefore -EINVAL and NOT
    one second.

    The carry that would make it one second belongs to [kern_select],
    which serves the [select] and [_newselect] numbers riscv64 does not
    have.  Importing its rule here would make the model answer a deadline
    where the kernel answers -EINVAL.  (musl's [select] wrapper does the same fold in
    USER space, which is why the difference is invisible through it and
    visible through [pselect] and through a raw call.) *)
Example pselect_the_timespec_is_judged_raw :
  (* tv_nsec exactly at NSEC_PER_SEC: out of range, not one second *)
  check_syscall
    (mkInput 72 [0; 0; 0; 0; ps_tsp; 0]
       (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
    (with_copyins [(ps_tsp, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
  = CheckOk pselect_model []
  (* and no carry rescues a negative tv_sec *)
  /\ check_syscall
       (mkInput 72 [0; 0; 0; 0; ps_tsp; 0]
          (bytes_at ps_tsp (word_le8 (Z_to_bv 64 (-1)) ++ word_le8 2000000000))
          ps_wmem)
       (with_copyins [(ps_tsp, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
     = CheckOk pselect_model []
  (* a negative tv_nsec is enormous as an unsigned long *)
  /\ check_syscall
       (mkInput 72 [0; 0; 0; 0; ps_tsp; 0]
          (bytes_at ps_tsp (word_le8 2 ++ word_le8 (Z_to_bv 64 (-1000000000))))
          ps_wmem)
       (with_copyins [(ps_tsp, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
     = CheckOk pselect_model []
  (* and the deadline a normalizing model would have answered instead *)
  /\ check_syscall
       (mkInput 72 [0; 0; 0; 0; ps_tsp; 0]
          (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
       (with_copyins [(ps_tsp, 16%nat)]
          (mkEffect 0 [(ps_tsp, repeat (Z_to_bv 8 0) 16)] [])) pselect_model
     = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** OVERLAPPING SETS ARE MODELED, and naming both writes is the whole
    point.  [set_fd_set] runs three times in [inp], [outp], [exp] order
    and the last write wins; [Run.apply_effect] applies [eff_writes] in
    that same order, so a ledger that names the two words separately is
    the faithful description of the call and the final memory it implies
    is right.

    The case below is [readfds] aliased with [exceptfds], the pair whose
    two words DIFFER: the file is readable but never exceptional, so the
    address takes the imported request first and zero second.  The model
    names both, in order.

    A MEMORY SNAPSHOT CANNOT SHOW THIS, which is why it is asserted here.
    A snapshot of memory taken after the call can only ever report, for
    two entries at one address, the bytes that survived — twice.  The
    second conjunct below is that snapshot written as a rejection: the
    snapshot-shaped ledger, which reports the surviving word for BOTH
    entries, is not a trace this model admits.

    Only the WRITING path is affected: an error return names no write, so
    the same aliased pointers answer an errno either way. *)
Example pselect_aliased_sets_are_modeled :
  check_syscall
    (mkInput 72 [4; ps_inp; 0; ps_inp; 0; 0]
       (bytes_at ps_inp (word_le8 8)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat); (ps_inp, 8%nat)]
       (mkEffect 1 [(ps_inp, word_le8 8); (ps_inp, word_le8 0)] [])) pselect_model
  = CheckOk pselect_model []
  (* the ledger a memory snapshot would produce: the surviving word
     reported for both entries, losing the first write entirely *)
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 0; ps_inp; 0; 0]
          (bytes_at ps_inp (word_le8 8)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat); (ps_inp, 8%nat)]
          (mkEffect 1 [(ps_inp, word_le8 0); (ps_inp, word_le8 0)] [])) pselect_model
     = CheckReject
  (* and aliasing [readfds] with [writefds], the pair whose two words
     AGREE, since both are the imported request *)
  /\ check_syscall
       (mkInput 72 [4; ps_inp; ps_inp; 0; 0; 0]
          (bytes_at ps_inp (word_le8 8)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat); (ps_inp, 8%nat)]
          (mkEffect 2 [(ps_inp, word_le8 8); (ps_inp, word_le8 8)] [])) pselect_model
     = CheckOk pselect_model []
  (* raise n past a closed descriptor and the errno still comes out *)
  /\ check_syscall
       (mkInput 72 [10; ps_inp; 0; ps_inp; 0; 0]
          (bytes_at ps_inp (word_le8 520)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat); (ps_inp, 8%nat)]
          (mkEffect (errno_ret EBADF) [] [])) pselect_model
     = CheckOk pselect_model [].
Proof.
  repeat split; first [ check_eq | vm_compute; reflexivity ].
Qed.

(** THE COPY-IN LEDGER FOLLOWS THE KERNEL'S WALK.  [core_sys_select]
    copies [inp], [outp] and [exp] in that order and returns -EFAULT at
    the first that faults, so a readable [readfds] and an unreadable
    [writefds] answer -EFAULT having read exactly the first word: the
    ledger [Select.pselect6_reads] gives is that one range.  An empty
    ledger claims the call read nothing and leaves a lazy page uncharged
    that Linux faults in; a ledger naming the faulting word as well claims
    a read that failed, against the convention that a failed copy
    records nothing.  Both are rejected.  And the 16-byte pack at [sig]
    is read before any set, the timespec at [tsp] between them. *)
Example pselect_efault_records_the_sets_read_before_it :
  check_syscall
    (mkInput 72 [4; ps_inp; 65536; 0; 0; 0]
       (bytes_at ps_inp (word_le8 8)) ps_wmem)
    (with_copyins [(ps_inp, 8%nat)] (mkEffect (errno_ret EFAULT) [] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 65536; 0; 0; 0]
          (bytes_at ps_inp (word_le8 8)) ps_wmem)
       (mkEffect (errno_ret EFAULT) [] []) pselect_model
     = CheckReject
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 65536; 0; 0; 0]
          (bytes_at ps_inp (word_le8 8)) ps_wmem)
       (with_copyins [(ps_inp, 8%nat); (65536, 8%nat)]
          (mkEffect (errno_ret EFAULT) [] [])) pselect_model
     = CheckReject
  /\ check_syscall
       (mkInput 72 [4; ps_inp; 0; 0; ps_tsp; ps_sig]
          (mem_join (bytes_at ps_inp (word_le8 8))
                   (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 0))
                            (bytes_at ps_sig (word_le8 0 ++ word_le8 8)))) ps_wmem)
       (with_copyins [(ps_sig, 16%nat); (ps_tsp, 16%nat); (ps_inp, 8%nat)]
          (mkEffect 1 [(ps_inp, word_le8 8)] [])) pselect_model
     = CheckOk pselect_model [].
Proof. repeat split; first [ check_eq | vm_compute; reflexivity ]. Qed.

(* =========================================================================
   ppoll (73)
   ========================================================================= *)

(** The ppoll fixtures sit well clear of the pselect6 ones so a bad
    address in one cannot be answered by the other's bytes.  [pp_ufds]
    has room for the 30-entry band ([Select.ppoll_nfds_max] * 8 = 240
    bytes) and the timeout and mask follow it. *)
Definition pp_ufds : word := 8192.

Definition pp_tsp : word := 8448.

Definition pp_sig : word := 8480.

(** Everything the ppoll examples name is writable, except where one
    passes [fun _ => None] on purpose. *)
Definition pp_wmem : word -> option byte :=
  bytes_at pp_ufds (repeat (Z_to_bv 8 0) 512).

(** One [struct pollfd]: [int fd], [short events], [short revents],
    little-endian, 8 bytes.  The [revents] the caller supplies is
    always 0 here — the kernel overwrites it whatever it held, and the
    write-back examples below are what say so. *)
Definition pp_entry (fd events : Z) : list byte :=
  word_le4 (Z_to_bv 64 fd) ++ word_le2 (Z_to_bv 64 events)
  ++ word_le2 (Z_to_bv 64 0).

Definition pp_entries (k : nat) (e : list byte) : list byte :=
  concat (repeat e k).

(** A 16-byte [struct __kernel_timespec]. *)
Definition pp_ts (sec nsec : Z) : list byte :=
  word_le8 (Z_to_bv 64 sec) ++ word_le8 (Z_to_bv 64 nsec).

(** POLL IS A DESCRIPTOR COUNT WHERE SELECT IS A BIT COUNT.  [do_poll]
    increments [count] once per entry whose [do_pollfd] answered a
    non-zero mask, so an entry asking for POLLIN|POLLOUT on a file that
    is ready for both contributes 1 — where the same descriptor named in
    both [readfds] and [writefds] contributes 2 to pselect6's return
    ([pselect_a_file_counts_once_per_set] above).  Importing select's
    rule here would answer 2, and the second conjunct states that as a
    rejection.

    The [revents] written back is [DEFAULT_POLLMASK & events] = 5, two
    bytes at offset 6 of the entry, and the [fd] and [events] fields in
    front of it are NOT rewritten — which is why the ledger names a
    2-byte write and not an 8-byte one.  The copy-in ledger names the
    whole 8-byte entry [do_sys_poll] copied, and the third conjunct is
    the same answer claiming no read at all, which is rejected. *)
Example ppoll_counts_descriptors_not_bits :
  check_syscall
    (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
       (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
    (with_copyins [(pp_ufds, 8%nat)] (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []))
    pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
          (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
       (with_copyins [(pp_ufds, 8%nat)] (mkEffect 2 [(pp_ufds + 6, word_le2 5)] []))
       pselect_model
     = CheckReject
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
          (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
       (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model
     = CheckReject.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(** THE ACCESS MODE IS NOT ONE OF [vfs_poll]'S INPUTS, and until this
    example nothing in the tree said so for [ppoll].

    [ppoll_revents_of] enumerates the descriptor kinds, which makes a
    MISSING arm a build error — the same shape, and the same reason, as
    [Locks.path_openers].  What it does not make is a WRONG arm visible:
    [check_ppoll] calls [Select.ppoll_outcome] directly rather than
    mirroring it, so the spec arm IS the checker arm and no agreement
    proof can disagree with it.  Masking the read-write arm's answer to 0
    therefore compiles green across every file that can see [Select.v],
    and [ppoll] on an O_RDWR descriptor then reports [revents] 0 and does
    not count the entry — a wrong modeled answer, not a decline.

    The kernel fact: [do_pollfd] (fs/select.c) hands the descriptor to
    [vfs_poll], which for a regular file has no [->poll] to call and
    yields [DEFAULT_POLLMASK] (include/linux/poll.h) whatever mode the
    file was opened in.  Linux v6.18.46.

    So this is [ppoll_counts_descriptors_not_bits] above on a model whose
    fd 3 is a read-write description instead of a read-only one, with two
    differences that are both deliberate.

    ITS OWN MODEL RATHER THAN A FOURTH ENTRY IN [pselect_model]: that
    fixture is shared by every example in this file, several of which
    name an [n] or an [nfds] covering every open descriptor, so a new
    entry would move answers that have nothing to do with the access
    mode.

    AND A REQUESTED {0,0} TIMEOUT RATHER THAN A NULL ONE, which is what
    makes the rejection bite on the thing it is about.  Under a NULL
    timeout a zero count is [unmodeled] — the call would never return,
    and [pselect_finish] says so — so a zero-mask arm would turn this
    example red by DECLINING, which is a gap rather than the wrong
    answer.  With {0,0} the zero count is representable, so such an arm
    answers 0 with [revents] 0, the second conjunct's claimed effect is
    ACCEPTED, and the example fails on the wrong answer itself.  The
    first conjunct fails alongside it, on the answer that is no longer
    given. *)
Definition pselect_model_rdwr : Model :=
  mkModel [(0, FdChannel 0); (3, FdFileRW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

Example ppoll_a_read_write_file_polls_as_any_other :
  check_syscall
    (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
       (mem_join (bytes_at pp_ufds (pp_entry 3 5))
                 (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
       (mkEffect 1 [(pp_ufds + 6, word_le2 5)] [])) pselect_model_rdwr
  = CheckOk pselect_model_rdwr []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entry 3 5))
                    (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
       (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
          (mkEffect 0 [(pp_ufds + 6, word_le2 0)] [])) pselect_model_rdwr
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** AN UNOPENED DESCRIPTOR IS AN ANSWER, NOT AN ERROR, and this is the
    one place ppoll and pselect6 disagree about the same descriptor.
    [max_select_fd] makes a closed fd -EBADF for the whole call
    ([pselect_a_closed_descriptor_below_n_is_ebadf] above); [do_pollfd]
    sets [mask = EPOLLNVAL] before [fdget] and keeps it when
    [fd_empty] holds, so the entry reports POLLNVAL (0x20) and COUNTS.
    The second conjunct states select's answer as the rejection it is. *)
Example ppoll_an_unopened_descriptor_is_pollnval_not_ebadf :
  check_syscall
    (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
       (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem)
    (with_copyins [(pp_ufds, 8%nat)] (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []))
    pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
          (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem)
       (with_copyins [(pp_ufds, 8%nat)] (mkEffect (errno_ret EBADF) [] [])) pselect_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A NEGATIVE [fd] IS NEITHER.  [do_pollfd] returns 0 before it calls
    [fdget], so the entry is not looked up at all: its [revents] is
    written as 0 and it does not count.  POLLNVAL — which is what a
    reader who took "not a valid descriptor" as the condition would
    write — is the rejection.

    The timeout is a requested {0,0} rather than NULL because a NULL
    one with a zero count never returns; see below. *)
Example ppoll_a_negative_fd_is_skipped_not_invalid :
  check_syscall
    (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
       (mem_join (bytes_at pp_ufds (pp_entry (-1) 1))
                 (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
       (mkEffect 0 [(pp_ufds + 6, word_le2 0)] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entry (-1) 1))
                    (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
       (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
          (mkEffect 1 [(pp_ufds + 6, word_le2 32)] [])) pselect_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** [events] IS A FILTER, and a bit outside [DEFAULT_POLLMASK] selects
    nothing.  [do_pollfd] answers [vfs_poll(...) & (demangle_poll(events)
    | EPOLLERR | EPOLLHUP)], and neither EPOLLERR nor EPOLLHUP is in
    [DEFAULT_POLLMASK], so a POLLPRI-only request on a regular file
    reports an empty [revents] and does not count — the file is never
    exceptional, exactly as [DEFAULT_POLLMASK] missing [POLLEX_SET]
    makes pselect6's [exceptfds] come back zeroed.  The second conjunct
    is the answer a model that echoed [events] back would give. *)
Example ppoll_events_filters_the_default_pollmask :
  check_syscall
    (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
       (mem_join (bytes_at pp_ufds (pp_entry 3 2))
                 (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
       (mkEffect 0 [(pp_ufds + 6, word_le2 0)] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entry 3 2))
                    (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
       (with_copyins [(pp_tsp, 16%nat); (pp_ufds, 8%nat)]
          (mkEffect 1 [(pp_ufds + 6, word_le2 2)] [])) pselect_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A CHANNEL IS DECLINED, for the reason [bits_all_pollable] declines
    it: a pipe's readiness is a function of what its peer has written so
    far, and [m_stdin] records which bytes will eventually arrive rather
    than which have.  Not even an [events] of 0 makes the answer
    derivable, since EPOLLERR and EPOLLHUP are in the filter
    unconditionally — which is what the second conjunct pins. *)
Example ppoll_a_channel_is_declined :
  check_syscall
    (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
       (mem_join (bytes_at pp_ufds (pp_entry 0 1))
                 (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
    (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entry 0 0))
                    (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
       (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
     = CheckUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.

(** THE STACK BOUND.  [do_sys_poll] keeps up to [N_STACK_PPS] = 30
    entries in [stack_pps] and chains [kmalloc]ed blocks after that, so
    at 31 entries the call can answer -ENOMEM and the model declines.
    Every entry here names [fd = -1], so nothing but the count can be
    the reason: at 30 the same array is inside the band, which the
    control states as a [<>] rather than by spelling out thirty
    2-byte writes. *)
Example ppoll_above_the_stack_bound_is_declined :
  check_syscall
    (mkInput 73 [pp_ufds; 31; pp_tsp; 0; 0; 0]
       (mem_join (bytes_at pp_ufds (pp_entries 31 (pp_entry (-1) 0)))
                 (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
    (mkEffect 0 [] []) pselect_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 73 [pp_ufds; 30; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entries 30 (pp_entry (-1) 0)))
                    (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
       (mkEffect 0 [] []) pselect_model
     <> CheckUnmodeled.
Proof. split; [vm_compute; reflexivity | vm_compute; discriminate]. Qed.

(** [nfds] ABOVE THE SOFT RLIMIT_NOFILE IS -EINVAL, AND IT IS DECIDED
    FIRST.  [do_sys_poll] tests [nfds > rlimit(RLIMIT_NOFILE)] before it
    copies a byte, so the answer here is -EINVAL even though [ufds] is
    unreadable: the -EFAULT that pointer would raise never happens.  The
    limit is answered from state ([State.m_nofile]), the same field
    [Fs.File.dup3_spec] tests. *)
Example ppoll_nfds_above_the_soft_limit_is_einval_before_the_copy :
  check_syscall
    (mkInput 73 [pp_ufds; 5; 0; 0; 0; 0] (fun _ => None) pp_wmem)
    (mkEffect (errno_ret EINVAL) [] []) (with_nofile 4 pselect_model)
  = CheckOk (with_nofile 4 pselect_model) []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 5; 0; 0; 0; 0] (fun _ => None) pp_wmem)
       (mkEffect (errno_ret EFAULT) [] []) (with_nofile 4 pselect_model)
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** AN UNREADABLE ARRAY IS -EFAULT once the limit test is past.  One
    [copy_from_user] takes the whole array, so a single unreadable byte
    fails all of it and nothing is written back. *)
Example ppoll_an_unreadable_array_is_efault :
  check_syscall
    (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0] (fun _ => None) pp_wmem)
    (mkEffect (errno_ret EFAULT) [] []) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** [nfds = 0] COPIES NOTHING FROM [ufds], and this says only that.
    [copy_from_user] of zero bytes reads nothing and the write-back
    loop writes none, so a pointer no byte of which is mapped is still
    a 0 return.  With a requested {0,0} the call polls once and returns
    0, and [poll_select_finish] writes nothing for it either.  What the
    pointer may NOT be is out of the user address space; the example
    below is that half. *)
Example ppoll_nfds_zero_reads_no_entry_from_ufds :
  check_syscall
    (mkInput 73 [65536; 0; pp_tsp; 0; 0; 0]
       (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat)] (mkEffect 0 [] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.

(** [nfds = 0] STILL RANGE-CHECKS [ufds], and the answer is -EFAULT.
    [do_sys_poll] guards its write-back loop with
    [if (!user_write_access_begin(ufds, nfds * sizeof(*ufds))) goto
    out_fds] (fs/select.c) and runs that call for every [nfds],
    including 0; [out_fds] returns the [err = -EFAULT] the function
    opened with.  riscv64's [user_write_access_begin] is [access_ok]
    on the untagged address (arch/riscv/include/asm/uaccess.h), and
    the generic [__access_ok] ends
    [return (size <= limit) && (addr <= (limit - size));]
    (include/asm-generic/access_ok.h): at [size = 0] the first
    conjunct is free and the second still refuses an [addr] above
    [TASK_SIZE_MAX].  [State.TASK_SIZE] is that limit, so
    [State.TASK_SIZE + 1] is outside it by one byte.

    The second conjunct is the 0 this call used to answer, now
    rejected.  The third is the ORDER: [user_write_access_begin] runs
    AFTER [do_poll], so with a NULL [tsp] and no entry the call never
    returns to reach it and the model declines rather than answering
    -EFAULT — the same shape, and the same reason, as
    [ppoll_a_null_timeout_with_nothing_ready_is_declined] below. *)
Example ppoll_nfds_zero_still_range_checks_ufds :
  check_syscall
    (mkInput 73 [Z_to_bv 64 (TASK_SIZE + 1); 0; pp_tsp; 0; 0; 0]
       (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
    pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [Z_to_bv 64 (TASK_SIZE + 1); 0; pp_tsp; 0; 0; 0]
          (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
       (with_copyins [(pp_tsp, 16%nat)] (mkEffect 0 [] [])) pselect_model
     = CheckReject
  /\ check_syscall
       (mkInput 73 [Z_to_bv 64 (TASK_SIZE + 1); 0; 0; 0; 0; 0]
          (fun _ => None) pp_wmem)
       (mkEffect (errno_ret EFAULT) [] []) pselect_model
     = CheckUnmodeled.
Proof.
  split; [check_eq | split; vm_compute; reflexivity].
Qed.

(** THE TIMEOUT WRITE-BACK, and it is [poll_select_finish]'s — the same
    function pselect6 reaches, with the same [PT_TIMESPEC] argument.  An
    empty request under a real deadline runs to expiry, returns 0 and
    writes 16 ZERO bytes over [*tsp], because [end_time] is in the past
    by then and the [rts.tv_sec < 0] clamp fires.  Put something ready
    in the array instead and the return comes back EARLY, so the
    remaining time is a live clock reading: UNMODELED, not an
    invented 0. *)
Example ppoll_a_deadline_expires_to_zeros_but_an_early_return_is_declined :
  check_syscall
    (mkInput 73 [0; 0; pp_tsp; 0; 0; 0]
       (bytes_at pp_tsp (pp_ts 0 1000000)) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat)]
       (mkEffect 0 [(pp_tsp, repeat (Z_to_bv 8 0) 16)] [])) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; 0; 0; 0]
          (mem_join (bytes_at pp_ufds (pp_entry 3 1))
                    (bytes_at pp_tsp (pp_ts 0 1000000))) pp_wmem)
       (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
     = CheckUnmodeled.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A NULL TIMEOUT WITH NOTHING READY IS DECLINED, and not answered 0.
    [schedule_hrtimeout_range_clock] treats a NULL expiry as infinite,
    so [do_poll]'s [timed_out] flag is never set and the loop cannot
    exit with a zero count: the call never returns.  Give it a ready
    descriptor and the same NULL timeout is an ordinary answer, which is
    the second conjunct — and is the shape libraries actually issue. *)
Example ppoll_a_null_timeout_with_nothing_ready_is_declined :
  check_syscall
    (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
       (bytes_at pp_ufds (pp_entry (-1) 0)) pp_wmem)
    (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
          (bytes_at pp_ufds (pp_entry 3 1)) pp_wmem)
       (with_copyins [(pp_ufds, 8%nat)] (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []))
       pselect_model
     = CheckOk pselect_model [].
Proof. split; [vm_compute; reflexivity | check_eq]. Qed.

(** THE WRITE-BACK GATE.  The array is readable, so the import succeeds
    and the call has an answer — but the entry is not WRITABLE, and the
    [revents] write-back is a [user_write_access_begin] plus a run of
    [unsafe_put_user]s, which lands an unspecified PREFIX and then
    faults.  Linux answers -EFAULT for the whole call after some entries
    may already have been updated; the model has no representation for
    that, so it declines rather than assert which entries landed. *)
Example ppoll_an_unwritable_array_is_declined :
  check_syscall
    (mkInput 73 [pp_ufds; 1; 0; 0; 0; 0]
       (bytes_at pp_ufds (pp_entry 3 1)) (fun _ => None))
    (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE ERRNO ORDER, AND IT IS NOT pselect6's.  pselect6 is out of
    argument registers, so it reads a {[sigset_t *], [size_t]} pack
    through [get_sigset_argpack] in the syscall entry — BEFORE the
    timeout — and an unreadable pack is the first -EFAULT it can raise
    ([pselect_a_bad_sigsetsize_beats_an_unreadable_set] above).  ppoll
    has five arguments and needs no pack: [get_timespec64] runs first
    and [set_user_sigmask] second.

    So an unreadable timeout beats a wrong [sigsetsize] here, where the
    transplanted pselect6 order would answer -EINVAL.  The second
    conjunct states that -EINVAL as the rejection it is.  The third is
    the other side of the same order: with the timeout fine, the wrong
    [sigsetsize] is answered, and it beats the -EFAULT the unreadable
    array would otherwise raise — [set_user_sigmask] runs before
    [do_sys_poll] copies anything. *)
Example ppoll_the_timeout_is_judged_before_the_signal_mask :
  check_syscall
    (mkInput 73 [0; 0; pp_tsp; pp_sig; 4; 0]
       (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
    (mkEffect (errno_ret EFAULT) [] []) pselect_model
  = CheckOk pselect_model []
  /\ check_syscall
       (mkInput 73 [0; 0; pp_tsp; pp_sig; 4; 0]
          (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
       (mkEffect (errno_ret EINVAL) [] []) pselect_model
     = CheckReject
  /\ check_syscall
       (mkInput 73 [pp_ufds; 1; pp_tsp; pp_sig; 4; 0]
          (mem_join (bytes_at pp_tsp (pp_ts 0 0))
                    (bytes_at pp_sig (word_le8 0 ++ word_le8 0))) pp_wmem)
       (with_copyins [(pp_tsp, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) pselect_model
     = CheckOk pselect_model [].
Proof.
  repeat split; first [ check_eq | vm_compute; reflexivity ].
Qed.

(** AN UNREADABLE MASK IS -EFAULT, and it is [set_user_sigmask]'s own
    [copy_from_user] rather than anything the syscall entry does — so it
    is raised only after the size test passes, which is the order the
    example above's third conjunct depends on.  A mask that IS readable
    would be INSTALLED, and that is declined; the pair is pinned in
    [Checks.Cases.Kernel.Signal] beside pselect6's and
    epoll_pwait's. *)
Example ppoll_an_unreadable_mask_is_efault :
  check_syscall
    (mkInput 73 [0; 0; pp_tsp; pp_sig; 8; 0]
       (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
    (with_copyins [(pp_tsp, 16%nat)] (mkEffect (errno_ret EFAULT) [] [])) pselect_model
  = CheckOk pselect_model [].
Proof. check_eq. Qed.
