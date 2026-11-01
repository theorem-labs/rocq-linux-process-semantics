(** * LinuxProcessSem.Sys.Drivers.Char.Random — getrandom (278)

    This file answers to Linux [drivers/char/random.c]: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** getrandom: only EINTR (the pool-not-ready wait, see the bound's
    comment below), kept admissible for a request above
    [getrandom_small_max] bytes and beside every answer that moves no
    byte.  The urandom pool is treated as always initialized (see the
    flags note at [getrandom_spec]), EFAULT is answered where
    [access_ok] refuses the destination and the fail-closed [unmodeled]
    where it admits a range the memory does not wholly back, and bad
    flags are unmodeled. *)
Definition getrandom_errnos : list Z := [EINTR].

(** THE SMALL-REQUEST BOUND.  getrandom(2) documents that once the
    pool is initialised a request of up to 256 bytes always returns as
    many bytes as requested and is not interrupted by a signal.  The
    kernel gives more than that.  In [get_random_bytes_user]
    (drivers/char/random.c) the copy loop consults [signal_pending]
    only when [ret % PAGE_SIZE == 0] — after a whole page has landed,
    and only while bytes remain, since the loop breaks first once the
    request is satisfied — and a signal there yields the short positive
    count, never -EINTR.  So the loop cannot cut any request of at most
    a page short, and a request of at most CHACHA_KEY_SIZE bytes never
    enters the loop at all.  Read at Linux v6.12.1 (the break at line
    474, the page test at lines 478-480) and at v7.1.8 (lines 464 and
    468-470), which bracket the v6.18.46 this tree cites and agree in
    control flow; the tree's own version was not read.  The only
    -EINTR is [wait_for_random_bytes], behind the [crng_ready] gate of
    [SYSCALL_DEFINE3(getrandom, ...)] (v6.12.1 lines 1403-1408, v7.1.8
    lines 1395-1400), entered only while the pool is not yet ready —
    which the flags note at [getrandom_spec] already assumes never
    happens once user code runs.  The bound is 256 rather than a page
    because getrandom(2)'s documented guarantee is what programs rely
    on: the spec claims of the kernel no more than the contract does.
    A request at or under this bound is delivered in full: see the
    small-request arm of [getrandom_spec]. *)
Definition getrandom_small_max : Z := 256.

(** [getrandom buf buflen flags]: environment bytes, but a nonzero
    request never "succeeds" with zero bytes.  Real getrandom blocks
    until it can deliver at least one byte, so a 0 return happens only
    for [buflen = 0] — consistent with the channel-read branch's >= 1
    lower bound.  A nonzero request of at most [getrandom_small_max]
    bytes is delivered IN FULL and is never interrupted (the bound's
    comment says why): the only outcome is [buflen] environment-chosen
    bytes and a return of [buflen].  Above that bound the delivered
    count stays environment-chosen in [1, buflen] (a signal can
    interrupt a large request after some bytes), beside the -EINTR
    alternative.  The zero-byte success carries no write entry (the
    canonical zero-byte shape, see [Uaccess.delivered_writes]); the
    zero-byte arm keeps its interrupted alternative and is not narrowed
    here.

    Flags: 0 and GRND_NONBLOCK are accepted and treated identically —
    on any modern kernel the urandom pool is initialized long before
    user code runs, so GRND_NONBLOCK never changes the outcome of an
    urandom read.  GRND_RANDOM (the blocking /dev/random pool) and any
    unknown flag bit are unmodeled: [unmodeled], fail closed.  That
    includes a set high half, which is a narrowing rather than a
    disagreement: [flags] is [unsigned int] at the boundary
    ([SYSCALL_DEFINE3(getrandom, ...)], drivers/char/random.c, Linux
    v6.18.46), so Linux discards bits 32-63 where this arm, comparing
    the whole word, declines.

    [buflen] IS BOUNDED BY [Uaccess.rw_bytes_max], for the same reason and by
    the same mechanism as [read]'s and [write]'s [count].  The
    destination check below is [State.copy_bytes_map] over [buflen],
    whose walk is [read_bytes_aux] over [word_to_nat buflen], so this is a
    fifth site that builds the unary numeral described there — and it
    does so before it looks at a single byte of memory, so an
    unbounded [buflen] takes the extracted checker down exactly as an
    unbounded [write] did.  The bound costs nothing real: Linux clamps
    a getrandom request at INT_MAX, and no program has a reason to ask
    for 128 KiB of entropy in one call.  Decided after the flag check,
    which Linux also makes first.  It also keeps the range test below
    exact: [import_ubuf] caps the length at [MAX_RW_COUNT] BEFORE its
    [access_ok], and every modeled [buflen] is already under that cap.

    THE RANGE TEST COMES BEFORE THE WALK, through [State.copy_bytes_map],
    whose note says why that order is the guard.  [SYSCALL_DEFINE3(getrandom,
    ...)] (drivers/char/random.c, Linux v6.18.46) imports the destination
    with [import_ubuf] (lib/iov_iter.c), which asks [access_ok] over the
    whole range before a byte moves, so a [buf] whose range wraps past
    2^64 and is backed at both ends is -EFAULT — the bare walk answered
    [Some] there and the arm delivered bytes and returned a count.  A
    range [access_ok] ADMITS that the memory does not wholly back stays
    [unmodeled]: Linux answers a partial copy or -EFAULT there, and which
    bytes landed first is not something this effect can state.  The
    zero-byte request is the same test at length 0, so it needs no arm
    of its own for the refusal.

    -EINTR SURVIVES INTO THE -EFAULT ANSWER, at every length.  The only
    -EINTR is [wait_for_random_bytes], and [SYSCALL_DEFINE3(getrandom,
    ...)] runs it BEFORE [import_ubuf], so an interrupted wait answers
    whatever the range verdict would have been.  The small-request
    narrowing above is a claim about a request that is DELIVERED; a
    refused range delivers nothing and keeps the alternative, exactly as
    the zero-byte success does.  [Checks.Cases.Drivers.Char.Random]'s
    [getrandom_wrap_] group pins both lengths, beside neighbours at the
    top of what [access_ok] accepts. *)
Definition getrandom_spec (buf buflen flags : word) : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned flags) 0 || Z.eqb (bv_unsigned flags) GRND_NONBLOCK) then unmodeled
  else
  if negb (modeled_rw_count buflen) then unmodeled   (* see [Uaccess.rw_bytes_max] *)
  else
  i <- input ;;
  let interrupted := (e <- errno_from getrandom_errnos ;; err_ret e) in
  match copy_bytes_map (in_wmem i) buf (bv_unsigned buflen) with
  | None =>
      if negb (access_okb buf (bv_unsigned buflen))
      then alt interrupted (err_ret EFAULT)   (* [import_ubuf]'s [access_ok] *)
      else unmodeled   (* admitted, not wholly writable: a partial copy, fail closed *)
  | Some _ =>
      if negb (w_is0 buflen)
      then
        if (bv_unsigned buflen <=? getrandom_small_max)%Z
        then
          (* THE SMALL REQUEST: full delivery, and nothing else — see
             [getrandom_small_max].  The bytes are still the
             environment's; only their number is fixed. *)
          (bs <- choose (fun bs : list byte =>
                           Z.of_nat (length bs) = bv_unsigned buflen) ;;
           pure (mkEffect (len_word bs) [(buf, bs)] []))
        else
          alt interrupted
            (bs <- choose (fun bs : list byte =>
                             (1 <= Z.of_nat (length bs))%Z
                             /\ (Z.of_nat (length bs) <= bv_unsigned buflen)%Z) ;;
             pure (mkEffect (len_word bs) [(buf, bs)] []))
      else
        (* A ZERO-BYTE REQUEST the range test admitted moves nothing:
           0, beside the interrupted alternative. *)
        alt interrupted (ret_only (Z_to_bv 64 0))
  end.
