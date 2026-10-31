import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Drivers.Char.Random — getrandom (278)

Mirrors `theories/LinuxProcessSem/Sys/Drivers/Char/Random.v`, which answers
to Linux `drivers/char/random.c`: it holds what the kernel defines there,
and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Drivers/Char/Random.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq file reads the copy loop at v6.12.1 and v7.1.8, "which bracket
the v6.18.46 this tree cites", and says the tree's own version was not
read; every number below was read at v6.18.46 and is labelled so, and
where the Rocq comment names a constant by an older name the docstring
says which.

Two spellings differ from Rocq without changing a value: Rocq's
`Z.eqb`/`Z.leb` tests are Lean's `==` on `Int` (a `Bool`) and `≤` on
`Int` (decided), with `negb`/`||` as `!`/`||`; and the `choose` guards
state Rocq's `Z.of_nat (length bs)` as the `Int` cast of `bs.length`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess

/-- EINTR only: the pool-not-ready wait, kept admissible for a request
above `getrandom_small_max` bytes and for a zero-byte one (the bound's
docstring says why not at or below it).  The Rocq `getrandom_errnos` comment argues the rest away;
the argument re-read at Linux v6.18.46, walking
`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
(drivers/char/random.c:1385-1412) down:

- -EINVAL is unreachable past the flag gate `getrandom_spec` takes
  first.  Linux answers it for a flag bit outside GRND_NONBLOCK,
  GRND_RANDOM and GRND_INSECURE (:1390-1391) and for GRND_INSECURE
  together with GRND_RANDOM (:1397-1398); every flag word but 0 and
  GRND_NONBLOCK is `unmodeled` here, so no modeled call reaches either.
- -EAGAIN (:1401-1402) and the wait (:1403-1405) sit behind
  `!crng_ready()` (:1400; the macro is at :90), and the urandom pool is
  treated as initialised before user code runs (the flags note on
  `getrandom_spec`; the premise is stated and not checked,
  `bugs/getrandom-answers-rest-on-a-seeded-pool.md`), so the -EAGAIN
  never fires.  What the wait can
  return is what this list keeps: `wait_for_random_bytes`
  (drivers/char/random.c:136-147, v6.18.46) sleeps in
  `wait_event_interruptible_timeout` (:142; include/linux/wait.h:535 at
  v6.18.46, whose own comment at :532-533 names the value), which yields
  -ERESTARTSYS (include/linux/errno.h:14, v6.18.46) when a signal
  arrives; the
  syscall passes it up (:143-144, :1404-1405), and
  `arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396,
  :438-443, v6.18.46) turns it into the -EINTR the program sees when the
  delivered signal's handler lacks SA_RESTART.
- -EFAULT is not injected, because neither of its sources is an
  alternative here.  `import_ubuf` range-tests the buffer
  (lib/iov_iter.c:1437-1438, v6.18.46) with the generic `__access_ok`
  (include/asm-generic/access_ok.h, v6.18.46); the zero-byte arm answers
  that verdict through `State.access_okb`, and the delivering arms do NOT
  ask it — the walk below judges bytes, not the range, so a writable view
  that answers `some` past `State.TASK_SIZE` or across the 2^64 wrap would
  be delivered where Linux answers -EFAULT.  That admission is inherited
  from the bare walk and recorded, with this arm named, in
  `bugs/wrapping-walks-unbounded-segments.md`.  `get_random_bytes_user`'s
  `return ret ? ret : -EFAULT` (drivers/char/random.c:481, v6.18.46), the
  copy that moved nothing, is a destination the walk refuses, so it is
  `unmodeled` rather than an errno. -/
def getrandom_errnos : List Int := [EINTR]

/-- THE SMALL-REQUEST BOUND.  getrandom(2) documents that once the pool
is initialised a request of up to 256 bytes always returns as many bytes
as requested and is not interrupted by a signal.  The kernel at v6.18.46
gives more than that.  In `get_random_bytes_user` (drivers/char/random.c:434-482,
v6.18.46) the copy loop (:460-476) consults `signal_pending` only when
`ret % PAGE_SIZE == 0` (:471-473) — after a whole page has landed, and
only while bytes remain, since the loop breaks first (:467-468) once the
request is satisfied — and a signal there yields the short positive
count (:481), never -EINTR.  So the loop cannot cut any request of at
most a page short, and a request of at most CHACHA_KEY_SIZE bytes (32,
include/crypto/chacha.h:25, v6.18.46) never enters the loop at all: it is copied
straight out of the key material (:455-458).  The Rocq comment reads the
same control flow at v6.12.1 (its "break at line 474, page test at lines
478-480") and at v7.1.8 (:464, :468-470) and says the tree's own
version was not read; it is read here, and the three agree.  The only
-EINTR is `wait_for_random_bytes` (drivers/char/random.c:136-147),
behind the `crng_ready` gate of `SYSCALL_DEFINE3(getrandom, ...)`
(:1400-1406; Rocq quotes v6.12.1's :1403-1408 and v7.1.8's :1395-1400),
entered only while the pool is not yet ready — which the flags note on
`getrandom_spec` already assumes never happens once user code runs.
The bound is 256 rather than a page for two reasons, and the second is
the load-bearing one across the supported set.  getrandom(2)'s documented
guarantee is what programs rely on, so the spec claims of the kernel no
more than the contract does; and through v5.17 the kernel itself cut
there: the copy loop of those kernels, `extract_crng_user`, read at
v4.17 and v5.17 in the file this arm cites throughout, set
`large_request = (nbytes > 256)` and, for a large request only, tested
`signal_pending` before every 64-byte block whenever `need_resched()`
held, answering -ERESTARTSYS when nothing had been copied yet and the
short count otherwise — so on those kernels a 257-byte request can be
interrupted or cut short where v6.18.46 delivers it in full.  256 is the
intersection: a bound at a page would prove a full delivery that a
supported kernel does not give.  A request at or under this bound is
delivered in full: see the small-request arm of `getrandom_spec`. -/
def getrandom_small_max : Int := 256

/-- `getrandom buf buflen flags`: environment bytes, but a nonzero
request never "succeeds" with zero bytes.  Real getrandom blocks until
it can deliver at least one byte, so a 0 return happens only for
`buflen = 0` — `get_random_bytes_user` (drivers/char/random.c:434-482,
v6.18.46) returns 0 for an empty iterator (:440-441) and otherwise
`ret ? ret : -EFAULT` (:481) — consistent with the channel-read arm's
>= 1 lower bound.  A nonzero request of at most `getrandom_small_max`
bytes is delivered IN FULL and is never interrupted (the bound's
docstring says why): the only outcome is `buflen` environment-chosen
bytes and a return of `buflen`.  Above that bound the delivered count
stays environment-chosen in `[1, buflen]` (a signal can interrupt a
large request after some bytes: the `signal_pending` break at :471-473
returns the count so far), beside the -EINTR alternative.  That range is
wider than any one kernel's short counts — a page multiple at v6.18.46,
a 64-byte multiple through v5.17 — and is Rocq's deliberate choice to
claim only what getrandom(2) documents; it costs priority 2, not 1.  The
zero-byte success carries no write entry (the canonical zero-byte
shape, `Uaccess.delivered_writes`); the zero-byte arm keeps its
interrupted alternative and is not narrowed here.

Flags: 0 and GRND_NONBLOCK are accepted and treated identically — on
any modern kernel the urandom pool is initialised long before user code
runs, so the `!crng_ready()` gate (drivers/char/random.c:1400, v6.18.46) that
holds the only branch on GRND_NONBLOCK (:1401-1402; the mask test at
:1390 merely admits the bit) never fires, and GRND_NONBLOCK never changes
the outcome of an urandom read.  That is a premise about the run, not a
fact about the syscall, and nothing checks it:
`bugs/getrandom-answers-rest-on-a-seeded-pool.md` records what rests on
it and what an unseeded pool answers instead.  GRND_RANDOM
(the blocking /dev/random pool), GRND_INSECURE and any unknown flag bit
are unmodeled: `unmodeled`, fail closed.  Linux's own answers there — a
plain read for GRND_RANDOM, which nothing past the mask test at
:1390-1391 and the conflict test at :1397-1398 reads; -EINVAL for a bit
outside the three (:1390-1391) — are declined, not contradicted.  That
includes a set high half, which is a narrowing rather than a
disagreement: `flags` is `unsigned int` at the boundary
(`SYSCALL_DEFINE3(getrandom, ...)`, drivers/char/random.c:1385, v6.18.46), so
Linux discards bits 32-63 where this arm, comparing the whole word,
declines.

`buflen` IS BOUNDED BY `Uaccess.rw_bytes_max`, for the same reason and
by the same mechanism as the hole guards that constant still stands in
front of: the destination check below is
`State.read_bytes_map i.in_wmem buf buflen`, whose cost is a list as
long as the request, paid before a single byte of memory is judged; the
`rw_bytes_max` docstring carries the argument and names this arm as one
of the sites it still guards.  The bound costs nothing real: Linux
clamps a getrandom request at MAX_RW_COUNT in `import_ubuf`
(lib/iov_iter.c:1435-1436, v6.18.46; `INT_MAX & PAGE_MASK`,
include/linux/fs.h:2838 at v6.18.46 — the Rocq comment says INT_MAX,
which is the clamp's rounding base), and no program has a reason to ask for 128 KiB of entropy in one
call.  Decided after the flag check, which Linux also makes first
(:1390 precedes the `import_ubuf` call at :1408).

A ZERO-BYTE REQUEST moves nothing, so `import_ubuf`'s `access_ok` on the
range (lib/iov_iter.c:1437-1438, v6.18.46, before `iov_iter_ubuf` at
:1440) is the
whole of what is left to decide — the same test `read` and `write` face,
spelled out here rather than through `Uaccess.access_ok_zero` because the
interrupted alternative has to survive into the -EFAULT arm.  (Linux can
be interrupted in `wait_for_random_bytes` at :1403 BEFORE it imports the
buffer at :1408, so -EINTR is admissible whatever the range verdict.)
The range test on a zero-byte request is younger than the supported set:
it arrived at v5.19 with `import_single_range`, the iterator import
that `import_ubuf` later replaced, and through v5.18 a zero-length
`getrandom` answered 0 at any address — the `while (nbytes)` loop of
`extract_crng_user` at v4.17 and v5.17, and the `if (!nbytes) return 0;`
that opens `get_random_bytes_user` at v5.18, run no `access_ok`.  So the -EFAULT arm
below refuses a 0 that supported kernels return; that is Rocq's arm, and
`bugs/getrandom-zero-length-refuses-the-pre-v5-19-zero.md` records it.
An unwritable destination on a nonzero request is a program bug and
fails closed: Linux would answer the short count or the -EFAULT of :481,
and the model says `unmodeled`. -/
def getrandom_spec (buf buflen flags : word) : Sys SyscallEffect :=
  if !(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK) then unmodeled
  else if !(modeled_rw_count buflen) then unmodeled   -- see `Uaccess.rw_bytes_max`
  else
  i <- input ;;
  match read_bytes_map i.in_wmem buf buflen with
  | none => unmodeled   -- unwritable destination buffer: program bug, fail closed
  | some _ =>
    let interrupted : Sys SyscallEffect := (e <- errno_from getrandom_errnos ;; err_ret e)
    if !(w_is0 buflen) then
      if bv_unsigned buflen ≤ getrandom_small_max then
        -- THE SMALL REQUEST: full delivery, and nothing else — see
        -- `getrandom_small_max`.  The bytes are still the environment's;
        -- only their number is fixed.
        bs <- choose (fun bs : List byte => (bs.length : Int) = bv_unsigned buflen) ;;
        Monad.pure (mkEffect (len_word bs) [(buf, bs)] [])
      else
        alt interrupted
          (bs <- choose (fun bs : List byte =>
                   1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned buflen) ;;
           Monad.pure (mkEffect (len_word bs) [(buf, bs)] []))
    else
      -- The zero-byte request: the range verdict, beside the interrupt
      -- (the docstring's last paragraph).
      if access_okb buf (bv_unsigned buflen) then alt interrupted (ret_only (Z_to_bv 64 0))
      else alt interrupted (err_ret EFAULT)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
