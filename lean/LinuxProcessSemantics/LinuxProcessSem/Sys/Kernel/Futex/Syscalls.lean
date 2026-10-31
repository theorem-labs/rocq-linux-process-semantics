import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: 61028314611f040514075982c2825fe4c38226c9 -/

/-! # LinuxProcessSem.Sys.Kernel.Futex.Syscalls — futex (98)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Futex/Syscalls.v`, which
answers to Linux `kernel/futex/syscalls.c`: it holds what the kernel
defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Kernel/Futex/Syscalls.lean`.

Every definition keeps the Rocq name and shape, and every kernel line
cited below was read at Linux v6.18.46 (commit 1f99e9ab748f) in the tree
AGENTS.md pins; Rocq cites the same functions at the same version without
line numbers.  THE BASELINE IS THE DAY TIP THE PORT WAS REBASED ONTO, not
the f44244ad6b80 the ticket named: the two Rocq futex files are identical
at both, and what moved between them in this spec's closure is the
urandom and tmp-seeding work, in four files: `State.v` (`FdEntry` gained
`FdUrandom`, `IoState` the urandom stream, `ProcInput` its constructor and
the tmp seeding), `Uapi.v` (`urandom_path`, `URANDOM_RDEV`,
`stat_chrdev_ok` and `stat_urandom_ok`), `Fs.v` (four lemmas on `fs_set`
and the path order, `path_ltb_total` to `fs_set_keys`) and `Monad.v`
(`set_urandom`).  None of it is read by any definition here: `futex_spec`
reads the input's memory and nothing of the model.
SIX CLAIMS ARE NOT ROCQ'S, because opening the kernel
showed Rocq's wrong, and each is corrected where it occurs below with
the lines that settle it: `futex_get_value_locked` is a `static inline`
in kernel/futex/futex.h:332-341 (v6.18.46), not in waitwake.c, which only calls it
(:452, :627); `fail_futex.ignore_private` is initialised false, not true;
the fault-injector site in `SYSCALL_DEFINE6(futex)` is excluded by the
timeout gate, not by a private-bit guard; `FLAGS_STRICT` is set by the
callers of `futex_wake` that want it, `SYSCALL_DEFINE4(futex_wake)` and
io_uring's wake, not by `futex2_to_flags`; `do_futex`'s switch has no
`default:` label, its -ENOSYS follows the switch; and musl's `__wake` is
a `static inline` in src/internal/pthread_impl.h, not in
src/thread/__wait.c.  The Rocq comment owes a `comments:` correction for
all six, for the file of `futex_queue` (corrected in the Cases twin's
header), and for the io_uring route to a waiter that its premise argument
omits (argued in the Cases twin's header too).

TWO SPELLINGS DIFFER FROM ROCQ WITHOUT CHANGING A VALUE.  Rocq's `negb b`
gates are Lean's `!b`, and Rocq's `Z.modulo` is `Int.fmod` rather than
Lean's `%`: `%` on `Int` is EUCLIDEAN and `Z.modulo` is FLOOR division, so
`Int.fmod` is the transcription that needs no argument about the sign of
its arguments, and `tools/check_lean_pins.py`'s DIV-1 asks for exactly that
where the divisor is a named constant.

WHY THIS SPEC IS TWO OP WORDS WIDE.  Every answer below rests on the
waiter set of a private futex key being empty in this model, an argument
that spans three files and is therefore stated where it can be checked:
`Checks/Cases/Kernel/Futex/Syscalls.lean`'s header carries it in full, and
Rocq's `Sys/Kernel/Futex/Syscalls.v` header carries the original.  The
consequence for this file is that an operation whose answer depends on a
waiter EXISTING is unanswerable here and declines. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The address a futex operation names must be naturally aligned.

`get_futex_key` (kernel/futex/core.c:548-770, v6.18.46) is the first thing both
modeled commands reach, and `if (unlikely((address % size) != 0)) return
-EINVAL;` (:569-570) is its first decision.  `size` is
`futex_size(flags)` (:561, v6.18.46), which `futex_to_flags`
(kernel/futex/futex.h:45-56) pins to 4 for every call reaching this
entry point (`Uapi.FUTEX_WORD_SIZE` carries that argument and the
`FLAGS_NUMA` doubling at :562-563 that never fires here).  The test is on
the address the CALLER PASSED, before `address -= key->both.offset`
(:571) and before any page is resolved, so it outranks every other answer
either command has. -/
def futex_aligned_b (uaddr : word) : Bool :=
  Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0

/-- `get_futex_key`'s two refusals, in its own order, and then the
command's own answer.

After the alignment test comes `if (unlikely(!access_ok(uaddr, size)))
return -EFAULT;` (kernel/futex/core.c:573-574, v6.18.46) — the RANGE verdict
`State.access_okb` decides, through the same `__access_ok` every other
spec here goes through.

THE -EFAULT IS A RANGE VERDICT AND NOT A PAGE LOOKUP, and that is the one
shape where the natural implementation of a futex spec — resolve the
buffer against the model's memory and answer -EFAULT when it is not there
— would be wrong.  On the private path `get_futex_key` returns as soon as
it has the mm and the address (:624-630), before any
`get_user_pages_fast`, so an address that is in range with NOTHING MAPPED
AT IT passes this and reaches the command.
`testing/syscall-check/tests/futex_private.c` pins the wake on such an
address answering 0 and rejects a kernel claiming -EFAULT for it;
`testing/syscall-check/tests/unmodeled_futex.c` pins the WAIT on the same
address, which does resolve the page, really is -EFAULT, and declines
here.

THE THIRD `get_futex_key` ERROR IS AN ENVIRONMENT OBLIGATION, AND ROCQ'S
REASON FOR IT IS WRONG AT THIS VERSION.  `should_fail_futex(fshared)`
(:576-577) is the fault injector.  Rocq's comment discharges it by saying
the injector ignores private keys because `fail_futex.ignore_private`
starts true; at v6.18.46 that field is initialised to FALSE
(kernel/futex/core.c:84-87), and `should_fail_futex`
(kernel/futex/core.c:95-101) short-circuits on :97-98 only when an
administrator has turned `ignore-private` on through debugfs (:115-116).
What holds instead is two things.  Without CONFIG_FAIL_FUTEX the whole
site is the stub `return false` (kernel/futex/futex.h:124-127, v6.18.46).  With it,
`fail_futex.attr` is `FAULT_ATTR_INITIALIZER` (:85), whose probability is
zero, so `should_fail` refuses until the injector is ARMED — by the
`fail_futex=` boot parameter (:89-93), the debugfs attribute (:105-118),
or a task's own fail-nth counter (`should_fail_ex`,
lib/fault-inject.c:124-143 (v6.18.46), consults `current->fail_nth` before the
probability test at :146-147; it is written through
/proc/<pid>/task/<tid>/fail-nth, `proc_fail_nth_write`,
fs/proc/base.c:1436-1450 (v6.18.46)) — and an armed fault injector is a deliberate
failure, not a configuration this model is in.  Rocq's comment owes that
correction.  THE OTHER INJECTOR SITE IS EXCLUDED BY THE TIMEOUT GATE AND
NOT BY THE PRIVATE BIT, which is a second correction Rocq owes: in
`SYSCALL_DEFINE6(futex)` (kernel/futex/syscalls.c:196-198, v6.18.46) the expression
`!(op & FUTEX_PRIVATE_FLAG)` is the `fshared` ARGUMENT to
`should_fail_futex`, not a guard, so a private op reaches `should_fail`
there exactly as at :576-577.  What keeps both modeled ops out is the
enclosing `if (utime && futex_cmd_has_timeout(cmd))` (:196): a wake's
command is not in `futex_cmd_has_timeout`'s list (:161-172), and the
modeled wait requires a NULL `utime`. -/
def futex_key_check (uaddr : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if !(futex_aligned_b uaddr) then err_ret EINVAL
  else if !(access_okb uaddr FUTEX_WORD_SIZE) then err_ret EFAULT
  else k

/-- FUTEX_WAKE with FUTEX_PRIVATE_FLAG: the number of waiters woken,
which is 0.

`futex_wake` (kernel/futex/waitwake.c:155-200, v6.18.46) reaches its count through
three gates and this spec answers past all three:

- `if (!bitset) return -EINVAL;` (:162-163, v6.18.46) cannot fire.  `do_futex`
  (kernel/futex/syscalls.c:112-159) overwrites `val3` with
  `FUTEX_BITSET_MATCH_ANY` on the `FUTEX_WAKE` arm (:131-132) before
  falling through to `FUTEX_WAKE_BITSET` (:133-135), so the bitset this
  command is given is never the caller's.  `FUTEX_WAKE_BITSET` is a
  DIFFERENT op word and is declined, which is what keeps that distinction
  from being a coincidence.
- `if ((flags & FLAGS_STRICT) && !nr_wake) return 0;` (:169-170) cannot
  fire either, and would be harmless if it did: `futex_to_flags`
  (kernel/futex/futex.h:45-56, v6.18.46) sets only `FLAGS_SIZE_32`, `FLAGS_SHARED`
  and `FLAGS_CLOCKRT`, never `FLAGS_STRICT`; the one place in
  kernel/futex/ that sets it is `SYSCALL_DEFINE4(futex_wake)`
  (kernel/futex/syscalls.c:366-383, v6.18.46, at :382), syscall 454, which has no
  arm here; the other setter is io_uring's `io_futex_wake`
  (io_uring/futex.c:314-329, v6.18.46, at :323), for a ring no arm here can create
  — and the answer it guards is the same 0.
- the count is 0 either way.  `if (!futex_hb_waiters_pending(hb))
  return ret;` (:175-176) returns the 0 `get_futex_key` left in `ret`
  (:165-167) when the hash bucket is empty; otherwise the loop at
  :180-195 runs over the bucket and `futex_match` (:181) accepts no key,
  by the empty-waiter-set argument this file's header points at, so
  `ret` is never incremented.  `futex_hb_waiters_pending`
  (kernel/futex/futex.h:400-411, v6.18.46) counts the WHOLE bucket, other
  processes' waiters included, and is 1 unconditionally without
  CONFIG_SMP, so the fast path is only a fast path: the argument is the
  loop's, not the count's.

THE COUNT ARGUMENT IS NOT READ, deliberately.  `nr_wake` bounds the
matches of the loop at :180-195, of which there are none, so 0 is the
answer for `INT_MAX` (what musl's `__wake` passes for a broadcast — `if
(cnt<0) cnt = INT_MAX;` in the `static inline` `__wake` of musl's
src/internal/pthread_impl.h, read at musl's git head in September 2026;
Rocq's comment places it in src/thread/__wait.c, which holds `__wait`)
and for 0 and for a negative alike.  A spec that gated on it would decline
calls Linux answers and would be claiming the count mattered. -/
def futex_wake_private_spec (uaddr : word) : Sys SyscallEffect :=
  futex_key_check uaddr (ret_only (Z_to_bv 64 0))

/-- `FUTEX_WORD_SIZE` as a `Nat`, for the copy-in ledger, which counts
bytes in `Nat` where `access_okb` takes an `Int` length.  `futex_word_size_nat_ok`
is what keeps the two spellings from drifting. -/
def FUTEX_WORD_SIZE_nat : Nat := 4

/-- The two spellings of the futex word's width are one value. -/
theorem futex_word_size_nat_ok : (FUTEX_WORD_SIZE_nat : Int) = FUTEX_WORD_SIZE := by decide

/-- FUTEX_WAIT with FUTEX_PRIVATE_FLAG and no timeout: -EAGAIN when the
word does not hold `val`, and a decline when it does.

`futex_wait_setup` (kernel/futex/waitwake.c:591-664, v6.18.46) reads the word after
`get_futex_key` (:617-619) and compares it before it queues anything:
`ret = futex_get_value_locked(&uval, uaddr);` (:627) and then `if (uval
!= val) { futex_q_unlock(hb); return -EWOULDBLOCK; }` (:642-645).
-EWOULDBLOCK IS -EAGAIN (include/uapi/asm-generic/errno.h:22, v6.18.46).  Every
caller between that and the syscall boundary passes the value through
unchanged: `__futex_wait` returns it at :683-684, before `futex_do_wait`
(:687), and `futex_wait` returns it untouched when `to` is NULL
(:718-719).  So this arm is not an approximation of a wait: it is the
branch on which Linux never waits, and the value test is what separates
it.

THE MATCHING CASE DECLINES, and that is the honest answer rather than a
gap grudgingly left.  Once `uval == val` the caller is queued (:660) and
`futex_do_wait` blocks in `schedule()`; the three things that could end
it are a wake, a timer and a signal (`__futex_wait`, :693-703), and the
model has none — this file's header points at the first, this arm
requires a NULL timeout, and the model delivers no signal.  There is no
step that resumes it, so no outcome to accept,
including the "returns 0 spuriously" one, which `__futex_wait` reaches
only after `futex_unqueue` finds the entry gone (:690-691), i.e. after
some task really did wake it.

A NON-NULL TIMEOUT IS DECLINED BEFORE ANY OF THIS, at `futex_spec`.

THE READ IS A COPY-IN.  `futex_get_value_locked`
(kernel/futex/futex.h:332-341, v6.18.46) is a `get_user`-class fetch of the four
bytes at `uaddr`, and it has happened on both the -EAGAIN arm and the
declining one, so `record_copyins` wraps the whole `some uval` arm.  The
`none` arm carries no ledger and answers no errno: a word the model
cannot read is one Linux would fault on (`futex_wait_setup` retries
through `get_user` at :632-634 and returns its error), but the model's
memory is a partial map rather than the kernel's page tables, so an
absent byte is an absent FACT and this fails closed. -/
def futex_wait_private_spec (uaddr val : word) : Sys SyscallEffect :=
  futex_key_check uaddr
    (i <- input ;;
     match read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
     | none => unmodeled   -- the word is not readable: fail closed
     | some uval =>
         record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
           (if bv_eqb (le_bytes_to_word uval) val
            then unmodeled  -- the caller would block, and nothing wakes it
            else err_ret EAGAIN))

/-- The op word decides everything, and it is tested WHOLE.

THE TEST IS ON THE FULL 64-BIT REGISTER, which is stricter than the
kernel's own reading and deliberately so, exactly as Rocq's
`Kernel.Fork.clone_fork_flags_b` is.  `SYSCALL_DEFINE6(futex, u32 __user
*, uaddr, int, op, ...)` (kernel/futex/syscalls.c:188-208, v6.18.46) declares `int
op`, so Linux discards everything above bit 31 and a register of
0x1_00000081 is a private wake to it.  Declining is the fail-closed
direction: the model refuses a call it could have answered rather than
answering one it should not.  Nothing musl issues sets those bits — its
`__wake` and `__wait` build the word from `FUTEX_WAKE`/`FUTEX_WAIT` and
`FUTEX_PRIVATE` alone (`__wake` in src/internal/pthread_impl.h and
`__wait` in src/thread/__wait.c at musl's git head in September 2026;
Rocq's comment cites the second file for both).

WHAT THE TWO WORDS EXCLUDE, and why each exclusion is a decline rather
than an omission:

- THE SHARED SPELLINGS, `FUTEX_WAKE` and `FUTEX_WAIT` with the private
  bit clear.  `futex_to_flags` (kernel/futex/futex.h:49-50, v6.18.46) then sets
  `FLAGS_SHARED` and `get_futex_key` takes the page-resolving path
  (kernel/futex/core.c:633-769, v6.18.46), whose key can be one another process
  holds — so neither the empty waiter set nor the "-EFAULT is only the
  range verdict" claim survives, and both are load-bearing above.
- `FUTEX_CLOCK_REALTIME` on either word.  `do_futex` tests `FLAGS_CLOCKRT`
  BEFORE its switch (kernel/futex/syscalls.c:118-123, v6.18.46) and permits the bit
  on only `FUTEX_WAIT_BITSET`, `FUTEX_WAIT_REQUEUE_PI` and
  `FUTEX_LOCK_PI2`, so a wake carrying it is -ENOSYS however well-formed
  the rest of the call is.  A spec that masked the op with
  `FUTEX_CMD_MASK` and threw the residue away would answer 0 there.
- EVERY OTHER COMMAND.  The bitset forms take the caller's `val3`
  (kernel/futex/syscalls.c:129-130, :133-135, v6.18.46) and so have an -EINVAL this
  spec does not model; `FUTEX_WAKE_OP` WRITES to `uaddr2` through
  `futex_atomic_op_inuser` (kernel/futex/waitwake.c:202-245, v6.18.46) before it
  looks at a waiter; the requeue and PI families need a second key, a
  lock word, or a waiter that exists.  All fall to `unmodeled`, which is
  where `do_futex`'s own `return -ENOSYS;` after its switch (:158; the
  switch has no `default:` label) also lives —
  and the model does not answer -ENOSYS for them, because the number IS
  in the kernel's table (include/uapi/asm-generic/unistd.h:270-271, v6.18.46) and
  the decline is this model's, not Linux's.

THE TIMEOUT ARGUMENT IS ONLY READ FOR A WAIT, which is the kernel's
asymmetry rather than a shortcut.  `SYSCALL_DEFINE6(futex)` fetches it
under `if (utime && futex_cmd_has_timeout(cmd))` (:196), and
`futex_cmd_has_timeout` (:161-172) lists `FUTEX_WAIT`, `FUTEX_LOCK_PI`,
`FUTEX_LOCK_PI2`, `FUTEX_WAIT_BITSET` and `FUTEX_WAIT_REQUEUE_PI` — not
`FUTEX_WAKE`.  So for a wake the third argument is dead, and gating on it
would decline the very calls this arm exists for: musl's `__wake` issues
a three-argument `__syscall`, leaving argument 3 whatever the register
held (GLib's `g_cond_broadcast`, glib/gthread-posix.c at its git head in
September 2026, passes a NULL fourth argument through `g_futex_simple`
and leaves the fifth and sixth to the registers), and
`testing/syscall-check/tests/futex_private.c`'s `wake_junk` case replays
a wake that reached the kernel with junk in a3, a4 and a5.  A non-NULL
`utime` on a
WAIT reaches `get_timespec64` (:199-200) and `futex_init_timeout`
(:175-186), which have an -EFAULT and an -EINVAL of their own AHEAD of
everything above, and then arms a timer whose -ETIMEDOUT this model has
no clock to produce; so it declines.

Arguments 4 and 5 (`uaddr2` and `val3`) are read for neither word:
`do_futex` overwrites `val3` on both arms (:127, :132) and passes
`uaddr2` only to commands outside them. -/
def futex_spec (uaddr op val utime : word) : Sys SyscallEffect :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  then futex_wake_private_spec uaddr
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
  then (if !(w_is0 utime) then unmodeled
        else futex_wait_private_spec uaddr (abi_low32 val))
  else unmodeled

/-- WHEN THE CALL READS USER MEMORY, as a predicate on the arguments
alone.

The copy-in ledger is not decoration: `Run.sstep_syscall` charges lazy
anonymous backing against `vm_limit` for the ranges in it, and an empty
ledger is independently a CLAIM — that the syscall read no user memory.
Rocq keeps this predicate so its OCaml conformance tester can call it
extracted rather than keep a second answer to the same question, and
`Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact` ties it to the
ledger every answered call really carries.  The Lean tree has no
extracted tester, so what the predicate buys here is that tie alone:
`Checks.Cases.Kernel.Futex.Syscalls.futex_copyins_exact` is its twin and
is the only reason this definition is not dead.

IT IS A CONJUNCTION where the spec is a nest of ordered tests, and that
costs nothing because it is only ever read on an ANSWERED call: the two
orderings differ on which of -EINVAL and -EFAULT wins, and neither of
those arms reads anything. -/
def futex_wait_reads_b (uaddr op utime : word) : Bool :=
  bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) && w_is0 utime
    && futex_aligned_b uaddr && access_okb uaddr FUTEX_WORD_SIZE

/-- The two admitted op words are different words, so no call is both a
wake and a wait.  Written out because the ledger argument needs it and
nothing else in this file does. -/
theorem futex_wake_not_wait (op : word) :
    bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) = true →
    bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) = false := by
  intro h
  rw [bv_eqb_eq] at h
  subst h
  decide

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
