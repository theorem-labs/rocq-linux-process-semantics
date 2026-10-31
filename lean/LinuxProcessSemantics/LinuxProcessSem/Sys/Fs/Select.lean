import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Select — pselect6 (72) and ppoll (73)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Select.v`, which answers to Linux
`fs/select.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Select.lean`.

Every definition keeps the Rocq name and shape, and each docstring carries
the kernel citation its decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f).  Every line cited here was
read in a checkout at that commit rather than copied across: the Rocq file
cites `fs/select.c` by FUNCTION and gives no line numbers for its ppoll
half at all, saying so in its own header ("READ FROM NO CHECKOUT"), so the
numbers below are this file's and not a transcription.  The argument behind
each decision, in full, stays on the Rocq definition of the same name.

THREE SPELLINGS DIFFER FROM ROCQ WITHOUT CHANGING A VALUE, and each is
forced by what Lean's core library has:

- `popcount_aux`, `bits_all_open` and `bits_all_pollable` take the 64-bit
  WORD whose bits they walk, where Rocq takes `bv_unsigned` of it as a `Z`
  and tests bits with `Z.testbit`.  Lean 4.34 has `Nat.testBit` and no
  `Int.testBit`, and routing a `Z` back through `Int.toNat` would read a
  negative argument as zero where `Z.testbit` reads it in two's complement
  — a difference no caller can reach (every caller passes a `bv_unsigned`
  or an `or` of them, all non-negative) but one nothing in the type would
  stop a later caller reaching.  `BitVec.getLsbD` is the exact reading and
  needs no such premise.  `pselect_core` builds the union of the three
  requested sets with `bv_or` for the same reason.
- `fd_set_scanned` masks with `2 ^ n.toNat - 1` where Rocq writes
  `Z.ones n`.  The two agree on every `n ≥ 0`, and only those reach it:
  `pselect_core` has answered -EINVAL for `n < 0` and declined `n` above 64
  before the mask is built.  Below zero they differ — `Z.ones n` is
  `Z.pred (Z.shiftl 1 n)`, which is -1 there, where `Int.toNat`'s clamp
  gives 0 — and nothing can reach that.
- `ppoll_revents_of` masks `events` against `default_pollmask` in `Nat`
  (`&&&`), where Rocq uses `Z.land`.  Both operands are non-negative by
  construction — a literal and a `bv_unsigned` — so `Int.toNat` is the
  identity on them and the two agree.

NO DEFINITION BELOW IS A BARE `match` WITH AN OVERLAPPING ARM, where
Rocq's have wildcards (`| _, _ => PsSigFault`, `| _ => pselect_err e`,
ppoll's `| tmo =>`).  For a definition whose body is the `match` itself,
Lean states one equation lemma per arm, and the lemma of an arm that
overlaps an earlier one carries a side condition (`tmo ≠ PsToDeadline →
…`); the ground evaluator the pins run under (`simp +ground`,
`Checks/Cases/Tactic.lean`) applies equation lemmas without discharging
such a condition, so a call reaching that arm never normalizes.  Spelling
the arm as the constructors it covers gives unconditional equations and
changes no value: each alternation below lists exactly the constructors
Rocq's wildcard stands for.  `pselect6_outcome`'s paired match keeps
Rocq's wildcards because its body is a `let`, which gives it a single
unfolding equation, and the match inside is then reduced by its matcher,
where overlap is harmless; `ppoll_outcome` is written the same way.

ONE DECLINE BEYOND ROCQ'S, and it is named here because
docs/syscalls/ppoll.md is the Rocq contract and stays as it is: `ppoll_core`
declines `nfds = 0` with a `ufds` that fails `access_okb`, where Rocq
answers 0 and Linux answers -EFAULT (the docstring of `ppoll_core` has the
kernel lines; bugs/ppoll-nfds-zero-answers-a-kernel-space-ufds.md records
the Rocq defect).  Every other `unmodeled` arm is Rocq's.

THE ENVIRONMENT OBLIGATION `bits_all_pollable` RESTS ON IS NOT DISCHARGED
HERE EITHER.  `vfs_poll` (include/linux/poll.h:78-83, Linux v6.18.46) hands back
`DEFAULT_POLLMASK` only for a file with no `->poll`, and procfs, sysctl,
kernfs, debugfs, tracefs, securityfs, POSIX message queues, ocfs2 dlmfs and
FUSE all install one on `S_IFREG` inodes.  So "a regular file is
unconditionally readable and writable" is a premise about the IMAGE the run
was given, not a fact about `S_IFREG`; Rocq's `bits_all_pollable` states it
in full and `bugs/pselect6-unchecked-environment-obligations.md` records
it.  The Lean tree has no replay harness to discharge it per run, so it is
carried here as it is carried there. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## pselect6 (72) -/

/-- The largest `n` whose answer is a function of the MODELED state, and it
is `Uapi.NR_OPEN_DEFAULT` rather than a number that happens to equal it.

`core_sys_select` clamps `n` to `fdt->max_fds` (fs/select.c:641-642, Linux
v6.18.46, commit 1f99e9ab748f) before it sizes the bitmaps (:649), and
`max_fds` is a property of the fd TABLE's allocation history, not of which
descriptors are open.  The model tracks open descriptors (`m_fds`) and not
the table that holds them, so above that floor it cannot say how many bytes
the kernel reads and writes back.  At or below it the clamp provably never
bites, which is the floor argument `NR_OPEN_DEFAULT`
(include/linux/fdtable.h:24, Linux v6.18.46) carries.  Being `BITS_PER_LONG` it is also
exactly one `long` of bitmap, which is why the modeled band needs no
multi-word bitmap walk at all.  The argument in full is on Rocq's
`Select.pselect_nfds_max`. -/
def pselect_nfds_max : Int := NR_OPEN_DEFAULT

/-- `FDS_BYTES(n)` (fs/select.c:381, Linux v6.18.46) for the modeled band.
`FDS_BYTES` rounds up to whole `long`s, so every `n` in `[1, 64]` costs
exactly one 8-byte word and `n = 0` costs none — and at `n = 0` neither
`get_fd_set` (:386-395) nor `set_fd_set` (:397-403) touches the pointer at
all, however wild it is, because both copy `FDS_BYTES(n)` = 0 bytes. -/
def pselect_touches_sets (n : Int) : Bool := !(n == 0)

/-- One requested descriptor set, as the kernel imports it: the bitmap word
at `p`, or all-zero when `p` is NULL (`get_fd_set`, fs/select.c:393, Linux
v6.18.46, memsets its kernel copy instead of reading) or when `n` is 0 (a zero-length
`copy_from_user` always succeeds).  `none` is the unreadable pointer that
`get_fd_set` (:391) answers -EFAULT for. -/
def read_fd_set (mp : word → Option byte) (p : word) (n : Int) : Option word :=
  if !(pselect_touches_sets n) then some (Z_to_bv 64 0)
  else if w_is0 p then some (Z_to_bv 64 0)
  else read_u64 mp p

/-- The bits of a requested set that `do_select` actually scans.
`max_select_fd` masks the partial last word with
`~(~0UL << (n & (BITS_PER_LONG-1)))` (fs/select.c:425, Linux v6.18.46), and
`do_select` breaks out of its inner loop at `i >= n` (:532-533), so a bit at
or above `n` is invisible to the -EBADF test (:433-435), to the scan and to
the returned count — and it is CLEARED in the write-back, because the result
words start zeroed (`zero_fd_set`, :405-409, called at :673-675) and are
assigned wholesale (:566-571). -/
def fd_set_scanned (v : word) (n : Int) : word :=
  bv_and v (Z_to_bv 64 (2 ^ n.toNat - 1))

/-- The bytes `set_fd_set` (fs/select.c:397-403, Linux v6.18.46) copies back
for one set: none when the set was not requested — a NULL `ufdset` returns 0
without copying (:402) and `FDS_BYTES(0)` is 0 — one little-endian word
otherwise. -/
def fd_set_writeback (p : word) (n : Int) (v : word) : List (word × List byte) :=
  if !(pselect_touches_sets n) then []
  else if w_is0 p then []
  else [(p, word_le8 v)]

/-- `do_select`'s return value is the TOTAL number of bits it set across the
result masks, not the number of ready descriptors: fs/select.c has three
independent `retval++`, one per mask (:540, :545, :550, Linux v6.18.46), so
a descriptor ready for both reading and writing increments `retval` twice.

The bits are read off the word rather than off its `Z` reading; the file
header says why. -/
def popcount_aux (v : word) (k : Nat) : Int :=
  match k with
  | 0 => 0
  | k' + 1 => (if v.getLsbD k' then 1 else 0) + popcount_aux v k'

def popcount64 (v : word) : Int := popcount_aux v 64

/-- Every descriptor named by a set bit of `v` below position `k` is OPEN.
This is `max_select_fd`'s `set & ~*open_fds` test (fs/select.c:433-435 and
:444-445, Linux v6.18.46), which `do_select` runs over the union of the
three requested sets (`BITS`, :415) BEFORE any descriptor is polled (:494) —
so one closed descriptor makes the whole call -EBADF whatever the others
would have answered. -/
def bits_all_open (fds : List (word × FdEntry)) (v : word) (k : Nat) : Bool :=
  match k with
  | 0 => true
  | k' + 1 =>
      (if v.getLsbD k'
       then (match fd_lookup fds (Z_to_bv 64 (k' : Int)) with
             -- KIND-BLIND ON PURPOSE, unlike `bits_all_pollable` below.  This
             -- asks only whether the descriptor is OPEN, which is what -EBADF
             -- turns on, and a new `FdEntry` constructor is open like any
             -- other.  Enumerating here would turn a future constructor into
             -- a compile error for no reason.
             | some _ => true
             | none => false)
       else true)
      && bits_all_open fds v k'

/-- Every descriptor named by a set bit of `v` below `k` has the CONSTANT
poll mask.

`vfs_poll` (include/linux/poll.h:78-83, Linux v6.18.46) returns
`DEFAULT_POLLMASK` (:24) for any file whose `f_op->poll` is NULL, and
`DEFAULT_POLLMASK` is `EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM`, which
meets `POLLIN_SET` (fs/select.c:459-460) and `POLLOUT_SET` (:461-462) and
misses `POLLEX_SET` (:463) — so a file or directory descriptor is
unconditionally readable and writable and never exceptional, with no
dependence on its contents, its offset or the passage of time.  That is what
makes an answer possible here without a readiness notion.  Which files have
no `->poll` is an obligation on the IMAGE and not a fact about `S_IFREG`;
the file header and Rocq's `Select.bits_all_pollable` state it in full.

`FdChannel` is the opposite case and is why this predicate exists: a pipe's
readiness is a function of what the peer has written SO FAR, which the model
does not represent. -/
def bits_all_pollable (fds : List (word × FdEntry)) (v : word) (k : Nat) : Bool :=
  match k with
  | 0 => true
  | k' + 1 =>
      (if v.getLsbD k'
       then (match fd_lookup fds (Z_to_bv 64 (k' : Int)) with
            -- ENUMERATED ON PURPOSE, no wildcard.  A `some _ => true`
            -- catch-all here would be extensionally identical today, and
            -- would silently absorb the NEXT `FdEntry` constructor —
            -- asserting a pipe end or a socket unconditionally readable AND
            -- writable, which is an unsound ACCEPT rather than a decline.
            -- Listing the kinds that ARE unconditionally pollable makes a
            -- new constructor a compile error instead.
            | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir => true
            | some (.FdFileA _ _) => true
            | some (.FdFileRW _ _) => true
            -- the same regular file, opened O_RDWR.  A regular file has no
            -- `->poll` whatever its access mode, so `vfs_poll` hands back
            -- `DEFAULT_POLLMASK` here as it does for the kinds above
            | some (.FdChannel _) | some (.FdSocket _) | none => false
            -- A PIPE END IS THE `FdChannel` CASE WITH THE PEER INSIDE THE
            -- MODEL, and it declines for the same reason.  `pipeanon_fops`
            -- sets `.poll = pipe_poll` (fs/pipe.c:1261, v6.18.46) and is the
            -- table both ends get (:946, :957), so a pipe end never takes
            -- `DEFAULT_POLLMASK`: `pipe_poll` (:660) reports EPOLLIN only on
            -- a non-empty ring (:690) and EPOLLOUT only when it is not full
            -- (:697).  Answering `true` would assert a fresh pipe's read end
            -- readable, which `pipe_poll` denies on an empty ring — and
            -- would assert it WRITABLE, which is wrong unconditionally,
            -- since the read end holds FMODE_READ alone and `pipe_poll`'s
            -- EPOLLOUT branch never runs for it.
            | some (.FdPipe _ _) => false
            | some (.FdDevNull _ _) => false
            -- FAIL-CLOSED, though derivable: `null_fops`
            -- (drivers/char/mem.c:644-652, v6.18.46) lists `.llseek`,
            -- `.read`, `.write`, `.read_iter`, `.write_iter`,
            -- `.splice_write` and `.uring_cmd` and no `.poll`, so `vfs_poll`
            -- hands back `DEFAULT_POLLMASK` for /dev/null exactly as it does
            -- for a regular file and the answer would be `true`.  It is
            -- declined until that arm is written with its own pin; a decline
            -- here is a gap, never a wrong answer.
            | some .FdUrandom => false
            -- FAIL-CLOSED, the same way: `urandom_fops`
            -- (drivers/char/random.c:1572-1581, v6.18.46), the table
            -- `memory_open`'s device list installs for minor 9
            -- (drivers/char/mem.c:701), has no `.poll` — the blocking
            -- `random_fops` (drivers/char/random.c:1560-1570) is the table
            -- that does, `.poll = random_poll` at :1563 — so the answer is
            -- `DEFAULT_POLLMASK` and would be `true`.  Not written; declined.
            )
       else true)
      && bits_all_pollable fds v k'

/-- A range the call will WRITE must be writable end to end, or the model
declines.

`set_fd_set` (fs/select.c:397-403, Linux v6.18.46) and `put_timespec64`
(kernel/time/time.c:903-912) are `copy_to_user`s, which copy a PREFIX and
then fault: an 8-byte write straddling a page boundary whose second page is
unmapped lands some bytes and fails, and a set written earlier in the `inp`,
`outp`, `exp` order (fs/select.c:688-690, Linux v6.18.46) stays written when
a later one faults.  What the CALLER then sees differs: `set_fd_set`'s
failure is the call's -EFAULT (:688-691), while `put_timespec64`'s is
discarded — `poll_select_finish` falls through to `sticky:` and returns
`ret` unchanged (:343-345, :361-364).  The model has no representation for
"some unspecified prefix landed" in either case, so it declines the whole
shape rather than assert a byte count it cannot derive.  The band is narrow: an unreadable set already
answered -EFAULT at import, so what is left is a set that is readable but
not writable, i.e. one living in .rodata. -/
def range_writable (i : SyscallInput) (a : word) (len : Int) : Bool :=
  match read_bytes_map i.in_wmem a (Z_to_bv 64 len) with
  | some _ => true
  | none => false

def writes_all_writable (i : SyscallInput) (ws : List (word × List byte)) : Bool :=
  ws.all (fun w => range_writable i w.1 (w.2.length : Int))

/-- The sixth argument, after `get_sigset_argpack` (fs/select.c:774-791,
Linux v6.18.46) and `set_user_sigmask` (kernel/signal.c:3281-3297).

Most architectures cannot take a seventh syscall argument, so `pselect6`
packs the signal mask into a {`sigset_t *`, `size_t`} pair in memory
(`struct sigset_argpack`, fs/select.c:769-772, Linux v6.18.46) and takes a pointer to that.
Both musl and glibc's `pselect` always pass one, and musl's plain `select`
passes the constant pair {NULL, 8} rather than a NULL pointer — so "no mask"
reaches the kernel as a real 16-byte read, and modeling only the NULL sixth
argument would leave `select` itself outside the modeled surface. -/
inductive PselectSig
  /-- the pair itself is unreadable: -EFAULT -/
  | PsSigFault
  /-- no mask: the sixth argument is NULL, or its first word is -/
  | PsSigNone
  /-- a mask with the wrong `sigsetsize`: -EINVAL -/
  | PsSigBadSize
  /-- a mask that would be installed: unmodeled -/
  | PsSigReal

def pselect_sigpack (mp : word → Option byte) (sig : word) : PselectSig :=
  if w_is0 sig then .PsSigNone
  else match read_u64 mp sig, read_u64 mp (sig + Z_to_bv 64 8) with
       | some sp, some ss =>
           if w_is0 sp then .PsSigNone
             -- `set_user_sigmask` returns 0 on a NULL mask (kernel/signal.c:
             -- 3285-3286) BEFORE it looks at the size (:3287), so {NULL,
             -- anything} is "no mask" and the 8 musl passes is never read.
           else if bv_unsigned ss == kernel_sigset_bytes then .PsSigReal
           else .PsSigBadSize
       | none, _ | some _, none => .PsSigFault

/-- The fifth argument, after `get_timespec64` (kernel/time/time.c:872-892,
Linux v6.18.46) and `poll_select_set_timeout` (fs/select.c:271-286).

`do_pselect` hands `poll_select_set_timeout` the RAW pair
(fs/select.c:751), and `get_timespec64` normalizes nothing, so
`timespec64_valid` (include/linux/time64.h:97-106) judges the fields exactly
as the program wrote them: `tv_sec < 0` is invalid (:100-101), and so is a
`tv_nsec` at or above `NSEC_PER_SEC` when read as `unsigned long` (:103),
which every negative value is.  A `tv_nsec` of 1000000000 is therefore
-EINVAL and NOT one second.

WHICH VALIDATOR, checked rather than assumed: `poll_select_set_timeout`
calls the NON-strict validator at fs/select.c:275 (Linux v6.18.46), and that
is `timespec64_valid` (include/linux/time64.h:97-106, Linux v6.18.46);
`timespec64_valid_strict` (include/linux/time64.h:108-116), which
additionally bounds `tv_sec` by `KTIME_SEC_MAX`, appears nowhere in
fs/select.c.  So a huge `tv_sec` is ACCEPTED here and saturated at
fs/select.c:283 by `timespec64_add_safe` (kernel/time/time.c, Linux
v6.18.46), not rejected.

The carry that would make 1000000000 one second belongs to a different
function: `kern_select` (fs/select.c:700-720, Linux v6.18.46, the fold at
:712-714), which serves the `select` and `_newselect` numbers riscv64 does
not have.

The three admissible shapes are kept apart because they decide the TIMEOUT
WRITE-BACK, which is the whole difficulty of this syscall; see
`pselect_finish`. -/
inductive PselectTimeout
  /-- `tsp` unreadable: -EFAULT -/
  | PsToFault
  /-- `timespec64_valid` rejects it: -EINVAL -/
  | PsToInval
  /-- `tsp` NULL: no deadline at all -/
  | PsToNone
  /-- exactly {0,0}: poll once and return -/
  | PsToZero
  /-- a real deadline -/
  | PsToDeadline

def pselect_timeout (mp : word → Option byte) (tsp : word) : PselectTimeout :=
  if w_is0 tsp then .PsToNone
  else match read_u64 mp tsp, read_u64 mp (tsp + Z_to_bv 64 8) with
       | some sec, some nsec =>
           if bv_signed sec < 0 then .PsToInval
           else if NSEC_PER_SEC ≤ bv_unsigned nsec then .PsToInval
                  -- the `unsigned long` cast in `timespec64_valid`
                  -- (include/linux/time64.h:103, Linux v6.18.46): a negative `tv_nsec` is an
                  -- enormous unsigned one
           else if w_is0 sec && w_is0 nsec then .PsToZero
           else .PsToDeadline
       | none, _ | some _, none => .PsToFault

/-- What `core_sys_select` answers, before `poll_select_finish` decides the
timeout write-back. -/
inductive PselectCore
  /-- the model declines -/
  | PsCoreGap
  /-- a deterministic errno -/
  | PsCoreErr (e : Int)
  | PsCoreDone (ret : Int) (ws : List (word × List byte))

/-- `core_sys_select` (fs/select.c:621-698, Linux v6.18.46) within the
modeled band.

ORDER, and it is the kernel's: `n < 0` is -EINVAL (:632-634) before anything
is read; the three sets are copied in, `inp` then `outp` then `exp`
(:669-672), and an unreadable one is -EFAULT; then `max_select_fd` (:494,
:433-435) answers -EBADF if any requested descriptor is closed, before a
single descriptor is polled.  The -ENOMEM the kernel can raise between the
-EINVAL and the -EFAULT (:653-660) is UNREACHABLE here: `core_sys_select`
allocates on the stack whenever `FDS_BYTES(n)` is at most
`SELECT_STACK_ALLOC / 6` = 42 bytes (:651, with `SELECT_STACK_ALLOC` = 256,
include/linux/poll.h:19, Linux v6.18.46), and the modeled band caps `FDS_BYTES(n)` at 8.
That is what lets this spec commit to an answer at all, rather than having
to union an allocation failure with every later verdict. -/
def pselect_core (i : SyscallInput) (m : Model) (n32 inp outp exp : word)
    : PselectCore :=
  let n := nfds_signed n32
  if n < 0 then .PsCoreErr EINVAL
  else if pselect_nfds_max < n then .PsCoreGap
  else
    match read_fd_set i.in_mem inp n,
          read_fd_set i.in_mem outp n,
          read_fd_set i.in_mem exp n with
    | some rin, some rout, some rex =>
        let win := fd_set_scanned rin n
        let wout := fd_set_scanned rout n
        let wex := fd_set_scanned rex n
        let all := bv_or (bv_or win wout) wex
        let k := n.toNat
        if !(bits_all_open (m_fds m) all k) then .PsCoreErr EBADF
        else if !(bits_all_pollable (m_fds m) all k) then .PsCoreGap
        else
          -- Every polled descriptor carries `DEFAULT_POLLMASK`, so the read
          -- and write sets come back UNCHANGED, the exception set comes back
          -- empty, and the count is the total number of bits across the
          -- three — two for a descriptor named in both `readfds` and
          -- `writefds`.
          .PsCoreDone (popcount64 win + popcount64 wout)
                      (fd_set_writeback inp n win
                       ++ fd_set_writeback outp n wout
                       ++ fd_set_writeback exp n (Z_to_bv 64 0))
    | none, _, _ | some _, none, _ | some _, some _, none => .PsCoreErr EFAULT

/-- An errno return: no user memory is written on any error path that the
modeled band reaches. -/
def pselect_err (e : Int) : Option (word × List (word × List byte)) :=
  some (errno_ret e, [])

/-- The 16 zero bytes `put_timespec64` (kernel/time/time.c:903-912, Linux
v6.18.46) writes for a remaining time of {0,0}: `struct __kernel_timespec`
is two 64-bit fields. -/
def pselect_timespec_zero : List byte := List.replicate 16 (Z_to_bv 8 0)

def pselect_writes (i : SyscallInput) (ret : Int) (ws : List (word × List byte))
    : Option (word × List (word × List byte)) :=
  if writes_all_writable i ws then some (Z_to_bv 64 ret, ws) else none

/-- `poll_select_finish` (fs/select.c:295-365, Linux v6.18.46) — and the
reason most of this syscall is not modeled.  STATED OVER AN ABSTRACT
`PselectCore` rather than over `core_sys_select`, because the kernel's
function is shared: ppoll (73) reaches the identical call with the identical
`PT_TIMESPEC` argument (:1116), so `ppoll_outcome` reuses this definition
unchanged and every sentence below is about both syscalls.

Every return that comes out of `core_sys_select` passes through it
(:760), errors included, and it writes the REMAINING TIME back to `*tsp`
(:313-314, :342-344).  That value is `end_time - ktime_get_ts64()`, sampled
after the work is done, so its content is a function of how long the call
took.  The model has no clock and no representation of elapsed time, so the
only returns it can describe are the ones where that write does not happen,
or happens with a value that is forced:

- `tsp` NULL (:303-304), or a requested timeout that normalized to {0,0}
  (:310-311, the pair `poll_select_set_timeout` stores at :279-280):
  `poll_select_finish` returns early and writes nothing at all.
- a real deadline that the call ran out: `end_time` is now in the past, the
  clamp at :315-316 fires, and exactly 16 zero bytes are written.  The
  hrtimer range slack only ever fires LATE
  (`hrtimer_set_expires_range_ns`, include/linux/hrtimer.h at Linux v6.18.46, keeps the soft
  expiry at the deadline and pushes the hard one out), so a deadline can
  never be reached early and the remaining time can never be positive.
- a real deadline that the call did NOT run out — any positive return, and
  every errno from `core_sys_select` — is where the value is a live clock
  reading.  UNMODELED.

The expiry case assumes `current->personality` carries no `STICKY_TIMEOUTS`:
`poll_select_finish` tests that bit (:306-307) before it looks at the
deadline and returns with `*tsp` untouched when it is set.  That is an
ENVIRONMENT PREMISE rather than a kernel fact — `execve` preserves the bit
and only `personality(2)` sets it — and the Lean tree has no harness to
discharge it per run; Rocq's `Select.pselect_finish` records how the Rocq
harness does.

Because every polled descriptor in the modeled band is always ready for
reading and writing and NEVER exceptional, a real deadline is reached
exactly when no bit below `n` is set in `readfds` or in `writefds`: an `n` of
0, NULL pointers for those two, or sets with no bit below `n`.  `exceptfds`
is not part of that condition — `DEFAULT_POLLMASK` misses `POLLEX_SET`
(fs/select.c:463, Linux v6.18.46), so an `exceptfds` bit never raises the count and the set
always comes back zeroed.  So there are two modeled shapes in which this
syscall waits, not one: the portable-sleep idiom
`select(0, NULL, NULL, NULL, &tv)`, and an `exceptfds`-only request naming an
open file or directory.

The NULL-timeout case has the opposite corner.
`schedule_hrtimeout_range_clock` (kernel/time/sleep_timeout.c:189-224, Linux v6.18.46)
treats a NULL expiry as infinite — it calls `schedule()` and returns -EINTR
(:206-209) — so `do_select`'s `timed_out` flag is never set and the loop
cannot exit with a zero count (fs/select.c:575-576, :603-605, Linux v6.18.46).  A zero count
under a NULL timeout therefore means the call never returns at all, and the
model has no way to say that: UNMODELED rather than an invented 0. -/
def pselect_finish (i : SyscallInput) (tsp : word) (tmo : PselectTimeout)
    (c : PselectCore) : Option (word × List (word × List byte)) :=
  match c with
  | .PsCoreGap => none
  | .PsCoreErr e =>
      match tmo with
      | .PsToDeadline => none   -- the errno carries a live clock reading with it
      | .PsToFault | .PsToInval | .PsToNone | .PsToZero => pselect_err e
  | .PsCoreDone ret ws =>
      match tmo with
      | .PsToNone => if ret == 0 then none else pselect_writes i ret ws
      | .PsToZero => pselect_writes i ret ws
      | .PsToDeadline =>
          if ret == 0
          then pselect_writes i 0 (ws ++ [(tsp, pselect_timespec_zero)])
          else none
      | .PsToFault | .PsToInval => none   -- unreachable: `pselect6_outcome` answers these first

/-- `pselect6 n inp outp exp tsp sig` — the ONE outcome the modeled band
admits, or `none` where the model declines (fail closed).

Nothing here is nondeterministic.  Readiness, the one thing this syscall
exists to report, is a kernel CONSTANT for every descriptor kind the model
has: `vfs_poll` (include/linux/poll.h:78-83, Linux v6.18.46) hands back
`DEFAULT_POLLMASK` for any file with no `->poll` method.  A descriptor whose
readiness is a schedule rather than a constant — the piped stdio channels —
is refused by `bits_all_pollable` instead of guessed at.

The arms below are in the kernel's own decision order, so reading them top
to bottom is reading `SYSCALL_DEFINE6(pselect6, ...)` (fs/select.c:793-803, Linux v6.18.46),
`do_pselect` (:728-761) and `core_sys_select` (:621-698) in sequence. -/
def pselect6_outcome (i : SyscallInput) (m : Model)
    (n32 inp outp exp tsp sig : word) : Option (word × List (word × List byte)) :=
  let core := pselect_core i m n32 inp outp exp
  match pselect_sigpack i.in_mem sig, pselect_timeout i.in_mem tsp with
  -- `get_sigset_argpack`, in the syscall entry (fs/select.c:799-800, Linux v6.18.46), before
  -- `do_pselect`
  | .PsSigFault, _ => pselect_err EFAULT
  -- `get_timespec64` (:739-740) and `poll_select_set_timeout` (:751-752)
  | _, .PsToFault => pselect_err EFAULT
  | _, .PsToInval => pselect_err EINVAL
  -- `set_user_sigmask` (:755-757)
  | .PsSigBadSize, _ => pselect_err EINVAL
  | .PsSigReal, _ => none    -- see `pselect_sigpack`
  -- `core_sys_select` (:759), then `poll_select_finish` (:760)
  | .PsSigNone, .PsToNone => pselect_finish i tsp .PsToNone core
  | .PsSigNone, .PsToZero => pselect_finish i tsp .PsToZero core
  | .PsSigNone, .PsToDeadline => pselect_finish i tsp .PsToDeadline core

def pselect6_spec (n32 inp outp exp tsp sig : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => unmodeled
  | some (r, ws) => Monad.pure (mkEffect r ws [])

/-! ## ppoll (73)

`SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned int, nfds,
struct __kernel_timespec __user *, tsp, const sigset_t __user *, sigmask,
size_t, sigsetsize)` (fs/select.c:1095-1117, Linux v6.18.46, commit
1f99e9ab748f) is defined in the same fs/select.c, so it belongs in this file
for the same reason pselect6 does, and it shares three of its four steps
verbatim.  Its body IS `do_pselect`'s with the middle replaced:

1. `get_timespec64` on a non-NULL `tsp` (:1102-1104), then
   `poll_select_set_timeout` (:1107-1108) — the same -EFAULT then -EINVAL,
   on the same RAW fields, judged by the same non-strict `timespec64_valid`.
   `pselect_timeout` answers it unchanged.
2. `set_user_sigmask` (:1111-1113), whose errnos `return` from the syscall
   entry DIRECTLY and never reach `poll_select_finish`.
3. `do_sys_poll` (:1115), where the two syscalls differ.
4. `poll_select_finish` (:1116), reached from step 3 alone, with
   `PT_TIMESPEC` — the same function, the same argument, the same
   remaining-time write-back.  `pselect_finish` answers it unchanged.

THE SIXTH ARGUMENT IS NOT PACKED HERE.  pselect6 needs seven values and has
six registers, so it takes a pointer to a {`sigset_t *`, `size_t`} pair and
unpacks it with `get_sigset_argpack` (:799); ppoll needs five and passes the
mask pointer and the size as arguments 3 and 4, counting from 0 as the
table's `in_arg i 3` and `in_arg i 4` do.  So ppoll has no -EFAULT for
an unreadable argpack and no `PsSigFault` equivalent AHEAD of the timeout —
its only mask -EFAULT is `set_user_sigmask`'s own copy from user memory
(kernel/signal.c:3289-3290, Linux v6.18.46), which runs AFTER the timeout is judged.
Reading the ORDER off pselect6 and transplanting it would put that -EFAULT
two steps too early.

WHAT `do_sys_poll` (fs/select.c:967-1039, Linux v6.18.46) ADDS.  Readiness is answered
exactly as `core_sys_select` answers it and for the same reason, so every
caveat `bits_all_pollable` carries carries here unchanged.  Three things are
genuinely new:

- AN UNOPENED DESCRIPTOR IS AN ANSWER, NOT AN ERROR.  Where `max_select_fd`
  makes one closed descriptor -EBADF for the whole call (:433-435),
  `do_pollfd` returns `EPOLLNVAL` for it (:864-865), which `do_poll` stores
  in the entry's `revents` (:914) and COUNTS (:915-916).  A negative `fd` is
  neither: `do_pollfd` returns 0 (:860-861) before `CLASS(fd, f)`, and the
  entry's `revents` is written as 0 and not counted.  This is the one place
  the two syscalls disagree about the same descriptor.
- THE ENTRY'S `events` IS A FILTER.  `do_pollfd` builds
  `filter = demangle_poll(pollfd->events) | EPOLLERR | EPOLLHUP` (:868) and
  answers `vfs_poll(...) & filter` (:870, :873).  Neither `EPOLLERR` nor
  `EPOLLHUP` is in `DEFAULT_POLLMASK`, so they contribute nothing, and what
  survives is `DEFAULT_POLLMASK & events`.  riscv64 has no `asm/poll.h`
  (arch/riscv/include/uapi/asm/ has no poll.h at the pinned commit), so its
  POLL* constants are include/uapi/asm-generic/poll.h's, which are
  bit-for-bit the EPOLL* values of include/uapi/linux/eventpoll.h:
  `mangle_poll` and `demangle_poll` (include/linux/poll.h:120-137, Linux v6.18.46) are the
  identity on every bit that can survive the mask, and on every bit of
  `events` that the mask can select.  So this spec needs no envelope on
  `events` at all.
- THE ARRAY IS COPIED IN AND WRITTEN BACK ENTRY BY ENTRY.  `do_sys_poll`
  copies `nfds` whole `struct pollfd`s with one `copy_from_user` (:991-993)
  and then, after `do_poll` (:1009), writes back the `revents` field of each
  — two bytes at offset 6 of each entry — with `unsafe_put_user` under one
  `user_write_access_begin` (:1012-1022).  The write-back runs on EVERY
  return out of `do_poll`, a zero count included, so a call that timed out
  still rewrites every entry's `revents`. -/

/-- `struct pollfd` is {`int fd`, `short events`, `short revents`}
(include/uapi/asm-generic/poll.h:36-40, Linux v6.18.46): 8 bytes on LP64
with no padding, and `revents` the last two of them.  `do_sys_poll` copies
the whole thing in (fs/select.c:991-993) and writes back only those two
(:1019-1020). -/
def pollfd_bytes : Int := 8

def pollfd_revents_off : Int := 6

/-- The largest `nfds` whose answer is a function of the MODELED state, and
it is a stack-allocation bound rather than a descriptor one.

`do_sys_poll` keeps the imported array in `stack_pps`, a `POLL_STACK_ALLOC`
= 256-byte buffer (fs/select.c:975, include/linux/poll.h:18-20, Linux
v6.18.46), and chains `kmalloc`ed `struct poll_list` blocks after it for
anything that does not fit (:999-1005); a failed `kmalloc` is -ENOMEM
(:1002-1004).  `N_STACK_PPS` (:964-965) is
`(sizeof(stack_pps) - sizeof(struct poll_list)) / sizeof(struct pollfd)` =
(256 - 16) / 8 = 30, `struct poll_list` (:838-842) being a pointer, an
`unsigned int` and a flexible array, so 16 bytes on LP64.  At or below 30
entries the chain is never extended (:995-996 breaks out), no allocation
happens and -ENOMEM does not exist — which is what lets this spec commit to
an answer at all, exactly as `core_sys_select`'s `SELECT_STACK_ALLOC`
argument does for pselect6.  Above it the model would have to union an
allocation failure with every verdict, so it declines.

This is a SMALLER band than pselect6's `pselect_nfds_max`, and for an
unrelated reason: pselect6 stops at `NR_OPEN_DEFAULT` because
`core_sys_select` clamps `n` to `fdt->max_fds` (:641-642); ppoll indexes no
bitmap and has no such clamp. -/
def ppoll_nfds_max : Int := 30

/-- `POLLNVAL`, the answer `do_pollfd` gives for a descriptor that is not
open: it returns `EPOLLNVAL` when `fd_empty(f)` holds (fs/select.c:864-865,
Linux v6.18.46).  0x20 in both the POLL*
(include/uapi/asm-generic/poll.h:11) and the EPOLL* encodings, which
coincide on riscv64. -/
def POLLNVAL : Int := 32

/-- `DEFAULT_POLLMASK` (include/linux/poll.h:24, Linux v6.18.46) is
`EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM` = 0x1|0x4|0x40|0x100. -/
def default_pollmask : Int := 325

/-- One imported entry's `fd`, read as the `int` it is: `do_pollfd`'s first
test is `fd < 0` (fs/select.c:860, Linux v6.18.46), which is signed. -/
def pollfd_fd (bs : List byte) : Int :=
  sint32 (le_bytes_to_word (bs.take 4))

/-- One imported entry's `events`.  Read as 16 unsigned bits: the field is a
`short` and `demangle_poll` (include/linux/poll.h:130-137, Linux v6.18.46)
takes it as a `u16`, but the sign cannot matter here — see the `events`
paragraph above. -/
def pollfd_events (bs : List byte) : Int :=
  bv_unsigned (le_bytes_to_word ((bs.drop 4).take 2))

/-- The array as `do_sys_poll` read it, entry by entry.  `bs` is the single
`copy_from_user`'s worth of bytes (fs/select.c:991-993, Linux v6.18.46); a
shorter list than `k` entries cannot arise, since the caller reads exactly
`pollfd_bytes * nfds` of them or none. -/
def decode_pollfds (bs : List byte) (k : Nat) : List (Int × Int) :=
  match k with
  | 0 => []
  | k' + 1 =>
      (pollfd_fd bs, pollfd_events bs)
        :: decode_pollfds (bs.drop pollfd_bytes.toNat) k'

/-- `do_pollfd` (fs/select.c:853-874, Linux v6.18.46) for one entry, or
`none` where the model declines.

The three arms are the function's own: `fd < 0` returns 0 (:860-861) without
looking anything up; a descriptor that is not open takes `EPOLLNVAL`
(:864-865); anything else is `vfs_poll` (:870) masked by the entry's filter
(:868, :873).

The mask is taken in `Nat`; the file header says why that is the same value
`Z.land` gives. -/
def ppoll_revents_of (fds : List (word × FdEntry)) (fd events : Int) : Option Int :=
  if fd < 0 then some 0
  else match fd_lookup fds (Z_to_bv 64 fd) with
       | none => some POLLNVAL
       -- `FdFileA` and `FdFileRW` are the same regular file opened
       -- O_APPEND or O_RDWR: no `->poll` whatever its access mode, so
       -- `vfs_poll` hands back `DEFAULT_POLLMASK` for them as for the three
       -- kinds beside them -- the argument `bits_all_pollable` makes for
       -- pselect6
       | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir
       | some (.FdFileA _ _) | some (.FdFileRW _ _) =>
           some ((default_pollmask.toNat &&& events.toNat : Nat) : Int)
       -- ENUMERATED ON PURPOSE, exactly as `bits_all_pollable` is and for
       -- the same reason: a `some _ => true` catch-all would be
       -- extensionally identical today and would silently absorb the next
       -- `FdEntry` constructor as unconditionally ready.  A channel, a
       -- socket and a pipe end each have a `->poll` method whose answer is a
       -- function of what a peer has done so far, which this model does not
       -- represent — and note that `EPOLLERR` and `EPOLLHUP` are in the
       -- filter unconditionally (fs/select.c:868, Linux v6.18.46), so not even an `events`
       -- of 0 makes such a descriptor's answer derivable.
       | some (.FdChannel _) | some (.FdSocket _) | some (.FdPipe _ _) => none
       | some (.FdDevNull _ _) => none
           -- FAIL-CLOSED, for the reason `bits_all_pollable` gives: the
           -- answer is `DEFAULT_POLLMASK` because `null_fops`
           -- (drivers/char/mem.c:644-652, Linux v6.18.46) has no `.poll`, and it is not
           -- written yet
       | some .FdUrandom => none
           -- the same: `urandom_fops` (drivers/char/random.c:1572-1581, Linux v6.18.46)
           -- has no `.poll` either

def ppoll_revents (fds : List (word × FdEntry)) (es : List (Int × Int))
    : Option (List Int) :=
  match es with
  | [] => some []
  | (fd, ev) :: rest =>
      match ppoll_revents_of fds fd ev with
      | none => none
      | some r =>
          match ppoll_revents fds rest with
          | none => none
          | some rs => some (r :: rs)

/-- `do_poll`'s return: the number of entries whose `do_pollfd` answered a
non-zero mask (fs/select.c:915-916, Linux v6.18.46).  Within the modeled
band that is exactly the number of non-zero `revents`, because every mask
this spec produces — 0, `EPOLLNVAL`, or a subset of `DEFAULT_POLLMASK` —
survives `mangle_poll` (:914) unchanged, so the mask is zero exactly when
the stored `revents` is.  Unlike pselect6's, this count is a DESCRIPTOR
count: one entry contributes at most 1 however many bits its `revents`
carries. -/
def ppoll_count (rs : List Int) : Int :=
  match rs with
  | [] => 0
  | r :: rest => (if r == 0 then 0 else 1) + ppoll_count rest

/-- The write-back: two bytes at offset 6 of each entry, in entry order, one
`unsafe_put_user` each (fs/select.c:1019-1020, Linux v6.18.46).  Named
separately rather than as one range because that is what the kernel writes —
the `fd` and `events` fields in between are not rewritten. -/
def ppoll_writeback (p : word) (rs : List Int) : List (word × List byte) :=
  match rs with
  | [] => []
  | r :: rest =>
      (p + Z_to_bv 64 pollfd_revents_off, word_le2 (Z_to_bv 64 r))
        :: ppoll_writeback (p + Z_to_bv 64 pollfd_bytes) rest

/-- `do_sys_poll` (fs/select.c:967-1039, Linux v6.18.46) within the modeled
band.

ORDER, and it is the kernel's: `nfds > rlimit(RLIMIT_NOFILE)` is -EINVAL
(:981-982) before a byte is copied; then the single `copy_from_user` of the
whole array (:991-993), an unreadable byte anywhere in it being -EFAULT with
nothing written back (`err` starts at -EFAULT, :971, and the jump at :993
keeps it); then `do_poll` (:1009).  The limit test is answered from state
rather than argued around — `State.m_nofile` carries the soft RLIMIT_NOFILE
the run was launched with — and it is tested BEFORE this spec's own
`ppoll_nfds_max` decline, so an `nfds` that is both above 30 and above the
limit gets the kernel's -EINVAL rather than a decline.

`nfds = 0` copies nothing: `len` is 0 (:984), the loop breaks before the
copy (:988-989), `do_poll` walks no entries and the write-back loop writes
none (:1019-1020).  But `user_write_access_begin(ufds, 0)` still runs
(:1012-1013).  On riscv64 that is `user_access_begin`
(arch/riscv/include/asm/uaccess.h:456-462, Linux v6.18.46;
include/linux/uaccess.h:568-569 makes the write form the same call), which
is `access_ok`, and `__access_ok` (include/asm-generic/access_ok.h:31-41,
Linux v6.18.46) with a `size` of 0 is
`addr <= TASK_SIZE_MAX`, `TASK_SIZE_MAX` being `TASK_SIZE` (:15-17).  So a
`ufds` above `TASK_SIZE` fails it, `do_sys_poll` jumps to `out_fds` with
`err` still the -EFAULT it started as (:971), and the call is -EFAULT — after
`do_poll` has run, so under a deadline the expiry is waited out first.  A
user-space `ufds` that is merely unmapped passes, and `nfds = 0` on it is
answered as Rocq answers it.

THE ONE DECLINE THIS FILE ADDS TO ROCQ'S.  Rocq's `ppoll_core` answers 0 for
that kernel-space `ufds` too ("however wild the pointer is"), which is an
answer Linux does not give; bugs/ppoll-nfds-zero-answers-a-kernel-space-ufds.md
records it.  The Lean twin declines the shape — `nfds = 0` with
`access_okb ufds 0` false, `State.access_okb` being the model's
`__access_ok` — rather than answering the -EFAULT, because an answer the Rocq
twin does not give would be the two specs disagreeing on an admitted
behaviour, while a declared decline is the shape a port may add.  The gate
sits where the kernel's test sits relative to the copy: nothing is read for
`nfds = 0`, so it is judged before the read. -/
def ppoll_core (i : SyscallInput) (m : Model) (ufds nfds : word) : PselectCore :=
  let n := bv_unsigned nfds
  if bv_unsigned (m_nofile m) < n then .PsCoreErr EINVAL
  else if ppoll_nfds_max < n then .PsCoreGap
  else if n == 0 && !(access_okb ufds 0) then .PsCoreGap
  else
    match read_bytes_map i.in_mem ufds (Z_to_bv 64 (pollfd_bytes * n)) with
    | none => .PsCoreErr EFAULT
    | some bs =>
        match ppoll_revents (m_fds m) (decode_pollfds bs n.toNat) with
        | none => .PsCoreGap
        | some rs => .PsCoreDone (ppoll_count rs) (ppoll_writeback ufds rs)

/-- `set_user_sigmask` (kernel/signal.c:3281-3297, Linux v6.18.46), reached
with the mask pointer and the size as separate arguments.

Its order is its own: a NULL `umask` returns 0 (:3285-3286) BEFORE the size
is looked at, so {NULL, anything} is "no mask"; then
`sigsetsize != sizeof(sigset_t)` is -EINVAL (:3287-3288); then the
`copy_from_user` is -EFAULT (:3289-3290).  A mask that would be INSTALLED is
where the model stops: `set_user_sigmask` saves `current->blocked` into
`current->saved_sigmask` and installs the caller's (:3292-3294). -/
inductive PpollSig
  /-- no mask: the pointer is NULL -/
  | PpSigNone
  /-- the wrong `sigsetsize`: -EINVAL -/
  | PpSigBadSize
  /-- the mask itself is unreadable: -EFAULT -/
  | PpSigFault
  /-- a mask that would be installed: unmodeled -/
  | PpSigReal

def ppoll_sigmask (mp : word → Option byte) (sig sigsetsize : word) : PpollSig :=
  if w_is0 sig then .PpSigNone
  else if !(bv_unsigned sigsetsize == kernel_sigset_bytes) then .PpSigBadSize
  else match read_bytes_map mp sig (Z_to_bv 64 kernel_sigset_bytes) with
       | some _ => .PpSigReal
       | none => .PpSigFault

/-- `ppoll ufds nfds tsp sigmask sigsetsize` — the ONE outcome the modeled
band admits, or `none` where the model declines (fail closed).

The arms are in the kernel's own decision order, so reading them top to
bottom is reading `SYSCALL_DEFINE5(ppoll, ...)` (fs/select.c:1095-1117,
Linux v6.18.46) in sequence.  Note where `poll_select_finish` is and is not:
the two `set_user_sigmask` errnos below return from the entry directly
(:1111-1113) and write no timeout back, while everything `ppoll_core`
answers — errnos included — passes through it (:1116). -/
def ppoll_outcome (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : Option (word × List (word × List byte)) :=
  let tmo := pselect_timeout i.in_mem tsp
  match tmo with
  -- `get_timespec64` (:1103-1104) and `poll_select_set_timeout` (:1107-1108)
  | .PsToFault => pselect_err EFAULT
  | .PsToInval => pselect_err EINVAL
  | .PsToNone | .PsToZero | .PsToDeadline =>
      -- `set_user_sigmask` (:1111-1113)
      match ppoll_sigmask i.in_mem sig sigsetsize with
      | .PpSigBadSize => pselect_err EINVAL
      | .PpSigFault => pselect_err EFAULT
      | .PpSigReal => none
      | .PpSigNone =>
          -- `do_sys_poll` (:1115), then `poll_select_finish` (:1116)
          pselect_finish i tsp tmo (ppoll_core i m ufds nfds)

def ppoll_spec (ufds nfds tsp sig sigsetsize : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => unmodeled
  | some (r, ws) => Monad.pure (mkEffect r ws [])

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
