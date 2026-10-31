import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.File — the fd table, dup (23), dup3 (24)

Mirrors `theories/LinuxProcessSem/Sys/Fs/File.v`, which answers to Linux
`fs/file.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/File.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq pins `SYSCALL_DEFINE1(dup)` to "byte-identical v5.9..v7.2",
`ksys_dup3` to "byte-identical v5.11..v7.2" and `struct fdtable` to
"byte-identical v5.4..v7.2"; every line here was read at v6.18.46
instead.  One fact of that text Rocq's prose does not carry: `ksys_dup3`
is `static` there (fs/file.c:1399), reached through
`SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int, newfd, int,
flags)` (:1433-1436) and `SYSCALL_DEFINE2(dup2, …)` (:1438-1455); nothing
below turns on it.

Two spellings differ from Rocq without changing a value: the flag test
is done on the `word` (`bv_and` with the complemented constant) where Rocq
does it on `bv_unsigned` in `Z` (`Z.ldiff`) — `O_CLOEXEC` is below
`2^64`, so the two agree — and Rocq's `Z.eqb`/`Z.ltb` Bool tests are
Lean's decidable `=`/`<` on `Int`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The kernel returns the LOWEST free descriptor: `get_unused_fd_flags`
(fs/file.c:620-623, Linux v6.18.46, commit 1f99e9ab748f) is
`__get_unused_fd_flags(flags, rlimit(RLIMIT_NOFILE))` (:615-618), which is
`alloc_fd(0, nofile, flags)`, and `alloc_fd` (:570-613) takes the first
clear bit `find_next_fd` (:544-565) reports at or after
`max(start, next_fd)` (:580-585) — the lowest free fd, because a close
lowers `next_fd` (`__put_unused_fd`, :630-631) — computed by
`State.alloc_fd`, whose header carries the reading of `next_fd`.  The
choice set is a singleton (no nondeterminism); the freeness conjunct only
empties it where `alloc_fd`'s scan bound (4096 fds) is exhausted, leaving
just the errno alternative.  Rocq calls that case unreachable because a
real kernel fails with -EMFILE at RLIMIT_NOFILE (`alloc_fd`, :591-593)
well before it; that holds exactly while the run's soft limit is at most
4097 — at 4097 Linux answers -EMFILE for the 4098th descriptor, which is
admitted — and `Run.valid_nofile` admits limits up to `2^31 - 64`:
`do_prlimit` (kernel/sys.c:1513-1515, Linux v6.18.46) refuses a hard limit
above the live `sysctl_nr_open`, whose own ceiling `sysctl_nr_open_max`
(fs/file.c:100-101, v6.18.46) the `nr_open` sysctl's table entry
(fs/file_table.c:151-158) applies through `proc_douintvec_minmax`
(kernel/sysctl.c:823, v6.18.46).  Under a larger limit a table holding
0..4096 makes Linux answer 4097 where this admits only the two errnos —
a priority-1 gap shared with Rocq's `lowest_fd` and every spec that
calls it, not closed here because the Rocq side has to move first; the
closing paragraph of bugs/fd-allocation-ignores-rlimit-nofile.md records
it beside the priority-2 divergence the rest of that entry describes,
which holds only below the scan wall.  The model fact is the Rocq-lemma
twin `State.alloc_fd_le`; the freeness conjunct that empties the choice
set there is what `Checks/Cases/Fs/File.lean`'s
`dup_never_answers_a_held_fd` reads.  `alloc_fd fds ≤ 4096` keeps an fd
from ever being confused with an error-encoded return.

WHAT THIS DOES NOT DO IS CONSULT THE LIMIT, and that is a known
divergence rather than a decline: Linux's `alloc_fd` takes
`end = rlimit(RLIMIT_NOFILE)` from `__get_unused_fd_flags`
(fs/file.c:615-618, Linux v6.18.46) and answers -EMFILE at `fd >= end`
(:591-593), so a modeled run can reach a state Linux would have refused.
Below the scan bound it costs priority 2 and not priority 1 — the -EMFILE
alternative keeps the kernel's own answer inside the admitted set — it
predates the limit being tracked at all, and the argument is recorded in
bugs/fd-allocation-ignores-rlimit-nofile.md.  Rocq: `File.lowest_fd`, and
the paragraph on `File.dup3_spec` that names the same bug. -/
def lowest_fd (fds : List (word × FdEntry)) : Sys word :=
  choose (fun fd => fd_lookup fds fd = none ∧ fd = alloc_fd fds)

/-! ## Descriptor duplication: dup (23) / dup3 (24) -/

/-- WHAT DUPLICATION SHARES, AND WHAT THIS MODEL CAN NAME.

`dup` and `dup3` install a second descriptor for the SAME OPEN FILE
DESCRIPTION: `SYSCALL_DEFINE1(dup, unsigned int, fildes)`
(fs/file.c:1457-1470, Linux v6.18.46, commit 1f99e9ab748f) hands
`fd_install` (:1465, defined :652) the very `struct file` pointer
`fget_raw` (:1460) returned, and `do_dup2` (:1265-1316) stores that same
pointer at `newfd` (:1304) after a `get_file` (:1303).  The file OFFSET
`f_pos` (include/linux/fs.h:1233, Linux v6.18.46) and the status flags
`f_flags` (:1218) are fields of that `struct file` (:1211), so the two fds
read and advance ONE offset; only the close-on-exec bit is per-descriptor,
living in the
descriptor table's `close_on_exec` bitmap (`struct fdtable`,
include/linux/fdtable.h:26-33 at Linux v6.18.46, the bitmap at :29) rather
than in the description.

This model keeps the offset INSIDE the per-fd entry (`State.FdEntry`:
`FdFile p offset`), so it cannot name one description from two fds.
Duplication is therefore modeled exactly for the entries that carry NO
per-description state, and declines for the ones that do.  Per kind,
each argued in full on Rocq's `File.dup_modeled_entry`:

- `FdChannel`: `true`.  A channel's read position is the model-wide
  `m_stdin` and its writes are trace events, so two fds naming one channel
  already share everything a description shares: copying the entry IS the
  sharing.
- `FdDir`: `true`.  Nullary, and no modeled arm observes a directory
  position.
- `FdFile`, `FdFileW`: `false`.  The entry carries `offset`, which read,
  readv, write, writev and lseek rewrite in place, so a copy would give
  the two fds INDEPENDENT offsets — a confident wrong answer rather than a
  gap.  The fix is an open file description layer in `State.lean`.
- `FdSocket`: `false`.  The entry carries the connection's remaining
  receive script, rewritten in place by a read; a copy would report the
  peer's reset once per fd where Linux reports it once per connection.
- `FdPipe`: `false`, and NOT the `FdChannel` case though it carries no
  offset either: a pipe end names a `pipe_inode_info` with reader and
    writer COUNTS, which the reference `get_file` (include/linux/fs.h:1261,
  Linux v6.18.46) takes for `do_dup2` (fs/file.c:1303) leaves untouched
  while `pipe_release` (fs/pipe.c:724-746, v6.18.46) moves them once per
  `struct file` release (:731, :733) — so a copied entry would let the
  table's count of live ends drift from the kernel's.  Rocq's paragraph
  carries the argument.
- `FdDevNull`: `true`, the `FdChannel` case with nothing to share at all:
    `null_lseek` (drivers/char/mem.c:561, Linux v6.18.46) pins `f_pos` at 0,
  `read_null` (:412) and `write_null` (:418) never move it, and
  `Fcntl.getfl_f_flags` and `Fcntl.setfl_noop_on` both decline the kind,
  so no modeled arm can tell a copied entry from a shared description.
- `FdUrandom`: `true`, /dev/null's argument with the BYTES to check as
    well: `urandom_fops` (drivers/char/random.c:1572-1581, Linux v6.18.46)
  seeks through `noop_llseek` (fs/read_write.c:324-327, v6.18.46), which
  returns `f_pos` unchanged, and reads through `urandom_read_iter`
  (drivers/char/random.c:1453-1475, v6.18.46), which hands the request to
  `get_random_bytes_user` (:1474) without touching the `struct kiocb`
  position `ki_pos` (include/linux/fs.h:409, v6.18.46); the two
  `Fcntl` predicates decline this kind too; and the bytes a read delivers
  are the front of the run's declared stream, `State.m_urandom`, the
  model's and not the entry's — so two fds on one description and two
  opens of the device read alike, as two `struct file`s on the random
  device draw from one generator.

ENUMERATED, no wildcard: the file header says why two Rocq arms are
absent and what lands them. -/
def dup_modeled_entry (e : FdEntry) : Bool :=
  match e with
  | .FdChannel _ | .FdDir => true
  | .FdFile _ _ | .FdFileW _ _ | .FdSocket _ => false
  | .FdFileA _ _ => false
  | .FdFileRW _ _ => false
      -- THE `FdFile` ARGUMENT UNCHANGED: the entry carries one `offset`
      -- that read, readv, write, writev and lseek all rewrite in place,
      -- so copying it would give the two fds independent positions in
      -- BOTH directions, where `do_dup2` (fs/file.c, Linux v6.18.46)
      -- stores the one `struct file` at both and gives them one offset
      -- (the header above; Rocq `File.dup_modeled_entry`)
  | .FdPipe _ _ => false
  | .FdDevNull _ _ => true
  | .FdUrandom => true

/-- dup's injectable failures: fd-table exhaustion at RLIMIT_NOFILE
(EMFILE, `alloc_fd`, fs/file.c:591-593, Linux v6.18.46, commit
1f99e9ab748f — which also keeps the spec receptive when no free fd exists)
and a descriptor table the kernel cannot grow (ENOMEM, `alloc_fdtable`,
fs/file.c:162-243, at :242, reached through `expand_files` :288-320 and
`expand_fdtable` :252-279 from `alloc_fd` :596; Rocq notes its shape
changed at v6.13 from a bare NULL to an ERR_PTR, but the errno set
`alloc_fd` can raise did not — at v6.18.46 `alloc_fdtable` also answers
-EMFILE at :197 and :213, already in the set).  ENFILE is NOT among them:
dup allocates no `struct file` — it takes a second reference to an
existing one — so the system-wide open-file limit cannot bite.  EBADF is
not injectable either: fd validity IS tracked.  Rocq: `File.dup_errnos`. -/
def dup_errnos : List Int := [ENOMEM, EMFILE]

/-- `dup oldfd`: a second descriptor for `oldfd`'s description, at the
LOWEST free fd, returned.

ORDER, from `SYSCALL_DEFINE1(dup, unsigned int, fildes)`
(fs/file.c:1457-1470, Linux v6.18.46, commit 1f99e9ab748f): `fget_raw`
(:1460, defined :1088-1091) runs FIRST, so a closed `oldfd` is -EBADF
(:1459, :1469) BEFORE any allocation — `dup` of a bad fd on a full table
is -EBADF, never -EMFILE.  Only then does `get_unused_fd_flags(0)` (:1463)
take the lowest free slot (`lowest_fd`, i.e. `State.alloc_fd`), which is
where the two injectable failures live (:1466-1467 releases the reference
on either).  `fget_raw` (not `fget`) means an O_PATH fd is dup-able too;
the model has no O_PATH fds, so nothing turns on it.  The new descriptor's
close-on-exec bit is cleared, `flags` being 0 (`__set_open_fd`, :333, from
`alloc_fd` :606).

`oldfd` arrives already truncated to 32 bits (see `Syscall.fd32`), so
`dup(2^32)` duplicates stdin and `dup(-1)` is -EBADF.
Rocq: `File.dup_spec`. -/
def dup_spec (oldfd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) oldfd with
  | none => err_ret EBADF
  | some e =>
      if !(dup_modeled_entry e) then unmodeled
      else
        alt (er <- errno_from dup_errnos ;; err_ret er)  -- untracked env failure or no free fd
            (fd <- lowest_fd (m_fds m) ;;
             set_fds (fd_insert (m_fds m) fd e) ;;
             ret_only fd)

/-- `(flags & ~O_CLOEXEC) == 0` — `ksys_dup3`'s first test
(fs/file.c:1405-1406, Linux v6.18.46, commit 1f99e9ab748f), on the
TRUNCATED word.

The truncation (`Syscall.flag32`) is applied HERE rather than at the
dispatcher, where `fd32`/`whence32`/`cmd32` are applied, because here it
is the only thing separating this model from a kernel that tested the full
64-bit argument: `SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int,
newfd, int, flags)` (fs/file.c:1433-1436, Linux v6.18.46) discards the high
half, so `dup3(2, 1, 2^32)` returns 1.
`testing/syscall-check/tests/dup_spec.c`'s
`d3-flags-hi` pins that from both sides; a caller reaching `dup3_spec`
without the truncation would answer -EINVAL there and the conform case
would go red.  Rocq: `File.dup3_flags_ok`. -/
def dup3_flags_ok (flags : word) : Bool :=
  bv_unsigned (bv_and (flag32 flags) (bv_not (Z_to_bv 64 O_CLOEXEC))) = 0

/-- `newfd < rlimit(RLIMIT_NOFILE)`, `ksys_dup3`'s third test
(fs/file.c:1411-1412, Linux v6.18.46, commit 1f99e9ab748f), answered from
STATE: `State.m_nofile` carries the soft RLIMIT_NOFILE the run was
launched with.  Why the limit cannot move during a run, and which
registers and arms that absence is held by, is on Rocq's
`File.dup3_spec`; what it costs if that stops being true lands here.
Rocq: `File.dup3_newfd_under_limit`. -/
def dup3_newfd_under_limit (newfd : word) (m : Model) : Bool :=
  bv_unsigned newfd < bv_unsigned (m_nofile m)

/-- `dup3 oldfd newfd flags`: install `oldfd`'s description at `newfd`,
silently closing whatever `newfd` held, and return `newfd`.

ORDER, from `ksys_dup3` (fs/file.c:1399-1431, Linux v6.18.46, commit
1f99e9ab748f), followed exactly:

1. `(flags & ~O_CLOEXEC) != 0` is -EINVAL (:1405-1406), before anything
   else.
2. `oldfd == newfd` is -EINVAL (:1408-1409) — unconditionally, and BEFORE
   any validity test, which is where dup3 differs from dup2
   (`SYSCALL_DEFINE2(dup2)`, :1438-1455, answers that corner case itself
   at :1440-1453, returning `newfd` for an open fd).  The comparison is on
   the truncated fds, so `dup3(2^32, 0, 0)` is -EINVAL too.
3. `newfd >= rlimit(RLIMIT_NOFILE)` is -EBADF (:1411-1412).
4. `expand_files` is CALLED next (:1415), but its result is not read yet.
5. `oldfd` not open is -EBADF (:1416-1418, `goto Ebadf`) — tested BEFORE
   step 4's result, so a missing `oldfd` beats an `expand_files` failure.
   Only then is that result read (:1419-1423), and only its -EMFILE
   becomes -EBADF (:1420-1421); its -ENOMEM is returned verbatim (:1422).

STEP 3 IS ANSWERED FROM STATE (`dup3_newfd_under_limit`), and tested
where `ksys_dup3` tests it, before the `oldfd` lookup: both orders agree
wherever both fire, and testing it in the kernel's place is what makes
the case where they DISAGREE come out right — a process holding an fd at
or above its own soft limit, reachable when a parent lowers the limit and
execs.  The gate reads a value nothing modeled writes, and that absence
is REGISTERED rather than only written down: in the Lean table neither
`setrlimit` (164) nor `prlimit64` (261) has an arm, and
`Checks/Cases/Fs/File.lean` holds both declines in the shape
tools/check_decline_registers.py reads, so porting either collides there
instead of silently invalidating this gate — Rocq's `File.dup3_spec`
carries the same argument for its table, where `prlimit64_spec` has an
arm that declines every resource but RLIMIT_CORE, the shape a Lean port
of 261 has to keep.  The one kernel writer of the soft limit is
`do_prlimit` (kernel/sys.c:1500, Linux v6.18.46; `*rlim = *new_rlim` at
:1536), reached from both syscalls and from `setrlimit`'s compat twin,
which shares number 164 (`COMPAT_SYSCALL_DEFINE2(setrlimit)`,
kernel/sys.c:1577; `__SC_COMP`, include/uapi/asm-generic/unistd.h:440) and
so is covered by the number-keyed register.

WHAT IS STILL DECLINED, AND WHY.  A free `newfd` at or above
`Uapi.NR_OPEN_DEFAULT` and below the limit.  Linux answers it out of two
facts this model does not carry — the descriptor table's current
`max_fds` and the `sysctl_nr_open` ceiling — through `expand_files`
(fs/file.c:288-320, Linux v6.18.46), which returns -EMFILE for
`nr >= sysctl_nr_open` (:310-311, rewritten to -EBADF by step 5) and,
through `expand_fdtable` (:252-279) and `alloc_fdtable` (:162-243),
-ENOMEM for an allocation that fails (:242), -EMFILE for a ceiling
lowered meanwhile (:197) or for a table too large to allocate (:213, which
needs `nr > INT_MAX / sizeof(struct file *)` and so a `newfd` near 2^28).
Success, -EBADF and -ENOMEM are each reachable for any such `newfd`, so
the model can neither answer success nor pick an errno, and declines.

A FREE `newfd` BELOW `Uapi.NR_OPEN_DEFAULT` IS ANSWERED, deterministically:
that constant is a floor on the live table's `max_fds` (the argument is on
`Uapi.NR_OPEN_DEFAULT`), so `expand_files` takes its `nr < fdt->max_fds`
early return (:299-300), allocates nothing, and neither errno exists.
`do_dup2`'s -EBUSY (:1301-1302, :1313-1315) needs a descriptor reserved
by another thread in a shared table, and the `filp_close` of the
displaced description (:1308-1309; fs/open.c:1558-1566, Linux v6.18.46)
happens after the swap with its return value DISCARDED, so no error can
come from the close.  An already-open `newfd`
is by construction below the table's `max_fds`, so `expand_files` returns
0 for it too.

O_CLOEXEC is accepted and IGNORED: `do_dup2` records it in the table's
bitmap alone (`__set_open_fd(fd, fdt, flags & O_CLOEXEC)`, :1305), and no
modeled execution can read that bit back — the reasoning over `execve`
(221) and `fcntl` (25) is on Rocq's `File.dup3_spec`, and stands or falls
with `Fcntl.fcntl_spec`'s decision to decline `F_GETFD`.  The displaced
entry is dropped exactly as Rocq's `Open.close_spec` drops one; the Lean
tree has no `close` arm yet, and the one it gains has to drop it the
same way.

ONE THING THIS FILE DOES NOT FIX is the allocator's disregard of the very
limit this spec tests; `lowest_fd` above carries that argument and names
the bugs entry.

The two returns are `newfd` ZERO-extended, where `do_dup2` returns an
`int` (:1311) that sign-extends at or above 2^31.  Neither arm can reach
that on a table a run can build: the free one is bounded by the explicit
`NR_OPEN_DEFAULT` test, and the already-open one by a RUN INVARIANT rather
than a test of its own — every fd a run holds came from `State.alloc_fd`
(at most 4096) or from this spec's free arm (below 64).  That invariant,
not the limit test, is what is load-bearing, since a caller may reach this
spec with any `unsigned long` in `State.m_nofile` and any table.
Rocq: `File.dup3_spec`. -/
def dup3_spec (oldfd newfd flags : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if !(dup3_flags_ok flags) then err_ret EINVAL
  else if bv_eqb oldfd newfd then err_ret EINVAL
  else if !(dup3_newfd_under_limit newfd m) then err_ret EBADF
  else
    match fd_lookup (m_fds m) oldfd with
    | none => err_ret EBADF
    | some e =>
        if !(dup_modeled_entry e) then unmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | none =>
              -- free: answered only below the embedded table's floor
              if bv_unsigned newfd < NR_OPEN_DEFAULT
              then set_fds (fd_insert (m_fds m) newfd e) ;; ret_only newfd
              else unmodeled
          | some _ => set_fds (fd_insert (m_fds m) newfd e) ;; ret_only newfd

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
