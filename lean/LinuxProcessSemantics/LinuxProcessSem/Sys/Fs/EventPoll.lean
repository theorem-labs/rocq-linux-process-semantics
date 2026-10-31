import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
partial: epoll_ctl_outcome -- Lean declines ahead of the Rocq change in #1925 when either implementation declines or QEMU can answer differently; channel epfds can also decline after the target poll check.
partial: epoll_pwait_outcome -- Lean declines ahead of the Rocq change in #1925 on QEMU disagreement, channel epfds, or the TASK_SIZE-to-LONG_MAX gap; the base answer is declined too.
drift-ticket: epoll_pwait_outcome R-Fs-EventPoll-rebase -- Rocq now declines a closed epfd beside an out-of-bounds maxevents or an access_ok-refused events range (T139, #1442); baseline moves after the T139 PR lands -/

/-! # LinuxProcessSem.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21), epoll_pwait (22)

Starts from `theories/LinuxProcessSem/Sys/Fs/EventPoll.v` at the base.
The QEMU computations prepare #1925's Rocq changes, while Lean declines
every disagreement with Linux rather than extending the base answer set.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/EventPoll.lean`.

The original port kept Rocq's definition names. Here `epoll_ctl_linux`
and `epoll_pwait_linux` carry the base outcome computations, with the
channel-epfd and LONG_MAX-gap declines added. The public outcome names
now apply `ep_join`; the QEMU helpers have no counterparts in the base
Rocq file. The comments beside those additions give their rationale.
Each Linux decision carries its kernel citation — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f).  Every line cited here was
read in a checkout at that commit rather than copied across: the Rocq file
cites by FUNCTION and gives no line numbers, so the numbers below are this
file's and not a transcription.  The Rocq file was read at b08e59f8, the
2026-09-11 commit that carries the `FdUrandom` arm #712 added; the header
names a71fd38a, the squash that landed that day's work on `main`, at which
`EventPoll.v` is byte-identical to b08e59f8's: the arm is here.  The
base Linux arguments remain on the Rocq definitions; their per-function
version windows are established in the Rocq header, including
the warning that `fs/eventpoll.c` is NOT frozen across the 6.18.x series
(a rework lands between v6.18.39 and v6.18.40 — read off both tags: 595 lines
of fs/eventpoll.c differ between them, and none between v6.18.40 and
v6.18.46). The Linux citations below identify a particular version,
not merely "v6.18"; the QEMU additions name their own source version.

THE BASE DESIGN declines `epoll_create1`'s SUCCESS arm, as the Rocq header
explains, because an epoll instance is an interest set over exactly the descriptor kinds whose
readiness this model cannot observe, and a nullary `State.FdEntry`
constructor for one would let `epoll_pwait` answer 0 on a whole-tree
absence claim the next change to this file silently falsifies.  Because no
fd in a modeled state is an epoll instance, `is_file_epoll` is false for
every descriptor these syscalls can be handed except a channel, whose far
end can be one and which declines (`ep_epfd_is_channel`), so both
`epoll_ctl` and `epoll_pwait` reach their -EINVAL arm on the other inputs
that get that far, and nothing here enters the interest-set machinery.
`Checks/Cases/Fs/EventPoll.lean` pins the corresponding Lean-only declines
per descriptor kind, for example `pwait_file_epfd_declines`.
What remains declined is
named on the arm that declines it, including the closed-epfd parameter
conflicts whose Linux ordering changed in v6.15.

ONE IMPORT OF THE ROCQ FILE IS NOT MIRRORED, on purpose.  Rocq imports
`Fs.Select` for one reason, its own comment says: the Example
`fd_can_poll_is_select_pollable`, which pins that this file's `fd_can_poll`
and `Select.bits_all_pollable` stay complementary.  That Example is a check
and not a dependency of the semantics, and in the Lean tree every check
lives in `Checks/Cases/` (the mmap template: no theorem in a `Sys/` file),
so its twin is `Checks/Cases/Fs/EventPoll.lean`'s
`fd_can_poll_is_select_pollable`, and THAT file imports `Sys.Fs.Select`
(landed in PR #805).  The trusted specification here depends on nothing
`Select` defines.

THREE PORT SPELLINGS preserve the base computations, independently of
the additional decline gates:

- `epoll_create1_outcome` masks the flag word on the WORD (`bv_and`)
  where Rocq masks `bv_unsigned` of it in `Z` (`Z.land`).  The mask is the
  32-BIT complement of `EPOLL_CLOEXEC` in both: Rocq writes it
  `Z.lnot EPOLL_CLOEXEC mod 2 ^ 32`, this file `2 ^ 32 - 1 - EPOLL_CLOEXEC`,
  and the two are the same number (4294443007), so the mask tests agree on every
  word — including a word with bits at or above 32, which a 64-bit
  complement would refuse and Rocq's 32-bit one does not.
- Rocq's `Z.eqb`, `Z.leb` and `Z.ltb` become Lean's decidable `==`, `≤` and
  `<` on `Int`, as `Sys/Mm/Mmap.lean` does.
- `EpollSigmask`'s constructors are written `.EpSigNone` etc. at their use
  sites; the names are Rocq's.

THE ENVIRONMENT OBLIGATION `fd_can_poll`'s `some false` arms rest on is not
discharged here either: it is the obligation `Select.bits_all_pollable`
carries, stated at length on the Rocq definition and recorded in
`bugs/pselect6-unchecked-environment-obligations.md`.  The Lean tree has no
replay harness to discharge it per run, so it is carried here as it is
carried there.

WHOSE ORDER THESE ERRNOS ARE: Linux's and QEMU's. Lean declines ahead of the
Rocq change in #1925: an answered join requires every QEMU answer to equal
Linux's answer. The joined answer set can be restored after the Lean twin
ports #1925's joined answers. These Lean-only declines reduce coverage; they
add no answer beyond the base Rocq spec. A program reaching one cannot satisfy
the modeled conjunct of strong equivalence through this Lean spec.
QEMU 11.1.1's user-mode emulation of the same interface (linux-user/syscall.c
of that release, `case TARGET_NR_epoll_pwait` in `do_syscall1`
at :13973-14050 and the
`epoll_create1` arm at :13939-13940) tests `maxevents` and locks the events
range for writing before it reads the sigmask or resolves the epfd, and
drops from `epoll_create1`'s word every bit its `fcntl_flags_tbl` does not
carry (QEMU 11.1.1 linux-user/thunk.c, `target_to_host_bitmask_len`). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## The constants -/

/-- `EPOLL_CLOEXEC`, and it is `O_CLOEXEC` rather than a value of its own:
`include/uapi/linux/eventpoll.h:23` defines it as `O_CLOEXEC`, and
`do_epoll_create` (fs/eventpoll.c:2430-2471, Linux v6.18.46) opens with
`BUILD_BUG_ON(EPOLL_CLOEXEC != O_CLOEXEC)` (:2437), so the identity is
compile-enforced upstream rather than conventional.  Spelled through
`Uapi.O_CLOEXEC` here for the same reason. -/
def EPOLL_CLOEXEC : Int := O_CLOEXEC

/-- `EPOLL_CTL_DEL` (include/uapi/linux/eventpoll.h:27, Linux v6.18.46).
The other two opcodes are deliberately absent: nothing below compares
against `EPOLL_CTL_ADD` or `EPOLL_CTL_MOD`, because every arm that
distinguishes them sits past the -EINVAL or the channel-epfd decline that
this model reaches first
(`epoll_ctl_outcome`).  Naming them here would be a constant with no
consumer. -/
def EPOLL_CTL_DEL : Int := 2

/-- `sizeof(struct epoll_event)` on riscv64, and it is 16 rather than 12.
`EPOLL_PACKED` is `__attribute__((packed))` only under `#ifdef __x86_64__`
(include/uapi/linux/eventpoll.h:77-81, Linux v6.18.46); every other
architecture, riscv64 included, gets the empty definition, so the
`__u64 data` member of `struct epoll_event` (:83-86) takes its natural
8-byte alignment and the struct carries four bytes of padding at offsets
4..7.  `epoll_ctl` (fs/eventpoll.c:2658-2668, Linux v6.18.46) copies
`sizeof(struct epoll_event)` bytes (:2664), so it copies the padding too: an
`event` pointer with twelve readable bytes and an unreadable thirteenth is
-EFAULT. -/
def epoll_event_bytes : Int := 16

/-- `EP_MAX_EVENTS` (fs/eventpoll.c:222, Linux v6.18.46), which is
`INT_MAX / sizeof(struct epoll_event)` — so it is a function of the 16
above and is 134217727 here, not the 178956970 an x86-64 reader would
compute from a packed 12.  `INT_MAX` is `((int)(~0U >> 1))`
(include/vdso/limits.h:8, Linux v6.18.46), 2147483647, and the division is C integer
division. -/
def EP_MAX_EVENTS : Int := 134217727

/-! ## `file_can_poll`, per descriptor kind -/

/-- `file_can_poll` (include/linux/poll.h:73-76, Linux v6.18.46) per
descriptor kind: does this file have a non-NULL `->poll` method?  `none`
where the model cannot say.

ENUMERATED ON PURPOSE, no wildcard: a `_ => some false` catch-all would be
extensionally identical today and would silently absorb the next
`State.FdEntry` constructor — answering -EPERM for a descriptor epoll would
happily accept, which is a modeled WRONG ANSWER rather than a decline — and
an epoll-instance constructor absorbed here would leave `epoll_ctl_outcome`
and `epoll_pwait_outcome` asserting -EINVAL for an epfd that IS an epoll
fd, silently converting the file header's reach argument into a false one.
Listing the kinds makes a new constructor a compile error instead, at the
site whose answer decides both.

WHY THIS IS AN `Option Bool` AND NOT A `Bool`: `FdChannel`.  The model does
not know what a channel's far end is (the direction is "an ASSUMPTION about
the environment rather than a fact about the fd number",
`bugs/channel-fds-assume-unidirectional-stdio.md`).  A pipe, a terminal and
a socket all define `->poll`; a REGULAR FILE and /dev/null do not —
`null_fops` (drivers/char/mem.c:644-652, Linux v6.18.46) carries `.llseek`, `.read`,
`.write`, `.read_iter`, `.write_iter`, `.splice_write` and `.uring_cmd`,
and no `.poll`.  So a channel spans both answers, and committing to either
is a guess: `some true` would answer -EINVAL where Linux answers -EPERM for
a file-backed or /dev/null channel, and `some false` would do the reverse
for a pipe.  Plain shell redirection gives a program a regular file or
/dev/null on fd 0 or 1 with no harness involved, so the wrong answer is one
a reference program's launcher can reach.  The argument in full, including
the earlier version of this arm that got it wrong, is on Rocq's
`EventPoll.fd_can_poll`.

THE `some false` ARMS ARE AN ENVIRONMENT OBLIGATION, the same one
`Select.bits_all_pollable` carries: no directory `file_operations` in the
tree defines `->poll`, and neither do the regular-file operations of the
ordinary on-disk and in-memory filesystems — but procfs, sysctl, kernfs,
debugfs, tracefs, securityfs, POSIX message queues, ocfs2 dlmfs and FUSE all
install one on `S_IFREG` inodes, so this is a premise about the IMAGE and
not a fact about `S_IFREG`.

THE `FdSocket` AND `FdPipe` ARMS NEED NO OBLIGATION, and they are the only
ones that do not.  A socket's file is minted by `sock_alloc_file`
(net/socket.c:476-501, Linux v6.18.46, at :483-485) with `socket_file_ops` (:156-173),
whose `.poll` is `sock_poll` (:1426-1445), set at line 160, unconditionally,
on every address family.  A pipe end gets `pipeanon_fops`
(fs/pipe.c:1257-1266, Linux v6.18.46) when `create_pipe_files`
(:926-980, at :946 and :957) mints it and `pipefifo_fops` (:1246-1255) when
a FIFO is opened; BOTH carry `.poll = pipe_poll` (:1261, :1250).  What
separates these two from `FdChannel` is not the kernel but the model: it
KNOWS these descriptors are a socket and a pipe, because it minted them
itself. -/
def fd_can_poll (e : FdEntry) : Option Bool :=
  match e with
  | .FdFile _ _ | .FdFileW _ _ | .FdFileA _ _ | .FdFileRW _ _ | .FdDir => some false
  | .FdSocket _ | .FdPipe _ _ => some true
  | .FdChannel _ => none
  | .FdDevNull _ _ => none
      -- FAIL-CLOSED, though the answer is exact and this file already
      -- states it: `null_fops` (drivers/char/mem.c:644-652, v6.18.46) has
      -- no `.poll`, so `file_can_poll` is false and `epoll_ctl` ADD is
      -- -EPERM (fs/eventpoll.c:2530-2531) — the `some false` the file kinds
      -- carry, with no environment obligation at all.  Declined until
      -- written with its own probe, as Rocq declines it.
  | .FdUrandom => none
      -- FAIL-CLOSED, and the answer is again exact: `urandom_fops`
      -- (drivers/char/random.c:1572-1581, v6.18.46) has no `.poll` either
      -- — `random_fops` (:1560-1570) has one, `random_poll` at :1563; the
      -- urandom table does not — so `file_can_poll` is false and
      -- `epoll_ctl` ADD is the same -EPERM.  Declined until written with
      -- its own probe, as Rocq declines it.

/-! ## epoll_create1 (20) -/

/-- QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, translates create flags
through `fcntl_flags_tbl`.
QEMU 11.1.1 linux-user/thunk.c, `target_to_host_bitmask_len`, sets the host
bits of matching rows.
Words with no matching row can create a descriptor where Linux v6.18.46
fs/eventpoll.c, `do_epoll_create`, returns EINVAL.
The gate selects translations retaining a host bit outside `O_CLOEXEC`.

QEMU 11.1.1 linux-user/syscall.c, `fcntl_flags_tbl`, matches access modes
`O_WRONLY` (1) and `O_RDWR` (2) as a pair of bits.
Its single-bit rows use riscv64's linux-user/generic/fcntl.h values.
The mask includes `O_CREAT` through `O_NONBLOCK` (0xFC0).
It includes `O_DSYNC`, `FASYNC`, and `O_DIRECT` (0x7000).
It includes `O_DIRECTORY`, `O_NOFOLLOW`, and `O_NOATIME` (0x70000).
It includes `O_PATH` (0x200000).
A set `O_DSYNC` bit matches the `O_DSYNC` row or the `O_SYNC` row.
The mask excludes `O_LARGEFILE` (0x8000), whose host value is zero on a
64-bit host.
It excludes `__O_SYNC` (0x100000) and `__O_TMPFILE` (0x400000), which match
no row alone. -/
def qemu_epoll_flags_rejected (flags32 : word) : Bool :=
  let acc := bv_unsigned (bv_and flags32 3)
  acc == 1 || acc == 2 || !(bv_unsigned (bv_and flags32 0x277FC0) == 0)

/-- `do_epoll_create` (fs/eventpoll.c:2430-2471, Linux v6.18.46):

    if (flags & ~EPOLL_CLOEXEC)
            return -EINVAL;                       (:2439-2440)
    error = ep_alloc(&ep);                        (:2444)
    ...
    fd = get_unused_fd_flags(O_RDWR | (flags & O_CLOEXEC));   (:2451)

ORDER, and it is the only behaviour this arm has: the flag word is judged
BEFORE `ep_alloc` and before any descriptor is reserved.  So a rejected
`epoll_create1` allocates nothing, consumes no fd number, and cannot answer
-ENOMEM or -EMFILE — the two errnos that follow it are unreachable on this
path rather than merely unmodeled.

`flags` is an `int` in `SYSCALL_DEFINE1(epoll_create1, int, flags)`
(fs/eventpoll.c:2473-2476, Linux v6.18.46), so the register's high half is discarded before
a bit is read; the dispatcher applies `Syscall.flag32` and this function
sees the low 32 bits.  The mask is taken over 32 bits accordingly (the file
header says how it is spelled): a `flags` of 2^32 is 0 after truncation and
is ACCEPTED, where a 64-bit mask would reject it.

THE SUCCESS ARM IS DECLINED, for the reason the file header gives: minting
an epoll fd needs a `State.FdEntry` constructor, and the only constructor
available without a readiness notion is a nullary one whose correctness
rests on an absence claim the next change falsifies.  So this syscall is
modeled on its rejecting half and nowhere else, and a program that
successfully creates an epoll fd leaves the modeled surface at that
call. -/
def epoll_create1_outcome (flags32 : word) : Option word :=
  if bv_unsigned (bv_and flags32 (Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC))) == 0
  then none                            -- a well-formed create: declined
  else if qemu_epoll_flags_rejected flags32 then some (errno_ret EINVAL)
  else none

def epoll_create1_spec (flags32 : word) : Sys SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | none => unmodeled
  | some r => Monad.pure (mkEffect r [] [])

/-! ## The shared `copy_from_user` verdict -/

/-- What a fixed-size `copy_from_user` does, in two answers.

`copy_from_user` (include/linux/uaccess.h:204-214, Linux v6.18.46) reaches
`_inline_copy_from_user` (:158-185) — on riscv64 through lib/usercopy.c's
`_copy_from_user` (:16-19, Linux v6.18.46), the `#else` branch of :209-213,
since nothing under arch/riscv defines `INLINE_COPY_FROM_USER`
(include/asm-generic/uaccess.h:94 does, Linux v6.18.46, for the
architectures that take that header) — which runs `access_ok(from, n)`
(:168) and jumps to its failure path when that fails, so the RANGE check
comes first and a range it rejects faults without a byte being read.
riscv64 takes that branch rather than the `can_do_masked_user_access()`
one: `masked_user_access_begin` is not defined in
arch/riscv/include/asm/uaccess.h at the pinned commit, so
include/linux/uaccess.h:36-42 (Linux v6.18.46; the `#else` half, :38-41) gives
`can_do_masked_user_access()` the value 0 and the address is never clamped.

`true` when the range check passes (`State.access_okb`, the kernel's own
`__access_ok` of include/asm-generic/access_ok.h:31-41, Linux v6.18.46,
with `State.TASK_SIZE` as its limit) and every byte is mapped; `false` — -EFAULT
— when the range check fails, or when it passes and some byte is unmapped.

THE `access_okb` CONJUNCT IS ALSO WHAT RULES OUT THE WRAP.
`State.read_bytes_map` walks in WORD arithmetic and wraps at 2^64, so a
16-byte read at 2^64 - 8 would read eight bytes from the top of the address
space and eight from address 0 and report success, where the kernel's
`access_ok` rejects the range outright (`__access_ok`'s subtraction, :40).
Testing the range before reading is what stops that here; see
`bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md` for the sites
where it is not yet tested.

IT IS `State.copy_bytes_map`'S VERDICT, spelled by hand because Rocq spells
it by hand: Rocq's `State.copy_bytes_map` names `EventPoll.copy_from_user_ok`
as one of the two callers still to move onto it.  Until Rocq moves it this
definition stays its twin, and `Checks/Cases/Fs/EventPoll.lean`'s
`copy_from_user_ok_is_copy_bytes_map` is what would notice the two
diverging. -/
def copy_from_user_ok (mp : word → Option byte) (a : word) (len : Int) : Bool :=
  access_okb a len
  && match read_bytes_map mp a (Z_to_bv 64 len) with
     | some _ => true
     | none => false

/-! ## epoll_ctl (21) -/

/-- Until #1925 lands, disagreement declines the entire input shape, including
Linux's answer. Keep the pair representation so porting #1925's joined answers changes only this join. -/
def ep_join (l : Option word) (q : Option (List word)) : Option (word × List word) :=
  match l, q with
  | some r, some rs => if rs.all (bv_eqb r) then some (r, []) else none
  | _, _ => none

def ep_answer (o : word × List word) (r : word) : Prop :=
  r = o.1 ∨ r ∈ o.2

def ep_answerb (o : word × List word) (r : word) : Bool :=
  bv_eqb r o.1 || o.2.any (bv_eqb r)

def ep_bytes_defined (mp : word → Option byte) (a : word) (len : Int) : Bool :=
  match read_bytes_map mp a (Z_to_bv 64 len) with
  | some _ => true
  | none => false

/-- QEMU 11.1.1 linux-user/uaccess.c, `lock_user`, checks access before
copying.
Its linux-user/qemu.h, `access_ok_untagged`, asks
`guest_range_valid_untagged` and `page_check_range` for the needed
permissions.
Read locks require `PAGE_READ`.
Write locks require `PAGE_READ | PAGE_WRITE`.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, answers failed epoll locks
with EFAULT.

The model bounds that verdict with `qemu_lock_may` and `qemu_lock_sure`.
The former requires a nonwrapping range defined in the view the lock needs.
Reads use `in_mem`.
Writes use `in_wmem`.
QEMU 11.1.1 include/user/guest-host.h,
`guest_range_valid_untagged_vaddr`, refuses a last byte above
`guest_addr_max`.
That limit stays below 2^64.
The sure gate adds `access_okb`, Socket’s `load_write_free`, and
`ep_stack_band_free`.
The arms include EFAULT unless the lock is sure.
They include later answers when the lock may succeed. -/
def qemu_lock_may (i : SyscallInput) (write : Bool) (a : word) (len : Int) : Bool :=
  decide (bv_unsigned a + len ≤ 2 ^ 64) &&
    ep_bytes_defined (if write then i.in_wmem else i.in_mem) a len

/-- The range misses the entry-stack band `[init_sp - stack_max_size,
init_sp)`.
`Run.init_machine_state` fills that band with zeros in both views.
QEMU's stack need not cover that band.
QEMU 11.1.1 linux-user/main.c, `handle_arg_stack_size`, lets `-s` or
`QEMU_STACK_SIZE` lower the default 8 MiB `guest_stack_size`.
QEMU 11.1.1 linux-user/elfload.c, `setup_arg_pages`, maps that size above a
`PROT_NONE` guard page.
The entry sp lies inside the stack.
The band's low end can lie in the guard page or below the stack.
A lock there can fail, so the model counts no band byte as sure. -/
def ep_stack_band_free (m : Model) (a : word) (len : Int) : Bool :=
  let sp := bv_unsigned (m_vmmaps m).vm_init_sp
  decide (bv_unsigned a + len ≤ sp - stack_max_size) ||
    decide (sp ≤ bv_unsigned a)

def qemu_lock_sure (i : SyscallInput) (m : Model) (write : Bool)
    (a : word) (len : Int) : Bool :=
  access_okb a len && qemu_lock_may i write a len
    && LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket.load_write_free
      (m_vmmaps m).vm_reserved i.in_wmem a (Z_to_bv 64 len)
    && ep_stack_band_free m a len

def qemu_after_lock (i : SyscallInput) (m : Model) (write : Bool)
    (a : word) (len : Int) (later : Option (List word)) : Option (List word) :=
  if !(qemu_lock_may i write a len) then some [errno_ret EFAULT]
  else if qemu_lock_sure i m write a len then later
  else match later with
    | some rs => some (errno_ret EFAULT :: rs)
    | none => none

/-- `ep_op_has_event(op)` is `op != EPOLL_CTL_DEL`
(include/linux/eventpoll.h:64-67, Linux v6.18.46), and it decides whether
the syscall entry copies the event struct at all.  `op` is an `int`, so the
comparison is over the low 32 bits: a register whose low half is 2 and
whose high half is set is still `EPOLL_CTL_DEL` to the kernel, because
`SYSCALL_DEFINE4` casts the argument to `int` on the way in
(`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-97, the cast at :88,
through `__SC_CAST`, include/linux/syscalls.h:132, both Linux v6.18.46) and
the high half is
gone before `op` is ever compared.  THIS FUNCTION does not narrow — it is
handed an already-narrowed word.  `Syscall.int32`, applied once in the
dispatcher arm, is that cast. -/
def ep_op_has_event (op32 : word) : Bool :=
  !(bv_unsigned op32 == EPOLL_CTL_DEL)

/-- A channel can be an epoll instance.  Whoever runs the process can hand
it an epoll fd on fd 0, 1 or 2: an epoll fd made without `EPOLL_CLOEXEC`
survives `execve`.  The model knows no channel's far end (`fd_can_poll`),
so `is_file_epoll` is unknown for a channel epfd.  Each arm declines at the
step that asks it (fs/eventpoll.c `do_epoll_ctl`, `ep_check_params`, Linux
v6.18.46). -/
def ep_epfd_is_channel (e : FdEntry) : Bool :=
  match e with
  | .FdChannel _ => true
  | _ => false

def epoll_ctl_after_copy (m : Model) (epfd tfd : word) : Option word :=
  match fd_lookup (m_fds m) epfd with
  | none => some (errno_ret EBADF)
  | some ee =>
      match fd_lookup (m_fds m) tfd with
      | none => some (errno_ret EBADF)
      | some te =>
          match fd_can_poll te with
          | some false => some (errno_ret EPERM)
          | some true =>
              -- `do_epoll_ctl` (fs/eventpoll.c, Linux v6.18.46) tests
              -- `is_file_epoll(f)` here.  For an epoll epfd it goes on to the
              -- `switch (op)` and can answer 0, so a channel epfd declines.
              if ep_epfd_is_channel ee then none else some (errno_ret EINVAL)
          | none => none        -- a channel: see `fd_can_poll`

/-- `epoll_ctl epfd op fd event` — the Linux outcome, or
`none` where it declines.

The arms are in the kernel's own decision order, so reading them top to
bottom is reading `epoll_ctl` (fs/eventpoll.c:2658-2668, Linux v6.18.46)
and then `do_epoll_ctl` (:2511-2651) in sequence.

1. `epoll_ctl` copies the event struct BEFORE calling `do_epoll_ctl`, hence
   before any descriptor is looked up:

       if (ep_op_has_event(op) &&
           copy_from_user(&epds, event, sizeof(struct epoll_event)))
               return -EFAULT;                       (:2663-2665)

   So -EFAULT on a bad `event` pointer BEATS -EBADF on `epfd`, -EBADF on
   the target, and -EPERM.  For `EPOLL_CTL_DEL` no copy happens and
   `event` is never dereferenced, however wild it is.
2. -EBADF if `epfd` is not open: `CLASS(fd, f)(epfd)` and `fd_empty(f)`
   (:2520-2522).
3. -EBADF if the target is not open: `CLASS(fd, tf)(fd)` and
   `fd_empty(tf)` (:2525-2527).
4. -EPERM if the target has no `->poll`:

       if (!file_can_poll(fd_file(tf)))
               return -EPERM;                        (:2530-2531)

   This is the arm worth knowing, because it sits BEFORE the check that
   `epfd` is an epoll fd.  So `epoll_ctl` on two ordinary files answers
   -EPERM, not -EINVAL.  Between it and step 5 sits
   `ep_take_care_of_epollwakeup` (:2534-2535), which clears a bit of the
   copied struct and cannot fail.
5. -EINVAL otherwise:

       error = -EINVAL;
       if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
               goto error_tgt_fput;                  (:2542-2544)

   No `State.FdEntry` constructor denotes an epoll instance, so
   `is_file_epoll(fd_file(f))` (:478-481) is false for every descriptor
   reachable here except a channel, which declines (`ep_epfd_is_channel`),
   and the SECOND disjunct holds for the others (`ctl_socket_target_is_einval`
   and `ctl_socket_on_itself_is_einval` pin it).  The first
   disjunct — the self-add check — is consequently never the reason, and
   the model needs no notion of description identity to get this errno
   right.

EVERYTHING PAST STEP 5 IS UNREACHABLE, which is why none of it appears
below: the `EPOLLEXCLUSIVE` rejections (:2551-2556), the `ep_loop_check`
-ELOOP, and the whole `switch (op)` with its -EEXIST and -ENOENT arms all
sit behind a `goto error_tgt_fput` that step 5 has already taken, or
behind step 5's channel-epfd decline.  An
unrecognised `op` is likewise -EINVAL through step 5 rather than through
the switch's fallthrough — the same errno by a different route, which is
why `op` is read here only to decide whether the event struct is copied.

THE CONTENTS OF THE EVENT STRUCT ARE NEVER USED, only its readability: this
arm needs the copy's VERDICT and not its bytes.  It nevertheless records no
copy-in, and that is a KNOWN-WRONG OMISSION rather than a consequence of
the bytes being unused — `State.eff_copyins` feeds the lazy-page accounting,
so a 16-byte `event` on a mapped-but-never-touched anonymous page is
faulted in and charged by Linux and not by this model.
`bugs/epoll-ctl-copyin-not-recorded.md` records it, and that `pselect6` has
the identical omission.

TWO ARMS DECLINE, named where each is decided: step 4 on a CHANNEL target,
where `fd_can_poll` cannot say whether the far end has a `->poll`, and
step 5 on a CHANNEL epfd (`ep_epfd_is_channel`).  Every other step
answers. -/
def epoll_ctl_linux (i : SyscallInput) (m : Model)
    (epfd op32 tfd event : word) : Option word :=
  if ep_op_has_event op32
  then if copy_from_user_ok i.in_mem event epoll_event_bytes
       then epoll_ctl_after_copy m epfd tfd
       else some (errno_ret EFAULT)
  else epoll_ctl_after_copy m epfd tfd

/-- QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, compares the raw
operation before locking a non-NULL event. -/
def epoll_ctl_qemu (i : SyscallInput) (m : Model)
    (epfd op32 tfd event : word) : Option (List word) :=
  let host := (epoll_ctl_after_copy m epfd tfd).map (fun r => [r])
  if w_is0 event then
    if ep_op_has_event op32 then some [errno_ret EFAULT] else host
  else if bv_unsigned (in_arg i 1) == EPOLL_CTL_DEL then host
  else qemu_after_lock i m false event epoll_event_bytes host

/-- `epoll_ctl epfd op fd event` returns the Linux answer alone when every QEMU answer agrees, or
`none` when either computation declines or the answers disagree. -/
def epoll_ctl_outcome (i : SyscallInput) (m : Model)
    (epfd op32 tfd event : word) : Option (word × List word) :=
  ep_join (epoll_ctl_linux i m epfd op32 tfd event)
    (epoll_ctl_qemu i m epfd op32 tfd event)

def epoll_ctl_spec (epfd op32 tfd event : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | none => unmodeled
  | some o =>
      r <- choose (ep_answer o) ;;
      Monad.pure (mkEffect r [] [])

/-! ## epoll_pwait (22) -/

/-- `set_user_sigmask` (kernel/signal.c:3281-3297, Linux v6.18.46), in its
own order:

    if (!umask)
            return 0;                                 (:3285-3286)
    if (sigsetsize != sizeof(sigset_t))
            return -EINVAL;                           (:3287-3288)
    if (copy_from_user(&kmask, umask, sizeof(sigset_t)))
            return -EFAULT;                           (:3289-3290)

NULL is tested BEFORE the size, so a NULL mask installs nothing whatever
size sits beside it: the `_NSIG/8` = 8 that musl's and glibc's `epoll_pwait`
wrappers pass beside the NULL when `epoll_wait` compiles to them on riscv64
(which has no `epoll_wait` number), or the 0 of a hand-written call.
Modeling only the size-8 case would leave the hand-written call outside the
modeled surface; modeling only the NULL-with-0 case would leave every
libc's `epoll_wait` outside it.

`sigsetsize` is a `size_t` and is compared FULL WIDTH, so it is not
narrowed by the dispatcher; a register whose low half is 8 and whose high
half is set is the wrong size.  `Uapi.kernel_sigset_bytes` is the 8.

A mask that WOULD BE INSTALLED is `unmodeled`, not an answer.
`Select.pselect_sigpack` declines the identical case. -/
inductive EpollSigmask
  /-- `umask` is NULL: nothing installed -/
  | EpSigNone
  /-- wrong `sigsetsize`: -EINVAL -/
  | EpSigBadSize
  /-- `umask` unreadable: -EFAULT -/
  | EpSigFault
  /-- a mask that would be installed: unmodeled -/
  | EpSigReal

def epoll_sigmask (mp : word → Option byte) (umask sigsetsize : word) : EpollSigmask :=
  if w_is0 umask then .EpSigNone
  else if !(bv_unsigned sigsetsize == kernel_sigset_bytes) then .EpSigBadSize
  else if copy_from_user_ok mp umask kernel_sigset_bytes then .EpSigReal
  else .EpSigFault

/-- Linux v6.18.46 include/asm-generic/access_ok.h [__access_ok] tests `size <= limit`
first because its subtraction is unsigned.
Over `Int`, the address test implies the size test because `bv_unsigned base` is nonnegative. -/
def access_ok_long_max (base : word) (len : Int) : Bool :=
  decide (bv_unsigned base ≤ 2 ^ 63 - 1 - len)

/-- `epoll_pwait epfd events maxevents timeout sigmask sigsetsize` — the
Linux outcome, or `none`.

ORDER, read off `epoll_pwait` (fs/eventpoll.c:2774-2783, Linux v6.18.46),
`do_epoll_pwait` (:2753-2772), `do_epoll_wait` (:2715-2738) and
`ep_check_params` (:2670-2689):

1. `ep_timeout_to_timespec(&to, timeout)` (:2118-2137) is an ARGUMENT to
   `do_epoll_pwait` (:2780-2782), so it runs first — and it cannot fail.
   It is also the only reader of `timeout`, and its result reaches only
   `ep_poll` (:2737), which no modeled path enters.  So `timeout` is not
   an argument of this function at all: no arm below depends on it,
   including the arms that would sleep.
2. `set_user_sigmask` (:2763-2765) — the first fallible step, and it
   precedes the epfd lookup.  A bad sigmask therefore BEATS a bad `epfd`.
3. -EBADF if `epfd` is not open: `CLASS(fd, f)(epfd)` and `fd_empty(f)`
   (:2722-2724).  Since v6.15 this precedes the parameter checks; through
   v6.14 it followed them, so the closed-fd arm below declines the shapes
   for which that changes the errno.
4. -EINVAL if `maxevents <= 0 || maxevents > EP_MAX_EVENTS` (:2674-2675).
   `maxevents` is an `int`, read signed (`Syscall.sint32`), and the `<= 0`
   half refuses every non-positive value before the bound is consulted.
   The second half would refuse a negative value too — `EP_MAX_EVENTS` has
   type `size_t` through its `sizeof`, so the comparison promotes
   `maxevents` to `unsigned long`, and a negative value becomes one far
   above the bound — so the errno is -EINVAL whichever half fires; what the
   signed reading fixes is that no negative `maxevents` reaches the range
   test of step 5 or the product in it.  (Rocq's comment says the order
   inside the `||` is load-bearing; it is not: both halves reject a
   negative value.)
5. -EFAULT if `access_ok(evs, maxevents * sizeof(struct epoll_event))`
   fails (:2678-2679).  The product is computed in 64-bit unsigned
   arithmetic (the `int` promotes to `size_t`) and CANNOT overflow, because
   step 4 has already bounded `maxevents` by `INT_MAX / 16`.  This is a
   pure RANGE check — Linux reads no byte and requires no mapping — and so
   is the model's: `State.access_okb` on the product, with no walk.
6. -EINVAL if `epfd` is not an epoll fd (:2685-2686).  It is not, for the
   reason the file header gives, unless `epfd` is a channel, which declines
   (`ep_epfd_is_channel`).  So the other calls that reach step 6
   have Linux answer -EINVAL and never reach `ep_poll`. The joined spec
   can still decline: `pwait_file_epfd_declines` and its siblings pin
   those Lean-only declines per descriptor kind.

NOTHING IS WRITTEN ON ANY MODELED PATH.  `ep_poll` is the only writer of
the `events` array, and step 6 stops short of it.  The `access_ok` of step
5 is a range verdict and not a store. -/
def epoll_pwait_linux (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : Option word :=
  match epoll_sigmask i.in_mem sigmask sigsetsize with
  | .EpSigBadSize => some (errno_ret EINVAL)
  | .EpSigFault => some (errno_ret EFAULT)
  | .EpSigReal => none
  | .EpSigNone =>
      match fd_lookup (m_fds m) epfd with
      | none =>
          /- Commit 6b47d35d4d9e moved the lookup ahead of parameter
          validation: fs/eventpoll.c:do_epoll_wait read at v6.15 and
          v6.18.46 returns -EBADF here even with bad parameters.  The same
          function read at v4.17, v5.10, v6.1, v6.12 and v6.14 checks the
          count first, giving -EINVAL for bad counts.  For a range past
          TASK_SIZE, v6.1's access_ok uses TASK_SIZE and gives -EFAULT.
          On riscv64, arch/riscv/include/asm/pgtable.h defines TASK_SIZE_MAX
          as LONG_MAX from ad5643cf2f69 until 890ba5be6335, so v6.14 passes
          that range.  `case TARGET_NR_epoll_pwait` in `do_syscall1`
          (linux-user/syscall.c, QEMU 11.1.1) checks the count and lock_user()s
          the events buffer before the host call, giving -EINVAL or -EFAULT
          too.  Neither answer is certain for these conflicting shapes;
          when both checks pass every kernel ordering gives -EBADF. -/
          let n := sint32 maxevents32
          if n ≤ 0 then none
          else if EP_MAX_EVENTS < n then none
          else if access_okb events (n * epoll_event_bytes)
               then some (errno_ret EBADF)
               else none
      | some e =>
          let n := sint32 maxevents32
          if n ≤ 0 then some (errno_ret EINVAL)
          else if EP_MAX_EVENTS < n then some (errno_ret EINVAL)
          else if access_okb events (n * epoll_event_bytes)
               then
                 -- `ep_check_params` (fs/eventpoll.c, Linux v6.18.46) tests
                 -- `is_file_epoll` last.  For an epoll epfd `ep_poll` runs and can
                 -- answer 0 or a count, so a channel epfd declines
                 -- (`ep_epfd_is_channel`).
                 if ep_epfd_is_channel e then none else some (errno_ret EINVAL)
               else if access_ok_long_max events (n * epoll_event_bytes)
                    /- Linux v6.14 arch/riscv/include/asm/pgtable.h uses
                    LONG_MAX for TASK_SIZE_MAX.
                    Its fs/eventpoll.c, do_epoll_wait, reaches EINVAL here.
                    Linux v6.18.46 fs/eventpoll.c, do_epoll_wait, rejects
                    the range with EFAULT. -/
                    then none
                    else some (errno_ret EFAULT)

/-- QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, checks count, events
lock, allocation, mask, then host descriptor. -/
def epoll_pwait_qemu (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : Option (List word) :=
  let n := sint32 maxevents32
  let later :=
    (if w_is0 sigmask then
        match fd_lookup (m_fds m) epfd with
        | none => some [errno_ret ENOMEM, errno_ret EBADF]
        | some e => if ep_epfd_is_channel e then none
                    else some [errno_ret ENOMEM, errno_ret EINVAL]
    else if !(bv_unsigned sigsetsize == kernel_sigset_bytes)
         then some [errno_ret ENOMEM, errno_ret EINVAL]
         /- `process_sigsuspend_mask` (linux-user/signal.c), called by
         `do_syscall1` (linux-user/syscall.c, QEMU 11.1.1), uses a read
         lock, not Linux's `access_ok`.
         Defined bytes past `TASK_SIZE` can therefore reach mask
         installation.  The model cannot represent that signal state,
         so even a possible successful lock must decline. -/
         else if qemu_lock_may i false sigmask 8 then none
              else some [errno_ret ENOMEM, errno_ret EFAULT])
  if decide (n ≤ 0) || decide (EP_MAX_EVENTS < n) then some [errno_ret EINVAL]
  else qemu_after_lock i m true events (n * epoll_event_bytes) later

/-- `epoll_pwait epfd events maxevents timeout sigmask sigsetsize` returns
the Linux answer alone when every QEMU answer agrees, or `none`
where either computation declines or the answers disagree. -/
def epoll_pwait_outcome (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : Option (word × List word) :=
  ep_join (epoll_pwait_linux i m epfd events maxevents32 sigmask sigsetsize)
    (epoll_pwait_qemu i m epfd events maxevents32 sigmask sigsetsize)

def epoll_pwait_spec (epfd events maxevents32 sigmask sigsetsize : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => unmodeled
  | some o =>
      r <- choose (ep_answer o) ;;
      Monad.pure (mkEffect r [] [])

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
