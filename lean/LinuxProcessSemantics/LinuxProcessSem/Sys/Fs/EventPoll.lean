-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/EventPoll.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # LinuxProcessSem.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21), epoll_pwait (22)

This file answers to Linux `fs/eventpoll.c`: it holds what the kernel
defines there, and nothing else.  Which file a spec belongs in is
therefore not a judgement call — look up where the kernel defines the
syscall.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/EventPoll.lean`.

Each Linux decision carries its kernel citation — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f).  Every line cited here was
read in a checkout at that commit rather than copied across: the Rocq file
cites by FUNCTION and gives no line numbers, so the numbers below are this
file's and not a transcription.  The per-function version windows are
established in the Rocq header, including the warning that
`fs/eventpoll.c` is NOT frozen across the 6.18.x series (a rework lands
between v6.18.39 and v6.18.40 — read off both tags: 595 lines of
fs/eventpoll.c differ between them, and none between v6.18.40 and
v6.18.46).  The Linux citations below identify a particular version, not
merely "v6.18".

ON riscv64 THERE IS NO `epoll_create` AND NO `epoll_wait`.  The generic
64-bit syscall table carries `epoll_create1` (20), `epoll_ctl` (21) and
`epoll_pwait` (22) only; glibc and musl both compile `epoll_create(size)`
to `epoll_create1(0)` and `epoll_wait(...)` to `epoll_pwait(..., NULL, 0)`.
So the `size <= 0` check in `SYSCALL_DEFINE1(epoll_create, int, size)` is
unreachable here and is not modeled.

THE DESIGN declines `epoll_create1`'s SUCCESS arm, and everything else
follows from that one decision.  An epoll instance is an interest set plus
a ready list, and `ep_poll` reports READINESS over the descriptors in it.
This model fixes readiness by construction for exactly the descriptor kinds
that `epoll_ctl` REFUSES: `Select.bits_all_pollable` can answer for a file
or a directory because `vfs_poll` hands back the constant `DEFAULT_POLLMASK`
to any file with no `->poll` method, and `do_epoll_ctl` rejects precisely
those descriptors with -EPERM because `file_can_poll` tests that same NULL
`->poll`.  The two predicates partition the descriptor kinds, and epoll gets
the half this model cannot observe: a pipe's readiness is a function of what
the peer has written SO FAR, which is wall-clock arrival, and `m_stdin` says
which bytes will EVENTUALLY arrive, not which have.

THAT LEAVES A CHOICE, AND THE OBVIOUS ONE IS A TRAP.  A nullary
`State.FdEntry` constructor for an epoll fd would compile, and every
`epoll_ctl` that could populate an interest set would decline, so no
reachable state would have a non-empty one, so `epoll_pwait` could answer 0
on the empty set.  It is still the wrong shape, because the 0 rests on a
WHOLE-TREE ABSENCE claim — "no modeled transition populates an interest
set" — that the next change to this file silently falsifies.  So the
interest set is not represented, no `FdEntry` constructor denotes an epoll
instance, and `epoll_create1` declines the arm that would mint one.

WHAT THAT BUYS.  Because no fd in a modeled state is an epoll instance,
`is_file_epoll` is FALSE for every descriptor the model can hand these
syscalls — so both `epoll_ctl` and `epoll_pwait` reach their -EINVAL arm on
every input that gets that far, and neither has any reachable path into the
interest-set machinery at all.  What remains unanswered is small and is
named on the arm that answers it: `epoll_ctl` declines a CHANNEL target,
because whether a channel has a `->poll` is the one thing `fd_can_poll`
cannot decide; `epoll_pwait` declines a real signal mask, which `pselect6`
already declines for the same reason.  Every other input to either is
answered.

That reach is load-bearing on a fact about a different type, so it is
guarded by one: `fd_can_poll` is enumerated over `State.FdEntry` with no
wildcard, so a new constructor is a COMPILE ERROR here.

ONE IMPORT OF THE ROCQ FILE IS NOT MIRRORED, on purpose.  Rocq imports
`Fs.Select` for one reason, its own comment says: the Example
`fd_can_poll_is_select_pollable`, which pins that this file's `fd_can_poll`
and `Select.bits_all_pollable` stay complementary.  That Example is a check
and not a dependency of the semantics, and in the Lean tree every check
lives in `Checks/Cases/`, so its twin is `Checks/Cases/Fs/EventPoll.lean`'s
`fd_can_poll_is_select_pollable`, and THAT file imports `Sys.Fs.Select`.
The trusted specification here depends on nothing `Select` defines.

THREE PORT SPELLINGS preserve the Rocq computations:

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
`bugs/pselect6-unchecked-environment-obligations.md`. -/

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
distinguishes them sits past the -EINVAL this model always reaches first
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
  else some (errno_ret EINVAL)

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

/-- `epoll_ctl epfd op fd event` — the one outcome the model admits, or
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
   `event` is never dereferenced, however wild it is — `epds` is left
   uninitialised in that case and the DEL path never reads it.
2. -EBADF if `epfd` is not open: `CLASS(fd, f)(epfd)` and `fd_empty(f)`
   (:2520-2522).
3. -EBADF if the target is not open: `CLASS(fd, tf)(fd)` and
   `fd_empty(tf)` (:2525-2527).
4. -EPERM if the target has no `->poll`:

       if (!file_can_poll(fd_file(tf)))
               return -EPERM;                        (:2530-2531)

   This is the arm worth knowing, because it sits BEFORE the check that
   `epfd` is an epoll fd.  So `epoll_ctl` on two ordinary files answers
   -EPERM, not -EINVAL: the epfd's epoll-ness is not tested until step 5,
   and a reader who assumed -EINVAL wins because "epfd isn't an epoll fd"
   would have the errno wrong.  Between it and step 5 sits
   `ep_take_care_of_epollwakeup` (:2534-2535), which clears a bit of the
   copied struct and cannot fail.
5. -EINVAL otherwise:

       error = -EINVAL;
       if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
               goto error_tgt_fput;                  (:2542-2544)

   No `State.FdEntry` constructor denotes an epoll instance, so
   `is_file_epoll(fd_file(f))` (:478-481) is false for every descriptor
   reachable here and the SECOND disjunct always holds.  The first
   disjunct — the self-add check, which compares `struct file` identity and
   therefore also catches adding a `dup` of the epfd — is consequently
   never the reason, and the model needs no notion of description identity
   to get this errno right.

EVERYTHING PAST STEP 5 IS UNREACHABLE, which is why none of it appears
below: the `EPOLLEXCLUSIVE` rejections (:2551-2556), the `ep_loop_check`
-ELOOP, and the whole `switch (op)` with its -EEXIST and -ENOENT arms all
sit behind a `goto error_tgt_fput` that step 5 has already taken.  An
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

ONE ARM DECLINES, named where it is decided: step 4 on a CHANNEL target,
where `fd_can_poll` cannot say whether the far end has a `->poll`.  Every
other step answers. -/
def epoll_ctl_outcome (i : SyscallInput) (m : Model)
    (epfd op32 tfd event : word) : Option word :=
  let after_copy : Option word :=
    match fd_lookup (m_fds m) epfd with
    | none => some (errno_ret EBADF)
    | some _ =>
        match fd_lookup (m_fds m) tfd with
        | none => some (errno_ret EBADF)
        | some te =>
            match fd_can_poll te with
            | some false => some (errno_ret EPERM)
            | some true => some (errno_ret EINVAL)
            | none => none        -- a channel: see `fd_can_poll`
  if ep_op_has_event op32
  then if copy_from_user_ok i.in_mem event epoll_event_bytes
       then after_copy
       else some (errno_ret EFAULT)
  else after_copy

def epoll_ctl_spec (epfd op32 tfd event : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | none => unmodeled
  | some r => Monad.pure (mkEffect r [] [])

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

A mask that WOULD BE INSTALLED is `unmodeled`, not an answer: this model has
no signals, so it cannot represent `current->blocked` changing, nor the
`restore_saved_sigmask_unless` that puts it back.
`Select.pselect_sigpack` declines the identical case for the identical
reason. -/
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

/-- `epoll_pwait epfd events maxevents timeout sigmask sigsetsize` — the
one outcome the model admits, or `none`.

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
   (:2722-2724).  Note this precedes the `maxevents` check, which is the
   reverse of the `epoll_ctl` ordering and is worth stating because the two
   files' checks look interchangeable and are not.
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
6. -EINVAL if `epfd` is not an epoll fd (:2685-2686).  It is not, ever, for
   the reason the file header gives, so every call that reaches step 6
   answers -EINVAL and `ep_poll` is unreachable.

NOTHING IS WRITTEN ON ANY MODELED PATH.  `ep_poll` is the only writer of
the `events` array, through `ep_send_events`, and step 6 stops short of it.
The `access_ok` of step 5 is a range verdict and not a store. -/
def epoll_pwait_outcome (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : Option word :=
  match epoll_sigmask i.in_mem sigmask sigsetsize with
  | .EpSigBadSize => some (errno_ret EINVAL)
  | .EpSigFault => some (errno_ret EFAULT)
  | .EpSigReal => none
  | .EpSigNone =>
      match fd_lookup (m_fds m) epfd with
      | none => some (errno_ret EBADF)
      | some _ =>
          let n := sint32 maxevents32
          if n ≤ 0 then some (errno_ret EINVAL)
          else if EP_MAX_EVENTS < n then some (errno_ret EINVAL)
          else
            if access_okb events (n * epoll_event_bytes)
            then some (errno_ret EINVAL)
            else some (errno_ret EFAULT)

def epoll_pwait_spec (epfd events maxevents32 sigmask sigsetsize : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => unmodeled
  | some r => Monad.pure (mkEffect r [] [])

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
