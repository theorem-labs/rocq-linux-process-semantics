import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # Checks.Cases.Fs.EventPoll — what epoll_create1, epoll_ctl and epoll_pwait answer, read off against Linux

Worked examples over `Sys.Fs.EventPoll`'s three specs.  Rocq keeps no
worked-cases file for them at the commit the header names (its
`theories/LinuxProcessSem/Checks/Cases/Fs/` directory has none), and sends
every claim to a probe against a real kernel
(`testing/syscall-check/tests/epoll_spec.c`). Lean replay now judges the
recorded traces too; the spec pins stay here and the checker pins live in
`Checks/Cases/Checks/Sys/Fs/EventPoll.lean`.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ, and
observable-answer claims follow Linux or QEMU source, with the citation
beside it — fs/eventpoll.c at Linux v6.18.46 (commit 1f99e9ab748f) unless
another file is named, the function and line on each pin.

QEMU 11.1.1 citations name their file and function, linux-user/syscall.c
`do_syscall1` unless another is named, and carry no line.

HOW THESE ARE STATED.  A check is stated on the relation itself
(`Checks/Cases/Mm/Mmap.lean`'s header says why): an `iff` over EVERY
outcome `o`,

    epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model []

pins the positive half (-EPERM is admitted, the model and the event list
untouched) and the negative half (nothing else is — not another errno, not
a write, not `Unmodeled`) in one statement.  `epoll_create1` answers with
a single outcome; `epoll_ctl` and `epoll_pwait` decline whenever QEMU can answer differently.
An `iff` pins either the single common answer or the whole-shape decline.
Each is closed by `ep_norm`; beside it, the concrete lie a kernel could
tell there is refuted by `ep_refute`.  The sections
follow the kernel's order — the syscall entry, then the callee's tests in
sequence — and each section pins the answer against the one the NEXT check
would have given, which is what makes the order a claim and not a
convention.

WHAT IS SYMBOLIC AND WHAT IS NOT.  A pin whose arm reads no user memory
takes the input `i` symbolic, which is the statement that no byte is read:
the `epoll_create1` pins are of that shape.  A symbolic `EPOLL_CTL_DEL` or
NULL-mask `epoll_pwait` pin instead names the condition each answer
depends on (`qemu_lock_may`, `qemu_lock_sure`, `in_arg i 1`), because
QEMU 11.1.1 linux-user/syscall.c `do_syscall1` locks the buffer or reads
the raw `op` register there.  A pin whose arm copies from user memory names the memory
through `ep_in`, so the copy's verdict is decided.
The symbolic pins use `ep_model` to distinguish descriptor kinds.
A pin on its fd 3 tests a regular file.
A pin on its fd 6 tests a socket.
The Rocq example twins share additional fixtures with `Checks/Cases/Checks/Sys/Fs/EventPoll.lean`.

THE ROCQ FILE'S ONE EXAMPLE HAS ITS TWIN HERE.  Rocq keeps
`fd_can_poll_is_select_pollable` beside its definitions, pinning that
`fd_can_poll` and `Select.bits_all_pollable` stay complementary; the Lean
tree keeps every check in `Checks/Cases/`, so the twin is
`fd_can_poll_is_select_pollable` below, and this file — not the trusted
spec twin — imports `Sys.Fs.Select` for it.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux or QEMU agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select (bits_all_pollable)
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic


set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-! ## The register

The specs' unfoldings, and the unfoldings of the outcome functions they
match on and of the sigmask reading, all at low priority like every other
(the `Checks/Cases/Tactic.lean` header says why); nothing for the gates
`ep_op_has_event`, `copy_from_user_ok`, `fd_can_poll` and `access_okb`,
which are decided, never unfolded.  The outcome functions ARE unfolded
because they are not gates: they are the `if`/`match` trees the gates
sit in, and a pin with a symbolic input needs the tree open so that the
closed gates in it can be decided while the open ones stay as stated. -/

attribute [sys_simp low]
  epoll_create1_spec.eq_1 epoll_create1_outcome.eq_1
  epoll_ctl_spec.eq_1 epoll_ctl_outcome.eq_1 epoll_ctl_linux.eq_1
  ep_epfd_is_channel.eq_1 epoll_ctl_after_copy.eq_1 epoll_ctl_qemu.eq_1 ep_join.eq_1 ep_answer.eq_1
  qemu_lock_sure.eq_1 LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket.load_write_free.eq_1 ep_stack_band_free.eq_1
  epoll_pwait_linux.eq_1 epoll_pwait_qemu.eq_1 qemu_after_lock.eq_1
  epoll_pwait_spec.eq_1 epoll_pwait_outcome.eq_1 epoll_sigmask.eq_1

/-- The simplifier preserves a decline when either implementation declines its answer set.
model: a rewrite of the spec's own answer-set join, for `sys_simp` -/
@[sys_simp] theorem ep_join_none_left (q : Option (List word)) : ep_join none q = none := by
  cases q <;> rfl

/-- model: a rewrite of the spec's own answer-set join, for `sys_simp` -/
@[sys_simp] theorem ep_join_none_right (l : Option word) : ep_join l none = none := by
  cases l <;> rfl

/-- Equal alternatives collapse to the Linux answer alone.
model: the Lean join requires agreement and returns no alternative answers -/
theorem ep_join_equal_answers_singleton :
    ep_join (some (errno_ret EINVAL))
      (some [errno_ret EINVAL, errno_ret EINVAL]) = some (errno_ret EINVAL, []) := by
  decide +kernel

/-- A matching first answer cannot hide a later disagreement.
model: every QEMU alternative must agree with the Linux answer -/
theorem ep_join_later_disagreement_declines :
    ep_join (some (errno_ret EINVAL))
      (some [errno_ret EINVAL, errno_ret ENOMEM]) = none := by
  decide +kernel

/-- A matching later answer cannot hide an earlier disagreement.
model: agreement is universal over the QEMU list, not membership in it -/
theorem ep_join_earlier_disagreement_declines :
    ep_join (some (errno_ret EINVAL))
      (some [errno_ret ENOMEM, errno_ret EINVAL]) = none := by
  decide +kernel

/-- Duplicate alternatives leave the represented outcome set unchanged.
model: a propositional rewrite for `sys_simp`, with no kernel content -/
@[sys_simp] theorem ep_or_repeat_right (a b : Prop) : (a ∨ b ∨ a) ↔ a ∨ b := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- model: a propositional rewrite for `sys_simp`, with no kernel content -/
@[sys_simp] theorem ep_or_repeat_left (a b : Prop) : (a ∨ a ∨ b) ↔ a ∨ b := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

macro "ep_simp" : tactic =>
    `(tactic| simp +decide only [sys_simp, *, ite_self, or_assoc, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, List.all_nil, List.all_cons, ↓reduceIte,
        outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, Model.mkModelOf.injEq,
        VmMaps.mkVmMapsFull.injEq, FdState.mkFdState.injEq, VmState.mkVmState.injEq,
        IoState.mkIoState.injEq, FsState.mkFsState.injEq, ProcState.mkProcState.injEq,
        LimState.mkLimState.injEq, TimeState.mkTimeState.injEq, Creds.mkCreds.injEq,
        event.ReadEv.injEq, event.WriteEv.injEq, event.ExitEv.injEq, event.KillEv.injEq,
        Option.some.injEq, List.cons.injEq, Prod.mk.injEq, reduceCtorEq,
        List.cons_ne_nil, List.nil_eq, List.mem_singleton, List.mem_cons, List.not_mem_nil,
        List.append_nil, List.nil_append, List.cons_append, List.append_assoc,
        and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or,
        and_self, or_self, and_assoc, and_or_left, or_and_right, iff_self, eq_self_iff_true,
        exists_or, exists_const, exists_false, exists_eq, exists_eq', exists_eq_left,
        exists_eq_left', exists_eq_right, exists_eq_right', exists_eq_right_right,
        exists_eq_right_right', exists_and_left, exists_and_right, exists_eq_or_imp, exists_eq_or_imp',
        exists_or_eq_imp, exists_or_eq_imp',
        not_or, not_exists, not_and, not_false_eq_true, not_true_eq_false, ne_eq,
        Bool.false_eq_true, Bool.true_eq_false])

macro "ep_norm" : tactic =>
  `(tactic| (ep_simp; first | done | sys_simp_pass +ground +decide -failIfUnchanged))

macro "ep_refute" : tactic =>
  `(tactic| (ep_norm; done))

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each numeral is. -/

/-- `EPOLL_CLOEXEC` is `O_CLOEXEC` (include/uapi/linux/eventpoll.h:23),
which is `02000000` (include/uapi/asm-generic/fcntl.h:62, both Linux
v6.18.46) — bit 19, 524288.  `do_epoll_create` compile-enforces the
identity with a `BUILD_BUG_ON` (fs/eventpoll.c:2437).
model: the model's own constant at a numeral; the kernel spelling is a macro of another macro, so its value is read off `Sys/Uapi/Fs.lean`'s `O_CLOEXEC` -/
example : EPOLL_CLOEXEC = 524288 := by decide

/-- …and spelled through `O_CLOEXEC`, as the kernel spells it.
model: the model's own identity between two of its constants -/
example : EPOLL_CLOEXEC = O_CLOEXEC := rfl

/-- The 32-bit complement of the mask, the number `epoll_create1_outcome`
masks with: every bit of an `int` but bit 19.
model: a closed arithmetic fact about the model's mask -/
example : (2 ^ 32 - 1 - EPOLL_CLOEXEC : Int) = 4294443007 := by decide

/-- `EPOLL_CTL_DEL` is 2.
kernel: include/uapi/linux/eventpoll.h:EPOLL_CTL_DEL@v6.18.46 -/
example : EPOLL_CTL_DEL = 2 := by decide

/-- `sizeof(struct epoll_event)` is 16 on riscv64: `EPOLL_PACKED` is
`__attribute__((packed))` only under `#ifdef __x86_64__`
(include/uapi/linux/eventpoll.h:77-81, Linux v6.18.46), so the `__u64
data` member of `struct epoll_event` (:83-86) is 8-aligned and four bytes
of padding follow the 4-byte `events`.
model: the model's own constant at a numeral; the kernel value is a `sizeof`, which no macro spells -/
example : epoll_event_bytes = 16 := by decide

/-- `EP_MAX_EVENTS` is `INT_MAX / sizeof(struct epoll_event)`
(fs/eventpoll.c:222, Linux v6.18.46) with `INT_MAX` = `((int)(~0U >> 1))`
(include/vdso/limits.h:8) = 2147483647: 134217727, in C integer division.
model: the model's own constant at a numeral; the kernel value is a quotient of a `sizeof`, which no macro spells -/
example : EP_MAX_EVENTS = 134217727 := by decide

/-- …and it IS that quotient, so a reader can re-derive it: 2^31 - 1 over
the 16 above.  A packed 12 would give 178956970 instead.
model: the derivation of the model's constant from its own `epoll_event_bytes` -/
example : EP_MAX_EVENTS = (2 ^ 31 - 1) / epoll_event_bytes := by decide

/-! ## `file_can_poll`, kind by kind

`file_can_poll` (include/linux/poll.h:73-76, Linux v6.18.46) is
`file->f_op->poll` read as a truth value, and `vfs_poll` (:78-83) is what
makes the same fact observable to `pselect6`: a NULL `->poll` hands back
`DEFAULT_POLLMASK` (:24).  So each arm of `fd_can_poll` is a claim about
one `file_operations` table, and the citation on each pin is that table's
installer. -/

/-- A regular file opened read-only has no `->poll`: the ordinary on-disk
and in-memory filesystems give `S_IFREG` inodes the `generic_file_*`
operations, and none of those tables carries `.poll`.  An IMAGE premise,
not an `S_IFREG` fact — `Sys/Fs/EventPoll.lean`'s `fd_can_poll` names the
filesystems that break it.
kernel: include/linux/poll.h:file_can_poll,vfs_poll@v6.18.46 -/
example : fd_can_poll (.FdFile [102] 7) = some false := by decide

/-- …and one opened for writing: the access mode does not change `f_op`.
kernel: include/linux/poll.h:file_can_poll,vfs_poll@v6.18.46 -/
example : fd_can_poll (.FdFileW [103] 9) = some false := by decide

/-- A directory has no `->poll`: no directory `file_operations` in the
tree defines one.
kernel: include/linux/poll.h:file_can_poll,vfs_poll@v6.18.46 -/
example : fd_can_poll .FdDir = some false := by decide

/-- A socket HAS a `->poll`, unconditionally: `sock_alloc_file`
(net/socket.c:476-501, at :483-485) installs `socket_file_ops` (:156-173), whose
`.poll` is `sock_poll` (:1426-1445), on every address family.  No
obligation: the model minted this descriptor itself.
kernel: include/linux/poll.h:file_can_poll; net/socket.c:sock_alloc_file,sock_poll@v6.18.46 -/
example : fd_can_poll (.FdSocket .SkFresh) = some true := by decide

/-- Both pipe ends HAVE a `->poll`: `create_pipe_files` (fs/pipe.c:926-980)
gives both files `pipeanon_fops` (at :946 and :957), whose `.poll` is
`pipe_poll` (:659-707).  The reader's end…
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
example : fd_can_poll (.FdPipe 0 false) = some true := by decide

/-- …and the writer's, by the same table.
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
example : fd_can_poll (.FdPipe 0 true) = some true := by decide

/-- A CHANNEL is declined: the model does not know whether its far end is
a pipe (whose `pipe_poll`, fs/pipe.c:659-707, IS a `->poll`) or a regular
file or /dev/null (whose tables have none — `memory_open`,
drivers/char/mem.c:707-727, installs `null_fops`, :644-652, which lists no
`.poll`).  Both answers are live, so neither is given.
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:pipe_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll (.FdChannel 2) = none := by decide

/-- /dev/null is declined though the answer is exact — `null_fops`
(drivers/char/mem.c:644-652), installed by `memory_open` (:707-727), has no
`.poll` — because the arm is not yet written with its own probe: a decline
is a gap, never a wrong answer.
kernel: include/linux/poll.h:file_can_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll (.FdDevNull true true) = none := by decide

/-- /dev/urandom likewise: `urandom_fops` (drivers/char/random.c:1572-1581)
has no `.poll` — `random_fops` (:1560-1570) has `random_poll`
(:1414), the urandom table does not — and the arm is declined until
probed.
kernel: include/linux/poll.h:file_can_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll .FdUrandom = none := by decide

/-- The complement claim, as a check rather than a sentence — the twin of
Rocq's Example of the same name, kept beside its definitions there and here
in the Cases file, where every Lean check lives.

`Select.bits_all_pollable` asks whether a descriptor has the CONSTANT
`DEFAULT_POLLMASK`; `fd_can_poll` asks whether it has a `->poll` method at
all.  `vfs_poll` (include/linux/poll.h:78-83, Linux v6.18.46) returns
`DEFAULT_POLLMASK` (:24) exactly when `->poll` is NULL, which is what
`file_can_poll` (:73-76) reads, so a descriptor is Select-pollable exactly
when this file can say `some false` — not by coincidence but because the
two read one kernel fact, and a descriptor kind whose `->poll` status
changes has to move in both files at once.  The three-valued form is what
makes this true rather than nearly true: a bare complement would force
`FdChannel` onto one side, and the two files DECLINE it for the same reason
from opposite directions.  Stated over a one-entry table at bit 0, which is
what `bits_all_pollable` scrutinises; the case split is over the
constructors, whose arguments neither side reads.
kernel: include/linux/poll.h:file_can_poll,vfs_poll@v6.18.46 -/
theorem fd_can_poll_is_select_pollable (e : FdEntry) :
    bits_all_pollable [(Z_to_bv 64 0, e)] 1 1 = true ↔ fd_can_poll e = some false := by
  cases e <;> first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => Option.noConfusion h⟩
    | exact ⟨fun h => Bool.noConfusion h,
             fun h => Option.noConfusion h (fun h' => Bool.noConfusion h')⟩

/-! ## `copy_from_user`, in two answers

`copy_from_user` (include/linux/uaccess.h:204-214, Linux v6.18.46) reaches
`_inline_copy_from_user` (:158-185; on riscv64 through lib/usercopy.c's
`_copy_from_user`, :16-19, Linux v6.18.46): `access_ok` over the whole range
(:168-169) and only then the copy (:178), so a range `__access_ok`
(include/asm-generic/access_ok.h:31-41) refuses faults before a byte is
read, and a range it accepts faults on the first unmapped byte.  These pins
are on the verdict alone; the syscall pins below carry each into an
errno. -/

/-- The mapped memories these checks read from: every address holds a
zero byte, or exactly `n` bytes from `lo` do. -/
def ep_mem_all : word → Option byte := fun _ => some 0

def ep_mem_run (lo n : Nat) : word → Option byte :=
  fun a => if lo ≤ a.toNat ∧ a.toNat < lo + n then some 0 else none

/-- A fully mapped 16-byte struct at a page boundary: readable.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 4096 16 = true := by decide

/-- NULL is a FAULT ADDRESS and not a range failure: `access_ok(NULL, 16)`
passes (`__access_ok`'s test is `size <= limit && addr <= limit - size`,
include/asm-generic/access_ok.h:40, and 0 is below both), and the copy
then faults on the unmapped page.  What `epoll_spec.c`'s `fault` case
sends.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok (fun _ => none) 0 16 = false := by decide

/-- Twelve mapped bytes of a sixteen-byte struct: a FAULT.  The struct is
16 bytes on riscv64 (`EPOLL_PACKED` is empty off x86-64,
include/uapi/linux/eventpoll.h:77-81), so the copy reads the four padding
bytes too, and the thirteenth is unmapped here.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok (ep_mem_run 4096 12) 4096 16 = false := by decide

/-- …and sixteen mapped bytes are enough.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok (ep_mem_run 4096 16) 4096 16 = true := by decide

/-- …but not from one byte later: the copy is of the whole struct, and its
last byte is then unmapped.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok (ep_mem_run 4096 16) 4097 16 = false := by decide

/-- The range test is FIRST and is the kernel's own: 16 bytes ending
exactly at `TASK_SIZE` (2^47 on Sv48) pass `__access_ok`
(include/asm-generic/access_ok.h:40, `addr <= limit - size` with equality).
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 140737488355312 16 = true := by decide   -- 2^47 - 16

/-- …and 16 bytes ending one past it fail, however readable the memory
says the bytes are: the range is refused before a byte is read.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 140737488355313 16 = false := by decide  -- 2^47 - 15

/-- THE WRAP: a struct at 2^64 - 8 would be read by the byte walk alone as
eight bytes off the top and eight off address 0 (`read_bytes_map` walks in
word arithmetic), and every byte is mapped here — but `__access_ok`'s
subtraction (include/asm-generic/access_ok.h:40) refuses the range
outright, so the verdict is a fault.  `bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md`
names the sites where the range is not yet tested first; this is not one.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 18446744073709551608 16 = false := by decide  -- 2^64 - 8

/-- `copy_from_user_ok` is `State.copy_bytes_map`'s verdict: both spell one
pair, `access_okb` and then `read_bytes_map`, and Rocq's `State.v` names
moving `EventPoll.copy_from_user_ok` onto `copy_bytes_map` as the follow-up
still owed.  Until it moves, this is what notices the two diverging.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem copy_from_user_ok_is_copy_bytes_map (mp : word → Option byte) (a : word) (len : Int) :
    copy_from_user_ok mp a len = (copy_bytes_map mp a len).isSome := by
  unfold copy_from_user_ok copy_bytes_map
  cases access_okb a len <;> cases read_bytes_map mp a (Z_to_bv 64 len) <;> rfl

/-! ## The fixtures

`ep_model` holds one descriptor of every kind the Lean `FdEntry` has: the
three standard channels, a read-only file (fd 3, path 102, offset 7), a
file opened for writing (fd 4, path 103, offset 9), a directory (fd 5), a
fresh socket (fd 6), the read and write ends of one empty pipe (fds 7 and
8, pipe 0), /dev/null read-write (fd 9) and /dev/urandom (fd 10).  Fd 99
and fd 4294967295 (what an `int` -1 arrives as after `fd32`) are closed.
Unlike `Locks.lean`'s and `Fcntl.lean`'s fixtures, this one is not
registered in `sys_simp`: closed descriptor lookups compute against it. -/

def ep_model : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
              (3, .FdFile [102] 7), (4, .FdFileW [103] 9), (5, .FdDir),
              (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdPipe 0 true),
              (9, .FdDevNull true true), (10, .FdUrandom) ])
    (pipes := [(0, ([], 0))])
    (fs := [([102], [120]), ([103], [121])])

/-- An input whose pre-syscall memory is `mem`, for the pins whose arm
copies from user memory: `ep_in` for the `epoll_ctl` (21) pins, `pw_in` for
the `epoll_pwait` (22) pins.  A spec called directly reads neither the
number nor, bar the raw `op` that `epoll_ctl_qemu` reads as `in_arg i 1`
(0 from this empty list), the argument list, so the two differ only in the
number the evidence checker reads off them to match a pin to its probe's
syscall; the table pins build their own inputs. -/
def ep_in (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 21 [] mem mem

def pw_in (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 22 [] mem mem

attribute [sys_simp low] ep_in.eq_1 pw_in.eq_1

/-- Pure evaluation lets the continuation precede the count guard.
model: equality with the previous spec helper body -/
theorem epoll_pwait_qemu_eq_guard_first (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) :
    epoll_pwait_qemu i m epfd events maxevents32 sigmask sigsetsize =
      (let n := sint32 maxevents32
       if decide (n ≤ 0) || decide (EP_MAX_EVENTS < n) then some [errno_ret EINVAL]
       else
         let later :=
           if w_is0 sigmask then
             match fd_lookup (m_fds m) epfd with
             | none => some [errno_ret ENOMEM, errno_ret EBADF]
             | some e => if ep_epfd_is_channel e then none
                         else some [errno_ret ENOMEM, errno_ret EINVAL]
           else if !(bv_unsigned sigsetsize == kernel_sigset_bytes)
                then some [errno_ret ENOMEM, errno_ret EINVAL]
                else if qemu_lock_may i false sigmask 8 then none
                     else some [errno_ret ENOMEM, errno_ret EFAULT]
         qemu_after_lock i m true events (n * epoll_event_bytes) later) := by
  rfl

/-- Integer subtraction makes the size guard redundant for a nonnegative address.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_long_max_eq_kernel_form (base : word) (len : Int) :
    access_ok_long_max base len =
      (decide (len ≤ 2 ^ 63 - 1) && decide (bv_unsigned base ≤ 2 ^ 63 - 1 - len)) := by
  have hbase : 0 ≤ bv_unsigned base := Int.natCast_nonneg _
  unfold access_ok_long_max
  by_cases h : bv_unsigned base ≤ 2 ^ 63 - 1 - len
  · have hlen : len ≤ 2 ^ 63 - 1 := by omega
    simp only [h, hlen, decide_true, Bool.true_and]
  · simp only [h, decide_false, Bool.and_false]

/-- Linux copies the readable ADD event and returns EPERM for a regular target.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, requests VERIFY_READ
through linux-user/uaccess.c, `lock_user`; the absent write view must not
turn that read into EFAULT. The kernel citation supports the Linux EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_read_only_event_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096
      (SyscallInput.mkInput 21 [5, 1, 3, 4096] (ep_mem_run 4096 16) (fun _ => none))
      ep_model o ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- Linux faults on the unreadable mask. QEMU 11.1.1 linux-user/syscall.c,
`do_syscall1`, requests VERIFY_WRITE for the events before allocating the
host array, so the absent write view faults before ENOMEM is possible.
Using the read view would instead make Lean decline the Linux EFAULT.
The kernel citation supports the Linux mask fault.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem pwait_read_only_events_unreadable_mask_is_efault (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 1 8192 8
      (SyscallInput.mkInput 22 [5, 4096, 1, 0, 8192, 8]
        (ep_mem_run 4096 16) (fun _ => none))
      ep_model o ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Linux's range check returns EFAULT for this ADD event. The conservative
QEMU lock bound retains the nonwrapping endpoint, leaving EPERM possible
in its overapproximation and forcing Lean to decline. This is no claim
that QEMU accepts this address: QEMU 11.1.1 include/user/guest-host.h,
`guest_range_valid_untagged_vaddr`, checks its own `guest_addr_max`.
The kernel citation supports only the Linux EFAULT.
kernel: fs/eventpoll.c:epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_word_space_end_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (2 ^ 64 - 16))
      (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- One byte farther wraps the event range. Linux's range check faults;
QEMU 11.1.1 include/user/guest-host.h, `guest_range_valid_untagged_vaddr`,
refuses an end beyond `guest_addr_max`, so the lock cannot reach the host
EPERM. The kernel citation supports the Linux EFAULT.
kernel: fs/eventpoll.c:epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_word_space_overrun_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (2 ^ 64 - 15))
      (ep_in ep_mem_all) ep_model o ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Linux copies this readable event and returns EPERM for the regular target.
The range ends at the stack band's lower edge, without using a band byte.
QEMU 11.1.1 linux-user/main.c, `handle_arg_stack_size`, and
linux-user/elfload.c, `setup_arg_pages`, motivate uncertainty inside the
band, not in this disjoint range. The kernel citation supports Linux EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_event_ending_at_stack_band_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (sp_window_lo - stack_max_size - 16))
      (ep_in ep_mem_all) ep_model o ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- Linux still returns EPERM after the readable copy. One byte is now in
the stack band: QEMU 11.1.1 linux-user/main.c, `handle_arg_stack_size`,
permits a smaller stack, and linux-user/elfload.c, `setup_arg_pages`,
places its guard below it. The uncertain lock makes Lean decline the
Linux answer. The kernel citation supports that base EPERM only.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_event_overlapping_stack_band_lower_edge_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (sp_window_lo - stack_max_size - 15))
      (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- Linux copies this readable event and returns EPERM for the regular target.
Starting at the entry sp misses the half-open stack band. QEMU 11.1.1
linux-user/main.c, `handle_arg_stack_size`, and linux-user/elfload.c,
`setup_arg_pages`, motivate the band exclusion; this range is outside it.
The kernel citation supports Linux EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_event_starting_at_stack_band_end_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 sp_window_lo)
      (ep_in ep_mem_all) ep_model o ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- Linux still returns EPERM, but one byte below the entry sp overlaps
the conservatively excluded band. QEMU 11.1.1 linux-user/main.c,
`handle_arg_stack_size`, and linux-user/elfload.c, `setup_arg_pages`,
allow a smaller stack than the model's initialized band, so Lean declines.
The kernel citation supports the Linux base answer only.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_event_overlapping_stack_band_upper_edge_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (sp_window_lo - 1))
      (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- This pin kills the single-conjunct `access_ok_long_max` bound-flip and bound-shift mutants.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_long_max_edge :
    access_ok_long_max (Z_to_bv 64 (2 ^ 63 - 17)) 16 = true ∧
    access_ok_long_max (Z_to_bv 64 (2 ^ 63 - 16)) 16 = false := by decide

/-- Linux v6.18.46 fs/eventpoll.c [ep_check_params] tests the count before `is_file_epoll`.
On a channel epfd, the count test answers -EINVAL before `is_file_epoll`
can trigger the model's decline.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_linux_count_precedes_access :
    epoll_pwait_linux (pw_in ep_mem_all) ep_model 0 4096
      (Z_to_bv 64 (EP_MAX_EVENTS + 1)) 0 0 = some (errno_ret EINVAL) := by decide

/-- QEMU's rejection masks exclude EPOLL_CLOEXEC, so Linux's mask detects their rejected bits.
Linux v6.18.46 fs/eventpoll.c [do_epoll_create] supplies the retained test order.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem qemu_epoll_flags_rejected_implies_linux_rejects (flags32 : word)
    (h : qemu_epoll_flags_rejected flags32 = true) :
    bv_unsigned (bv_and flags32 (Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC))) ≠ 0 := by
  intro hz
  have hw : bv_and flags32 (Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    exact Int.ofNat_inj.mp hz
  have hsmall (mask : word)
      (hm : bv_and (Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC)) mask = mask) :
      bv_and flags32 mask = 0 := by
    rw [← hm]
    change flags32 &&& ((Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC)) &&& mask) = 0
    rw [← BitVec.and_assoc]
    change bv_and (bv_and flags32 (Z_to_bv 64 (2 ^ 32 - 1 - EPOLL_CLOEXEC))) mask = 0
    rw [hw]
    exact BitVec.zero_and
  have hacc := hsmall 3 (by decide)
  have hbits := hsmall 0x277FC0 (by decide)
  simp only [qemu_epoll_flags_rejected, hacc, hbits] at h
  exact Bool.noConfusion h

/-- A raw DEL truncates to DEL, so NULL-event and raw-operation tests give the same host answer.
QEMU 11.1.1 linux-user/syscall.c [do_syscall1] supplies the retained test order.
model: canonical operation narrowing justifies the equivalent ctl check-swap mutant -/
theorem epoll_ctl_qemu_del_null_is_host (i : SyscallInput) (m : Model) (epfd tfd : word)
    (hraw : in_arg i 1 = 2) :
    epoll_ctl_qemu i m epfd (int32 (in_arg i 1)) tfd 0 =
      (epoll_ctl_after_copy m epfd tfd).map (fun r => [r]) := by
  simp [epoll_ctl_qemu, hraw, w_is0, ep_op_has_event, int32, abi_low32,
    bv_unsigned, Z_to_bv, EPOLL_CTL_DEL]

/-! ## epoll_create1 (20): `do_epoll_create`'s one `if`

`if (flags & ~EPOLL_CLOEXEC) return -EINVAL;` (fs/eventpoll.c:2439-2440,
Linux v6.18.46) is the first statement of `do_epoll_create` (:2430-2471)
that can fail — the `BUILD_BUG_ON` above it (:2437) is compile-time — and
everything that can answer anything else sits below it: `ep_alloc`
(called at :2444, defined :1341-1363) with its -ENOMEM,
`get_unused_fd_flags` (called at :2451; fs/file.c:620-623, Linux v6.18.46,
whose `alloc_fd` at :570-613 chooses the -EMFILE) and `anon_inode_getfile`
(fs/anon_inodes.c:200-205, Linux v6.18.46).  So for a flag word with any bit outside the
mask, -EINVAL is the only answer, the model is untouched and no event is
emitted, whatever the model.  Every `iff` below that answers -EINVAL pins all of that at once;
the refutations name the lies.  Linux's answer, that is: QEMU 11.1.1's
user-mode emulation translates the word through `fcntl_flags_tbl` first and
drops the bits that table does not carry, so it hands out a descriptor for
bit 31 or bit 20 alone where the kernel answers -EINVAL; the spec declines
those words.

The spec answers -EINVAL only where `qemu_epoll_flags_rejected` holds.  That
test names the words whose translation keeps a host bit other than
`O_CLOEXEC`, which the host's `do_epoll_create` refuses.  The translation is
`target_to_host_bitmask_len` (linux-user/thunk.c, QEMU 11.1.1), called from
`do_syscall1`.  `epoll_dropped_flag_linux_declines` and
`epoll_dropped_flag_qemu_fd_declines` in `Checks/Cases/Checks/Sys/Fs/EventPoll.lean`
pin both answers on bit 31 as declines. -/

/-- Bit 0, the lowest bit outside the mask: -EINVAL from the gate.  The
first word `epoll_spec.c`'s `badflags` case sends.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- badflags -/
theorem create_bit_0_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- The accepted bit does not excuse a refused one: `EPOLL_CLOEXEC | 1`
leaves bit 0 in the residue `flags & ~EPOLL_CLOEXEC`.  The second word of
the `badflags` case.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_plus_bit_0_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    epoll_create1_spec 524289 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Bit 18, immediately below the mask's one bit: -EINVAL, so the mask is
not a bound from below.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_18_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 262144 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Bit 20, immediately above it: -EINVAL, so the mask is not a bound from
above either.  QEMU 11.1.1's `target_to_host_bitmask_len`
(linux-user/thunk.c), called from `do_syscall1`, maps bit 20 alone to no
host bit.  So QEMU can create the fd, and the spec declines.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_20_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 1048576 i m o ↔ o = Unmodeled := by
  ep_norm

/-- Bit 31 alone: the residue is the `if` condition itself, a truthiness
test and not a sign test, so the `int`'s sign bit is refused exactly as
bit 0 is.  No row of QEMU 11.1.1's `fcntl_flags_tbl` (linux-user/syscall.c)
matches bit 31, so `do_syscall1` hands the host 0.  So QEMU can create the
fd, and the spec declines.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_sign_bit_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 2147483648 i m o ↔ o = Unmodeled := by
  ep_norm

/-- Every bit of the `int`, `epoll_create1(-1)`: -EINVAL.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_all_ones_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 4294967295 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- A refused word never yields a DESCRIPTOR: `do_epoll_create` returns at
:2440, before `get_unused_fd_flags` at :2451 reserves one.  The lie the
`badflags` mutation tells (`--mutate epoll_create1:ret=0`).
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_create1:ret=0 -- badflags -/
theorem create_bit_0_fd_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- …nor fd 3, the number a fresh process would get.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_0_fd_three_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect 3 [] []) m' evs) := by
  ep_refute

/-- The errno-precedence pin: -ENOMEM is UNREACHABLE on a refused word,
because `ep_alloc` (fs/eventpoll.c:1341-1363, called at :2444) sits below
the gate.  A kernel reporting the allocation failing for a word it never
allocated for is lying.
kernel: fs/eventpoll.c:do_epoll_create,ep_alloc@v6.18.46 -/
theorem create_bit_0_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  ep_refute

/-- -EMFILE the same way: `alloc_fd` (fs/file.c:570-613, Linux v6.18.46),
reached through `get_unused_fd_flags` (fs/file.c:620-623) from the call at
line 2451 of `do_epoll_create`, is below the gate, so a full descriptor
table cannot turn a refused flag word into -EMFILE.
kernel: fs/eventpoll.c:do_epoll_create; fs/file.c:get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem create_bit_0_emfile_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  ep_refute

/-- The gate never declines: a refused word is answered, so a checker that
goes unmodeled on it has lost precision the kernel does not lose.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_0_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ epoll_create1_spec 1 i m Unmodeled := by
  ep_refute

/-- The -EINVAL is INERT: nothing above the gate stores or allocates, so an
outcome carrying an event beside the right errno is refused too.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_einval_with_an_event_rejected (i : SyscallInput) (m m' : Model) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' [WriteEv 1 65]) := by
  ep_refute

/-! ### The accepted words decline rather than answer

Every word inside the mask passes the gate, and everything past the gate
ends in a descriptor or in an errno the model cannot place (-ENOMEM,
-EMFILE, `anon_inode_getfile`'s failures).  The model has no `FdEntry` for
an epoll instance — `Sys/Fs/EventPoll.lean`'s header says why a nullary
one would be the wrong shape — so the arm declines: `Unmodeled`, and the
`iff` says the decline is keyed on the flag word and on nothing else.  The
intersection of the supported implementations is not empty here; the model
simply cannot represent what every one of them does, which costs priority
3 and nothing else.  The refutations say what the decline is NOT: it is
not an -EINVAL a narrower mask would produce, and it is not an admission
of the descriptor. -/

/-- The empty word, `epoll_create(size)` as glibc and musl compile it:
past the gate, declined.  `epoll_spec.c`'s `create` case observes the
kernel handing out a descriptor and the model declining.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- create -/
theorem create_zero_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 0 i m o ↔ o = Unmodeled := by
  ep_norm

/-- `EPOLL_CLOEXEC` alone, the one accepted bit: declined.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 524288 i m o ↔ o = Unmodeled := by
  ep_norm

/-- Bit 32 alone, handed to the spec DIRECTLY: the spec's own mask is
32 bits wide (the Rocq `Z.lnot EPOLL_CLOEXEC mod 2 ^ 32`), so it accepts
the word without the table's narrowing.  `SYSCALL_DEFINE1(epoll_create1,
int, flags)` (fs/eventpoll.c:2473-2476) declares an `int`, so the kernel
never sees the bit at all.
kernel: fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem create_bit_32_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 4294967296 i m o ↔ o = Unmodeled := by
  ep_norm

/-- The descriptor Linux DOES hand back for `epoll_create1(0)` is not
admitted: an acceptor built on this spec answers unmodeled and never
accepts — the fail-closed half.  What this pin rules out is a spec that
admitted the success without a descriptor kind to record it in.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- create -/
theorem create_zero_descriptor_not_admitted (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 0 i m (Ok (mkEffect 3 [] []) m' evs) := by
  ep_refute

/-- …and -EINVAL for the accepted bit is refused: the lie a spec with a
narrower mask, or a 64-bit complement, would tell.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 524288 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-! ## epoll_ctl (21), in the kernel's order

`SYSCALL_DEFINE4(epoll_ctl, int, epfd, int, op, int, fd, struct
epoll_event __user *, event)` (fs/eventpoll.c:2658-2668, Linux v6.18.46)
copies the struct first (:2663-2665) and then calls `do_epoll_ctl`
(:2511-2651), which resolves `epfd` (:2520-2522), resolves the target
(:2525-2527), tests the target's `->poll` (:2530-2531), and only then asks
whether `epfd` is an epoll fd (:2542-2544).  Each section below pins one
of those five decisions against the one after it. -/

/-! ### 1. The copy, before any descriptor is resolved

`if (ep_op_has_event(op) && copy_from_user(&epds, event, sizeof(struct
epoll_event))) return -EFAULT;` — in the syscall entry (:2663-2665), so an
unreadable struct is -EFAULT whatever the descriptors are, and for
`EPOLL_CTL_DEL` the struct is never read at all
(`ep_op_has_event`, include/linux/eventpoll.h:64-67, Linux v6.18.46). -/

/-- The `op` that skips the copy is 2 and only 2, judged on the narrowed
word this function is handed.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 2 = false := by decide

/-- `EPOLL_CTL_ADD` (1) copies.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 1 = true := by decide

/-- `EPOLL_CTL_MOD` (3) copies.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 3 = true := by decide

/-- An op the kernel does not know (0) copies anyway: the test is
`op != EPOLL_CTL_DEL` and nothing else.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 0 = true := by decide

/-- This function does NOT narrow: 2^32 + 2 is not 2 to it.  The table's
`int32` is the `int` cast, applied once, before the word reaches here; the
pins under "Through the table" show the narrowing where it happens.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 4294967298 = true := by decide

/-- `ADD` with a NULL `event` on a CLOSED epfd and a closed target: -EFAULT,
because the copy runs in the entry before `do_epoll_ctl` looks anything up.
`epoll_spec.c`'s `fault` case, `epoll_ctl(-1, ADD, -1, NULL)`; -1 is
4294967295 after the `int` narrowing.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem ctl_add_null_event_on_closed_epfd_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 4294967295 1 4294967295 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- The precedence: -EBADF for the closed epfd is refused here, because
the copy (:2663-2665) precedes the lookup (:2520-2522).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_null_event_on_closed_epfd_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 4294967295 1 4294967295 0 (ep_in (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_raw_operation_controls_event_lock_or_declines (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 4294967295 2 4294967295 ev i ep_model o
      ↔ (w_is0 ev = true ∨ (bv_unsigned (in_arg i 1) == 2) = true ∨
          qemu_lock_sure i ep_model false ev 16 = true) ∧
          o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model []
        ∨ (w_is0 ev = false ∧ (bv_unsigned (in_arg i 1) == 2) = false ∧
          qemu_lock_sure i ep_model false ev 16 = false ∧ o = Unmodeled) := by
  cases hz : w_is0 ev <;>
    cases hop : (bv_unsigned (in_arg i 1) == 2) <;>
    cases ha : access_okb ev 16 <;>
    cases hm : qemu_lock_may i false ev 16 <;> ep_norm <;>
      simp only [hop, ha, hm, Bool.false_eq_true, ↓reduceIte] <;> ep_norm
  all_goals split <;> simp only [Bool.eq_false_iff] at * <;> ep_norm

/-- A QEMU read-lock failure can disagree with Linux's DEL answer. Lean
declines the whole symbolic input, including the base EBADF answer.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_qemu_lock_can_fail_declines (ev : word) (i : SyscallInput)
    (hz : w_is0 ev = false)
    (hop : (bv_unsigned (in_arg i 1) == 2) = false)
    (hs : qemu_lock_sure i ep_model false ev 16 = false) :
    epoll_ctl_spec 4294967295 2 4294967295 ev i ep_model Unmodeled := by
  exact (ctl_del_raw_operation_controls_event_lock_or_declines ev i Unmodeled).mpr
    (Or.inr ⟨hz, hop, hs, rfl⟩)

/-- Lean refuses QEMU's EFAULT on DEL: either the common EBADF is admitted,
or the disagreement declines the whole shape.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_declines_or_refuses_qemu_efault (ev : word) (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 4294967295 2 4294967295 ev i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  rw [ctl_del_raw_operation_controls_event_lock_or_declines]
  simp only [reduceCtorEq, and_false, or_false]
  rintro ⟨_, he⟩
  have hr := congrArg SyscallEffect.eff_ret (outcome.Ok.inj he).1
  revert hr
  decide +kernel

/-- An op the kernel does not know (7) still COPIES: `ep_op_has_event` is
`op != EPOLL_CTL_DEL`, so a NULL struct under op 7 is -EFAULT, not the
-EINVAL of the `switch`'s fallthrough — which is never reached anyway
(section 5).
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_unknown_op_null_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 7 3 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Twelve readable bytes are a FAULT: the copy is of
`sizeof(struct epoll_event)`, 16 on riscv64, padding included.  A spec
built on the x86-64 packed 12 would have answered -EPERM here (the target
is a file).
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem ctl_add_twelve_readable_bytes_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 12)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and -EPERM, the packed-struct lie, is refused there.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_twelve_readable_bytes_is_not_eperm (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 12)) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- Sixteen readable bytes are past the copy: the next decision answers.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem ctl_add_sixteen_readable_bytes_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 16)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_event_past_task_size_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 140737488355313 (ep_in ep_mem_all) ep_model o   -- 2^47 - 15
      ↔ o = Unmodeled := by
  ep_norm

/-- The whole shape declines, including the base EFAULT and QEMU's EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_event_past_task_size_whole_shape_declines :
    epoll_ctl_spec 5 1 3 140737488355313 (ep_in ep_mem_all) ep_model Unmodeled := by
  exact (ctl_add_event_past_task_size_declines _).2 rfl

/-- …and a struct ending exactly AT `TASK_SIZE` passes the range test and
reads, so the target's -EPERM answers.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_add_event_ending_at_task_size_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 140737488355312 (ep_in ep_mem_all) ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- The wrapped range: a struct at 2^64 - 8 is -EFAULT, not the -EPERM a
byte walk that wrapped to address 0 would have read its way to.
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_add_wrapped_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 18446744073709551608 (ep_in ep_mem_all) ep_model o   -- 2^64 - 8
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- The CONTENTS of the struct are never used, only its readability: a
struct of all-ones bytes answers exactly as one of zeros.  `epds->events`
is read by the `EPOLLEXCLUSIVE` block (:2551-2556) and by `ep_insert` and
`ep_modify`, all behind the -EINVAL of section 5.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_event_contents_not_judged (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (fun _ => some 255)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-! ### 2. The epfd, before the target

`CLASS(fd, f)(epfd); if (fd_empty(f)) return -EBADF;` (:2520-2522), with
`fd_empty` include/linux/file.h:45-48, Linux v6.18.46. -/

/-- A closed epfd with a readable struct is -EBADF, whatever the target:
here the target is a FILE, whose -EPERM (section 4) would apply if the
epfd were open.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_epfd_is_ebadf (o : outcome SyscallEffect) :
    epoll_ctl_spec 99 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- The precedence: the target's -EPERM is refused on a closed epfd,
because the epfd lookup (:2520-2522) precedes the `->poll` test
(:2530-2531).
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_epfd_is_not_eperm (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 99 1 3 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-! ### 3. The target, before its `->poll`

`CLASS(fd, tf)(fd); if (fd_empty(tf)) return -EBADF;` (:2525-2527) — a
second `fd_empty` test, reached only past the first. -/

/-- An open epfd and a closed target: the target's own -EBADF.
`epoll_spec.c`'s `tgtbad` case, `epoll_ctl(dirfd, ADD, -1, &ev)`.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- tgtbad -/
theorem ctl_closed_target_is_ebadf (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 4294967295 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- The precedence: -EINVAL for "epfd is not an epoll fd" is refused on a
closed target, because the target lookup (:2525-2527) precedes the
`is_file_epoll` test (:2542-2544) — fd 5 is a directory, so a model
testing epoll-ness first would have answered -EINVAL here.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_target_is_not_einval (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 4294967295 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-! ### 4. The target's `->poll`, before the epfd's epoll-ness

`if (!file_can_poll(fd_file(tf))) return -EPERM;` (:2530-2531), with
`file_can_poll` include/linux/poll.h:73-76, Linux v6.18.46.  This is the arm worth
knowing: it sits BEFORE the check that `epfd` is an epoll fd, so
`epoll_ctl` on two ordinary files is -EPERM and not -EINVAL, and a reader
who assumed -EINVAL wins because "epfd isn't an epoll fd" has the errno
wrong.  Between this test and the next sits `ep_take_care_of_epollwakeup`
(fs/eventpoll.c:2487-2491, Linux v6.18.46, or :2493-2496 when the kernel is
built without CONFIG_PM_SLEEP; called at :2534-2535), which clears a bit of
the copied struct and cannot fail under either definition. -/

/-- Both fds the same directory — two rejections hold at once, and the
kernel decides the first: -EPERM.  `epoll_spec.c`'s `perm` case, and the
pin a model that checked epoll-ness first would fail.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- perm -/
theorem ctl_dir_on_dir_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- …and the -EINVAL that also applies is refused: the `perm` mutation
(`--mutate epoll_ctl:ret=-EINVAL`).
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EINVAL -- perm -/
theorem ctl_dir_on_dir_einval_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- A read-only file as the target: -EPERM, no `->poll` on a regular file
(the image premise `Sys/Fs/EventPoll.lean`'s `fd_can_poll` states).
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- A file opened for writing too: the access mode does not give a file a
`->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_write_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 4 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- The epfd's kind is not what decides section 4: a SOCKET as the epfd
and a file as the target is still the target's -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_socket_epfd_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 6 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- `MOD` and `DEL` reach the same -EPERM: the `->poll` test does not read
`op`.  `DEL` here with a wild `event` and a symbolic input, since no copy
happens on Linux.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_mod_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 3 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_file_target_is_eperm_or_declines (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 2 3 ev i ep_model o
      ↔ (w_is0 ev = true ∨ (bv_unsigned (in_arg i 1) == 2) = true ∨
          qemu_lock_sure i ep_model false ev 16 = true) ∧
          o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model []
        ∨ (w_is0 ev = false ∧ (bv_unsigned (in_arg i 1) == 2) = false ∧
          qemu_lock_sure i ep_model false ev 16 = false ∧ o = Unmodeled) := by
  cases hz : w_is0 ev <;>
    cases hop : (bv_unsigned (in_arg i 1) == 2) <;>
    cases ha : access_okb ev 16 <;>
    cases hm : qemu_lock_may i false ev 16 <;> ep_norm <;>
      simp only [hop, ha, hm, Bool.false_eq_true, ↓reduceIte] <;> ep_norm
  all_goals split <;> simp only [Bool.eq_false_iff] at * <;> ep_norm

/-- The -EPERM is inert: no write, no event, the model untouched — a
kernel reporting the file added (0) is refused.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_file_target_success_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- THE COPY-IN LEDGER IS EMPTY on every answered arm, this -EPERM past a
landed 16-byte copy included, and that is a KNOWN-WRONG OMISSION rather than
a kernel fact: Linux consumed the struct at :2663-2665, and
`bugs/epoll-ctl-copyin-not-recorded.md` says why the ledger cannot move
before the harness's does.  Pinned so the omission is visible and deliberate
— the `perm` case's `smuggle-copyin` mutation offers exactly this ledger and
the model refuses it — not because the refusal is what the kernel does.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:smuggle-copyin:a3:16 -- perm -/
theorem ctl_dir_on_dir_copyin_not_recorded (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [] [(4096, 16)]) m' evs) := by
  ep_refute

/-! ### 5. The epfd's epoll-ness: -EINVAL for every pollable target, bar a channel epfd

`error = -EINVAL; if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
goto error_tgt_fput;` (:2542-2544), with `is_file_epoll` :478-481.  No
`FdEntry` denotes an epoll instance, so the second disjunct holds for
every epfd the model can hold except a channel, whose far end can be one
and which declines (`ep_epfd_is_channel`), and a target WITH a `->poll` — a socket, a
pipe end — gets past section 4 to this -EINVAL.  Everything after it —
the `EPOLLEXCLUSIVE` rejections (:2551-2556), `ep_loop_check`
(:2396-2414), the `switch (op)` with its -EEXIST and -ENOENT — is behind
the `goto` and unreachable. -/

/-- A socket target on a directory epfd: past -EPERM, stopped at -EINVAL.
`epoll_spec.c`'s `inval` case.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- inval -/
theorem ctl_socket_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and -EPERM is exactly the answer a socket target cannot get
(`sock_poll`, net/socket.c:1426-1445, Linux v6.18.46, is what `socket_file_ops` installs
as `.poll` at line 160): the `inval` mutation (`--mutate epoll_ctl:ret=-EPERM`).
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EPERM -- inval -/
theorem ctl_socket_target_eperm_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- Nor is the socket ADDED: the directory epfd is not an epoll fd, so
`ep_insert` is never reached and 0 is a lie.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll@v6.18.46 -/
theorem ctl_socket_target_success_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- The read end of a pipe: `pipe_poll` (fs/pipe.c:659-707) is its
`->poll`, so -EINVAL, not -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_read_end_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 7 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and -EPERM is refused for it: `pipe_poll` IS a `->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_read_end_target_eperm_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 7 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- …and the write end, by the same table.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_write_end_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 8 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- An op the kernel does not know, on a pollable target: -EINVAL through
section 5, not through the `switch`'s fallthrough — the same errno by a
route that never reaches the switch.  `ep_op_has_event(7)` is true, so
the struct was copied first.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
theorem ctl_unknown_op_socket_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 7 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The self-add disjunct is never the reason: the same pollable fd as
epfd and target (a socket on itself) is -EINVAL by `!is_file_epoll` alone,
so the model needs no description identity — and the answer is the same
-EINVAL either way.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll@v6.18.46 -/
theorem ctl_socket_on_itself_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 6 1 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-! ### The two declines: a channel target, and a channel epfd at section 5

`fd_can_poll` cannot say whether a channel's far end has a `->poll` — a
pipe or a terminal has one, a regular file or /dev/null has none — so both
-EPERM and -EINVAL are live for the same call, and the spec declines
rather than guess.  The intersection is not empty for any ONE far end; it
is the model's ignorance of which far end this run has that makes a
committed answer a guess.  `epoll_spec.c`'s `chan` case observes the
harness's pipe answering -EINVAL and the model declining. -/

/-- fd 2 as the target: declined, whatever the epfd.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_ctl -- chan -/
theorem ctl_channel_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- Neither live answer is admitted: not the pipe's -EINVAL…
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_ctl -- chan -/
theorem ctl_channel_target_einval_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- …nor the regular file's -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_channel_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- The first decline is the TARGET's, not the epfd's: a channel as the epfd with
a file as the target is answered, -EPERM, because section 4 reads the
target's `->poll` and the epfd's kind is not consulted until section 5.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_channel_epfd_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 2 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- /dev/null and /dev/urandom as targets decline too, for the reason on
their `fd_can_poll` arms: the answer (-EPERM: no `.poll` in `null_fops`,
drivers/char/mem.c:644-652, nor in `urandom_fops`,
drivers/char/random.c:1572-1581) is exact and not yet written with its
own probe.  A decline here is a gap and never a wrong answer.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_devnull_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 9 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- /dev/urandom as the target: declined, `urandom_fops`
(drivers/char/random.c:1572-1581) carrying no `.poll` where `random_fops`
(:1560-1570) carries `random_poll` (:1414); the exact -EPERM waits for its
probe.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_urandom_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 10 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- …and the exact answer is not admitted until then: a spec that answered
-EPERM for /dev/null without the probe would pass every other pin here.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_devnull_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 9 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- …nor for /dev/urandom: the same exact -EPERM, refused until its probe.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_urandom_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 10 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- The decline is BEHIND the copy: `DEL` on a channel target declines with
a symbolic input, and `ADD` on a channel target with an unreadable struct
is the copy's -EFAULT, not a decline.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_channel_target_declines (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 2 2 ev i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- `ADD` on a channel target with a NULL struct: the copy's -EFAULT
(fs/eventpoll.c:2663-2665) answers before the target is looked at, so the
channel's decline is never reached.
kernel: fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_add_channel_target_null_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 2 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-! ## epoll_pwait (22), in the kernel's order

`SYSCALL_DEFINE6(epoll_pwait, …)` (fs/eventpoll.c:2774-2783, Linux
v6.18.46) evaluates `ep_timeout_to_timespec` (:2118-2137, which cannot
fail) as an argument and calls `do_epoll_pwait` (:2753-2772), which runs
`set_user_sigmask` (kernel/signal.c:3281-3297, called at :2763-2765)
FIRST, then `do_epoll_wait` (:2715-2738): the epfd lookup (:2722-2724),
then `ep_check_params` (:2670-2689): the `maxevents` bounds (:2674-2675),
the `access_ok` of the `events` range (:2678-2679), the epoll-ness of the
epfd (:2685-2686).  `ep_poll` (:2199-2317, called at :2737) is behind
that last -EINVAL, or a channel epfd's decline there, and is never
reached.  The lookup moved ahead of the
parameter checks in v6.15 (commit 6b47d35d4d9e); fs/eventpoll.c:do_epoll_wait
at v4.17, v5.10, v6.1, v6.12 and v6.14 checks the count and range first.
The closed-epfd conflict pins below therefore decline both errnos.  Where
QEMU 11.1.1's user-mode order differs on the shapes still answered,
the join declines the whole shape instead of admitting a different answer.  The case
`TARGET_NR_epoll_pwait` in `do_syscall1` tests the count, locks `events`
for writing, allocates the host array (-ENOMEM), and only then reads the
mask. -/

/-! ### 1. The signal mask, before the epfd

`set_user_sigmask`: a NULL `umask` returns 0 (kernel/signal.c:3285-3286, Linux v6.18.46)
BEFORE the size is looked at (:3287-3288), then the copy (:3289-3290),
then the install (:3292-3294) the model cannot represent.  Pinned first on
`epoll_sigmask` alone, then through the syscall. -/

/-- A NULL mask is "no mask", whatever the size and whatever the memory:
`epoll_wait(…)` as musl and glibc compile it on riscv64,
`epoll_pwait(…, NULL, _NSIG/8)`, and a hand-written `(…, NULL, 0)` alike.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_null_is_none (mp : word → Option byte) (ss : word) :
    epoll_sigmask mp 0 ss = .EpSigNone := rfl

/-- A non-NULL mask with a size other than 8 is -EINVAL before the mask is
read: no memory is consulted.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_size_7_is_bad_size (mp : word → Option byte) :
    epoll_sigmask mp 4096 7 = .EpSigBadSize := rfl

/-- The size is a `size_t`, compared full width: 2^32 + 8 is the wrong
size, where a narrowed comparison would have accepted it.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_size_high_half_is_bad_size (mp : word → Option byte) :
    epoll_sigmask mp 4096 4294967304 = .EpSigBadSize := rfl

/-- The right size and an unreadable mask: -EFAULT.  Address 8 passes
`access_ok` and page 0 is unmapped — `epoll_spec.c`'s `pwsigfault` pair.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_unreadable_is_fault :
    epoll_sigmask (fun _ => none) 8 8 = .EpSigFault := rfl

/-- The right size and a readable mask: the mask WOULD BE INSTALLED, which
is where the model stops.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_readable_is_real :
    epoll_sigmask ep_mem_all 4096 8 = .EpSigReal := rfl

/-- Through the syscall: a wrong `sigsetsize` on a CLOSED epfd with
`maxevents` 0 is -EINVAL from the mask — two later rejections that never
run.  `epoll_spec.c`'s `sigsize` case; the reverse of `epoll_ctl`'s
ordering, where the fds are resolved before anything else is judged.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem pwait_bad_sigsetsize_beats_closed_epfd (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 0 4096 7 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The precedence: the closed epfd's -EBADF is refused, because
`set_user_sigmask` (called at fs/eventpoll.c:2763-2765) runs before
`do_epoll_wait`'s lookup (:2722-2724).
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_sigsetsize_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 0 4096 7 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- An unreadable mask and unwritable events buffer on a closed epfd:
Linux faults on the mask; QEMU faults on the events lock. The probe below
instead supplies writable events and is pinned separately.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, checks the events lock first.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_is_efault (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 8 8 (pw_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- The probe's readable/writable events buffer and unreadable mask.
Linux answers EFAULT, but QEMU can answer ENOMEM after locking events,
so the joined spec declines even that Linux answer.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, allocates before reading the mask.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_writable_events_declines (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 8 8
        (pw_in (ep_mem_run 4096 16)) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The precedence again: the closed epfd's -EBADF is refused under an
unreadable mask, `set_user_sigmask` running first.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 8 8 (pw_in (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_mask_bad_size_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 0 7 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- …and its -EINVAL is refused: a model testing the size before the
pointer would answer it.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_mask_bad_size_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 0 7 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_refute

/-- A REAL mask — readable, the right size — declines: `set_user_sigmask`
saves the blocked set and installs the caller's (kernel/signal.c:
3292-3294), and `restore_saved_sigmask_unless` (include/linux/sched/signal.h:
548-554, Linux v6.18.46), called at fs/eventpoll.c:2769 (Linux v6.18.46),
puts it back afterwards.  The
intersection is not empty — every kernel answers -EBADF for this closed
epfd — but the model declines rather than answer around it.  `epoll_spec.c`'s `realmask`
case observes exactly that -EBADF and the model declining.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem pwait_real_mask_declines (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 4096 8 (pw_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- …and the kernel's -EBADF is NOT admitted around the install: the
fail-closed half.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem pwait_real_mask_ebadf_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 4096 8 (pw_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-! ### 2. Closed epfd and parameter-order conflicts

The v6.18.46 lookup in fs/eventpoll.c:do_epoll_wait precedes
`ep_check_params`; the pre-v6.15 checks can win on a closed descriptor. -/

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_closed_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- The closed fd's -EBADF cannot become -EINVAL with good parameters;
fs/eventpoll.c `do_epoll_wait` at v6.14 and v6.18.46 stops at the lookup.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_pwait:ret=-EINVAL -- pwbadfd -/
theorem pwait_closed_epfd_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_refute

/-- A closed epfd with a NULL mask and count zero declines: fs/eventpoll.c:
do_epoll_wait at v6.18.46 returns -EBADF, but at v6.14 the count wins,
-EINVAL, as in `case TARGET_NR_epoll_pwait` in `do_syscall1`
(linux-user/syscall.c, QEMU 11.1.1).
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedzero -/
theorem pwait_closed_epfd_maxevents_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 0 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The zero-count -EINVAL from fs/eventpoll.c:do_epoll_wait at v6.14 and
`case TARGET_NR_epoll_pwait` in `do_syscall1` (linux-user/syscall.c,
QEMU 11.1.1) is not made certain on a closed epfd:
fs/eventpoll.c:do_epoll_wait at v6.18.46 instead returns -EBADF.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedzero -/
theorem pwait_closed_epfd_maxevents_zero_is_not_einval (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 0 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- At maxevents zero, the closed-fd -EBADF of
fs/eventpoll.c:do_epoll_wait at v6.18.46 cannot be the modeled outcome,
since v6.14's same function and `case TARGET_NR_epoll_pwait` in
`do_syscall1` (linux-user/syscall.c, QEMU 11.1.1) return -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedzero -/
theorem pwait_closed_epfd_maxevents_zero_is_not_ebadf (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 0 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- With a closed epfd and count EP_MAX_EVENTS+1, fs/eventpoll.c:do_epoll_wait
at v6.18.46 stops at -EBADF; its v6.14 implementation and
`case TARGET_NR_epoll_pwait` in `do_syscall1` (linux-user/syscall.c,
QEMU 11.1.1) stop at -EINVAL instead.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedmax -/
theorem pwait_closed_epfd_maxevents_above_bound_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 134217728 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The too-large count's -EBADF at fs/eventpoll.c:do_epoll_wait v6.18.46
and -EINVAL at v6.14 or `case TARGET_NR_epoll_pwait` in `do_syscall1`
(linux-user/syscall.c, QEMU 11.1.1) are both refused as Ok for the closed
descriptor, so the older order cannot replace the new one.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedmax -/
theorem pwait_closed_epfd_maxevents_above_bound_neither_errno_is_ok (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 134217728 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ epoll_pwait_spec 4294967295 4096 134217728 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  constructor <;> ep_refute

/-- For one event above TASK_SIZE and a closed epfd,
fs/eventpoll.c `do_epoll_wait` returns -EBADF from v6.15 (read at
v6.18.46); v6.1 checks access_ok against TASK_SIZE first, giving -EFAULT,
as does lock_user in `case TARGET_NR_epoll_pwait` in `do_syscall1`
(linux-user/syscall.c, QEMU 11.1.1) before the host call.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedrange -/
theorem pwait_closed_epfd_bad_range_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 140737488355329 1 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The out-of-range event pointer cannot make either the -EBADF of
fs/eventpoll.c `do_epoll_wait` v6.18.46 or the -EFAULT of its v6.1
access_ok against TASK_SIZE a certain closed-fd answer; lock_user in
`case TARGET_NR_epoll_pwait` in `do_syscall1` (linux-user/syscall.c,
QEMU 11.1.1) also gives -EFAULT before the host call.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- pwclosedrange -/
theorem pwait_closed_epfd_bad_range_neither_errno_is_ok (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 140737488355329 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ epoll_pwait_spec 4294967295 140737488355329 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  constructor <;> ep_refute

/-- Two events straddle TASK_SIZE: fs/eventpoll.c `do_epoll_wait` at
v6.1 checks the full range before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes the range product from a one-event range.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_two_events_past_task_size_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 140737488355312 2 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- Two events straddle TASK_SIZE: fs/eventpoll.c `do_epoll_wait` at
v6.1 checks the full range before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes the range product from a one-event range.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_two_events_past_task_size_neither_errno_is_ok (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 140737488355312 2 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ epoll_pwait_spec 4294967295 140737488355312 2 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  constructor <;> ep_refute

/-- The low 32 bits mean -1: fs/eventpoll.c `do_epoll_wait` at v6.14
checks the signed count before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes n ≤ 0 from n = 0.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_minus_one_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 4294967295 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The low 32 bits mean -1: fs/eventpoll.c `do_epoll_wait` at v6.14
checks the signed count before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes n ≤ 0 from n = 0.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_minus_one_neither_errno_is_ok (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ epoll_pwait_spec 4294967295 4096 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  constructor <;> ep_refute

/-- The sign bit alone means INT_MIN: fs/eventpoll.c `do_epoll_wait` at
v6.14 checks the signed count before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes n ≤ 0 from n = 0.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_int_min_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 2147483648 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The sign bit alone means INT_MIN: fs/eventpoll.c `do_epoll_wait` at
v6.14 checks the signed count before the fd, unlike v6.18.46.
Lean declines every null-mask call on a closed epfd, so this pin no
longer distinguishes n ≤ 0 from n = 0.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_int_min_neither_errno_is_ok (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 2147483648 0 0 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ epoll_pwait_spec 4294967295 4096 2147483648 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  constructor <;> ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_closed_epfd_two_events_ending_at_task_size_declines (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 140737488355296 2 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 140737488355296 32 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_closed_epfd_two_events_ending_at_task_size_whole_shape_declines (i : SyscallInput)
    (_m' : Model) (_evs : List event) :
    epoll_pwait_spec 4294967295 140737488355296 2 0 0 i ep_model Unmodeled := by
  cases h : qemu_lock_may i true 140737488355296 32 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Two events end exactly at TASK_SIZE: fs/eventpoll.c `do_epoll_wait`
at v6.1 and v6.18.46 reaches -EBADF in every kernel ordering.
Mappings are irrelevant to the kernels.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_two_events_ending_at_task_size_is_not_einval (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 140737488355296 2 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  cases h : qemu_lock_may i true 140737488355296 32 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_at_bound_declines (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 134217727 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 2147483632 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- The inclusive EP_MAX_EVENTS bound passes, as does its byte range:
fs/eventpoll.c `do_epoll_wait` at v6.14 and v6.18.46 reaches -EBADF
in every kernel ordering.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_at_bound_is_not_einval (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 134217727 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  cases h : qemu_lock_may i true 4096 2147483632 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_refute

/-! ### 3. `maxevents`, signed, before the range

`if (maxevents <= 0 || maxevents > EP_MAX_EVENTS) return -EINVAL;`
(fs/eventpoll.c:2674-2675, Linux v6.18.46).  `maxevents` is an `int`, and
the `<= 0` half refuses every non-positive value; the second half would
refuse a negative one as well, since `EP_MAX_EVENTS` is a `size_t` through
its `sizeof` and the promotion turns a negative `maxevents` into an
`unsigned long` far above the bound.  So the errno is -EINVAL whichever
half fires, and what the signed reading pins is that no negative
`maxevents` reaches the range test of section 4. -/

/-- `maxevents` 0 on an open fd: -EINVAL.  `epoll_spec.c`'s `pwmaxev`
case, first call.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxev -/
theorem pwait_maxevents_zero_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 0 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `maxevents` -1 — 4294967295 after the `int` narrowing, read SIGNED:
-EINVAL from the `<= 0` half.  The `pwmaxev` case's second call.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxev -/
theorem pwait_maxevents_minus_one_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 4294967295 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `INT_MIN` too: the sign bit alone is a negative `int`.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_int_min_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 2147483648 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- THE POSITION OF THE BOUND TEST IS OBSERVABLE: `maxevents` 0 with an
`events` pointer 8 bytes below 2^63 — a range every `access_ok` refuses —
is -EINVAL, because `maxevents <= 0` (fs/eventpoll.c:2674-2675) is decided
before the range (:2678-2679).  A spec that dropped or shifted the
non-positive test would let 0 reach the range test and answer -EFAULT
here; every pin above with `events` at 4096 could not tell the two apart.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_zero_beats_wild_events (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 0 0 0 i ep_model o   -- 2^63 - 8
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and -1 the same way: a negative `maxevents` never reaches the range
test, so the wild pointer is not looked at.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_beats_wild_events (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 4294967295 0 0 i ep_model o   -- 2^63 - 8
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The range's -EFAULT is refused for `maxevents` 0: the bound is decided
first, so the pointer is never judged.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_zero_wild_events_efault_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 9223372036854775800 0 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- …and for -1: the input that catches a spec reading the count UNSIGNED
with no upper bound, which would compute `access_ok(2^63 - 8,
4294967295 * 16)`, fail it, and answer -EFAULT — where at `events` 4096 the
same product fits under `TASK_SIZE` and that spec answers -EINVAL by the
epoll-ness arm instead.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_wild_events_efault_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 9223372036854775800 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- A rejected wait never reports 0 ready events: the `pwmaxev` mutation
(`--mutate epoll_pwait:ret=0`).
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_pwait:ret=0 -- pwmaxev -/
theorem pwait_maxevents_zero_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 0 0 0 i ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- The lie a spec that read `maxevents` UNSIGNED and had no upper bound
would tell on an `events` pointer far enough up: 4294967295 passes such a
gate and `access_ok(events, 4294967295 * 16)` fails, -EFAULT.  At THIS
`events`, 4096, that product (68719476720 bytes) still fits under
`TASK_SIZE`, so the same wrong spec would answer -EINVAL here by the
epoll-ness arm and this refutation alone would not catch it;
`pwait_maxevents_minus_one_beats_wild_events` above, with `events` at
2^63 - 8, is the pin that does.  Refused here all the same: `ep_check_params`
bounds the value on both sides before the range is examined.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_efault_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- `EP_MAX_EVENTS + 1` = 134217728: -EINVAL, the other end of the same
test.  `epoll_spec.c`'s `pwmaxhi` case.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxhi -/
theorem pwait_maxevents_max_plus_one_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 134217728 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- THE BOUND IS VISIBLE: at `EP_MAX_EVENTS` itself with `events` at
2^47 - 16, the bound passes and the RANGE fails — 134217727 * 16 bytes
from there run past `TASK_SIZE` — so the answer is -EFAULT, where one more
event is -EINVAL from the bound.  The pair fixes `EP_MAX_EVENTS` at
134217727 and not at the x86-64 178956970.
Under v6.14's `LONG_MAX` limit (section 4) the range passes and fd 5
answers -EINVAL, so the spec declines.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_at_bound_with_refused_range_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 134217727 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Unmodeled := by
  ep_norm

/-- One more than the bound, same `events`: -EINVAL from the bound, the
range never examined.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_past_bound_is_not_range_checked (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 134217728 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-! ### 4. The `events` range, before the epfd's epoll-ness

`if (!access_ok(evs, maxevents * sizeof(struct epoll_event))) return
-EFAULT;` (fs/eventpoll.c:2678-2679, Linux v6.18.46): a pure range check, with the product
in 64-bit unsigned arithmetic that section 3 has already kept from
overflowing.  Linux reads no byte here and requires no mapping, so the
model's Linux half (`epoll_pwait_linux`) tests the product with `access_okb`
and `access_ok_long_max` and nothing else.  The second test declines a
range that `TASK_SIZE` refuses and `LONG_MAX` passes.  `LONG_MAX` is
riscv64's `TASK_SIZE_MAX` at v6.14 (arch/riscv/include/asm/pgtable.h), and
`__access_ok` (include/asm-generic/access_ok.h) compares against it.
QEMU 11.1.1's `do_syscall1` locks the buffer for writing instead
(`qemu_after_lock`), and that lock does read the mapping. -/

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_ending_at_task_size_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 1 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 140737488355312 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_ending_at_task_size_whole_shape_declines (i : SyscallInput) (_m' : Model)
    (_evs : List event) :
    epoll_pwait_spec 5 140737488355312 1 0 0 i ep_model Unmodeled := by
  cases h : qemu_lock_may i true 140737488355312 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- One byte higher, the range ends past `TASK_SIZE`: -EFAULT before the
fd is looked at for its kind.  `epoll_spec.c`'s `pwevpast` case.
Under v6.14's `LONG_MAX` limit (section 4) the range passes and fd 5
answers -EINVAL, so the spec declines.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_past_task_size_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355313 1 0 0 i ep_model o   -- 2^47 - 15
      ↔ o = Unmodeled := by
  ep_norm

/-- …never -EINVAL: the `pwevpast` mutation.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_past_task_size_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 140737488355313 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_near_2_63_is_efault_or_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 1 0 0 i ep_model o   -- 2^63 - 8
      ↔ (qemu_lock_may i true 9223372036854775800 16 = false ∧
          o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model []) ∨
        (qemu_lock_may i true 9223372036854775800 16 = true ∧ o = Unmodeled) := by
  cases h : qemu_lock_may i true 9223372036854775800 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_events_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 0 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 0 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_events_whole_shape_declines (i : SyscallInput) (_m' : Model) (_evs : List event) :
    epoll_pwait_spec 5 0 1 0 0 i ep_model Unmodeled := by
  cases h : qemu_lock_may i true 0 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-! ### 5. The epfd's epoll-ness

`if (!is_file_epoll(file)) return -EINVAL;` (fs/eventpoll.c:2685-2686, Linux v6.18.46),
with `is_file_epoll` :478-481. -/

/-- fd 2, everything else valid: declined.  A channel's far end can be an
epoll instance: an epoll fd made without `EPOLL_CLOEXEC` survives `execve`.
So `is_file_epoll` is unknown for it.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_channel_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 2 4096 1 0 0 i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_file_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 3 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_dir_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_socket_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 6 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_pipe_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 7 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_devnull_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 9 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_urandom_epfd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 10 4096 1 0 0 i ep_model o
      ↔ o = Unmodeled := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_norm

/-- No count is ever returned: 0 ready events would need `ep_poll`, which
is behind the channel decline.
kernel: fs/eventpoll.c:ep_check_params,do_epoll_wait@v6.18.46 -/
theorem pwait_channel_epfd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 2 4096 1 0 0 i ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- …and nothing is written to `events`: the -EINVAL carries no write.
kernel: fs/eventpoll.c:ep_check_params,do_epoll_wait@v6.18.46 -/
theorem pwait_einval_writes_nothing (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [(4096, List.replicate 16 0)] []) m' evs) := by
  cases h : qemu_lock_may i true 4096 16 <;>
    sys_simp_pass +ground +decide -failIfUnchanged at h <;> ep_norm <;>
    simp only [h] <;> ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_mask_declines (epfd : word) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec epfd 4096 1 0 0 i ep_model o ↔ o = Unmodeled := by
  have hz : epoll_sigmask i.in_mem 0 0 = .EpSigNone := rfl
  have hn : sint32 (1 : word) = 1 := by decide +kernel
  have hc : access_okb (4096 : word) 16 = true := by decide +kernel
  have hmax : ¬ EP_MAX_EVENTS < 1 := by decide +kernel
  have hl : epoll_pwait_linux i ep_model epfd 4096 1 0 0 =
      (match fd_lookup (m_fds ep_model) epfd with
       | none => some (errno_ret EBADF)
       | some e => if ep_epfd_is_channel e then none else some (errno_ret EINVAL)) := by
    simp only [epoll_pwait_linux, hz, hn, epoll_event_bytes, Int.one_mul, hc, hmax,
      show ¬ (1 : Int) ≤ 0 from by decide, ↓reduceIte]
    rfl
  have hq : epoll_pwait_qemu i ep_model epfd 4096 1 0 0 =
      qemu_after_lock i ep_model true 4096 16
        (match fd_lookup (m_fds ep_model) epfd with
         | none => some [errno_ret ENOMEM, errno_ret EBADF]
         | some e => if ep_epfd_is_channel e then none
                     else some [errno_ret ENOMEM, errno_ret EINVAL]) := by
    simp only [epoll_pwait_qemu, show w_is0 (0 : word) = true from rfl, hn, epoll_event_bytes, Int.one_mul, hmax,
      show ¬ (1 : Int) ≤ 0 from by decide, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff]
  unfold epoll_pwait_outcome
  rw [hl, hq]
  cases hf : fd_lookup (m_fds ep_model) epfd with
  | none =>
    cases hm : qemu_lock_may i true 4096 16 <;>
      cases hs : qemu_lock_sure i ep_model true 4096 16 <;>
      simp only [qemu_after_lock, hm, hs, ep_join, Bool.false_eq_true, ↓reduceIte] <;>
      rfl
  | some e =>
    cases e <;> cases hm : qemu_lock_may i true 4096 16 <;>
      cases hs : qemu_lock_sure i ep_model true 4096 16 <;>
      simp only [ep_epfd_is_channel, qemu_after_lock, hm, hs, ep_join,
        Bool.false_eq_true, ↓reduceIte] <;>
      rfl

/-! ## Through the table: numbers, argument slots and the `int` casts

`__NR_epoll_create1` 20, `__NR_epoll_ctl` 21, `__NR_epoll_pwait` 22
(include/uapi/asm-generic/unistd.h:77-81, Linux v6.18.46, the same numbers
scripts/syscall.tbl:32-34 carries, from which riscv64's generated
unistd_64.h is built); there is no
`epoll_create` and no `epoll_wait` number in that table.  riscv64's
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-97, the cast at :88)
hands the registers through `__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46),
so every `int` argument — `flags`, `epfd`, `op`, `fd`, `maxevents` — is
narrowed to its low 32 bits before the callee sees it, and a `size_t` or
a pointer is not.  The table lines apply `flag32`, `fd32` and `int32` for
exactly that reason; these pins are what would catch a line reading the
wrong slot or the whole register. -/

/-- The three numbers are modeled.
kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_create1@v6.18.46 -/
example : (20 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_ctl@v6.18.46 -/
example : (21 : Int) ∈ modeled_sysnos := by decide
/-- kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_pwait@v6.18.46 -/
example : (22 : Int) ∈ modeled_sysnos := by decide

/-- Syscall 20 reads its flag word from a0: bit 0 there is the -EINVAL of
`create_bit_0_is_einval`, through the dispatcher.
kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_create1; fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem sysno_20_is_epoll_create1 (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 20 [1, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- …and from a0 only: the same bit in a1 is not judged, so -EINVAL is
refused (the word in a0 is 0, accepted and declined).
kernel: fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem sysno_20_reads_a0_only (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 20 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- `flags` narrows: 2^32 in a0 is 0 to the `int` and the create is
well-formed, so -EINVAL is refused — `epoll_spec.c`'s `trunc` case sees
the kernel hand out a descriptor.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- trunc -/
theorem sysno_20_bit_32_is_not_einval (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 20 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- …and the high half does not rescue a bad low half: 2^32 + 1 is
-EINVAL.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem sysno_20_bit_32_over_bit_0_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 20 [4294967297, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- …and through the table the narrowed word DECLINES, the `trunc` case's
other half: 2^32 in a0 is the well-formed create the model does not mint.
Stated as the decline itself rather than as an `iff` so that
`tools/check_decline_registers.py` reads it as the shape decline it is (an
`iff` through the dispatcher is a shape that reader refuses); the
refutation above says the -EINVAL is not admitted beside it.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- trunc -/
theorem sysno_20_bit_32_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 20 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := by
  ep_norm

/-- Syscall 21, `epoll_ctl(dirfd, ADD, dirfd, &ev)` with a readable
struct: the -EPERM of `ctl_dir_on_dir_is_eperm`, through the dispatcher —
a0 the epfd, a1 the op, a2 the target, a3 the struct.
kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_ctl; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_is_epoll_ctl (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 5, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- `epoll_ctl(-1, ADD, -1, NULL)`, the `fault` case as the registers carry
it: -1 sign-extended in a0 and a2, NULL in a3, -EFAULT.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem sysno_21_fault_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [Z_to_bv 64 (-1), 1, Z_to_bv 64 (-1), 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- `epoll_ctl(-1, DEL, -1, NULL)`, the `delbad` case: -EBADF, the op in a1
skipping the copy.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- delbad -/
theorem sysno_21_delbad_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [Z_to_bv 64 (-1), 2, Z_to_bv 64 (-1), 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- `op` narrows: 2^32 + 2 in a1 IS `EPOLL_CTL_DEL` to the kernel, so no
copy happens and the NULL struct is not read — -EBADF for the closed
epfd, where a full-register comparison would have copied and faulted.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_op_narrows (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [4294967295, 4294967298, 4294967295, 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …and the -EFAULT a full-register `op` comparison would produce is
refused.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem sysno_21_op_high_half_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [4294967295, 4294967298, 4294967295, 0, 0, 0]
                      (fun _ => none) (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- `epfd` and `fd` narrow: 2^32 + 5 in a0 and 2^32 + 3 in a2 alias onto
the directory and the file, so the answer is the file's -EPERM and not the
-EBADF a 64-bit lookup would give.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_fds_narrow (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [4294967301, 1, 4294967299, 4096, 0, 0] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- …and the -EBADF a 64-bit lookup would give is refused.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem sysno_21_fds_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [4294967301, 1, 4294967299, 4096, 0, 0] ep_mem_all ep_mem_all)
        ep_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- WHICH SLOT IS WHICH: `epoll_ctl(dirfd, ADD, sockfd, &ev)`, the `inval`
case — a0 the epfd (the directory), a2 the target (the socket) — is the
socket's -EINVAL.  Every other table pin here puts the same kind, or a closed
number, in both slots, so a line reading the epfd from a2 and the target
from a0 would pass them all; here it would make the directory the target and
answer -EPERM.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- inval -/
theorem sysno_21_inval_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 6, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and the exchanged reading's -EPERM is refused: the `inval` mutation
through the dispatcher.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EPERM -- inval -/
theorem sysno_21_inval_case_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [5, 1, 6, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- The struct POINTER does not narrow: 2^32 + 4096 in a3 with only
[4096, 4112) mapped is -EFAULT, where a narrowed pointer would have read
the mapped struct and answered -EPERM.
no-row: this synthetic read view contains only sixteen bytes and no executable text or stack; a running task cannot have exactly that memory map
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem sysno_21_event_pointer_is_full_width (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 3, 4294971392, 0, 0]
                    (ep_mem_run 4096 16) (ep_mem_run 4096 16)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_is_epoll_pwait_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 0, 0]
      (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_pwbadfd_case_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_epfd_narrows_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [4294967301, 4096, 1, 0, 0, 0]
      (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_timeout_is_not_read_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 123456789, 0, 0]
      (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_negative_timeout_is_not_read_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, Z_to_bv 64 (-1), 0, 0]
      (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- The `sigsize` case as the registers carry it: a4 the mask pointer, a5
the size 7, -EINVAL from the mask before the closed epfd in a0.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem sysno_22_sigsize_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 0, 0, 4096, 7] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `epoll_pwait(-1, &ev, 1, 0, &mask, 8)`, the `realmask` case as the
registers carry it: a4 the mask, a5 its size, declined.  A line reading the
mask from a3 (the timeout, 0 here) would see no mask and answer the closed
epfd's -EBADF; one reading the size from a3 would answer the bad size's
-EINVAL.
Stated as the decline itself, the shape `tools/check_decline_registers.py`
reads (an `iff` through the dispatcher is one it refuses); the refutation
beside it says what the exchanged reading would have answered.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem sysno_22_realmask_case_declines :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 4096, 8] ep_mem_all ep_mem_all) ep_model
      Unmodeled := by
  ep_norm

/-- …and the closed epfd's -EBADF, which a line taking the mask from a3
would answer, is refused.
no-row: ep_mem_all supplies readable bytes at every address, including kernel-only addresses; no real task can supply this synthetic memory view
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem sysno_22_realmask_case_ebadf_not_admitted (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 4096, 8] ep_mem_all ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- `maxevents` narrows, observably: 2^32 + 1 in a2 is 1 to the `int`, so
with `events` at 2^47 - 15 the RANGE fails and the answer is -EFAULT — a
full-register 4294967297 would have failed the BOUND and answered -EINVAL.
Under v6.14's `LONG_MAX` limit (section 4) the range passes and fd 5
answers -EINVAL, so the spec declines.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_pwait,ep_check_params@v6.18.46 -/
theorem sysno_22_maxevents_narrows (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 140737488355313, 4294967297, 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- …and the bound's -EINVAL, which the full register would have earned,
is refused.
no-row: the corpus holds no row of this exact call, a maxevents wider than 32 bits
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem sysno_22_maxevents_full_register_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 22 [5, 140737488355313, 4294967297, 0, 0, 0]
                      (fun _ => none) (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_sigsetsize_is_full_width_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 4096, 4294967304] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_sigmask_pointer_is_full_width_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 4294971392, 8]
      (ep_mem_run 4096 16) (ep_mem_run 4096 16))
        ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `EventPoll.fd_can_poll`, EventPoll.v:281-282 at 96c2debdb.
The assumed tmpfs file has no ->poll even when opened O_RDWR; fs/eventpoll.c,
do_epoll_ctl, Linux v6.18.46 answers -EPERM when file_can_poll is false.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem a17_rdwr_cannot_epoll :
    fd_can_poll (.FdFileRW [102] 0) = some false := by
  rfl

/-- Rocq: `EventPoll.fd_can_poll`, EventPoll.v:281-282 at 96c2debdb.
The assumed tmpfs file has no ->poll in append mode either: O_APPEND moves
where a write lands, not the file's f_op; fs/eventpoll.c, do_epoll_ctl,
Linux v6.18.46 answers -EPERM when file_can_poll is false.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem a17_append_cannot_epoll :
    fd_can_poll (.FdFileA [102] 0) = some false := by
  rfl


/-! ## Shared fixtures for the Rocq example twins -/

def epoll_row_model : Model :=
  fixture_of (fds := [(0, .FdDir)])

def epoll_lock_mem (a : word) : Option byte :=
  if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4112 then some 0 else none

def epoll_lock_model : Model :=
  fixture_of (fds := [(0, .FdDir)]) (h := mkVmMaps [] [(4096, 4096)] 0 0 demo_limit)

def epoll_ctl_raw_in (op ev : word) : SyscallInput :=
  SyscallInput.mkInput 21 [9999, op, 9999, ev] (fun _ => none) (fun _ => none)

def epoll_mask_count_in (n : word) : SyscallInput :=
  SyscallInput.mkInput 22 [0, 4096, n, 0, 8, 8] (fun _ => none) (fun _ => none)

def epoll_lock_in (write : Bool) : SyscallInput :=
  SyscallInput.mkInput 22 [0, 4096, 1, 0, 0, 0] epoll_lock_mem
    (if write then epoll_lock_mem else fun _ => none)

def epoll_row_pwait_in (epfd events n : word) : SyscallInput :=
  SyscallInput.mkInput 22 [epfd, events, n, 0, 0, 0] (fun _ => none) (fun _ => none)

def epoll_load_model : Model :=
  fixture_of (fds := [(0, .FdDir)]) (h := mkVmMaps [(4096, 4096)] [] 0 0 demo_limit)

/-- Linux copies this readable event and answers EPERM for the directory
as target. The conservative QEMU lock bound refuses to call a writable
LOAD overlap sure: QEMU 11.1.1 linux-user/uaccess.c, `lock_user`, relies
on linux-user/qemu.h, `access_ok_untagged`, and its page permissions.
Lean therefore declines the base answer here. This pins that coverage
refusal, not a claim that the overlapping LOAD must fault under QEMU.
The kernel citation supports only Linux's EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_event_in_writable_load_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 0 1 0 4096
      (SyscallInput.mkInput 21 [0, 1, 0, 4096] epoll_lock_mem epoll_lock_mem)
      epoll_load_model o ↔ o = Unmodeled := by
  ep_norm

def epoll_read_only_closed_in : SyscallInput :=
  SyscallInput.mkInput 22 [9999, 4096, 1, 0, 0, 0] epoll_lock_mem (fun _ => none)

def epoll_wrap_in : SyscallInput :=
  SyscallInput.mkInput 21 [0, 1, 0, 18446744073709551608]
    (fun _ => some 0) (fun _ => some 0)

def epoll_stack_model : Model :=
  fixture_of (fds := [(0, .FdDir)])
    (h := VmMaps.mkVmMapsFull [] [(8384512, 8192)] [] 0 0
      demo_limit 0 16777216)

def epoll_stack_mem (a : word) : Option byte :=
  if 8384512 ≤ bv_unsigned a ∧ bv_unsigned a < 8392704 then some 0
  else none

def epoll_stack_in (events : word) : SyscallInput :=
  SyscallInput.mkInput 22 [0, events, 1, 0, 0, 0]
    epoll_stack_mem epoll_stack_mem

/-- The entry-stack fixture has a regular and a pollable target on distinct descriptors. -/
def epoll_stack_ctl_model : Model :=
  fixture_of (fds := [(0, .FdDir), (3, .FdFile [] 0), (6, .FdSocket .SkFresh)])
    (h := VmMaps.mkVmMapsFull [] [(8384512, 8192)] [] 0 0 demo_limit 0 16777216)

def epoll_stack_ctl_in (tfd : word) : SyscallInput :=
  SyscallInput.mkInput 21 [0, 1, tfd, 8388608] epoll_stack_mem epoll_stack_mem

/-- Linux copies this mapped stack event, then answers EPERM for the regular target.
QEMU 11.1.1 linux-user/main.c, `handle_arg_stack_size`, allows a smaller stack
than the model's initialized band; linux-user/syscall.c, `do_syscall1`,
returns EFAULT when its event read lock fails. The conservative lock bound
therefore leaves EFAULT possible. Lean declines both answers on this ADD shape.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_file_target_declines :
    epoll_ctl_spec 0 1 3 8388608 (epoll_stack_ctl_in 3) epoll_stack_ctl_model Unmodeled := by
  have ho : epoll_ctl_outcome (epoll_stack_ctl_in 3) epoll_stack_ctl_model
      0 1 3 8388608 = none := by decide +kernel
  unfold epoll_ctl_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- The pollable socket reaches Linux's EINVAL instead of the regular target's EPERM.
The same stack lock uncertainty still leaves QEMU's EFAULT possible; Lean declines
this whole shape, including the base EINVAL.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_socket_target_declines :
    epoll_ctl_spec 0 1 6 8388608 (epoll_stack_ctl_in 6) epoll_stack_ctl_model Unmodeled := by
  have ho : epoll_ctl_outcome (epoll_stack_ctl_in 6) epoll_stack_ctl_model
      0 1 6 8388608 = none := by decide +kernel
  unfold epoll_ctl_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- A missing target reaches Linux's EBADF after the stack event copy.
QEMU can fail the uncertain entry-stack lock first, so Lean declines even EBADF.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_closed_target_declines :
    epoll_ctl_spec 0 1 9999 8388608 (epoll_stack_ctl_in 9999) epoll_stack_ctl_model Unmodeled := by
  have ho : epoll_ctl_outcome (epoll_stack_ctl_in 9999) epoll_stack_ctl_model
      0 1 9999 8388608 = none := by decide +kernel
  unfold epoll_ctl_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-! ## Lean declines ahead of the Rocq change in #1925 -/

/-- Linux v6.18.46 fs/eventpoll.c [do_epoll_ctl] tests `is_file_epoll` after target pollability.
A channel epfd can hold an epoll instance, so the model declines at that test.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_channel_epfd_spec_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 0 1 6 4096
      (SyscallInput.mkInput 21 [0, 1, 6, 4096] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Unmodeled := by
  ep_norm

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_event_past_task_size_declines :
    epoll_ctl_spec 5 2 6 (Z_to_bv 64 (2 ^ 47))
      (SyscallInput.mkInput 21 [5, 4294967298, 6, Z_to_bv 64 (2 ^ 47)]
        ep_mem_all ep_mem_all) ep_model
      Unmodeled := by
  have ho : epoll_ctl_outcome
      (SyscallInput.mkInput 21 [5, 4294967298, 6, Z_to_bv 64 (2 ^ 47)]
        ep_mem_all ep_mem_all) ep_model 5 2 6 (Z_to_bv 64 (2 ^ 47))
      = none := by
    decide +kernel
  unfold epoll_ctl_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_high_del_declines :
    epoll_ctl_spec 9999 2 9999 4096 (epoll_ctl_raw_in 4294967298 4096) epoll_row_model
      Unmodeled := by
  have ho : epoll_ctl_outcome (epoll_ctl_raw_in 4294967298 4096) epoll_row_model
      9999 2 9999 4096 = none := by
    decide +kernel
  unfold epoll_ctl_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_mask_count_declines :
    epoll_pwait_spec 0 4096 0 8 8 (epoll_mask_count_in 0) epoll_row_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_mask_count_in 0) epoll_row_model
      0 4096 0 8 8 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_mask_count_overflow_declines :
    epoll_pwait_spec 0 4096 134217728 8 8 (epoll_mask_count_in 134217728) epoll_row_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_mask_count_in 134217728) epoll_row_model
      0 4096 134217728 8 8 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_events_declines :
    epoll_pwait_spec 0 0 1 0 0 (epoll_row_pwait_in 0 0 1) epoll_row_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_row_pwait_in 0 0 1) epoll_row_model
      0 0 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this whole shape, including every proposed answer.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params@v6.18.46 -/
theorem pwait_events_null_enomem (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 0 0 1 0 0 (epoll_row_pwait_in 0 0 1) epoll_row_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  have ho : epoll_pwait_outcome (epoll_row_pwait_in 0 0 1) epoll_row_model
      0 0 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  simp only [unmodeled, reduceCtorEq, not_false_eq_true]

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_events_whole_shape_declines :
    epoll_pwait_spec 0 4096 1 0 0 (epoll_lock_in true) epoll_lock_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_lock_in true) epoll_lock_model
      0 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_read_only_declines :
    epoll_pwait_spec 0 4096 1 0 0 (epoll_lock_in false) epoll_lock_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_lock_in false) epoll_lock_model
      0 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this whole shape, including every proposed answer.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params@v6.18.46 -/
theorem pwait_events_read_only_enomem (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 0 4096 1 0 0 (epoll_lock_in false) epoll_lock_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  have ho : epoll_pwait_outcome (epoll_lock_in false) epoll_lock_model
      0 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  simp only [unmodeled, reduceCtorEq, not_false_eq_true]

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_writable_load_declines :
    epoll_pwait_spec 0 4096 1 0 0 (epoll_lock_in true) epoll_load_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_lock_in true) epoll_load_model
      0 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_read_only_closed_declines :
    epoll_pwait_spec 9999 4096 1 0 0 epoll_read_only_closed_in epoll_lock_model
      Unmodeled := by
  have ho : epoll_pwait_outcome epoll_read_only_closed_in epoll_lock_model
      9999 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- Lean declines this whole shape, including every proposed answer.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params@v6.18.46 -/
theorem pwait_events_read_only_closed_enomem_rejected (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 9999 4096 1 0 0 epoll_read_only_closed_in epoll_lock_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  have ho : epoll_pwait_outcome epoll_read_only_closed_in epoll_lock_model
      9999 4096 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  simp only [unmodeled, reduceCtorEq, not_false_eq_true]

/-- Lean declines this shape when the implementations can disagree.
The Linux answer is retained only when every computed QEMU answer agrees;
otherwise even the base answer is declined ahead of the Rocq change in #1925.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_events_stack_band_declines :
    epoll_pwait_spec 0 8388608 1 0 0 (epoll_stack_in 8388608) epoll_stack_model
      Unmodeled := by
  have ho : epoll_pwait_outcome (epoll_stack_in 8388608) epoll_stack_model
      0 8388608 1 0 0 = none := by
    decide +kernel
  unfold epoll_pwait_spec
  rw [bind_input_iff, bind_get_model_iff, ho]
  rfl

/-- The conservative QEMU helper retains the host's EINVAL after the events lock,
its allocation's ENOMEM, and the uncertain lock's EFAULT. These are the modeled
branches of QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, epoll_pwait case;
this statement does not attribute QEMU's allocation to Linux's ep_check_params.
model: computation of the explicit conservative QEMU helper answer list -/
theorem pwait_qemu_directory_epfd_answers :
    epoll_pwait_qemu (pw_in ep_mem_all) ep_model 5 9223372036854775808 1 0 0 =
      some [errno_ret EFAULT, errno_ret ENOMEM, errno_ret EINVAL] := by
  decide +kernel

/-- Synthetic defined events above LONG_MAX expose the QEMU half's descriptor gate.
A channel's far end can be an epoll instance when QEMU reaches the host call.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, reaches the host `epoll_pwait`.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params@v6.18.46 -/
theorem pwait_qemu_channel_epfd_declines :
    epoll_pwait_qemu (pw_in ep_mem_all) ep_model 0 9223372036854775808 1 0 0 = none := by
  decide +kernel

/-- With no bytes at the mask address, the read lock fails.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, can fail its allocation first;
linux-user/signal.c, `process_sigsuspend_mask`, then faults on the mask.
model: computation of the QEMU helper's allocation and mask-lock answer list -/
theorem pwait_qemu_unreadable_mask_answers :
    epoll_pwait_qemu (pw_in (ep_mem_run 4096 16)) ep_model
      5 4096 1 140737488355328 8 = some [errno_ret ENOMEM, errno_ret EFAULT] := by
  decide +kernel

/-- Only the low events buffer is writable; the mask at TASK_SIZE is readable.
QEMU's mask read lock can succeed where Linux's range test fails.
QEMU 11.1.1 linux-user/signal.c, `process_sigsuspend_mask`, uses a read lock
when called by linux-user/syscall.c, `do_syscall1`.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params@v6.18.46 -/
theorem pwait_qemu_mask_past_task_size_declines :
    epoll_pwait_qemu (SyscallInput.mkInput 22 [] ep_mem_all (ep_mem_run 4096 16)) ep_model
      5 4096 1 140737488355328 8 = none := by
  decide +kernel

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
