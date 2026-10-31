-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/EventPoll.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.EventPoll — what epoll_create1, epoll_ctl and epoll_pwait answer, read off against Linux

Worked examples over `Sys.Fs.EventPoll`'s three specs.  Rocq keeps no
worked-cases file for them at f1006fe8 (its
`theories/LinuxProcessSem/Checks/Cases/Fs/` directory has no
`EventPoll.v`), and sends every claim to a probe against a real kernel
(`testing/syscall-check/tests/epoll_spec.c`).  So this file has no Rocq
twin to mirror; what it pins is the answer the ported spec gives, with
the kernel line each answer rests on.  The checker pins live in
`Checks/Cases/Checks/Sys/Fs/EventPoll.lean`.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ,
and every claim in it is a claim about what Linux does, with the citation
beside it — fs/eventpoll.c at Linux v6.18.46 (commit 1f99e9ab748f) unless
another file is named, the function and line on each pin.

HOW THESE ARE STATED.  A check is stated on the relation itself
(`Checks/Cases/Mm/Mmap.lean`'s header says why): an `iff` over EVERY
outcome `o`,

    epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model []

pins the positive half (-EPERM is admitted, the model and the event list
untouched) and the negative half (nothing else is — not another errno,
not a write, not `Unmodeled`) in one statement.  Each of the three specs
gives ONE answer per input or declines it; an `iff` pins that answer or
the decline.  Each is closed by `ep_norm`; beside it, the concrete lie a
kernel could tell there is refuted by `ep_refute`.  The sections follow
the kernel's order — the syscall entry, then the callee's tests in
sequence — and each section pins the answer against the one the NEXT
check would have given, which is what makes the order a claim and not a
convention.

WHAT IS SYMBOLIC AND WHAT IS NOT.  A pin whose arm reads no user memory
takes the input `i` symbolic, which is the statement that no byte is
read: the `epoll_create1` pins and the `EPOLL_CTL_DEL` pins are of that
shape, since `ep_op_has_event` keeps `EPOLL_CTL_DEL` away from the copy
(include/linux/eventpoll.h:64-67, Linux v6.18.46).  A pin whose arm
copies from user memory names the memory through `ep_in` or `pw_in`, so
the copy's verdict is decided.  The pins use `ep_model` to distinguish
descriptor kinds: fd 3 is a regular file, fd 6 a socket, and so on down
the fixture's docstring.

THE THREE DECLINES, and they are the only ones: `epoll_create1` declines
a well-formed flag word (its success arm is not modeled), `epoll_ctl`
declines a target whose `->poll` the model cannot decide (a channel,
/dev/null, /dev/urandom), and `epoll_pwait` declines a signal mask that
would be installed.  Every other input to any of the three is answered,
including every closed descriptor and every refused range.

THE ROCQ FILE'S ONE EXAMPLE HAS ITS TWIN HERE.  Rocq keeps
`fd_can_poll_is_select_pollable` beside its definitions, pinning that
`fd_can_poll` and `Select.bits_all_pollable` stay complementary; the Lean
tree keeps every check in `Checks/Cases/`, so the twin is
`fd_can_poll_is_select_pollable` below, and this file — not the trusted
spec twin — imports `Sys.Fs.Select` for it.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

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
  epoll_ctl_spec.eq_1 epoll_ctl_outcome.eq_1
  epoll_pwait_spec.eq_1 epoll_pwait_outcome.eq_1 epoll_sigmask.eq_1

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

/-- `EPOLL_CLOEXEC` is `O_CLOEXEC`, bit 19
(include/uapi/linux/eventpoll.h:23, with the `BUILD_BUG_ON` of
fs/eventpoll.c:2437, Linux v6.18.46).
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
(include/uapi/linux/eventpoll.h:77-81, Linux v6.18.46), so the `__u64 data`
member takes its natural alignment and the struct carries four bytes of
padding.
model: the model's own constant at a numeral; the kernel value is a `sizeof`, which no macro spells -/
example : epoll_event_bytes = 16 := by decide

/-- `EP_MAX_EVENTS` is `INT_MAX / sizeof(struct epoll_event)`
(fs/eventpoll.c:222, Linux v6.18.46) with `INT_MAX` = `((int)(~0U >> 1))`
(include/vdso/limits.h:8, Linux v6.18.46).
model: the model's own constant at a numeral; the kernel value is a quotient of a `sizeof`, which no macro spells -/
example : EP_MAX_EVENTS = 134217727 := by decide

/-- …and it IS that quotient, so a reader can re-derive it: 2^31 - 1 over
the 16 above.  A packed 12 would give 178956970 instead.
model: the derivation of the model's constant from its own `epoll_event_bytes` -/
example : EP_MAX_EVENTS = (2 ^ 31 - 1) / epoll_event_bytes := by decide

/-! ## `file_can_poll`, kind by kind

`file_can_poll` (include/linux/poll.h:73-76, Linux v6.18.46) is
`file->f_op->poll` read as a truth value, and it is what `do_epoll_ctl`
(fs/eventpoll.c:2530-2531) tests for its -EPERM. -/

/-- A regular file opened for reading has no `->poll`.
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
`.poll` is `sock_poll` (:1426-1445, set at :160).
kernel: include/linux/poll.h:file_can_poll; net/socket.c:sock_alloc_file,sock_poll@v6.18.46 -/
example : fd_can_poll (.FdSocket .SkFresh) = some true := by decide

/-- Both pipe ends HAVE a `->poll`: `create_pipe_files` (fs/pipe.c:926-980)
gives both files `pipeanon_fops` (at :946 and :957), whose `.poll` is
`pipe_poll` (:1261).
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
example : fd_can_poll (.FdPipe 0 false) = some true := by decide

/-- …and the writer's, by the same table.
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
example : fd_can_poll (.FdPipe 0 true) = some true := by decide

/-- A CHANNEL is declined: the model does not know whether its far end is
a pipe (whose `pipe_poll`, fs/pipe.c:659-707, IS a `->poll`) or a regular
file or /dev/null (which have none).
kernel: include/linux/poll.h:file_can_poll; fs/pipe.c:pipe_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll (.FdChannel 2) = none := by decide

/-- /dev/null is declined though the answer is exact — `null_fops`
(drivers/char/mem.c:644-652), installed by `memory_open` (:707-727), has no
`.poll` — because the spec declines it until it has its own probe.
kernel: include/linux/poll.h:file_can_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll (.FdDevNull true true) = none := by decide

/-- /dev/urandom likewise: `urandom_fops` (drivers/char/random.c:1572-1581)
has no `.poll` — `random_fops` (:1560-1570) has `random_poll`
(:1563) and the urandom table does not.
kernel: include/linux/poll.h:file_can_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
example : fd_can_poll .FdUrandom = none := by decide

/-- The complement claim, as a check rather than a sentence — the twin of
Rocq's Example of the same name, kept beside its definitions there and here
in `Checks/Cases/`: the descriptor kinds `Select.bits_all_pollable` can
answer for are exactly the kinds `epoll_ctl` refuses with -EPERM, because
both read the same NULL `->poll`.
kernel: include/linux/poll.h:file_can_poll,vfs_poll@v6.18.46 -/
theorem fd_can_poll_is_select_pollable (e : FdEntry) :
    bits_all_pollable [(Z_to_bv 64 0, e)] 1 1 = true ↔ fd_can_poll e = some false := by
  cases e <;> first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    -- The kinds `fd_can_poll` answers `some true` for: `FdSocket`, `FdPipe`.
    -- Each goal is a CLOSED proposition after the arms reduce, but the
    -- constructor's own arguments are free variables in the terms around it,
    -- so `decide` is given the reduced proposition by ascription and
    -- `absurd` does the (definitional) match back onto the goal.
    | exact ⟨fun h => absurd h (by decide : ¬(false = true)),
             fun h => absurd h (by decide : ¬(some true = some false))⟩
    -- …and the kinds it declines: `FdChannel`, `FdDevNull`, `FdUrandom`.
    | exact ⟨fun h => absurd h (by decide : ¬(false = true)),
             fun h => absurd h (by decide : ¬((none : Option Bool) = some false))⟩

/-! ## `copy_from_user`, in two answers

`copy_from_user` (include/linux/uaccess.h:204-214, Linux v6.18.46) reaches
`_inline_copy_from_user` (:158-185), whose `access_ok` (:168) is the RANGE
test and runs before a byte is read.  `ep_mem_all` maps every address;
`ep_mem_run lo n` maps exactly `n` bytes from `lo`. -/

def ep_mem_all : word → Option byte := fun _ => some 0

def ep_mem_run (lo n : Nat) : word → Option byte :=
  fun a => if lo ≤ a.toNat ∧ a.toNat < lo + n then some 0 else none

/-- A fully mapped 16-byte struct at a page boundary: readable.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 4096 16 = true := by decide

/-- NULL is a FAULT ADDRESS and not a range failure: `access_ok(NULL, 16)`
passes and the byte walk then finds nothing mapped.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok (fun _ => none) 0 16 = false := by decide

/-- Twelve mapped bytes of a sixteen-byte struct: a FAULT.  The struct is
16 bytes on riscv64, so the thirteenth byte is read and is unmapped.
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
exactly at `TASK_SIZE` (2^47 on Sv48) pass `__access_ok`.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 140737488355312 16 = true := by decide   -- 2^47 - 16

/-- …and 16 bytes ending one past it fail, however readable the memory
says the bytes are: the range is refused before a byte is read.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 140737488355313 16 = false := by decide  -- 2^47 - 15

/-- THE WRAP: a struct at 2^64 - 8 would be read by the byte walk alone as
eight bytes off the top and eight off address 0, and the range test is
what refuses it.  `linux-process-semantics@ff0313ba4f:bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md`
names the sites where the range is not yet tested first; this is not one.
kernel: include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
example : copy_from_user_ok ep_mem_all 18446744073709551608 16 = false := by decide  -- 2^64 - 8

/-- `copy_from_user_ok` is `State.copy_bytes_map`'s verdict: both spell one
pair, `access_okb` and then `read_bytes_map`, and Rocq's `State.v` names
this function as one of the two callers still to move onto it.
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
number nor the argument list, so the two differ only in the number the
evidence checker reads off them to match a pin to its probe's syscall;
the table pins build their own inputs. -/
def ep_in (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 21 [] mem mem

def pw_in (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 22 [] mem mem

attribute [sys_simp low] ep_in.eq_1 pw_in.eq_1

/-- The read-only memory of a probe's recording is enough for `epoll_ctl`:
the arm reads the event struct and writes nothing, so the input's
post-syscall memory decides no answer.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_read_only_event_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096
      (SyscallInput.mkInput 21 [5, 1, 3, 4096] (ep_mem_run 4096 16) (fun _ => none))
      ep_model o ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- …and for `epoll_pwait` the same: an unreadable mask is -EFAULT
whatever the events buffer is, because nothing is written on any modeled
path.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem pwait_read_only_events_unreadable_mask_is_efault (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 1 8192 8
      (SyscallInput.mkInput 22 [5, 4096, 1, 0, 8192, 8]
        (ep_mem_run 4096 16) (fun _ => none))
      ep_model o ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-! ## epoll_create1 (20): `do_epoll_create`'s one `if`

`if (flags & ~EPOLL_CLOEXEC) return -EINVAL;` (fs/eventpoll.c:2439-2440,
Linux v6.18.46) is the first statement of `do_epoll_create` (:2430-2471)
that can fail, and it precedes `ep_alloc` (:2444) and
`get_unused_fd_flags` (:2451).  The mask is taken over 32 bits, because
`flags` is an `int` (:2473).  A word inside the mask passes the gate and
is declined: minting an epoll descriptor needs a `State.FdEntry` the
model does not have. -/

/-- Bit 0 alone: -EINVAL, the model untouched, no event.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- badflags -/
theorem create_bit_0_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- `EPOLL_CLOEXEC` beside bit 0: an accepted bit does not excuse a
refused one, because the residue keeps only the bits outside the mask.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_plus_bit_0_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    epoll_create1_spec 524289 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Bit 18, just below `EPOLL_CLOEXEC`'s bit 19.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_18_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 262144 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Bit 20, just above it: the mask is a mask and not a bound.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_20_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 1048576 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Bit 31, the sign bit of the `int`: the residue is used as the `if`
condition itself (:2439), so a negative residue is as refused as 1 is.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_sign_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 2147483648 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- Every bit of the `int` at once.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_all_ones_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 4294967295 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- A descriptor 0 for a refused word is a lie: the gate returns before
`get_unused_fd_flags` (:2451) reserves a number.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_create1:ret=0 -- badflags -/
theorem create_bit_0_fd_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- …and so is descriptor 3.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_0_fd_three_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect 3 [] []) m' evs) := by
  ep_refute

/-- -ENOMEM is unreachable on a refused word: `ep_alloc` (:2444, with its
-ENOMEM at fs/eventpoll.c:1341-1363) runs below the gate.
kernel: fs/eventpoll.c:do_epoll_create,ep_alloc@v6.18.46 -/
theorem create_bit_0_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  ep_refute

/-- -EMFILE likewise: `get_unused_fd_flags` (:2451) is below the gate.
kernel: fs/eventpoll.c:do_epoll_create; fs/file.c:get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem create_bit_0_emfile_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  ep_refute

/-- A refused word is ANSWERED and never declined.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_bit_0_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ epoll_create1_spec 1 i m Unmodeled := by
  ep_refute

/-- The -EINVAL is inert: an event beside the right errno is refused too.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_einval_with_an_event_rejected (i : SyscallInput) (m m' : Model) :
    ¬ epoll_create1_spec 1 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' [WriteEv 1 65]) := by
  ep_refute

/-! ### The accepted words decline rather than answer

Every word inside the mask passes the gate, and everything past the gate
ends in a descriptor or in an errno the model cannot place (-ENOMEM,
-EMFILE).  The model has no epoll `FdEntry`, so the arm declines. -/

/-- The empty flag word, which is what `epoll_create(size)` compiles to
on riscv64: past the gate, declined.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- create -/
theorem create_zero_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 0 i m o ↔ o = Unmodeled := by
  ep_norm

/-- `EPOLL_CLOEXEC` alone, the one accepted bit: declined.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 524288 i m o ↔ o = Unmodeled := by
  ep_norm

/-- Bit 32 is not part of the `int` the mask is taken over, so the word
is the empty word and is declined, not refused.
kernel: fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem create_bit_32_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    epoll_create1_spec 4294967296 i m o ↔ o = Unmodeled := by
  ep_norm

/-- The descriptor Linux DOES hand back for `epoll_create1(0)` is not
admitted: the arm declines, and an acceptor built on it must too.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- create -/
theorem create_zero_descriptor_not_admitted (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 0 i m (Ok (mkEffect 3 [] []) m' evs) := by
  ep_refute

/-- …and the -EINVAL a narrower mask would have produced for
`EPOLL_CLOEXEC` is refused.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_cloexec_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ epoll_create1_spec 524288 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-! ## epoll_ctl (21), in the kernel's order

`SYSCALL_DEFINE4(epoll_ctl, int, epfd, int, op, int, fd, struct
epoll_event __user *, event)` (fs/eventpoll.c:2658-2668, Linux v6.18.46)
copies the event struct and then calls `do_epoll_ctl` (:2511-2651), whose
tests run in the order the sections below follow. -/

/-! ### 1. The copy, before any descriptor is resolved

`if (ep_op_has_event(op) && copy_from_user(&epds, event, sizeof(struct
epoll_event))) return -EFAULT;` (:2663-2665), in the syscall entry, so an
unreadable `event` beats -EBADF on either descriptor. -/

/-- `EPOLL_CTL_DEL` (2) does not copy.
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
`int32` is the `int` cast, applied once, before the word reaches here.
kernel: include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
example : ep_op_has_event 4294967298 = true := by decide

/-- `ADD` with a NULL `event` on a CLOSED epfd and a closed target: -EFAULT,
because the copy runs in the entry before `do_epoll_ctl` looks anything up.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem ctl_add_null_event_on_closed_epfd_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 4294967295 1 4294967295 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and the -EBADF the other order would give is refused.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_null_event_on_closed_epfd_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 4294967295 1 4294967295 0 (ep_in (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- Under `EPOLL_CTL_DEL` no copy happens, so the wildest `event` pointer
is never dereferenced and the closed epfd decides: -EBADF, at every
`event` and every input.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- delbad -/
theorem ctl_del_closed_epfd_is_ebadf (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 4294967295 2 4294967295 ev i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …so -EFAULT under `EPOLL_CTL_DEL` is a lie whatever the pointer:
`epds` is left uninitialised and the DEL path never reads it.
kernel: fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_del_closed_epfd_efault_rejected (ev : word) (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_ctl_spec 4294967295 2 4294967295 ev i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- An unrecognised op copies, so a NULL `event` beside it is -EFAULT.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_unknown_op_null_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 7 3 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Twelve readable bytes are not a `struct epoll_event`: -EFAULT.
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem ctl_add_twelve_readable_bytes_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 12)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and the -EPERM an x86-64 reader's packed 12 would have reached is
refused.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_twelve_readable_bytes_is_not_eperm (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 12)) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- Sixteen readable bytes reach the target, which has no `->poll`: -EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem ctl_add_sixteen_readable_bytes_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (ep_mem_run 4096 16)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- A struct one byte past `TASK_SIZE` is refused by the range test
before a byte is read: -EFAULT.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_add_event_past_task_size_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 140737488355313 (ep_in ep_mem_all) ep_model o   -- 2^47 - 15
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and one ending exactly at `TASK_SIZE` passes it and reaches the
target: -EPERM.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_add_event_ending_at_task_size_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 140737488355312 (ep_in ep_mem_all) ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- A struct that would WRAP the address space is -EFAULT: the range test
refuses it, where a byte walk alone would read eight bytes off the top
and eight off address 0.
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_add_wrapped_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 18446744073709551608 (ep_in ep_mem_all) ep_model o   -- 2^64 - 8
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and so is a struct that ends exactly at the top of the word space:
2^64 - 16 is past `TASK_SIZE` like every address above it.
kernel: fs/eventpoll.c:epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_event_at_word_space_end_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (2 ^ 64 - 16))
      (ep_in ep_mem_all) ep_model o ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and one byte further on, which would overrun it.
kernel: fs/eventpoll.c:epoll_ctl; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ctl_word_space_overrun_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 (Z_to_bv 64 (2 ^ 64 - 15))
      (ep_in ep_mem_all) ep_model o ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- The CONTENTS of the struct are never judged, only its readability: a
struct of 0xff bytes answers exactly as a struct of zeros does.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_event_contents_not_judged (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in (fun _ => some 255)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-! ### 2. The epfd, before the target

`CLASS(fd, f)(epfd); if (fd_empty(f)) return -EBADF;` (:2520-2522), with
`fd_empty` include/linux/file.h:45-48, Linux v6.18.46. -/

/-- A closed epfd with a readable event and an open target: -EBADF.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_epfd_is_ebadf (o : outcome SyscallEffect) :
    epoll_ctl_spec 99 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …and the -EPERM the target's missing `->poll` would give is refused:
the epfd is resolved first.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_epfd_is_not_eperm (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 99 1 3 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-! ### 3. The target, before its `->poll`

`CLASS(fd, tf)(fd); if (fd_empty(tf)) return -EBADF;` (:2525-2527) — a
second `fd_empty` test, reached only past the first. -/

/-- A closed target under an open epfd: -EBADF.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- tgtbad -/
theorem ctl_closed_target_is_ebadf (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 4294967295 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …and the -EINVAL of the epoll-ness test is refused: the target is
resolved first.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_closed_target_is_not_einval (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 4294967295 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-! ### 4. The target's `->poll`, before the epfd's epoll-ness

`if (!file_can_poll(fd_file(tf))) return -EPERM;` (:2530-2531).  This is
the arm worth knowing: it sits BEFORE the test that `epfd` is an epoll
fd, so `epoll_ctl` on two ordinary files is -EPERM and not -EINVAL. -/

/-- A directory target under a directory epfd: -EPERM.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- perm -/
theorem ctl_dir_on_dir_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- …and the -EINVAL a reader who assumed the epoll-ness test came first
would expect is refused.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EINVAL -- perm -/
theorem ctl_dir_on_dir_einval_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- A regular-file target: -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- A file opened for writing: the access mode does not change `f_op`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_write_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 4 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- The TARGET and not the epfd is asked for its `->poll`: a socket epfd
with a file target is still -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_socket_epfd_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 6 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- `EPOLL_CTL_MOD` reaches the same test: the op decides only whether the
struct is copied.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_mod_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 3 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- `EPOLL_CTL_DEL` on a file target is -EPERM at every `event` pointer
and every input: skipping the copy does not skip the `->poll` test.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_file_target_is_eperm (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 2 3 ev i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- The success `EPOLL_CTL_ADD` would have on an epoll epfd is refused
here: the target has no `->poll`.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem ctl_file_target_success_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 3 4096 (ep_in ep_mem_all) ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- The copy-in is NOT recorded, which is a known-wrong omission and not
a kernel claim:
`linux-process-semantics@ff0313ba4f:bugs/epoll-ctl-copyin-not-recorded.md`.
The pin fixes the model's answer, so the omission is visible where it is
made.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:smuggle-copyin:a3:16 -- perm -/
theorem ctl_dir_on_dir_copyin_not_recorded (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 5 4096 (ep_in ep_mem_all) ep_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [] [(4096, 16)]) m' evs) := by
  ep_refute

/-! ### 5. The epfd's epoll-ness: -EINVAL for every pollable target

`error = -EINVAL; if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
goto error_tgt_fput;` (:2542-2544), with `is_file_epoll` :478-481.  No
`State.FdEntry` denotes an epoll instance, so the second disjunct always
holds and every call that reaches here is -EINVAL. -/

/-- A socket target, which HAS a `->poll`: -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- inval -/
theorem ctl_socket_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and the -EPERM of the previous test is refused for it.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EPERM -- inval -/
theorem ctl_socket_target_eperm_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- …and so is the success an epoll epfd would have given.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll@v6.18.46 -/
theorem ctl_socket_target_success_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 6 4096 (ep_in ep_mem_all) ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- A pipe's read end: -EINVAL, by the same route.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_read_end_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 7 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and -EPERM for it is refused.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_read_end_target_eperm_rejected (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 7 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- The write end answers the same: both ends carry `pipe_poll`.
kernel: fs/eventpoll.c:do_epoll_ctl; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem ctl_pipe_write_end_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 8 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- An unrecognised op with a pollable target is -EINVAL through the
epoll-ness test, not through the `switch`'s fallthrough.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/eventpoll.h:ep_op_has_event@v6.18.46 -/
theorem ctl_unknown_op_socket_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 7 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A socket added to itself: -EINVAL, and the model needs no notion of
description identity to get it right, because the second disjunct is
what holds.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll@v6.18.46 -/
theorem ctl_socket_on_itself_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 6 1 6 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A CHANNEL epfd is judged like any other descriptor: it is open, so
the socket target's -EINVAL is the answer.  The epfd's kind is read by
nothing this arm reaches.
kernel: fs/eventpoll.c:do_epoll_ctl,is_file_epoll@v6.18.46 -/
theorem ctl_channel_epfd_socket_target_is_einval (o : outcome SyscallEffect) :
    epoll_ctl_spec 0 1 6 4096
      (SyscallInput.mkInput 21 [0, 1, 6, 4096] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-! ### The one decline: a target whose `->poll` the model cannot decide

`fd_can_poll` cannot say whether a channel's far end has a `->poll` — a
pipe or a terminal has one, a regular file or /dev/null has none — so the
arm declines there, and it declines /dev/null and /dev/urandom until each
has its own probe. -/

/-- A channel target: declined.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_ctl -- chan -/
theorem ctl_channel_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- …and neither errno is admitted for it: not the -EINVAL a pollable
target would get,
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_ctl -- chan -/
theorem ctl_channel_target_einval_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- …nor the -EPERM an unpollable one would.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_channel_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 2 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- A channel EPFD with a file target is answered, because it is the
TARGET whose `->poll` is read: -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_channel_epfd_file_target_is_eperm (o : outcome SyscallEffect) :
    epoll_ctl_spec 2 1 3 4096 (ep_in ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- /dev/null as a target: declined, though the kernel's answer is -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_devnull_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 9 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- /dev/urandom likewise.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_urandom_target_declines (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 10 4096 (ep_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- The declined /dev/null target admits no -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_devnull_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 9 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- …nor the declined /dev/urandom one.
kernel: fs/eventpoll.c:do_epoll_ctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem ctl_urandom_target_eperm_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_ctl_spec 5 1 10 4096 (ep_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- `EPOLL_CTL_DEL` on a channel target declines at every `event` and
every input: the decline is the target's `->poll`, not the copy.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_channel_target_declines (ev : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 2 2 ev i ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- …while `EPOLL_CTL_ADD` on the same target with a NULL `event` is
ANSWERED: the copy fails before the target is looked at.
kernel: fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem ctl_add_channel_target_null_event_is_efault (o : outcome SyscallEffect) :
    epoll_ctl_spec 5 1 2 0 (ep_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-! ## epoll_pwait (22), in the kernel's order

`SYSCALL_DEFINE6(epoll_pwait, …)` (fs/eventpoll.c:2774-2783, Linux
v6.18.46) evaluates `ep_timeout_to_timespec` (:2118-2137, which cannot
fail and is the only reader of `timeout`), then `do_epoll_pwait`
(:2753-2772) installs the mask, then `do_epoll_wait` (:2715-2738)
resolves the epfd, then `ep_check_params` (:2670-2689) judges the count,
the range and the file. -/

/-! ### 1. The signal mask, before the epfd

`set_user_sigmask`: a NULL `umask` returns 0 (kernel/signal.c:3285-3286,
Linux v6.18.46) BEFORE the size is looked at (:3287-3288), then the copy
(:3289-3290). -/

/-- A NULL mask installs nothing, whatever size sits beside it.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_null_is_none (mp : word → Option byte) (ss : word) :
    epoll_sigmask mp 0 ss = .EpSigNone := rfl

/-- A non-NULL mask with a size other than 8 is -EINVAL before the mask is
read.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_size_7_is_bad_size (mp : word → Option byte) :
    epoll_sigmask mp 4096 7 = .EpSigBadSize := rfl

/-- The size is a `size_t`, compared full width: 2^32 + 8 is the wrong
size.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_size_high_half_is_bad_size (mp : word → Option byte) :
    epoll_sigmask mp 4096 4294967304 = .EpSigBadSize := rfl

/-- The right size and an unreadable mask: -EFAULT.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_unreadable_is_fault :
    epoll_sigmask (fun _ => none) 8 8 = .EpSigFault := rfl

/-- The right size and a readable mask: the mask WOULD BE INSTALLED,
which this model has no signals to represent.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigmask_readable_is_real :
    epoll_sigmask ep_mem_all 4096 8 = .EpSigReal := rfl

/-- Through the syscall: a wrong `sigsetsize` on a CLOSED epfd is -EINVAL,
so the mask is judged before the descriptor.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem pwait_bad_sigsetsize_beats_closed_epfd (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 0 4096 7 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and the -EBADF the epfd would have given is refused.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_sigsetsize_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 0 4096 7 i ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- An unreadable mask of the right size: -EFAULT, again before the epfd.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_is_efault (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 8 8 (pw_in (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and a mapped events buffer does not rescue it: the mask is read and
the events array is not.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_mapped_events_is_efault (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 8 8
        (pw_in (ep_mem_run 4096 16)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and the closed epfd's -EBADF is refused beside it.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_unreadable_sigmask_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 8 8 (pw_in (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- NULL is tested BEFORE the size, so a NULL mask beside a size of 7
installs nothing and the closed epfd decides: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_mask_bad_size_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 0 7 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …so the -EINVAL a size-first reading would give is refused.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_null_mask_bad_size_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 0 7 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- A mask that WOULD BE INSTALLED is declined: this model has no signals.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem pwait_real_mask_declines (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 4096 8 (pw_in ep_mem_all) ep_model o ↔ o = Unmodeled := by
  ep_norm

/-- …and the closed epfd's -EBADF is not admitted behind it.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem pwait_real_mask_ebadf_not_admitted (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 4096 8 (pw_in ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-! ### 2. The epfd, before the count and the range

`CLASS(fd, f)(epfd); if (fd_empty(f)) return -EBADF;` (:2722-2724), which
precedes `ep_check_params` — the reverse of the `epoll_ctl` ordering, and
worth stating because the two files' checks look interchangeable. -/

/-- A closed epfd with a NULL mask: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …and -EINVAL for it is refused.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_pwait:ret=-EINVAL -- pwbadfd -/
theorem pwait_closed_epfd_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- A closed epfd beside a `maxevents` of 0: -EBADF, because the lookup
precedes the count test.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_zero_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 0 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …so the count's -EINVAL is refused there.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_zero_is_not_einval (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 4096 0 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- A closed epfd beside a count above `EP_MAX_EVENTS`: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_above_bound_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 134217728 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- A closed epfd beside a range `access_ok` would refuse: -EBADF, not
-EFAULT.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_bad_range_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 140737488355329 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …and that -EFAULT is refused.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_bad_range_is_not_efault (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 4294967295 140737488355329 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- A closed epfd beside two events ending past `TASK_SIZE`: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_two_events_past_task_size_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 140737488355312 2 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- A closed epfd beside `maxevents` = -1: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_minus_one_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 4294967295 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- A closed epfd beside `maxevents` = `INT_MIN`: -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_int_min_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 2147483648 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- A closed epfd beside a count at the bound and a readable range:
-EBADF still.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_at_bound_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 4294967295 4096 134217727 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-! ### 3. `maxevents`, signed, before the range

`if (maxevents <= 0 || maxevents > EP_MAX_EVENTS) return -EINVAL;`
(fs/eventpoll.c:2674-2675, Linux v6.18.46).  `maxevents` is an `int`, so
a negative value is refused by the first half and never reaches the
product of the range test. -/

/-- `maxevents` = 0 on an OPEN epfd: -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxev -/
theorem pwait_maxevents_zero_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 0 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `maxevents` = -1, read signed: -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxev -/
theorem pwait_maxevents_minus_one_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 4294967295 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `maxevents` = `INT_MIN`: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_int_min_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 2147483648 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The count is judged before the range: a count of 0 beside an events
pointer `access_ok` would refuse is still -EINVAL.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_zero_beats_wild_events (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 0 0 0 i ep_model o   -- 2^63 - 8
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and so is a count of -1 beside it.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_beats_wild_events (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 4294967295 0 0 i ep_model o   -- 2^63 - 8
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The -EFAULT the range would have given is refused at a count of 0.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_zero_wild_events_efault_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 9223372036854775800 0 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- …and at a count of -1, which is what fixes that the signed test comes
first.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_wild_events_efault_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 9223372036854775800 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- A success for a refused count is a lie: `ep_poll` is never reached.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_pwait:ret=0 -- pwmaxev -/
theorem pwait_maxevents_zero_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 0 0 0 i ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- …and -EFAULT for a count of -1 beside a readable range is refused.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_minus_one_efault_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 4294967295 0 0 i ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- One past `EP_MAX_EVENTS`: -EINVAL by the second half of the test.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- pwmaxhi -/
theorem pwait_maxevents_max_plus_one_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 134217728 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A count AT the bound is accepted by the count test and the range is
then judged: `EP_MAX_EVENTS * 16` bytes from 2^47 - 16 run past
`TASK_SIZE`, so -EFAULT.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_at_bound_with_refused_range_is_efault (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 134217727 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …while one past the bound never reaches the range test at all.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_maxevents_past_bound_is_not_range_checked (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 134217728 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-! ### 4. The `events` range, before the epfd's epoll-ness

`if (!access_ok(evs, maxevents * sizeof(struct epoll_event))) return
-EFAULT;` (fs/eventpoll.c:2678-2679, Linux v6.18.46): a pure range check,
with the product in 64-bit unsigned arithmetic and no byte read. -/

/-- One event ending exactly at `TASK_SIZE` passes the range test and
reaches the epoll-ness test: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_ending_at_task_size_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355312 1 0 0 i ep_model o   -- 2^47 - 16
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- One byte further on it does not: -EFAULT.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_past_task_size_is_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 140737488355313 1 0 0 i ep_model o   -- 2^47 - 15
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …and the -EINVAL of the next test is refused there, which is what
makes the range test's position a claim.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_past_task_size_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ epoll_pwait_spec 5 140737488355313 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- An events pointer near the top of the signed range is refused by the
same test.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem pwait_events_near_2_63_is_efault (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 9223372036854775800 1 0 0 i ep_model o   -- 2^63 - 8
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- A NULL events pointer PASSES the range test — `access_ok` is a range
verdict and not a mapping one — so the epoll-ness test answers: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwait_null_events_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 0 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-! ### 5. The epfd's epoll-ness

`if (!is_file_epoll(file)) return -EINVAL;` (fs/eventpoll.c:2685-2686,
Linux v6.18.46), with `is_file_epoll` :478-481.  No descriptor the model
can hold is an epoll instance, so every call that reaches here is
-EINVAL, whatever kind the epfd is. -/

/-- A channel epfd: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_channel_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 2 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A regular-file epfd: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_file_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 3 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A directory epfd: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_dir_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 5 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A socket epfd: -EINVAL, though a socket HAS a `->poll`.  The test is
whether the file is an epoll instance, not whether it is pollable.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_socket_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 6 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A pipe epfd: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_pipe_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 7 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A /dev/null epfd: -EINVAL.  `epoll_pwait` reads no `->poll`, so the
kinds `epoll_ctl` declines are answered here.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_devnull_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 9 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A /dev/urandom epfd: -EINVAL.
kernel: fs/eventpoll.c:ep_check_params,is_file_epoll@v6.18.46 -/
theorem pwait_urandom_epfd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    epoll_pwait_spec 10 4096 1 0 0 i ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- A success for an epfd that is not an epoll instance is a lie.
kernel: fs/eventpoll.c:ep_check_params,do_epoll_wait@v6.18.46 -/
theorem pwait_channel_epfd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 2 4096 1 0 0 i ep_model (Ok (mkEffect 0 [] []) m' evs) := by
  ep_refute

/-- NOTHING IS WRITTEN on any modeled path: `ep_poll` is the only writer
of the events array and the -EINVAL stops short of it, so the right errno
beside a store is refused.
kernel: fs/eventpoll.c:ep_check_params,do_epoll_wait@v6.18.46 -/
theorem pwait_einval_writes_nothing (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ epoll_pwait_spec 5 4096 1 0 0 i ep_model
        (Ok (mkEffect (errno_ret EINVAL) [(4096, List.replicate 16 0)] []) m' evs) := by
  ep_refute

/-! ## Through the table: numbers, argument slots and the `int` casts

`__NR_epoll_create1` 20, `__NR_epoll_ctl` 21, `__NR_epoll_pwait` 22
(include/uapi/asm-generic/unistd.h:77-81, Linux v6.18.46).  The pins
below are on `Specs.syscall_spec`, so they read the register file the way
the dispatcher does and fix which slot each argument comes from and which
cast is applied to it. -/

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_create1@v6.18.46 -/
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

/-- …and from a0 ONLY: the same bit in a1 is not the flag word.
kernel: fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem sysno_20_reads_a0_only (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 20 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- Bit 32 of a0 is narrowed away by the `int` cast, so no -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- trunc -/
theorem sysno_20_bit_32_is_not_einval (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 20 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- …while bit 32 over bit 0 is -EINVAL, because the low half survives.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem sysno_20_bit_32_over_bit_0_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 20 [4294967297, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  ep_norm

/-- The narrowed word is the empty word, which is declined.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_create1 -- trunc -/
theorem sysno_20_bit_32_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 20 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := by
  ep_norm

/-- Syscall 21 is `epoll_ctl`, with epfd in a0, op in a1, fd in a2 and the
event pointer in a3.
kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_ctl; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_is_epoll_ctl (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 5, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- The probe's `fault` case through the table.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem sysno_21_fault_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [Z_to_bv 64 (-1), 1, Z_to_bv 64 (-1), 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- The probe's `delbad` case: `EPOLL_CTL_DEL` skips the copy, so the
closed epfd answers.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- delbad -/
theorem sysno_21_delbad_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [Z_to_bv 64 (-1), 2, Z_to_bv 64 (-1), 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- `op` is an `int`: a high half over `EPOLL_CTL_DEL` is still
`EPOLL_CTL_DEL`, so no copy runs and the closed epfd answers -EBADF.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_op_narrows (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [4294967295, 4294967298, 4294967295, 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- …so the -EFAULT a full-width `op` would have produced is refused.
kernel: include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem sysno_21_op_high_half_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [4294967295, 4294967298, 4294967295, 0, 0, 0]
                      (fun _ => none) (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  ep_refute

/-- Both descriptors are `int`s too: 2^32 + 5 is fd 5 and 2^32 + 3 is fd 3.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem sysno_21_fds_narrow (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [4294967301, 1, 4294967299, 4096, 0, 0] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) ep_model [] := by
  ep_norm

/-- …so the -EBADF a full-width reading would give is refused.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem sysno_21_fds_high_half_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [4294967301, 1, 4294967299, 4096, 0, 0] ep_mem_all ep_mem_all)
        ep_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- The probe's `inval` case through the table.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- inval -/
theorem sysno_21_inval_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 6, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and -EPERM for it is refused.
probe: testing/syscall-check/tests/epoll_spec.c#reject --mutate epoll_ctl:ret=-EPERM -- inval -/
theorem sysno_21_inval_case_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 21 [5, 1, 6, 4096, 0, 0] ep_mem_all ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  ep_refute

/-- The event POINTER is full width — a pointer is no `int` — so
2^32 + 4096 is not 4096 and its struct is unreadable: -EFAULT.
kernel: fs/eventpoll.c:epoll_ctl; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem sysno_21_event_pointer_is_full_width (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 21 [5, 1, 3, 4294971392, 0, 0]
                    (ep_mem_run 4096 16) (ep_mem_run 4096 16)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- Syscall 22 is `epoll_pwait`: epfd a0, events a1, maxevents a2, timeout
a3, sigmask a4, sigsetsize a5.  A directory epfd with one event and a NULL
mask is -EINVAL.
kernel: include/uapi/asm-generic/unistd.h:__NR_epoll_pwait; fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem sysno_22_is_epoll_pwait (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 0, 0]
      (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The probe's `pwbadfd` case: a closed epfd is -EBADF.
kernel: fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem sysno_22_pwbadfd_case_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ep_model [] := by
  ep_norm

/-- The epfd is an `int`: 2^32 + 5 is fd 5, which is open, so the answer
is the epoll-ness test's -EINVAL and not -EBADF.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:do_epoll_wait@v6.18.46 -/
theorem sysno_22_epfd_narrows_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [4294967301, 4096, 1, 0, 0, 0]
      (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- `timeout` is read by nothing the model answers: a huge one changes no
answer.
kernel: fs/eventpoll.c:epoll_pwait,ep_timeout_to_timespec@v6.18.46 -/
theorem sysno_22_timeout_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 123456789, 0, 0]
      (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- …and neither does a negative one, which is the "block forever" value.
kernel: fs/eventpoll.c:epoll_pwait,ep_timeout_to_timespec@v6.18.46 -/
theorem sysno_22_negative_timeout_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, Z_to_bv 64 (-1), 0, 0]
      (fun _ => none) (fun _ => none))
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The probe's `sigsize` case through the table.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem sysno_22_sigsize_case (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 0, 0, 4096, 7] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The probe's `realmask` case: declined.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem sysno_22_realmask_case_declines :
    syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 4096, 8] ep_mem_all ep_mem_all) ep_model
      Unmodeled := by
  ep_norm

/-- …and the -EBADF behind it is not admitted.
probe: testing/syscall-check/tests/epoll_spec.c#fail-closed --expect-unmodeled epoll_pwait -- realmask -/
theorem sysno_22_realmask_case_ebadf_not_admitted (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 22 [Z_to_bv 64 (-1), 4096, 1, 0, 4096, 8] ep_mem_all ep_mem_all) ep_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  ep_refute

/-- `maxevents` is an `int`: 2^32 + 1 is 1, so the count passes and the
refused range answers -EFAULT.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_pwait,ep_check_params@v6.18.46 -/
theorem sysno_22_maxevents_narrows_is_efault (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 140737488355313, 4294967297, 0, 0, 0]
                    (fun _ => none) (fun _ => none)) ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-- …so the -EINVAL a full-register count above the bound would give is
refused.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem sysno_22_maxevents_full_register_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 22 [5, 140737488355313, 4294967297, 0, 0, 0]
                      (fun _ => none) (fun _ => none)) ep_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  ep_refute

/-- `sigsetsize` is a `size_t` and is compared FULL WIDTH: 2^32 + 8 is the
wrong size, so -EINVAL and not the decline a readable mask would give.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_sigsetsize_is_full_width_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 4096, 4294967304] ep_mem_all ep_mem_all)
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ep_model [] := by
  ep_norm

/-- The sigmask POINTER is full width too: 2^32 + 4096 is not 4096, so the
mask is unreadable and the answer is -EFAULT, where a narrowed pointer
would have found the readable mask and declined.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sysno_22_sigmask_pointer_is_full_width_is_efault (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 22 [5, 4096, 1, 0, 4294971392, 8]
      (ep_mem_run 4096 16) (ep_mem_run 4096 16))
        ep_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] := by
  ep_norm

/-! ## A17: FdFileRW and FdFileA -/

/-- A tmpfs file opened O_RDWR has no `->poll`, so `epoll_ctl` refuses it
with -EPERM like any other regular file.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem a17_rdwr_cannot_epoll :
    fd_can_poll (.FdFileRW [102] 0) = some false := by
  rfl

/-- …and so does one opened O_APPEND.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem a17_append_cannot_epoll :
    fd_can_poll (.FdFileA [102] 0) = some false := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
