import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.EventPoll — what the epoll CHECKERS accept and refuse, read off against Linux

Pins over `Checks.Sys.Fs.EventPoll.check_epoll_create1`, `check_epoll_ctl`
and `check_epoll_pwait`, the twins of
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`.  Not part of the
trusted specification: this file is QA on the checkers, written to be
READ, and every claim in it is a claim about what Linux or QEMU does, with
the citation beside it — fs/eventpoll.c at Linux v6.18.46 (commit
1f99e9ab748f) unless another file is named, read in a checkout at that
commit.
QEMU 11.1.1 citations name their file and function, linux-user/syscall.c
`do_syscall1` unless another is named, and carry no line.

WHAT THIS TWINS, AND WHAT IT DOES NOT.  The pins stated through the
checker restate examples from `theories/LinuxProcessSem/Checks/Cases/Fs/EventPoll.v`
in the section "Rocq checker examples" below.
Their docstrings give the mapping as `#1925 counterpart: <name> (Checks/Cases/Fs/EventPoll.v)`.
That mapping is prose that no guard reads.
It stops being complete when a moved pin loses its mapping or a new Rocq restatement omits one.
This file mirrors no Rocq file, so it carries no coverage register.
`tools/check_lean_cases_parity.py` refuses a register at such a path.
The spec pins stay in `Checks/Cases/Fs/EventPoll.lean`.
The KERNEL argument for each answer is beside the spec-level
pin of the same claim in that file; each docstring here keeps only the
reading its own verdict rests on.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file tie
each checker to its spec in both directions, and a checker that declined
every input would still meet all five of them against a spec changed to
decline everywhere; a checker that accepted every return-only effect
would meet them against a spec changed to match.  What the lemmas cannot
see is a lie told from OUTSIDE: an errno the kernel would not return, a
success where the kernel refuses, a ledger beside a return the kernel
gives with none, a decline where the kernel answers.  Each pin below
names one such concrete answer and the verdict on it, so a checker that
accepted everything, rejected everything or declined everything fails
here by name.

HOW THESE ARE STATED. The row pins apply the checker the way the dispatcher
does: `check_epoll_create1_row`,
`check_epoll_ctl_row` and `check_epoll_pwait_row` below are the argument
narrowing of Rocq's `arm_epoll_create1`, `arm_epoll_ctl` and
`arm_epoll_pwait` (`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and
of the rows for 20, 21 and 22 in `Sys/SyscallTable.lean`, spelled once —
and proved to be that narrowing, not merely described as it: the last
section closes each row's `CheckOk` against `dispatch spec_table` through
the registered arm, which unifies only if the row narrows every register
as `Sys/Registry/Fs/EventPoll.lean` does. The later table pins also exercise
`check_syscall` through the registered arms.
The model is `Checks/Cases/Fs/EventPoll.lean`'s `ep_model`, imported
rather than copied, so a pin on fd 3 is a pin on a regular file and a pin
on fd 6 a pin on a socket in both files at once; the memories are that
file's `ep_mem_all` and `ep_mem_run`.  The inputs carry the register file
a tracer would record, because the rows read the registers; the spec
pins' `ep_in` and `pw_in` carry none, because a spec called directly
reads the memory and, for QEMU's raw `op`, only `in_arg`'s default on
the empty list.  The equalities are closed by `rfl` or, for an
`epoll_pwait` answer set, by `decide +kernel` on `pwait_row_answerb` or
`pwait_row_rejectb`: `Model` has no `DecidableEq`, so `decide` does not
compare verdicts, and the checker on a closed input reduces to a
constructor by evaluation alone.  A refusal to
decline is stated as the exact verdict and the disequality derived from
it by `rw`, so the stronger fact is what a reader sees; the three
`_answers_whatever_it_is_shown` pins quantify over the effect instead,
and are proved by handing the hypothesis straight to the prelude's
`check_ret_only_no_unmodeled` or to `check_ep_answer_no_unmodeled`: on a
closed input the row is definitionally
that call, so the type checker evaluates the outcome function itself.  (A
separate `have … := rfl` on the pwait outcome hit the elaborator's
recursion limit; the defeq route does not.)

WHAT THE ARGUMENT-POSITION PINS ARE FOR.  A row that read the registers
in the wrong order would still satisfy every lemma of the checker file,
because those are stated over the checker's own arguments.  So several
pins below choose inputs on which a swap changes the answer: a socket
epfd beside a file target (-EPERM) against a file epfd beside a socket
target (-EINVAL) separates the two fd registers of `epoll_ctl`; a DEL on
a file with an unreadable event pointer (-EPERM, no copy) against an ADD
there (-EFAULT) separates `op` from `fd`. Lean declines the mask/size and
closed-epfd timeout shapes that the base answered differently, so those
pins now assert whole-shape declines, including the base answers; they
no longer distinguish those register swaps by an accepted errno.
Which fd register is narrowed to `int` is pinned
the same way, by values whose high half decides the answer; where the
spec itself reads only the low half — `epoll_create1_outcome`'s 32-bit
mask, `sint32` on the count — the row's cast is unobservable and the pin
says so rather than claim it.

WHICH PINS CARRY A `probe:` LINE.  Some `= CheckOk` pins cite the
`conform` case of `testing/syscall-check/tests/epoll_spec.c` whose
recorded run (`testing/syscall-check/traces/epoll_spec/`) issued the pin's
syscall with the pin's shape and got the pin's errno: for those,
`tools/check_lean_pin_evidence.py`'s PROBE-RET holds the errno to a return
a real kernel gave, which no kernel reading can.  The kernel reading each
of them rests on stays in its docstring, with the file and line.  The
kernel-cited pins lack a probe line for two reasons.  A
`= CheckReject` or `= CheckUnmodeled` verdict is read as POSITIVE by that
tool's polarity rule — `\bUnmodeled\b` does not match inside
`CheckUnmodeled` — so the `reject --mutate` or `fail-closed` case that
matches such a pin would be refused as the wrong polarity; and a pin
fixing two errnos, or one whose input no recorded case ran, has no run to
cite.  The `≠ CheckUnmodeled` pins read negative and could cite a
`fail-closed` case for polarity, but a decline the model made elsewhere is
no evidence that it does not decline here, so none does.
The flag-translation, high-DEL, mask-count and events-lock probes remain
deferred until the Lean twin ports #1925's joined answers. Their shapes are pinned here against the cited implementation
source, including the base answer on each Lean decline.

ONE PIN STATES A KNOWN OMISSION rather than a kernel fact, and says so
where it stands: `epoll_ctl_a_recorded_copy_in_is_rejected`.  The spec
records no copy-in for the event struct it reads
(`bugs/epoll-ctl-copyin-not-recorded.md`), so the checker refuses an
effect that records one; the pin exists so that the day the spec records
it, this file stops compiling at the line that has to move.

NOTHING HERE EXECUTES THE ROCQ CHECKER. These pins state the Lean verdicts
against the cited implementation behavior. On the Lean disagreement
shapes they explicitly offer the base answer and require a decline. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventPoll

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
-- Selective: only the fixtures, so that no spec-level pin name is brought
-- into a namespace that states the checker's verdict under a like name.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll
  (ep_model ep_mem_all ep_mem_run ep_in pw_in
   epoll_row_model epoll_lock_mem epoll_lock_model
   epoll_ctl_raw_in epoll_mask_count_in epoll_lock_in
   epoll_row_pwait_in epoll_load_model epoll_read_only_closed_in
   epoll_wrap_in epoll_stack_model epoll_stack_mem
   epoll_stack_in epoll_stack_ctl_model epoll_stack_ctl_in)

/-! ## The dispatcher's application of each checker -/

/-- `check_epoll_create1` as the dispatcher applies it: `flags` narrowed to
`int` by `flag32` — Rocq's `arm_epoll_create1` and the row for 20 in
`Sys/SyscallTable.lean`.  When the checked-arm table gains the arm, its
`ca_check_arm_epoll_create1` unfolds to this application. -/
def check_epoll_create1_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_create1 (flag32 (in_arg i 0)) eff m

/-- `check_epoll_ctl` as the dispatcher applies it: `epfd` and `fd`
narrowed by `fd32`, `op` by `int32`, the `event` pointer as it arrives —
Rocq's `arm_epoll_ctl` and the row for 21. -/
def check_epoll_ctl_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m

/-- `check_epoll_pwait` as the dispatcher applies it: `epfd` by `fd32`,
`maxevents` by `int32`, the `events` pointer, `sigmask` and `sigsetsize`
as they arrive, and the fourth register — `timeout` — not read at all:
Rocq's `arm_epoll_pwait` and the row for 22. -/
def check_epoll_pwait_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4)
    (in_arg i 5) eff m

private def pwait_row_answerb (i : SyscallInput) (m : Model) (rv : word) : Bool :=
  match epoll_pwait_outcome i m (fd32 (in_arg i 0)) (in_arg i 1)
      (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) with
  | none => false
  | some o => ep_answerb o rv

private def pwait_row_rejectb (i : SyscallInput) (m : Model) (rv : word) : Bool :=
  match epoll_pwait_outcome i m (fd32 (in_arg i 0)) (in_arg i 1)
      (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) with
  | none => false
  | some o => !ep_answerb o rv

/-- The row checker admits `rv` when the outcome tree admits it.
model: a proof step from the outcome tree to the row checker's verdict -/
private theorem pwait_row_ok (i : SyscallInput) (m : Model) (rv : word)
    (h : pwait_row_answerb i m rv = true) :
    check_epoll_pwait_row i (mkEffect rv [] []) m = CheckOk m [] := by
  unfold pwait_row_answerb at h
  unfold check_epoll_pwait_row check_epoll_pwait
  split at h <;> simp_all only [check_ep_answer, Bool.false_eq_true, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The row checker refuses `rv` when the outcome tree refuses it.
model: a proof step from the outcome tree to the row checker's verdict -/
private theorem pwait_row_reject (i : SyscallInput) (m : Model) (rv : word)
    (h : pwait_row_rejectb i m rv = true) :
    check_epoll_pwait_row i (mkEffect rv [] []) m = CheckReject := by
  unfold pwait_row_rejectb at h
  unfold check_epoll_pwait_row check_epoll_pwait
  split at h <;> simp_all only [check_ep_answer, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte]

/-! ## The register files

What a tracer records at the `ecall`: the number in a7 and the six
argument registers, with the pre-syscall memory for the arms that read
one.  `create1_call` hands its row a memory with no byte mapped, which is
the statement that the row reads none; the other two take the memory a pin
chooses, because both arms read through it. -/

/-- `epoll_create1(flags)`: syscall 20. -/
def create1_call (flags : word) : SyscallInput :=
  SyscallInput.mkInput 20 [flags, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `epoll_ctl(epfd, op, fd, event)`: syscall 21, over the memory `mem`. -/
def ctl_call (epfd op tfd ev : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 21 [epfd, op, tfd, ev, 0, 0] mem mem

/-- `epoll_pwait(epfd, events, maxevents, timeout, sigmask, sigsetsize)`:
syscall 22, over the memory `mem`. -/
def pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 22 [epfd, events, maxevents, timeout, sigmask, sigsetsize] mem mem

/-! ## The checker's own shape: the outcome first, then the effect's ledgers -/

/-- A return-only arm rejects an effect that carries a write beside the
kernel's own errno: `epoll_ctl` stores nothing on a path that ends in
-EPERM (`do_epoll_ctl` returns at :2530-2531 before any store), so each
empty ledger `check_ep_answer` demands is load-bearing.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_an_effect_with_a_write_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EPERM) [(4096, [0])] [] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and the same odd-shaped effect against a declined call — a channel
target, whose `->poll` the model cannot see — is `CheckUnmodeled`, not
`CheckReject`: the outcome is computed before the effect is looked at.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_declined_call_is_declined_whatever_the_effect_shape :
    check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EPERM) [(4096, [0])] [] [] [] []) ep_model
      = CheckUnmodeled := by
  rfl

/-- The known omission, stated where it stands (file header): the spec
records no copy-in for the sixteen bytes `epoll_ctl` reads at :2663-2665,
so an effect that records the read is refused although the return is the
kernel's.  This pin moves the day `bugs/epoll-ctl-copyin-not-recorded.md`
closes.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_recorded_copy_in_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
      (with_copyins [(4096, 16)] (mkEffect (errno_ret EPERM) [] [])) ep_model
      = CheckReject := by
  rfl

/-- The three ledgers the two pins above leave untested — a zero-fill, an
unmap and a copy — are each rejected beside the same -EPERM, one at a
time, so that no single empty-ledger test of `check_ret_only` can be
dropped without a pin here going red.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [(4096, 16)] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- `epoll_pwait` writes nothing on any modeled path — `ep_poll`
(fs/eventpoll.c:2199, Linux v6.18.46), the only route from this syscall to
a store into the array (through `ep_send_events`, fs/eventpoll.c:2072),
sits behind the -EINVAL of `ep_check_params` (:2685-2686) — so a zero-fill
of the events array beside that errno is rejected.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_an_effect_with_a_zero_fill_is_rejected :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and so are the other four ledgers beside it: a write into the array,
an unmap, a copy, and a recorded copy-in of a mask that was NULL and so
never read (kernel/signal.c:3285-3286), one at a time.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [(4096, [0])] [] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (with_copyins [(8192, 8)] (mkEffect (errno_ret EINVAL) [] [])) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and against a mask that would be installed the same shape is
declined, not rejected.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_declined_call_is_declined_whatever_the_effect_shape :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
      = CheckUnmodeled := by
  rfl

/-! ## epoll_create1 (20): one `if`, then a decline

`do_epoll_create` (fs/eventpoll.c:2430-2471, Linux v6.18.46) tests
`flags & ~EPOLL_CLOEXEC` (:2439-2440) before `ep_alloc`
(fs/eventpoll.c:1341-1363, Linux v6.18.46) and before any descriptor is
reserved (:2451); a flag word that passes goes on to mint an
epoll instance, which the model has no descriptor kind for, so the checker
declines there whatever the kernel showed. -/

/-- A well-formed create — no flags, or `EPOLL_CLOEXEC` alone — is
declined whatever descriptor the kernel handed back: the success arm is
the spec's one decline for this number, and the checker's verdict does not
depend on the effect.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_well_formed_create_is_declined :
    check_epoll_create1_row (create1_call 0) (mkEffect 3 [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 524288) (mkEffect 3 [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 0) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- A stray bit — bit 0 here — is -EINVAL at `do_epoll_create`'s
:2439-2440 (fs/eventpoll.c:2430-2471, Linux v6.18.46), and the checker
accepts that errno with the model untouched.  The cited run issued this
call with this flag word and recorded that return.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- badflags -/
theorem epoll_create1_a_stray_flag_is_einval :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- A descriptor for a stray flag is the lie `do_epoll_create` never tells:
the test at :2439-2440 returns before `get_unused_fd_flags`
(fs/file.c:620-623, Linux v6.18.46; called at :2451) runs, so no fd number
is ever consumed on this path, and 3 — the lowest free
number — is rejected, as is 0.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_descriptor_for_a_stray_flag_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect 3 [] []) ep_model = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect 0 [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Another errno for the same stray bit is rejected too: -EBADF, -EPERM
and -EFAULT are answers other arms of this file give and this one never
does — the pin that separates the create arm's errno from its neighbours'.
`do_epoll_ctl` and `epoll_ctl` are cited for where those three errnos ARE
spelled; the decision that none of them is this arm's is
`do_epoll_create`'s, which spells only -EINVAL.
kernel: fs/eventpoll.c:do_epoll_create; fs/eventpoll.c:do_epoll_ctl; fs/eventpoll.c:epoll_ctl@v6.18.46 -/
theorem epoll_create1_a_foreign_errno_for_a_stray_flag_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- -ENOMEM and -EMFILE are the two errnos `do_epoll_create` CAN return,
and both are rejected for a stray bit: `ep_alloc` (fs/eventpoll.c:1341-1363,
Linux v6.18.46; -ENOMEM at :1347, called at :2444) and `get_unused_fd_flags`
(fs/file.c:620-623, Linux v6.18.46; reaching `alloc_fd`'s -EMFILE at
fs/file.c:591, called at :2451) both sit below the gate at :2439-2440, so
neither a failed allocation nor a full descriptor table is an answer for a
word the gate refused.  The spec-level twins are
`create_bit_0_enomem_rejected` and `create_bit_0_emfile_rejected` in
`Checks/Cases/Fs/EventPoll.lean`.
kernel: fs/eventpoll.c:do_epoll_create,ep_alloc; fs/file.c:get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem epoll_create1_enomem_and_emfile_for_a_stray_flag_are_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret ENOMEM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EMFILE) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The checker's own shape on the create arm: the right errno beside a
write is rejected, since `do_epoll_create` returns at :2439-2440 without
touching user memory.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_an_effect_with_a_write_is_rejected :
    check_epoll_create1_row (create1_call 1)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [(4096, [0])] [] [] [] []) ep_model
      = CheckReject := by
  rfl

/-- …and so is each of the other four ledgers beside it — a zero-fill, an
unmap, a copy, a recorded copy-in — one at a time: `do_epoll_create` takes
an `int` and reads no user memory at all.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_every_other_ledger_beside_the_errno_is_rejected :
    check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        ep_model
        = CheckReject
    ∧ check_epoll_create1_row (create1_call 1)
        (with_copyins [(4096, 16)] (mkEffect (errno_ret EINVAL) [] [])) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The return is compared at full width: the kernel returns a `long`, so
-EINVAL arrives as the 64-bit word 2^64 - 22, and a return holding only
its low 32 bits (4294967274) is rejected.
kernel: fs/eventpoll.c:do_epoll_create,epoll_create1@v6.18.46 -/
theorem epoll_create1_a_truncated_return_is_rejected :
    check_epoll_create1_row (create1_call 1) (mkEffect 4294967274 [] []) ep_model = CheckReject := by
  rfl

/-- `flags` is an `int` (:2473): riscv64's `__SYSCALL_DEFINEx` narrows the
register through `__SC_CAST` before `do_epoll_create` sees it.  A register
holding 2^32 is `flags = 0`, a well-formed create the checker declines —
not a stray bit answered -EINVAL — while 2^32 + 1 keeps its low stray bit
and is -EINVAL.  The row applies `flag32` for this reason, but the pin
cannot see the cast: `epoll_create1_outcome` masks with a 32-bit word, so
bit 32 is dropped by the spec with or without it.  What is pinned is the
kernel fact alone.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_create1,do_epoll_create@v6.18.46 -/
theorem epoll_create1_bit_32_of_flags_is_dropped :
    check_epoll_create1_row (create1_call 4294967296) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 4294967297) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- Every bit of the `int` but bit 19 — `EPOLL_CLOEXEC` is `O_CLOEXEC`,
02000000 — is a stray bit at :2439-2440: bit 31 (2147483648, the `int`'s
sign bit), the CLOEXEC bit beside bit 0 (524289, a word the badflags case
of `epoll_spec.c` also ran), an all-ones `int` (4294967295) and an all-ones
register (18446744073709551615, the same `int` once narrowed) are all
-EINVAL.
QEMU 11.1.1 linux-user/syscall.c [do_syscall1] drops bit 31 during flag
translation, so the model declines that word.
kernel: fs/eventpoll.c:do_epoll_create,epoll_create1@v6.18.46 -/
theorem epoll_create1_every_other_bit_is_a_stray_bit :
    check_epoll_create1_row (create1_call 2147483648) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_create1_row (create1_call 524289) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_create1_row (create1_call 4294967295) (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_create1_row (create1_call 18446744073709551615)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## epoll_ctl (21): the copy, the two lookups, the target's `->poll`, -EINVAL

`epoll_ctl` (fs/eventpoll.c:2658-2668, Linux v6.18.46) copies the event
struct at :2663-2665 whenever `ep_op_has_event(op)` — every op but
`EPOLL_CTL_DEL` — and only then calls `do_epoll_ctl`
(fs/eventpoll.c:2511-2651, Linux v6.18.46): -EBADF for the epfd
(:2520-2522), -EBADF for the target (:2525-2527), -EPERM for a target with
no `->poll` (:2530-2531), and -EINVAL (:2542-2544) for every descriptor
this model can hold as `epfd` but a channel, since none of the others is
an epoll instance.  A channel epfd declines there.

Every pin below that names the top of the address space reads it as
`State.TASK_SIZE`, the Sv48 top: `TASK_SIZE_MAX` is `TASK_SIZE`
(include/asm-generic/access_ok.h, Linux v6.18.46), which is 2^47 under
Sv48 and another power under Sv39 or Sv57 (arch/riscv/include/asm/pgtable.h,
Linux v6.18.46).  A run declaring another size is refused rather than
graded (`bugs/va-size-declines-every-non-sv48-run.md`), so the pins hold
under the one size the spec compares against.  They also read the address
as the register holds it: riscv's `access_ok`
(arch/riscv/include/asm/uaccess.h, Linux v6.18.46) judges
`untagged_addr(addr)`, the identity while no `prctl` has enabled pointer
masking, which no modeled program can request. -/

/-- -EFAULT on the event struct BEATS -EBADF on a closed epfd: the copy is
in the syscall entry, `epoll_ctl` (fs/eventpoll.c:2658-2668, Linux
v6.18.46, at :2663-2665), the lookup in the callee, `do_epoll_ctl`
(fs/eventpoll.c:2511-2651, Linux v6.18.46, at :2520-2522).  Both fds here
are what an `int` -1 arrives as after `fd32`, and the pointer is NULL over
an unmapped memory.  The cited run issued exactly this register file and
recorded -EFAULT.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- fault -/
theorem epoll_ctl_efault_beats_ebadf_on_epfd :
    check_epoll_ctl_row (ctl_call 4294967295 1 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- -EBADF ahead of the copy is the other order, and the checker rejects
it: `do_epoll_ctl` is not entered once the copy has faulted.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_ebadf_ahead_of_the_copy_is_rejected :
    check_epoll_ctl_row (ctl_call 4294967295 1 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  rfl

/-- `EPOLL_CTL_DEL` never reads the event struct — `ep_op_has_event`
(include/linux/eventpoll.h, Linux v6.18.46) is `op != EPOLL_CTL_DEL`, and
the copy at `epoll_ctl`'s :2663-2665 (fs/eventpoll.c:2658-2668, Linux
v6.18.46) is behind it — so with both fds closed the answer is the -EBADF
of `do_epoll_ctl`'s :2520-2522 (fs/eventpoll.c:2511-2651, Linux v6.18.46)
whatever the pointer holds: NULL, or a wild 2^64 - 8 over a memory with no
byte mapped.  The cited run issued the NULL shape and recorded -EBADF.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- delbad -/
theorem epoll_ctl_del_never_reads_the_event :
    check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 18446744073709551608 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- -EFAULT under `EPOLL_CTL_DEL` is rejected: no copy happens, so the
pointer's readability is never judged.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_efault_under_del_is_rejected :
    check_epoll_ctl_row (ctl_call 4294967295 2 4294967295 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckReject := by
  rfl

/-- `op` is an `int` (:2658), narrowed by `__SC_CAST` before
`ep_op_has_event` compares it: a register whose low half is 2 and whose
high half is set is `EPOLL_CTL_DEL` to the kernel, and the row applies
`int32` so that it is here too — -EBADF for the closed fds, not the
-EFAULT an un-narrowed 2^32 + 2 would copy its way to, which is rejected.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_the_row_narrows_op_to_int :
    check_epoll_ctl_row (ctl_call 4294967295 4294967298 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967295 4294967298 4294967295 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- An `op` the kernel does not know — 7 — still copies: `ep_op_has_event`
asks only whether `op` is `EPOLL_CTL_DEL`, so with an unreadable pointer
the answer is -EFAULT before the switch that would have refused the op —
the -EINVAL `do_epoll_ctl` sets at :2611 and keeps for an op no case
matches is rejected here.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_an_unknown_op_still_copies :
    check_epoll_ctl_row (ctl_call 5 7 3 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 7 3 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Twelve mapped bytes of the sixteen-byte struct are a fault: the copy
at :2663-2665 is `sizeof(struct epoll_event)`, which is 16 on riscv64
(`EPOLL_PACKED` is empty off x86-64), so the four padding bytes are read
too and the thirteenth is unmapped here.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_twelve_mapped_bytes_are_a_fault :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 12))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- The -EPERM a twelve-byte reading would reach — an x86-64 reader's
struct size — is rejected: the copy faults first.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_over_a_short_struct_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 12))
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckReject := by
  rfl

/-- Sixteen mapped bytes reach the target: fd 3 is a regular file of the
image's filesystem, whose `file_operations` carry no `->poll`, so
`file_can_poll` (include/linux/poll.h, Linux v6.18.46) is false and the
answer is `do_epoll_ctl`'s -EPERM (fs/eventpoll.c:2511-2651, Linux
v6.18.46, at :2530-2531).  The claim is the fixture's, not every regular
file's: a procfs regular file polls through `proc_reg_poll`
(fs/proc/inode.c, Linux v6.18.46), and which kinds the spec reads as
never pollable is argued on `Sys/Fs/EventPoll.lean`.  The cited run added
a regular file over a fully mapped struct and recorded -EPERM.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- perm -/
theorem epoll_ctl_sixteen_mapped_bytes_reach_the_target :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 (ep_mem_run 4096 16))
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- The copy's range is judged before a byte is read, by `__access_ok`'s
`addr <= limit - size` with `TASK_SIZE_MAX` as the limit: a struct at
2^47 - 15 ends one byte past the top of the user address space and is
-EFAULT although every byte is mapped, while one at 2^47 - 16 ends exactly
at it and reaches the target (-EPERM).
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_the_struct_is_judged_against_the_address_space_top :
    check_epoll_ctl_row (ctl_call 5 1 3 140737488355313 ep_mem_all)
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 140737488355312 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_past_the_address_space_top_declines :
    check_epoll_ctl_row (ctl_call 5 1 3 140737488355313 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- A struct at 2^64 - 8 wraps the address space, and `__access_ok` refuses
it outright — -EFAULT, not the wrapped read of eight bytes from the top and
eight from address 0 that a word-arithmetic walk would report; the -EPERM
that walk would then reach on the file target is rejected.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_wrapping_struct_is_efault :
    check_epoll_ctl_row (ctl_call 5 1 3 18446744073709551608 ep_mem_all)
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 18446744073709551608 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A closed epfd is -EBADF (:2520-2522) once the struct has been read,
and the -EPERM a kernel that looked the target up first would give is
rejected: fd 99 is closed in the fixture.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_closed_epfd_is_ebadf_after_the_copy :
    check_epoll_ctl_row (ctl_call 99 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 99 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- A closed target is -EBADF (:2525-2527), before its `->poll` could be
asked for, and -EINVAL there is rejected.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_closed_target_is_ebadf :
    check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Nor is the -EPERM of a file target the answer for a CLOSED one: the
target's `fdget` fails at :2525-2527 before `file_can_poll` is asked at
:2530-2531, so -EPERM beside fd 99 is rejected.
kernel: fs/eventpoll.c:do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_eperm_for_a_closed_target_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 99 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckReject := by
  rfl

/-- A regular-file target is -EPERM (:2530-2531) BEFORE the epfd is tested
for being an epoll fd (:2542-2544), so two ordinary descriptors answer
-EPERM and never -EINVAL: the -EINVAL is rejected, and so is 0.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_file_target_is_eperm_not_einval :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- A file opened for writing and a directory answer the same -EPERM: the
access mode does not change `f_op`, and the fixture's directory is read
through operations with no `.poll` — `simple_dir_operations`
(fs/libfs.c:230-237, Linux v6.18.46) is the shape, and the kinds the spec
reads as never pollable are argued on `Sys/Fs/EventPoll.lean`, beside
`Select.bits_all_pollable`.  The epfd here is the read-only file, which
`do_epoll_ctl` never asks about before the target.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_write_file_and_a_directory_target_are_eperm :
    check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …and for those two targets the -EINVAL of the epfd test and the 0 of
a completed ADD are rejected, as they are for the read-only file:
:2530-2531 returns before :2542-2544 whatever the target's access mode, and
a directory reaches no further either.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_einval_and_success_for_a_write_file_or_a_directory_target_are_rejected :
    check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 4 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 3 1 5 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A socket target HAS a `->poll` (`sock_poll`, installed on every
family), so it passes :2530-2531 and reaches :2542-2544, where the epfd —
a directory here, not an epoll instance — is -EINVAL.  -EPERM there is
rejected, and so is the 0 an epoll fd would have earned.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll; net/socket.c:sock_alloc_file,sock_poll@v6.18.46 -/
theorem epoll_ctl_a_socket_target_is_einval :
    check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 6 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Both ends of a pipe answer as the socket does: `pipeanon_fops`
(fs/pipe.c:1257-1266, Linux v6.18.46) carries `pipe_poll`, so the target
passes and the epfd fails :2542-2544.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem epoll_ctl_both_pipe_ends_are_einval :
    check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- …and for both ends the -EPERM of a target without `->poll` and the 0
an epoll epfd would have earned are rejected: `pipe_poll` is there, so
:2530-2531 passes, and the directory epfd fails :2542-2544.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll; fs/pipe.c:create_pipe_files,pipe_poll@v6.18.46 -/
theorem epoll_ctl_eperm_and_success_for_a_pipe_target_are_rejected :
    check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 7 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 1 8 4096 ep_mem_all) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two fd registers are not interchangeable, and the row reads them
in the kernel's order: a socket epfd beside a file target is -EPERM (the
target has no `->poll`), a file epfd beside a socket target is -EINVAL
(the target polls, the epfd is no epoll fd).
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_the_target_not_the_epfd_is_asked_for_poll :
    check_epoll_ctl_row (ctl_call 6 1 3 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 3 1 6 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- `EPOLL_CTL_DEL` on a file target is still -EPERM: skipping the copy
does not skip :2530-2531.  Beside it, an ADD with the same unreadable
pointer is -EFAULT — the pair that separates the `op` register from the
`fd` register, since exchanging the two changes the answer.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_del_on_a_file_target_is_still_eperm :
    check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none))
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 5 1 3 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl⟩

/-- The two answers `EPOLL_CTL_DEL` has once it reaches the switch — 0 for
a descriptor the interest set holds (:2627) and -ENOENT for one it does not
(:2629) — are both rejected on a file target: :2530-2531 has returned
-EPERM before the switch at :2612 is entered.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_del_on_a_file_target_never_reaches_the_switch :
    check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none))
        (mkEffect (errno_ret ENOENT) [] []) ep_model
        = CheckReject
    ∧ check_epoll_ctl_row (ctl_call 5 2 3 0 (fun _ => none)) (mkEffect 0 [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- `epfd` and `fd` are `int`s (:2658), narrowed by `__SC_CAST`; the row
applies `fd32` to both, so 2^32 + 5 is the directory and 2^32 + 3 the
file, and the answer is the -EPERM of fds 5 and 3 rather than the -EBADF
of two numbers no table holds.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_the_row_narrows_both_fds_to_int :
    check_epoll_ctl_row (ctl_call 4294967301 1 4294967299 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_ctl_row (ctl_call 4294967301 1 4294967299 4096 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The return is compared at full width: -EPERM is the 64-bit word
2^64 - 1, and its low 32 bits alone (4294967295) are rejected.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_ctl_a_truncated_return_is_rejected :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) (mkEffect 4294967295 [] []) ep_model
      = CheckReject := by
  rfl

/-- A channel target is declined whatever the kernel answered: the model
does not know whether fd 0's far end has a `->poll`, so neither the -EPERM
of a file-backed channel nor the -EINVAL of a pipe-backed one is an answer
it gives.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_channel_target_is_declined :
    check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_ctl_row (ctl_call 5 1 0 4096 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- /dev/null and /dev/urandom targets are declined although the answer is
exact — neither `null_fops` (drivers/char/mem.c:644-652, Linux v6.18.46)
nor `urandom_fops` (drivers/char/random.c:1572-1581, Linux v6.18.46; unlike
`random_fops` at :1560-1571, which has `.poll = random_poll`) has a
`.poll`, and `memory_open` installs them, so both are -EPERM — because the
spec declines them until each is written with its own probe; a decline is
a gap, never a wrong answer.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem epoll_ctl_devnull_and_urandom_targets_are_declined :
    check_epoll_ctl_row (ctl_call 5 1 9 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_ctl_row (ctl_call 5 1 10 4096 ep_mem_all)
        (mkEffect (errno_ret EPERM) [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- A channel EPFD is not a channel target: the epfd is only looked up
(:2520-2522), never asked for its `->poll`, so fd 0 as epfd beside a file
target is the ordinary -EPERM.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_channel_epfd_is_judged :
    check_epoll_ctl_row (ctl_call 0 1 3 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-! ## epoll_pwait (22): the mask, the epfd, the count, the range, -EINVAL

`epoll_pwait` (fs/eventpoll.c:2774-2783, Linux v6.18.46) hands the mask to
`set_user_sigmask` (kernel/signal.c:3281-3297, Linux v6.18.46) inside
`do_epoll_pwait` (fs/eventpoll.c:2753-2772, Linux v6.18.46, at
:2763-2765) before `do_epoll_wait` (fs/eventpoll.c:2715-2738, Linux
v6.18.46) looks the epfd up (:2722-2724) and `ep_check_params`
(fs/eventpoll.c:2670-2689, Linux v6.18.46) judges the count (:2674-2675),
the range (:2678-2679) and the file (:2685-2686).  The address-space top
the range and mask pins name is the Sv48 `State.TASK_SIZE`, under the
premise the `epoll_ctl` section states: a run declaring another size is
refused, and no modeled program has enabled pointer masking. -/

/-- A `sigsetsize` other than eight beside a non-NULL mask is -EINVAL at
`set_user_sigmask`'s :3287-3288 (kernel/signal.c:3281-3297, Linux
v6.18.46), and that BEATS the -EBADF of a closed epfd: `do_epoll_pwait`
(fs/eventpoll.c:2753-2772, Linux v6.18.46) installs the mask before
`do_epoll_wait` is entered.  The cited run issued a closed epfd beside a
seven-byte size and recorded -EINVAL.
probe: testing/syscall-check/tests/epoll_spec.c#conform -- sigsize -/
theorem epoll_pwait_a_bad_sigsetsize_beats_a_closed_epfd :
    check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 4096 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- -EBADF ahead of the mask is the other order, and the checker rejects
it: `set_user_sigmask` has returned -EINVAL before the epfd is resolved.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_ebadf_ahead_of_the_sigmask_is_rejected :
    check_epoll_pwait_row (pwait_call 4294967295 4096 0 0 4096 7 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  rfl

/-- A mask of the kernel's size that cannot be read is -EFAULT at
`set_user_sigmask`'s :3289-3290 (kernel/signal.c:3281-3297, Linux
v6.18.46), again before `do_epoll_pwait` (fs/eventpoll.c:2753-2772, Linux
v6.18.46) reaches the epfd. Here the events buffer is unwritable too,
so QEMU agrees by failing its events lock. The writable-buffer probe is
pinned separately below.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, checks the events lock first.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_an_unreadable_mask_is_efault :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model
      = CheckOk ep_model [] := by
  rfl

/-- Recording the probe's writable events buffer must decline its EFAULT,
since QEMU can fail allocation after locking events.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, allocates before reading the mask.
kernel: kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_unreadable_mask_writable_events_declines :
    check_epoll_pwait_row
        (pwait_call 4294967295 4096 1 0 8 8 (ep_mem_run 4096 16))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled := by
  rfl

/-- …and -EBADF for the closed epfd beside that unreadable mask is the
other order, rejected: the copy at kernel/signal.c:3289-3290 has failed
before `do_epoll_wait` looks the epfd up.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_ebadf_ahead_of_an_unreadable_mask_is_rejected :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model
      = CheckReject := by
  repeat' apply And.intro
  all_goals first | (apply pwait_row_ok; decide +kernel) | (apply pwait_row_reject; decide +kernel) | rfl

/-- Seven mapped bytes of the mask are a fault: the copy at
kernel/signal.c:3289-3290 is `sizeof(sigset_t)`, eight on riscv64, and the
eighth byte is unmapped here — -EFAULT before the epfd, so the closed
epfd's -EBADF is rejected.  With the eighth byte mapped the mask would be
installed, and the call is declined whatever the epfd.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_seven_mapped_bytes_of_the_mask_are_a_fault :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 7))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 7))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4096 8 (ep_mem_run 4096 8))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled := by
  repeat' apply And.intro
  all_goals first | (apply pwait_row_ok; decide +kernel) | (apply pwait_row_reject; decide +kernel) | rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_a_null_mask_ignores_the_size_declines :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 7 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 7 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_null_mask_of_the_kernels_size_installs_nothing_declines :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 8 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 0 8 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_a_zero_size_beside_a_mask_declines :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8192 0 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 8192 0 ep_mem_all)
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait@v6.18.46 -/
theorem epoll_pwait_the_null_test_on_the_mask_is_full_width_declines :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4294967296 7 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 4294967296 7 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- A readable mask of the kernel's size WOULD BE INSTALLED
(kernel/signal.c:3292-3294) for the call's duration, which the model does
not represent, so the call is declined whatever the kernel answered —
the -EINVAL every other arm of this fixture ends in included.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_a_readable_mask_is_declined :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 8 ep_mem_all)
        (mkEffect 0 [] []) ep_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:epoll_pwait,do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem epoll_pwait_the_mask_registers_are_read_in_order_and_the_size_full_width_declines :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 8 8192 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 8192 4294967304 ep_mem_all)
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem epoll_pwait_the_mask_pointer_is_read_full_width_declines :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 140737488355336 8 (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 140737488355336 8 (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait@v6.18.46 -/
theorem epoll_pwait_the_mask_is_judged_against_the_address_space_top_declines :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 140737488355320 8 (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 140737488355321 8 (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 140737488355321 8 (fun a => if bv_unsigned a < 140737488355328 then some 0 else none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_across_timeout_values_declines :
    check_epoll_pwait_row (pwait_call 4294967295 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 4294967295 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row
        (pwait_call 4294967295 4096 1 18446744073709551615 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967295 4096 1 4294967296 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- `maxevents <= 0` is -EINVAL (:2674-2675): zero, an `int` -1 (the
register 4294967295, which `int32` keeps and `sint32` reads as -1) and
`INT_MIN` (2147483648) alike, and the -EFAULT a range test on the negative product
would have given is rejected.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_non_positive_maxevents_is_einval :
    check_epoll_pwait_row (pwait_call 5 4096 0 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 4294967295 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 2147483648 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 4096 4294967295 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `maxevents > EP_MAX_EVENTS` is -EINVAL (:2674-2675), and the bound is
`INT_MAX / 16` — 134217727 — on riscv64, where the struct is 16 bytes.
At the bound exactly the product is 2147483632 and the range test
decides: an array ending exactly at the top of the address space
(2^47 - 2147483632 = 140735340871696) passes and reaches the -EINVAL of
:2685-2686, one byte higher is -EFAULT (:2678-2679); one above the bound
is -EINVAL wherever the array is.
The model declines the one-byte-higher input: from ad5643cf2f69 until its
revert 890ba5be6335, arch/riscv/include/asm/pgtable.h sets `TASK_SIZE_MAX`
to `LONG_MAX`, so v6.14's `do_epoll_wait` passes it and answers the
non-epoll -EINVAL.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem epoll_pwait_the_bound_is_int_max_over_sixteen :
    check_epoll_pwait_row (pwait_call 5 140735340871696 134217727 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 140735340871697 134217727 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 140735340871697 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- The bound is tested before the range (:2674-2675 before :2678-2679):
an array at 2^63 - 8 is -EINVAL under a count above the bound, and the
-EFAULT its range would draw is rejected; under a count of 1 the same
array is -EFAULT.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem epoll_pwait_the_bound_is_tested_before_the_range :
    check_epoll_pwait_row (pwait_call 5 9223372036854775800 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckOk ep_model []
    ∧ check_epoll_pwait_row (pwait_call 5 9223372036854775800 134217728 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckReject
    ∧ check_epoll_pwait_row (pwait_call 5 9223372036854775800 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckOk ep_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem epoll_pwait_the_array_is_a_range_verdict_not_a_read_declines :
    check_epoll_pwait_row (pwait_call 5 140737488355313 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 140737488355312 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 0 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 140737488355313 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:ep_check_params@v6.18.46 -/
theorem epoll_pwait_every_fixture_epfd_declines :
    check_epoll_pwait_row (pwait_call 0 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 1 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 2 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 3 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 6 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 7 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 8 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 9 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 10 4096 1 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_success_on_a_non_epoll_fd_declines :
    check_epoll_pwait_row (pwait_call 3 4096 1 0 0 0 (fun _ => none))
        (mkEffect 0 [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 3 4096 1 0 0 0 (fun _ => none))
        (mkEffect 1 [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- `epfd` and `maxevents` are `int`s (:2774-2776), narrowed by
`__SC_CAST`, so 2^32 + 5 is fd 5 and 2^32 + 1 a count of 1, and the answer
is the -EINVAL of an open non-epoll fd with a good count — not the -EBADF
of a number no table holds.  The count is read through `sint32`, which takes the low 32
bits itself, so the row's `int32` on it is unobservable — and this pair
cannot see the count's reading at all: narrowed, the count is 1 and fd 5
is -EINVAL; read at full width, 2^32 + 1 is above `EP_MAX_EVENTS` and
-EINVAL too.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_narrowed_epfd_and_count_declines :
    check_epoll_pwait_row (pwait_call 4294967301 4096 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 4294967301 4096 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) ep_model
        = CheckUnmodeled  := by
  exact ⟨rfl, rfl⟩


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_pwait,do_epoll_wait,ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem epoll_pwait_the_count_reads_as_int_declines :
    check_epoll_pwait_row (pwait_call 5 140737488355313 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) ep_model
        = CheckUnmodeled
    ∧ check_epoll_pwait_row (pwait_call 5 140737488355313 4294967297 0 0 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) ep_model
        = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_truncated_return_declines :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect 4294967274 [] []) ep_model
      = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-! ## Nothing declines where the spec answers

A checker that answered `CheckUnmodeled` on every input would meet its
five obligations against a spec that declined everywhere.  These pins
refuse that on one answered input per syscall, in two shapes: the exact
verdict's disequality, and a refusal over EVERY effect, which is the
statement that the decision not to decline is made before the effect is
looked at. -/

/-- A stray create flag is never declined: the disequality, derived from
`epoll_create1_a_stray_flag_is_einval`.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_stray_flag_never_declines :
    check_epoll_create1_row (create1_call 1) (mkEffect (errno_ret EINVAL) [] []) ep_model
      ≠ CheckUnmodeled := by
  rw [epoll_create1_a_stray_flag_is_einval]
  exact fun h => nomatch h

/-- …and over every effect: the outcome function answers -EINVAL for the
flag word alone, and `check_ret_only` never declines.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_stray_flag_answers_whatever_it_is_shown (eff : SyscallEffect) :
    check_epoll_create1_row (create1_call 1) eff ep_model ≠ CheckUnmodeled := by
  intro h
  exact check_ret_only_no_unmodeled eff (errno_ret EINVAL) ep_model [] h

/-- …and over every MODEL as well as every effect: the gate reads the flag
word alone.  The spec-level pin `create_bit_0_never_unmodeled` in
`Checks/Cases/Fs/EventPoll.lean` carries the refutation; here the
checker's `check_epoll_create1_sound_unmodeled` turns a decline of the row
into a decline of the spec, which that pin refutes.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_create1_a_stray_flag_never_declines_for_any_model (m : Model)
    (eff : SyscallEffect) :
    check_epoll_create1_row (create1_call 1) eff m ≠ CheckUnmodeled :=
  fun h =>
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.create_bit_0_never_unmodeled
      (create1_call 1) m (check_epoll_create1_sound_unmodeled _ _ _ _ h)

/-- A file target is never declined: derived from
`epoll_ctl_a_file_target_is_eperm_not_einval`.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_file_target_never_declines :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) (mkEffect (errno_ret EPERM) [] []) ep_model
      ≠ CheckUnmodeled := by
  rw [epoll_ctl_a_file_target_is_eperm_not_einval.1]
  exact fun h => nomatch h

/-- …and over every effect.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem epoll_ctl_a_file_target_answers_whatever_it_is_shown (eff : SyscallEffect) :
    check_epoll_ctl_row (ctl_call 5 1 3 4096 ep_mem_all) eff ep_model ≠ CheckUnmodeled := by
  exact check_ep_answer_no_unmodeled (errno_ret EPERM, []) eff ep_model

/-- Valid-count null-mask waits decline even the base answer: QEMU can
fault on the buffer or return ENOMEM before the host descriptor check.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_non_epoll_fd_declines :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  rfl


/-- Valid-count null-mask waits decline even the base answer: QEMU can
fault on the buffer or return ENOMEM before the host descriptor check.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_non_epoll_fd_declines_every_effect (eff : SyscallEffect) :
    check_epoll_pwait_row (pwait_call 5 4096 1 0 0 0 (fun _ => none)) eff ep_model
      = CheckUnmodeled  := by
  rfl


/-- Valid-count null-mask waits decline even the base answer: QEMU can
fault on the buffer or return ENOMEM before the host descriptor check.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_pwait_a_null_mask_declines (epfd : word)
    (eff : SyscallEffect) :
    check_epoll_pwait_row (pwait_call epfd 4096 1 0 0 0 (fun _ => none)) eff ep_model
      = CheckUnmodeled := by
  apply check_epoll_pwait_complete_unmodeled
  exact (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_null_mask_declines
    (fd32 epfd) (pwait_call epfd 4096 1 0 0 0 (fun _ => none)) Unmodeled).mpr rfl


/-! ## The rows are the dispatcher's

`Sys/Registry/Fs/EventPoll.lean` registers the three arms the spec's
dispatcher applies, and `Checks/Cases/SyscallTable.lean` pins that 20, 21
and 22 look them up.  What nothing above pins is that the ROWS at the top
of this file narrow the registers as those arms do: a row applying `fd32`
where the arm applies `flag32` would satisfy every pin above — both take
the low 32 bits — and still not be the dispatcher's application.  Each
theorem here closes the row's `CheckOk` against `dispatch spec_table`
through the registered arm, by the checker's two `Ok` lemmas; the `exact`
unifies only if the row's narrowing is the arm's, term for term.  The
number is a hypothesis because a row is stated over any input, and the
last pin says the register files above carry it.  These carry `model:`
lines: they claim nothing about Linux, only that two definitions of this
tree coincide. -/

/-- Any input the dispatcher routes to 20 is answered by
`check_epoll_create1_row` exactly as `dispatch spec_table` admits it: the
row is `Sys.Registry.Fs.EventPoll.epoll_create1_arm`'s application.
model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_create1_row_is_the_dispatcher_on_20 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h20 : bv_unsigned i.in_sysno = 20) :
    check_epoll_create1_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_create1_arm (by rw [h20]; rfl)]
  exact ⟨check_epoll_create1_sound_ok _ _ _ _ _ i, check_epoll_create1_complete_ok _ _ _ _ _ i⟩

/-- The same for 21: `check_epoll_ctl_row` is
`Sys.Registry.Fs.EventPoll.epoll_ctl_arm`'s application.
model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_ctl_row_is_the_dispatcher_on_21 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h21 : bv_unsigned i.in_sysno = 21) :
    check_epoll_ctl_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_ctl_arm (by rw [h21]; rfl)]
  exact ⟨check_epoll_ctl_sound_ok i _ _ _ _ _ _ _ _, check_epoll_ctl_complete_ok i _ _ _ _ _ _ _ _⟩

/-- The same for 22: `check_epoll_pwait_row` is
`Sys.Registry.Fs.EventPoll.epoll_pwait_arm`'s application, the fourth
register skipped included.
model: two definitions of the tree coincide, the row and the registered arm -/
theorem epoll_pwait_row_is_the_dispatcher_on_22 (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h22 : bv_unsigned i.in_sysno = 22) :
    check_epoll_pwait_row i eff m = CheckOk m' evs ↔ dispatch spec_table i m (Ok eff m' evs) := by
  rw [dispatch_arm spec_table i m _ Sys.Registry.Fs.EventPoll.epoll_pwait_arm (by rw [h22]; rfl)]
  exact ⟨check_epoll_pwait_sound_ok i _ _ _ _ _ _ _ _ _,
    check_epoll_pwait_complete_ok i _ _ _ _ _ _ _ _ _⟩

/-- The register files above carry the numbers the three theorems assume:
a7 is 20, 21 and 22 whatever the other registers hold.
model: the number a same-file register file carries in a7 -/
theorem the_register_files_carry_their_numbers
    (flags epfd op tfd ev events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) :
    bv_unsigned (create1_call flags).in_sysno = 20
    ∧ bv_unsigned (ctl_call epfd op tfd ev mem).in_sysno = 21
    ∧ bv_unsigned (pwait_call epfd events maxevents timeout sigmask sigsetsize mem).in_sysno = 22 :=
  ⟨rfl, rfl, rfl⟩


-- lean-port sentinel: ticket V-Fs-EventPoll appends below this line

section V_Fs_EventPoll

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-EventPoll — epoll_create1, epoll_ctl and epoll_pwait over the real table

WHAT IS STATED HERE.  Each pin here states a call a probe
(`testing/syscall-check/tests/epoll_spec.c`,
`testing/syscall-check/tests/scenarios/wait_slot_close_reopen.c`) makes,
or a call that separates the arm's reading of its registers from a wrong
one.  Verdict and witness names end in `_over_the_real_table`.

WHAT A PIN HERE ADDS to the row-level pins above is the ARM's claim:
the lookup at 20, 21 or 22 finds the registered arm, and that arm hands
the checker the registers the row names, narrowed as the row narrows
them.  The calls that open a descriptor first (`perm`, `tgtbad`,
`inval`, `chan`) are stated at `ep_model`: the directory the run opened
with `openat(".")` at fd 3 is the fixture's directory, fd 5, and the
run's socket at fd 4 is the fixture's socket, fd 6.  The event struct and
stack pointers are 4096 and the readable signal mask 8192; the boundary
and fault addresses are the recorded ones.

POLARITY: the evidence line is `kernel:` on each pin about the kernel's
answer, `CheckOk`, `CheckReject` and `CheckUnmodeled` alike, and `model:`
on pins about the table's own contents. -/

/-- The lookup on `create1_call` finds `arm_epoll_create1`.
model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_create1_call (flags : word) :
    lookup_ca checked_table (bv_unsigned (create1_call flags).in_sysno)
      = some arm_epoll_create1 :=
  lookup_ca_checked_table_epoll_create1

/-- The table applies `check_epoll_create1_row` with the row's register readings.
model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_create1_call (flags : word)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (create1_call flags) eff m
      = check_epoll_create1_row (create1_call flags) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_create1_call flags)

/-- The lookup on `ctl_call` finds `arm_epoll_ctl`.
model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_ctl_call (epfd op tfd ev : word) (mem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (ctl_call epfd op tfd ev mem).in_sysno)
      = some arm_epoll_ctl :=
  lookup_ca_checked_table_epoll_ctl

/-- The table applies `check_epoll_ctl_row` with the row's register readings.
model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_ctl_call (epfd op tfd ev : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (ctl_call epfd op tfd ev mem) eff m
      = check_epoll_ctl_row (ctl_call epfd op tfd ev mem) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_ctl_call epfd op tfd ev mem)

/-- The lookup on `pwait_call` finds `arm_epoll_pwait`.
model: `lookup_ca` over `checked_table` at the call's closed syscall number -/
theorem lookup_pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte) :
    lookup_ca checked_table
        (bv_unsigned (pwait_call epfd events maxevents timeout sigmask sigsetsize mem).in_sysno)
      = some arm_epoll_pwait :=
  lookup_ca_checked_table_epoll_pwait

/-- The table applies `check_epoll_pwait_row` with the row's register readings.
model: `check_syscall` through the registered arm, unfolded -/
theorem check_syscall_pwait_call (epfd events maxevents timeout sigmask sigsetsize : word)
    (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (pwait_call epfd events maxevents timeout sigmask sigsetsize mem) eff m
      = check_epoll_pwait_row (pwait_call epfd events maxevents timeout sigmask sigsetsize mem)
          eff m :=
  check_syscall_of_found _ _ _ _
    (lookup_pwait_call epfd events maxevents timeout sigmask sigsetsize mem)

/-! ### The recorded calls, through `check_syscall` -/

/-- The probe's `conform -- badflags` calls answer -EINVAL at
`do_epoll_create` (fs/eventpoll.c:2439-2440, Linux v6.18.46), before
allocation.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem badflags_einval_accepted_over_the_real_table (m : Model) :
    check_syscall (create1_call 1)
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (create1_call 0x80001)
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- The probe's `reject --mutate epoll_create1:ret=0 -- badflags` is refused,
as is the fd 3 returned by a well-formed create: `do_epoll_create` returns
-EINVAL at fs/eventpoll.c:2439-2440 (Linux v6.18.46).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem badflags_descriptors_rejected_over_the_real_table (m : Model) :
    check_syscall (create1_call 1)
      (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (create1_call 1)
      (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `fail-closed -- create` and `trunc`, and the scenario's
`epfirst`, reach `do_epoll_create`'s fd installation
(fs/eventpoll.c:2463-2464, Linux v6.18.46), outside the modeled surface;
flags 2^32 become zero through the `int` parameter at :2473.
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_and_trunc_declined_over_the_real_table (m : Model) :
    check_syscall (create1_call 0)
      (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (create1_call (2^32))
      (mkEffect 3 [] []) m = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The probe's `conform -- fault` gets -EFAULT from `epoll_ctl`'s copy at
fs/eventpoll.c:2663-2665 (Linux v6.18.46), before `do_epoll_ctl` resolves
either fd.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem fault_efault_accepted_over_the_real_table (m : Model) :
    check_syscall (ctl_call 18446744073709551615 1 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] :=
  rfl

/-- The probe's `conform -- delbad` skips the copy through `ep_op_has_event`
and reaches `do_epoll_ctl`'s -EBADF at fs/eventpoll.c:2520-2522 (Linux
v6.18.46); the probe's `ret=-EFAULT` mutation is refused.
kernel: include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem delbad_ebadf_accepted_over_the_real_table :
    check_syscall (ctl_call 18446744073709551615 2 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 18446744073709551615 2 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckReject := by
  simp only [check_syscall_ctl_call]
  exact ⟨epoll_ctl_del_never_reads_the_event.1, epoll_ctl_efault_under_del_is_rejected⟩

/-- The probe's `conform -- perm` names its opened directory as both the
epfd and the target (the fixture's directory, fd 5): `do_epoll_ctl`
returns -EPERM at fs/eventpoll.c:2530-2531 before the -EINVAL test at
:2542-2544 (Linux v6.18.46), so the probe's `ret=-EINVAL` is refused.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem perm_eperm_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `reject --mutate epoll_ctl:smuggle-copyin:a3:16 -- perm`
records the copy `epoll_ctl` performs at fs/eventpoll.c:2663-2665 (Linux
v6.18.46), which the spec omits; this pins the known omission in
`bugs/epoll-ctl-copyin-not-recorded.md`.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem perm_recorded_copyin_rejected_over_the_real_table :
    check_syscall (ctl_call 5 1 5 4096 ep_mem_all)
      (with_copyins [(4096, 16)] (mkEffect (errno_ret EPERM) [] [])) ep_model
      = CheckReject :=
  rfl

/-- The probe's `conform -- tgtbad`, with its opened directory (fd 5) as the
epfd, reaches `do_epoll_ctl`'s target lookup and -EBADF at
fs/eventpoll.c:2525-2527 (Linux v6.18.46).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem tgtbad_ebadf_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 18446744073709551615 4096 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model [] := by
  simp only [check_syscall_ctl_call]
  exact epoll_ctl_a_closed_target_is_ebadf.1

/-- The probe's `conform -- inval` has its socket at fd 4, represented here by
fd 6: the target polls, so `do_epoll_ctl` reaches -EINVAL at
fs/eventpoll.c:2542-2544 (Linux v6.18.46), and the probe's `ret=-EPERM` is
refused.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll; net/socket.c:sock_alloc_file,sock_poll@v6.18.46 -/
theorem inval_einval_accepted_over_the_real_table :
    check_syscall (ctl_call 5 1 6 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call 5 1 6 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `fail-closed -- chan` records -EINVAL, but fd 2's channel
leaves its target's poll operation unknown to the model at
`do_epoll_ctl`'s gate (fs/eventpoll.c:2530-2531, Linux v6.18.46); the
opened epfd is the fixture's directory, fd 5.
kernel: fs/eventpoll.c:do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem chan_declined_over_the_real_table :
    check_syscall (ctl_call 5 1 2 4096 ep_mem_all)
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled :=
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwbadfd_ebadf_over_the_real_table_declines :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- The probe's `conform -- pwmaxev` supplies zero and -1 counts:
`ep_check_params` returns -EINVAL at fs/eventpoll.c:2674-2675 (Linux
v6.18.46); its `ret=0` mutation at zero is refused.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwmaxev_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 4096 0 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 4096 18446744073709551615 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (pwait_call 5 4096 0 0 0 0 (fun _ => none))
      (mkEffect 0 [] []) ep_model = CheckReject := by
  simp only [check_syscall_pwait_call]
  exact ⟨epoll_pwait_a_non_positive_maxevents_is_einval.1,
    epoll_pwait_a_non_positive_maxevents_is_einval.2.1, rfl⟩

/-- The probe's `conform -- sigsize` reaches `set_user_sigmask`'s size
rejection at kernel/signal.c:3287-3288 before reading the mask or
resolving the epfd through `do_epoll_pwait` (fs/eventpoll.c:2763-2767,
Linux v6.18.46).
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem sigsize_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 0 0 8192 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwinval_einval_over_the_real_table_declines :
    check_syscall (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- The probe's `conform -- pwmaxhi` exceeds `EP_MAX_EVENTS` (INT_MAX/16):
`ep_check_params` returns -EINVAL at fs/eventpoll.c:2674-2675 (Linux
v6.18.46).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwmaxhi_einval_accepted_over_the_real_table :
    check_syscall (pwait_call 5 4096 0x8000000 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `conform -- pwsigfault` faults in `set_user_sigmask` at
kernel/signal.c:3289-3290, before `do_epoll_pwait` reaches the closed epfd
(fs/eventpoll.c:2763-2767, Linux v6.18.46).
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwsigfault_efault_accepted_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 8 8 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- The probe's `conform -- pwevfault` places the events range past the user
limit: `ep_check_params` returns -EFAULT at fs/eventpoll.c:2678-2679
(Linux v6.18.46).
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevfault_efault_accepted_over_the_real_table :
    check_syscall (pwait_call 5 0x7ffffffffffffff8 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckOk ep_model [] :=
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevtop_einval_over_the_real_table_declines :
    check_syscall (pwait_call 5 (2^47 - 16) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall (pwait_call 5 (2^47 - 16) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- The probe's `fail-closed --expect-unmodeled epoll_pwait -- pwevpast`
ends one byte past the Sv48 limit.
Linux v6.18.46 fs/eventpoll.c [ep_check_params] returns EFAULT there.
At v6.14, fs/eventpoll.c `do_epoll_wait` passes that range under
`LONG_MAX`, so the spec declines both errnos.
kernel: fs/eventpoll.c:ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwevpast_errnos_declined_over_the_real_table :
    check_syscall (pwait_call 5 (2^47 - 15) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall (pwait_call 5 (2^47 - 15) 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The probe's `fail-closed -- realmask` records -EBADF after
`set_user_sigmask` installs a readable mask at kernel/signal.c:3292-3294
(Linux v6.18.46); the model declines that signal-state change.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem realmask_declined_over_the_real_table :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 8192 8 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled :=
  rfl

/-! ### The arm's reading of its registers -/

/-- The `badflags` gate reads a0 through `epoll_create1`'s flags parameter
(fs/eventpoll.c:2473, Linux v6.18.46): an arm reading a1 would accept
-EINVAL in the first conjunct and decline the second.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create1_flags_are_a0_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 20 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 20 [1, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- A widened version of `perm` still names directory fd 5 twice through
`epoll_ctl`'s int parameters (fs/eventpoll.c:2658, Linux v6.18.46); an arm
reading either fd whole would answer -EBADF instead of the accepted -EPERM
and would accept the rejected -EBADF.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_ctl,do_epoll_ctl; include/linux/poll.h:file_can_poll@v6.18.46 -/
theorem ctl_both_fds_are_narrowed_over_the_real_table :
    check_syscall (ctl_call (2^32 + 5) 1 (2^32 + 5) 4096 ep_mem_all)
      (mkEffect (errno_ret EPERM) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall (ctl_call (2^32 + 5) 1 (2^32 + 5) 4096 ep_mem_all)
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- A widened `delbad` op is DEL through `epoll_ctl`'s int parameter
(fs/eventpoll.c:2658, Linux v6.18.46); an arm reading the whole op copies
NULL at :2663-2665, flipping the accepted -EBADF and rejected -EFAULT.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; include/linux/eventpoll.h:ep_op_has_event; fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_op_is_narrowed_over_the_real_table :
    check_syscall (ctl_call 18446744073709551615 (2^32 + 2) 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckOk ep_model []
    ∧ check_syscall
        (ctl_call 18446744073709551615 (2^32 + 2) 18446744073709551615 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/eventpoll.c:epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_epfd_is_narrowed_over_the_real_table_declines :
    check_syscall (pwait_call (2^32 + 5) 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall (pwait_call (2^32 + 5) 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:ep_timeout_to_timespec,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_timeout_is_not_a_spec_argument_over_the_real_table_declines :
    check_syscall (pwait_call 5 4096 1 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall (pwait_call 5 4096 1 18446744073709551615 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_timeout_is_not_the_mask_over_the_real_table_declines :
    check_syscall (pwait_call 18446744073709551615 4096 1 18446744073709551615 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall
        (pwait_call 18446744073709551615 4096 1 18446744073709551615 0 0 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: kernel/signal.c:set_user_sigmask; fs/eventpoll.c:do_epoll_pwait,do_epoll_wait@v6.18.46 -/
theorem pwait_mask_is_a4_and_size_is_a5_over_the_real_table_declines :
    check_syscall (pwait_call 18446744073709551615 4096 1 0 0 7 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled
    ∧ check_syscall (pwait_call 18446744073709551615 4096 1 0 8 7 (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-! ### The witness the table hands `receptive` -/

/-- The table's witnesses for `badflags` and `create` are the -EINVAL of
`do_epoll_create` at fs/eventpoll.c:2439-2440 and the decline before its
descriptor installation at :2463-2464 (Linux v6.18.46).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create1_witness_over_the_real_table (m : Model) :
    syscall_spec_witness (create1_call 1) m
      = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ syscall_spec_witness (create1_call 0) m = Unmodeled :=
  ⟨rfl, rfl⟩

/-- The witness for `fault` is `epoll_ctl`'s copy failure at
fs/eventpoll.c:2663-2665 (Linux v6.18.46).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_witness_over_the_real_table :
    syscall_spec_witness
        (ctl_call 18446744073709551615 1 18446744073709551615 0 (fun _ => none)) ep_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) ep_model [] :=
  rfl

/-- The witness for `pwinval` is `ep_check_params`' -EINVAL
(fs/eventpoll.c:2685-2686, Linux v6.18.46); `realmask` is declined at
`set_user_sigmask`'s state change (kernel/signal.c:3292-3294).
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_witness_declines_over_the_real_table :
    syscall_spec_witness (pwait_call 5 4096 1 0 0 0 (fun _ => none)) ep_model
      = Unmodeled
    ∧ syscall_spec_witness (pwait_call 18446744073709551615 4096 1 0 8192 8 ep_mem_all) ep_model
      = Unmodeled :=
  ⟨rfl, rfl⟩

end V_Fs_EventPoll

/-! ## Rocq checker examples -/


/-- Bit 31 through the checker: Linux's `do_epoll_create` answers -EINVAL.
QEMU 11.1.1's flag translation in `do_syscall1` drops the bit, so QEMU can
return a descriptor.  The checker declines both effects.
#1925 counterpart: epoll_dropped_flag_linux_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_dropped_flag_linux_declines :
  check_epoll_create1 2147483648
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: epoll_dropped_flag_qemu_fd_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem epoll_dropped_flag_qemu_fd_declines :
  check_epoll_create1 2147483648
    (mkEffect 3 [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- Bit 20 and access mode 3: Linux's `do_epoll_create` answers -EINVAL for
each.  QEMU 11.1.1's `target_to_host_bitmask_len` (linux-user/thunk.c)
maps each word to 0, so QEMU can return a descriptor.  The checker
declines both effects on both words.
#1925 counterpart: create_translate_bit20_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit20_einval :
  check_epoll_create1 1048576
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: create_translate_bit20_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit20_zero :
  check_epoll_create1 1048576
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: create_translate_acc3_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_acc3_einval :
  check_epoll_create1 3
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: create_translate_acc3_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_acc3_zero :
  check_epoll_create1 3
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- Bit 0 (`O_WRONLY`) and bit 11 (`O_NONBLOCK`) survive QEMU 11.1.1's flag
translation in `do_syscall1`.  The host's `do_epoll_create` refuses each
with -EINVAL, as Linux does.  The checker accepts -EINVAL and rejects a
descriptor.
#1925 counterpart: create_translate_bit0_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit0_einval :
  check_epoll_create1 1
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: create_translate_bit0_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit0_zero :
  check_epoll_create1 1
    (mkEffect 0 [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: create_translate_nonblock_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_nonblock_einval :
  check_epoll_create1 2048
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: create_translate_nonblock_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_nonblock_zero :
  check_epoll_create1 2048
    (mkEffect 0 [] []) epoll_row_model = CheckReject := by
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_ebadf_declines :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 4096) 9999 2 9999 4096
    (mkEffect (errno_ret EBADF) [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_zero_declines :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 4096) 9999 2 9999 4096
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_eperm_declines :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 4096) 9999 2 9999 4096
    (mkEffect (errno_ret EPERM) [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- The same high-half DEL with a NULL `event`: QEMU 11.1.1's `do_syscall1`
locks nothing and passes NULL to the host.  Linux's `do_epoll_ctl` and the
host both answer -EBADF for fd 9999.  The checker accepts -EBADF, and
rejects -EFAULT, 0 and -EPERM.
#1925 counterpart: ctl_high_del_null_efault (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_null_efault :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 0) 9999 2 9999 0
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: ctl_high_del_null_ebadf (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_null_ebadf :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 0) 9999 2 9999 0
    (mkEffect (errno_ret EBADF) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: ctl_high_del_null_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_null_zero :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 0) 9999 2 9999 0
    (mkEffect 0 [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: ctl_high_del_null_eperm (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_null_eperm :
  check_epoll_ctl (epoll_ctl_raw_in 4294967298 0) 9999 2 9999 0
    (mkEffect (errno_ret EPERM) [] []) epoll_row_model = CheckReject := by
  rfl

/-- A plain DEL beside a non-NULL unmapped `event`: Linux's `epoll_ctl`
skips the copy.  QEMU 11.1.1's `do_syscall1` sees a full register of 2
and skips its lock too.  Both reach the -EBADF of `do_epoll_ctl`.  The
checker accepts -EBADF, and rejects -EFAULT, 0 and -EPERM.
#1925 counterpart: ctl_ordinary_del_efault (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_ordinary_del_efault :
  check_epoll_ctl (epoll_ctl_raw_in 2 4096) 9999 2 9999 4096
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: ctl_ordinary_del_ebadf (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_ordinary_del_ebadf :
  check_epoll_ctl (epoll_ctl_raw_in 2 4096) 9999 2 9999 4096
    (mkEffect (errno_ret EBADF) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: ctl_ordinary_del_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_ordinary_del_zero :
  check_epoll_ctl (epoll_ctl_raw_in 2 4096) 9999 2 9999 4096
    (mkEffect 0 [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: ctl_ordinary_del_eperm (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_ordinary_del_eperm :
  check_epoll_ctl (epoll_ctl_raw_in 2 4096) 9999 2 9999 4096
    (mkEffect (errno_ret EPERM) [] []) epoll_row_model = CheckReject := by
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_bad_mask_count_zero_efault_declines :
  check_epoll_pwait (epoll_mask_count_in 0) 0 4096 0 8 8
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_mask_count_zero_success_declines :
  check_epoll_pwait (epoll_mask_count_in 0) 0 4096 0 8 8
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_mask_count_zero_write_declines :
  check_epoll_pwait (epoll_mask_count_in 0) 0 4096 0 8 8
    (mkEffect (errno_ret EFAULT) [(4096, [0])] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_bad_mask_count_overflow_efault_declines :
  check_epoll_pwait (epoll_mask_count_in 134217728) 0 4096 134217728 8 8
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_mask_count_overflow_success_declines :
  check_epoll_pwait (epoll_mask_count_in 134217728) 0 4096 134217728 8 8
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_bad_mask_count_overflow_write_declines :
  check_epoll_pwait (epoll_mask_count_in 134217728) 0 4096 134217728 8 8
    (mkEffect (errno_ret EFAULT) [(4096, [0])] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- A valid count leaves the unreadable mask's -EFAULT as the only answer.
#1925 counterpart: pwait_mask_fault_valid_count_efault (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl,do_epoll_wait,do_epoll_pwait@v6.18.46 -/
theorem pwait_mask_fault_valid_count_efault :
  check_epoll_pwait (epoll_mask_count_in 1) 0 4096 1 8 8
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- QEMU's count-first -EINVAL requires an invalid count.
#1925 counterpart: pwait_mask_fault_valid_count_einval_rejected (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_pwait; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pwait_mask_fault_valid_count_einval_rejected :
  check_epoll_pwait (epoll_mask_count_in 1) 0 4096 1 8 8
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckReject := by
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_null_einval_declines :
  check_epoll_pwait (epoll_row_pwait_in 0 0 1) 0 0 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_null_0_declines :
  check_epoll_pwait (epoll_row_pwait_in 0 0 1) 0 0 1 0 0
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- `events` at 2^47 + 4096, between `TASK_SIZE` and `LONG_MAX`.  Linux's
`ep_check_params` answers -EFAULT at v6.18.46, where `access_ok` compares
against `TASK_SIZE`.  At v6.14 riscv64's `TASK_SIZE_MAX` is `LONG_MAX`
(arch/riscv/include/asm/pgtable.h), so the range passes and fd 0 answers
-EINVAL.  The checker declines -EINVAL, -EFAULT and 0.
#1925 counterpart: pwait_events_long_max_gap_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_long_max_gap_einval :
  check_epoll_pwait (epoll_row_pwait_in 0 140737488359424 1) 0 140737488359424 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: pwait_events_long_max_gap_efault (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_long_max_gap_efault :
  check_epoll_pwait (epoll_row_pwait_in 0 140737488359424 1) 0 140737488359424 1 0 0
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: pwait_events_long_max_gap_0 (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_long_max_gap_0 :
  check_epoll_pwait (epoll_row_pwait_in 0 140737488359424 1) 0 140737488359424 1 0 0
    (mkEffect 0 [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- `events` at 2^63, above `LONG_MAX`: Linux's `ep_check_params` answers
-EFAULT under either limit.  QEMU 11.1.1's `do_syscall1` fails its write
lock of the unmapped range with -EFAULT too.  The checker accepts -EFAULT
and rejects -EINVAL.
#1925 counterpart: pwait_events_past_long_max_efault (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_past_long_max_efault :
  check_epoll_pwait (epoll_row_pwait_in 0 9223372036854775808 1) 0 9223372036854775808 1 0 0
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: pwait_events_past_long_max_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_past_long_max_einval :
  check_epoll_pwait (epoll_row_pwait_in 0 9223372036854775808 1) 0 9223372036854775808 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckReject := by
  have ho : epoll_pwait_outcome (epoll_row_pwait_in 0 9223372036854775808 1) epoll_row_model 0 9223372036854775808 1 0 0 = some (errno_ret EFAULT, []) := by decide +kernel
  unfold check_epoll_pwait
  rw [ho]
  have h : ep_answerb (errno_ret EFAULT, []) (errno_ret EINVAL) = false := by decide +kernel
  simp only [check_ep_answer, h, Bool.false_eq_true, ↓reduceIte]

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_writable_einval_declines :
  check_epoll_pwait (epoll_lock_in true) 0 4096 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_lock_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_writable_declines :
  check_epoll_pwait (epoll_lock_in true) 0 4096 1 0 0
    (mkEffect (errno_ret EFAULT) [] []) epoll_lock_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_writable_load_declines :
  check_epoll_pwait (epoll_lock_in true) 0 4096 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_load_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_read_only_closed_declines :
  check_epoll_pwait epoll_read_only_closed_in 9999 4096 1 0 0
    (mkEffect (errno_ret EBADF) [] []) epoll_lock_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- An ADD `event` at 2^64 - 8 whose bytes are defined: the range
wraps.  Linux's `__access_ok` (include/asm-generic/access_ok.h, Linux
v6.18.46) refuses it with -EFAULT.  QEMU 11.1.1's `guest_range_valid_untagged_vaddr`
(include/user/guest-host.h) refuses it too.  The checker accepts -EFAULT,
and rejects -EPERM and -EINVAL.
#1925 counterpart: ctl_add_wrapped_defined_event_efault_ok (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_wrapped_defined_event_efault_ok :
  check_epoll_ctl epoll_wrap_in 0 1 0 18446744073709551608
    (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  change check_ep_answer (errno_ret EFAULT, []) (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckOk epoll_row_model []
  have h : ep_answerb (errno_ret EFAULT, []) (errno_ret EFAULT) = true :=
    (ep_answerb_spec _ _).mpr (Or.inl rfl)
  simp only [check_ep_answer, h, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- #1925 counterpart: ctl_add_wrapped_defined_event_eperm_rejected (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_wrapped_defined_event_eperm_rejected :
  check_epoll_ctl epoll_wrap_in 0 1 0 18446744073709551608
    (mkEffect (errno_ret EPERM) [] []) epoll_row_model = CheckReject := by
  change check_ep_answer (errno_ret EFAULT, []) (mkEffect (errno_ret EPERM) [] []) epoll_row_model = CheckReject
  have h : ep_answerb (errno_ret EFAULT, []) (errno_ret EPERM) = false := by decide +kernel
  simp only [check_ep_answer, h, Bool.false_eq_true, ↓reduceIte]

/-- #1925 counterpart: ctl_add_wrapped_defined_event_einval_rejected (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_wrapped_defined_event_einval_rejected :
  check_epoll_ctl epoll_wrap_in 0 1 0 18446744073709551608
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckReject := by
  change check_ep_answer (errno_ret EFAULT, []) (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckReject
  have h : ep_answerb (errno_ret EFAULT, []) (errno_ret EINVAL) = false := by decide +kernel
  simp only [check_ep_answer, h, Bool.false_eq_true, ↓reduceIte]


/-! Create flag words with one bit outside `EPOLL_CLOEXEC`.  Linux's
`do_epoll_create` answers -EINVAL for each.  QEMU 11.1.1's
`fcntl_flags_tbl` (linux-user/syscall.c) maps bits 12 (`O_DSYNC`), 18
(`O_NOATIME`) and 21 (`O_PATH`) to host bits, and the host answers -EINVAL
too.  The checker accepts that -EINVAL.  Bit 22 (`__O_TMPFILE`) matches no
row alone, and bit 15 (`O_LARGEFILE`) has host value 0 on a 64-bit host.
So QEMU can return a descriptor for those two, and the checker declines
-EINVAL there. -/

/-- #1925 counterpart: create_translate_bit12_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit12_einval :
  check_epoll_create1 4096
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: create_translate_bit12_zero (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit12_zero :
  check_epoll_create1 4096
    (mkEffect 0 [] []) epoll_row_model = CheckReject := by
  rfl

/-- #1925 counterpart: create_translate_bit21_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit21_einval :
  check_epoll_create1 2097152
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl

/-- #1925 counterpart: create_translate_bit15_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit15_einval :
  check_epoll_create1 32768
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: create_translate_bit22_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit22_einval :
  check_epoll_create1 4194304
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  rfl

/-- #1925 counterpart: create_translate_bit18_einval (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_create@v6.18.46 -/
theorem create_translate_bit18_einval :
  check_epoll_create1 262144
    (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckOk epoll_row_model [] := by
  rfl


/-! Writable, defined `events` in the entry-stack band, count 1, a NULL
mask and open non-epoll fd 0.  QEMU 11.1.1's `handle_arg_stack_size`
(linux-user/main.c) can set a stack smaller than 8 MiB.  Its
`setup_arg_pages` (linux-user/elfload.c) maps a guard page below the stack.
So a write lock in the band can fail. Lean declines the whole shape,
including Linux's -EINVAL. At 4096 bytes below the band the lock is sure,
but QEMU's possible allocation failure still makes Lean decline. -/

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_stack_band_declines :
  check_epoll_pwait (epoll_stack_in 8388608) 0 8388608 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_stack_model =
      CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_below_stack_band_declines :
  check_epoll_pwait (epoll_stack_in 8384512) 0 8384512 1 0 0
    (mkEffect (errno_ret EFAULT) [] []) epoll_stack_model =
      CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl

/-- Sibling of `pwait_events_below_stack_band_declines`: the same input
also declines the base Linux answer, -EINVAL for the directory epfd.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_below_stack_band_base_answer_declines :
  check_epoll_pwait (epoll_stack_in 8384512) 0 8384512 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) epoll_stack_model = CheckUnmodeled := by
  rfl


/-! Channel fd 0 as the epfd, past the earlier tests.  A channel's far end
can be an epoll instance, so `is_file_epoll` is unknown for it.  For an
epoll epfd, fs/eventpoll.c `do_epoll_ctl` (Linux v6.18.46) goes on to its
`switch (op)`.  For an epoll epfd, fs/eventpoll.c `do_epoll_wait` (Linux
v6.18.46) goes on to `ep_poll`.  Either can answer 0, so both checkers
decline. Directory fd 5 makes the Linux half answer -EINVAL. The ctl
checker accepts it when QEMU agrees; the pwait shape below declines
because QEMU can fail before reaching the host descriptor check. -/

/-- Socket target fd 6: the checker declines -EINVAL.
#1925 counterpart: ctl_channel_epfd_einval_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_channel_epfd_einval_declines :
  check_epoll_ctl (SyscallInput.mkInput 21 [0, 1, 6, 4096] ep_mem_all ep_mem_all)
    0 1 6 4096 (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  rfl

/-- …and declines 0, the answer of an `EPOLL_CTL_ADD` that succeeds.
#1925 counterpart: ctl_channel_epfd_zero_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_channel_epfd_zero_declines :
  check_epoll_ctl (SyscallInput.mkInput 21 [0, 1, 6, 4096] ep_mem_all ep_mem_all)
    0 1 6 4096 (mkEffect 0 [] []) ep_model = CheckUnmodeled := by
  rfl

/-- Directory fd 5 as the epfd, same socket target: the checker accepts -EINVAL.
#1925 counterpart: ctl_dir_epfd_still_einval (Checks/Cases/Fs/EventPoll.v).
probe: testing/syscall-check/tests/epoll_spec.c#conform -- inval -/
theorem ctl_dir_epfd_still_einval :
  check_epoll_ctl (SyscallInput.mkInput 21 [5, 1, 6, 4096] ep_mem_all ep_mem_all)
    5 1 6 4096 (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckOk ep_model [] := by
  rfl

/-- Count 1, `events` at 4096 and a NULL mask: the checker declines -EINVAL.
#1925 counterpart: pwait_channel_epfd_einval_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_channel_epfd_einval_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [0, 4096, 1, 0, 0, 0] ep_mem_all ep_mem_all)
    0 4096 1 0 0 (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  rfl

/-- …and declines 0 ready events.
#1925 counterpart: pwait_channel_epfd_zero_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_channel_epfd_zero_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [0, 4096, 1, 0, 0, 0] ep_mem_all ep_mem_all)
    0 4096 1 0 0 (mkEffect 0 [] []) ep_model = CheckUnmodeled := by
  rfl

/-- Lean declines ahead of the Rocq change in #1925. The input shape
can produce a QEMU answer different from the base Linux answer, so the whole
shape is declined, including its base answer.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_dir_epfd_still_einval_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [5, 4096, 1, 0, 0, 0] ep_mem_all ep_mem_all)
    5 4096 1 0 0 (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled  := by
  repeat' apply And.intro
  all_goals rfl


/-- The synthetic high events range makes Linux answer -EFAULT, so this decline
must come from QEMU's possible host call on an epoll instance behind the channel.
QEMU 11.1.1 linux-user/syscall.c, `do_syscall1`, reaches the host `epoll_pwait`.
#1925 counterpart: pwait_qemu_channel_epfd_einval_declines (Checks/Cases/Fs/EventPoll.v).
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_qemu_channel_epfd_einval_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [] ep_mem_all ep_mem_all) 0 9223372036854775808 1 0 0
    (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  rfl

/-- Sibling of `pwait_qemu_channel_epfd_einval_declines`: the base Linux
answer is -EFAULT for this events range, and Lean declines that answer too.
kernel: fs/eventpoll.c:do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_qemu_channel_epfd_base_answer_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [] ep_mem_all ep_mem_all) 0 9223372036854775808 1 0 0
    (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled := by
  rfl

/-- A mask QEMU can read-lock must not turn Linux's range fault into a modeled answer.
QEMU 11.1.1 linux-user/signal.c, `process_sigsuspend_mask`, uses a read lock
when called by linux-user/syscall.c, `do_syscall1`.
#1925 counterpart: pwait_qemu_mask_past_task_size_efault_declines (Checks/Cases/Fs/EventPoll.v).
kernel: kernel/signal.c:set_user_sigmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwait_qemu_mask_past_task_size_efault_declines :
  check_epoll_pwait (SyscallInput.mkInput 22 [] ep_mem_all (ep_mem_run 4096 16))
    5 4096 1 140737488355328 8
    (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled := by
  rfl


/-! ## Lean: the base answer is declined on each disagreement shape -/

/-- The base answer on `ctl_add_event_past_task_size_whole_shape_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_add_event_past_task_size_whole_shape_declines_base_answer_declines  :
    check_epoll_ctl (ep_in ep_mem_all) 5 1 3 140737488355313
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_add_event_past_task_size_whole_shape_declines)

/-- The base answer on `pwait_null_mask_bad_size_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_null_mask_bad_size_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 4294967295 4096 1 0 7
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_null_mask_bad_size_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_closed_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 4294967295 4096 1 0 0
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_closed_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_closed_epfd_two_events_ending_at_task_size_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_two_events_ending_at_task_size_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 4294967295 140737488355296 2 0 0
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_closed_epfd_two_events_ending_at_task_size_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_closed_epfd_two_events_ending_at_task_size_whole_shape_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_two_events_ending_at_task_size_whole_shape_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 4294967295 140737488355296 2 0 0
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_closed_epfd_two_events_ending_at_task_size_whole_shape_declines i ep_model [])

/-- The base answer on `pwait_closed_epfd_maxevents_at_bound_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_closed_epfd_maxevents_at_bound_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 4294967295 4096 134217727 0 0
      (mkEffect (errno_ret EBADF) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_closed_epfd_maxevents_at_bound_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_events_ending_at_task_size_whole_shape_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_ending_at_task_size_whole_shape_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 5 140737488355312 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_ending_at_task_size_whole_shape_declines i ep_model [])

/-- The base answer on `pwait_null_events_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_null_events_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 5 0 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_null_events_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_null_events_whole_shape_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_null_events_whole_shape_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 5 0 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_null_events_whole_shape_declines i ep_model [])

/-- The base answer on `pwait_file_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_file_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 3 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_file_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_dir_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_dir_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 5 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_dir_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_socket_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_socket_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 6 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_socket_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_pipe_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_pipe_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 7 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_pipe_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_devnull_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_devnull_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 9 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_devnull_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `pwait_urandom_epfd_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_urandom_epfd_declines_base_answer_declines (i : SyscallInput) :
    check_epoll_pwait i 10 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_urandom_epfd_declines i Unmodeled).mpr rfl)

/-- The base answer on `ctl_high_del_event_past_task_size_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_high_del_event_past_task_size_declines_base_answer_declines  :
    check_epoll_ctl (SyscallInput.mkInput 21 [5, 4294967298, 6, Z_to_bv 64 (2 ^ 47)]
        ep_mem_all ep_mem_all) 5 2 6 (Z_to_bv 64 (2 ^ 47))
      (mkEffect (errno_ret EINVAL) [] []) ep_model = CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_high_del_event_past_task_size_declines)

/-- The base answer on `epoll_high_del_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem epoll_high_del_declines_base_answer_declines  :
    check_epoll_ctl (epoll_ctl_raw_in 4294967298 4096) 9999 2 9999 4096
      (mkEffect (errno_ret EBADF) [] []) epoll_row_model = CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.epoll_high_del_declines)

/-- The base answer on `epoll_mask_count_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_mask_count_declines_base_answer_declines  :
    check_epoll_pwait (epoll_mask_count_in 0) 0 4096 0 8 8
      (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.epoll_mask_count_declines)

/-- The base answer on `pwait_bad_mask_count_overflow_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_bad_mask_count_overflow_declines_base_answer_declines  :
    check_epoll_pwait (epoll_mask_count_in 134217728) 0 4096 134217728 8 8
      (mkEffect (errno_ret EFAULT) [] []) epoll_row_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_bad_mask_count_overflow_declines)

/-- The base answer on `epoll_events_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_events_declines_base_answer_declines  :
    check_epoll_pwait (epoll_row_pwait_in 0 0 1) 0 0 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) epoll_row_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.epoll_events_declines)

/-- The base answer on `epoll_events_whole_shape_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem epoll_events_whole_shape_declines_base_answer_declines  :
    check_epoll_pwait (epoll_lock_in true) 0 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) epoll_lock_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.epoll_events_whole_shape_declines)

/-- The base answer on `pwait_events_read_only_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_read_only_declines_base_answer_declines  :
    check_epoll_pwait (epoll_lock_in false) 0 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) epoll_lock_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_read_only_declines)

/-- The base answer on `pwait_events_writable_load_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_writable_load_declines_base_answer_declines  :
    check_epoll_pwait (epoll_lock_in true) 0 4096 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) epoll_load_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_writable_load_declines)

/-- The base answer on `pwait_events_read_only_closed_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_read_only_closed_declines_base_answer_declines  :
    check_epoll_pwait epoll_read_only_closed_in 9999 4096 1 0 0
      (mkEffect (errno_ret EBADF) [] []) epoll_lock_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_read_only_closed_declines)

/-- The base answer on `pwait_events_stack_band_declines` is declined too: Lean declines the whole shape.
kernel: fs/eventpoll.c:do_epoll_pwait,do_epoll_wait,ep_check_params@v6.18.46 -/
theorem pwait_events_stack_band_declines_base_answer_declines  :
    check_epoll_pwait (epoll_stack_in 8388608) 0 8388608 1 0 0
      (mkEffect (errno_ret EINVAL) [] []) epoll_stack_model = CheckUnmodeled := by
  exact check_epoll_pwait_complete_unmodeled _ _ _ _ _ _ _ _ (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_stack_band_declines)

/-- Sibling of `ctl_stack_event_file_target_declines`: the base Linux
answer is -EPERM for the regular-file target, and Lean declines it too.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_file_target_base_answer_declines :
    check_epoll_ctl
      (SyscallInput.mkInput 21 [0, 1, 3, 8388608] epoll_stack_mem epoll_stack_mem)
      0 1 3 8388608 (mkEffect (errno_ret EPERM) [] []) epoll_stack_ctl_model =
      CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_stack_event_file_target_declines

/-- Sibling of `ctl_stack_event_socket_target_declines`: the base Linux
answer is -EINVAL for the directory epfd and socket target, and Lean declines it too.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_socket_target_base_answer_declines :
    check_epoll_ctl
      (SyscallInput.mkInput 21 [0, 1, 6, 8388608] epoll_stack_mem epoll_stack_mem)
      0 1 6 8388608 (mkEffect (errno_ret EINVAL) [] []) epoll_stack_ctl_model =
      CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_stack_event_socket_target_declines

/-- Sibling of `ctl_stack_event_closed_target_declines`: the base Linux
answer is -EBADF for the missing target, and Lean declines it too.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_stack_event_closed_target_base_answer_declines :
    check_epoll_ctl (epoll_stack_ctl_in 9999)
      0 1 9999 8388608 (mkEffect (errno_ret EBADF) [] []) epoll_stack_ctl_model =
      CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_stack_event_closed_target_declines

/-- The whole symbolic DEL disagreement gate declines the base EBADF answer, not only the concrete high-operation examples.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_closed_symbolic_base_answer_declines (ev : word) (i : SyscallInput)
    (hz : w_is0 ev = false)
    (hop : (bv_unsigned (in_arg i 1) == 2) = false)
    (hs : qemu_lock_sure i ep_model false ev 16 = false) :
    check_epoll_ctl i 4294967295 2 4294967295 ev (mkEffect (errno_ret EBADF) [] []) ep_model =
      CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled _ _ _ _ _ _ _
    ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_del_raw_operation_controls_event_lock_or_declines ev i Unmodeled).mpr
      (Or.inr ⟨hz, hop, hs, rfl⟩))

/-- The same nonnull-event, raw-operation and uncertain-lock gate declines the base EPERM answer for the file target.
kernel: fs/eventpoll.c:epoll_ctl,do_epoll_ctl@v6.18.46 -/
theorem ctl_del_file_symbolic_base_answer_declines (ev : word) (i : SyscallInput)
    (hz : w_is0 ev = false)
    (hop : (bv_unsigned (in_arg i 1) == 2) = false)
    (hs : qemu_lock_sure i ep_model false ev 16 = false) :
    check_epoll_ctl i 5 2 3 ev (mkEffect (errno_ret EPERM) [] []) ep_model =
      CheckUnmodeled := by
  exact check_epoll_ctl_complete_unmodeled i 5 2 3 ev ep_model
    (mkEffect (errno_ret EPERM) [] [])
    ((LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.ctl_del_file_target_is_eperm_or_declines ev i Unmodeled).mpr
      (Or.inr ⟨hz, hop, hs, rfl⟩))

/-- When this events lock may succeed, QEMU can disagree with the base EFAULT answer, so Lean declines that answer for every such input.
kernel: fs/eventpoll.c:do_epoll_pwait,ep_check_params; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pwait_near_2_63_symbolic_base_answer_declines (i : SyscallInput)
    (hmay : qemu_lock_may i true 9223372036854775800 16 = true) :
    check_epoll_pwait i 5 9223372036854775800 1 0 0
      (mkEffect (errno_ret EFAULT) [] []) ep_model = CheckUnmodeled := by
  apply check_epoll_pwait_complete_unmodeled
  exact (LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventPoll.pwait_events_near_2_63_is_efault_or_declines i Unmodeled).mpr
    (Or.inr ⟨hmay, rfl⟩)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventPoll
