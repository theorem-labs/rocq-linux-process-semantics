import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Kernel.Fork — what `set_tid_address`, `clone` and `clone3` answer, read off against Linux

Worked examples over `Sys.Kernel.Fork.set_tid_address_spec`,
`Sys.Kernel.Fork.clone_spec` and `Sys.Kernel.Fork.clone3_spec` (the clone
half is its own section further down and mirrors no Rocq worked-cases
file, as it says there).  Mirrors
`theories/LinuxProcessSem/Checks/Cases/Kernel/Fork.v`, whose
`set_tid_address_first_choice_is_within_modeled_envelope` is stated over
the SPEC — its hypothesis is `set_tid_address_spec i m (Ok eff m' evs)` —
and proved through the executable checker's completeness lemma; it is
one-directional and speaks of `Ok` outcomes only.
`set_tid_address_first_call_draws_a_live_tid` below names it as its
`rocq-twin:` and says strictly more: an `iff` over EVERY outcome, which
adds that the path never yields `Unmodeled` and that every tid inside the
envelope is admitted, neither of which the Rocq lemma states, so both
halves are pinned against the kernel here and nowhere else.  Not part of
the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  Each decision of the spec gets an `iff` over EVERY
outcome `o` — the positive half (what is admitted) and the negative half
(nothing else is) in one statement — and beside it the concrete mistake a
lying kernel could report, refuted on its own.  Both are closed by the
tactics of `Checks/Cases/Tactic.lean`: `sys_norm` reads the call off its
monad primitives and decides the closed gates, `sys_refute` is `sys_norm`
that must close the goal.

`set_tid_address_spec`'s ONE DECISION IS A MATCH, NOT A GATE, and that costs one step
`Checks/Cases/Kernel/Exit.lean`'s symbolic checks do not pay.  A gate over
a symbolic model survives `sys_simp_pass` as a readable `if`, which
`split` cases on; a MATCH on `m_tid m` does not, because the register
carries `m_tid.eq_1` and the first pass would open the getter into a
projection chain the hypothesis `m_tid m = none` no longer rewrites.  So
each check hands the arm it is about to `simp only` FIRST, with the
spec's own unfolding and the reading of `get_model` and nothing else, and
`sys_norm` reads what the match reduces to.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! The spec's unfolding.  The line lives here rather than in
`Checks/Cases/Tactic.lean`'s register on purpose: a port PR creates its
own files and edits no shared one, so that ports merge in any order
(docs/merge-commutativity.md).  `Checks/Cases/Kernel/Sys.lean` imports
this module for exactly this line, since `getpid_spec` and `gettid_spec`
ARE `set_tid_address_spec`; any other Cases module pinning through arm 96
does the same or registers the line itself. -/
attribute [sys_simp low] set_tid_address_spec.eq_1

/-! ## The envelope the model draws from

`PID_MAX_ENVELOPE` is the EXCLUSIVE upper bound.  The pins below spell it
as the numeral 4194304 so a reader sees the register value a kernel could
answer, and the boundary checks on either side of it are what make the
exclusivity observable.  Why the model's bound is `2^22` — the two arms of
`PID_MAX_LIMIT` and the five writes every `pid_max` passes through — is
argued on the definition in `Sys/Kernel/Fork.lean`, with its citations,
and is not a claim any pin here can carry: `PID_MAX_LIMIT` is a
conditional expression over `CONFIG_BASE_SMALL` and `PAGE_SIZE`, not a
literal, so the evidence checker cannot evaluate it and no header spells
4194304. -/

/-- The model's envelope end at a numeral: `2^22`.
model: the model's own constant at a numeral; the kernel reading behind it is on `Sys/Kernel/Fork.lean`'s `PID_MAX_ENVELOPE` -/
example : PID_MAX_ENVELOPE = 4194304 := by decide

/-! ## The first call: the draw

`set_tid_address` has no error path and validates no argument
(`SYSCALL_DEFINE1(set_tid_address, int __user *, tidptr)`,
kernel/fork.c:1747-1752, Linux v6.18.46), so the only question a check can
ask of the first call is which tids it may answer. -/

/-- The whole first call, for every outcome: some tid strictly inside the
envelope, returned in a0, recorded in `m_tid`, with no memory written, no
memory zeroed and no event emitted.  The tid is the ENVIRONMENT's, so the
statement is existential: the model commits to the envelope and to nothing
narrower.  The lower end is `alloc_pid`'s `int pid_min = 1`
(kernel/pid.c:226) and its own `tid < 1` rejection (kernel/pid.c:199); the
upper end is `idr_alloc_cyclic`'s exclusive `end` (lib/idr.c:102) applied
to a `pid_max` clamped to `PID_MAX_LIMIT` (`include/linux/threads.h`), the
constant `2^22` bounds.
rocq-twin: set_tid_address_first_choice_is_within_modeled_envelope
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem set_tid_address_first_call_draws_a_live_tid (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (o : outcome SyscallEffect) :
    set_tid_address_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_norm

/-- tid 1 is admitted: `pid_min` starts at 1 because "init really needs
pid 1" (kernel/pid.c:226-230, Linux v6.18.46), and init really holds it.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_may_draw_one (i : SyscallInput) (m : Model) (h : m_tid m = none) :
    set_tid_address_spec i m (Ok (mkEffect 1 [] []) (with_tid 1 m) []) :=
  (set_tid_address_first_call_draws_a_live_tid i m h _).mpr ⟨1, rfl, by decide, by decide⟩

/-- ...and so is `2^22 - 1`, the largest tid the exclusive `end` leaves:
`idr_alloc_cyclic(&tmp->idr, NULL, pid_min, pid_max, GFP_ATOMIC)`
(kernel/pid.c:238-239, Linux v6.18.46) with `@end: The maximum ID
(exclusive)` (lib/idr.c:102) allocates up to `pid_max - 1`, and a fresh
pid namespace's `pid_max` IS `PID_MAX_LIMIT` (`create_pid_namespace`,
kernel/pid_namespace.c:110), so this is a tid a real kernel hands out, not
only the edge of an over-approximation.
kernel: kernel/pid.c:alloc_pid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem set_tid_address_may_draw_the_envelope_top (i : SyscallInput) (m : Model)
    (h : m_tid m = none) :
    set_tid_address_spec i m (Ok (mkEffect 4194303 [] []) (with_tid 4194303 m) []) :=
  (set_tid_address_first_call_draws_a_live_tid i m h _).mpr ⟨4194303, rfl, by decide, by decide⟩

/-- A kernel answering tid 0 is lying.  `alloc_pid` allocates from
`pid_min`, initialised to 1 and only ever raised (kernel/pid.c:226-232,
Linux v6.18.46), the requested-tid path of the same function spells the
predicate out as `if (tid < 1 || tid >= pid_max)` (kernel/pid.c:199), and
the two `nr = 0` defaults between that allocation and `task_pid_vnr`'s
answer cannot fire for `current` (the chain is on `PID_MAX_ENVELOPE`'s
docstring).  This is the one over-approximation the model must not make,
and the reason is the Rocq definition's, read there from musl 1.2.6,
`src/exit/exit.c`, `exit`: `int prev = a_cas(exit_lock, 0, tid); if (prev
== tid) a_crash();` — a tid of 0 makes the first ORDINARY `exit`
indistinguishable from a recursive one and crash before `exit_group`
(issue #246).
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_zero_tid_rejected (i : SyscallInput) (m : Model)
    (h : m_tid m = none) :
    ¬ set_tid_address_spec i m (Ok (mkEffect 0 [] []) (with_tid 0 m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- ...and so is one answering `2^22` itself.  `idr_alloc_cyclic`'s `end`
is EXCLUSIVE (lib/idr.c:102, Linux v6.18.46), so `pid_max` is never
allocated, and no namespace's `pid_max` exceeds `pid_max_max =
PID_MAX_LIMIT` (kernel/pid.c:65; the five writes are on
`PID_MAX_ENVELOPE`'s docstring, two of them the clamps at kernel/pid.c:773
and kernel/pid.c:805; the constant itself is `include/linux/threads.h`'s).
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:register_pidns_sysctls,pid_idr_init@v6.18.46 -/
theorem set_tid_address_envelope_end_rejected (i : SyscallInput) (m : Model)
    (h : m_tid m = none) :
    ¬ set_tid_address_spec i m (Ok (mkEffect 4194304 [] []) (with_tid 4194304 m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- A kernel reporting an errno on the first call is lying: there is no
error path to take.  `-EINVAL` is what `alloc_pid` answers for a bad
REQUESTED tid (kernel/pid.c:198-200, Linux v6.18.46), and `set_tid_address`
requests none.  The refutation needs only the envelope: `errno_ret EINVAL`
is `2^64 - 22`, which no tid the draw admits can be, whatever post-model
the lie comes with.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_first_call_never_answers_an_errno (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (m' : Model) :
    ¬ set_tid_address_spec i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' []) := by
  intro hspec
  obtain ⟨x, ho, -, hhi⟩ := (set_tid_address_first_call_draws_a_live_tid i m h _).mp hspec
  cases ho
  exact absurd hhi (by decide)

/-- THE CALL WRITES NO USER MEMORY, whatever `tidptr` holds.  The body is
two statements (kernel/fork.c:1749-1751, Linux v6.18.46): the pointer is
STORED in `current->clear_child_tid` and never dereferenced, so no byte
moves at the call, and a kernel reporting one written here is lying.  The
write THROUGH the pointer is a different event — `put_user(0,
tsk->clear_child_tid)` in `mm_release` (kernel/fork.c:1442), reached only
from `exit_mm_release` (kernel/fork.c:1457) and `exec_mm_release`
(kernel/fork.c:1463) at this task's own exit or exec, beside a
`do_futex(…, FUTEX_WAKE, …)` (kernel/fork.c:1443-1444) under the same
`atomic_read(&mm->mm_users) > 1` guard (kernel/fork.c:1437) — and whether
THAT write is ever admitted is the exit and exec arms' question, not this
one's.  The argument that it is not (this model admits no second holder
of an mm) is a claim about the model, so it sits on the spec's docstring
and not under a kernel citation here.
kernel: kernel/fork.c:set_tid_address,mm_release,exit_mm_release,exec_mm_release@v6.18.46 -/
theorem set_tid_address_writes_no_user_memory (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid tidptr : word) (b : byte) :
    ¬ set_tid_address_spec i m (Ok (mkEffect tid [(tidptr, [b])] []) (with_tid tid m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-! `mkEffect` fixes the unmap, copy and copy-in ledgers to empty by
construction, so a refutation of a lie in one of them has to spell the
full constructor.  The four below do, one per ledger `mkEffect` hides
plus the zeros ledger it exposes, so that every field of the effect has a
named lie beside the `iff` that refuses them all at once. -/

/-- ...nor does it zero a range: the same two statements move no byte in
any direction.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_zeroes_no_user_memory (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid tidptr n : word) :
    ¬ set_tid_address_spec i m
        (Ok (SyscallEffect.mkEffectU tid [] [(tidptr, n)] [] [] []) (with_tid tid m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- ...nor unmap one: nothing in `kernel/fork.c`'s two statements touches
the address space.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_unmaps_nothing (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid tidptr n : word) :
    ¬ set_tid_address_spec i m
        (Ok (SyscallEffect.mkEffectU tid [] [] [(tidptr, n)] [] []) (with_tid tid m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- ...nor copy memory to memory.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_copies_nothing (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid src dst n : word) :
    ¬ set_tid_address_spec i m
        (Ok (SyscallEffect.mkEffectU tid [] [] [] [MemCopy.mkCopy src dst n] []) (with_tid tid m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- ...nor READ the word `tidptr` points at.  `int __user *tidptr` is a
pointer STORED (kernel/fork.c:1749, Linux v6.18.46), not a value fetched:
no `get_user` or `copy_from_user` runs, so a copy-in ledger naming the four
bytes at `tidptr` — the mistake the signature invites — is a lie.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_copies_in_nothing (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid tidptr : word) :
    ¬ set_tid_address_spec i m
        (Ok (with_copyins [(tidptr, 4)] (mkEffect tid [] [])) (with_tid tid m) []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-- Whatever tid the first call answers, the post-model is the one that
RECORDS it.  `task_pid_vnr(current)` (kernel/fork.c:1751, Linux v6.18.46)
reads a value the task already holds and that nothing changes while it
stays its own thread-group leader (the condition, and the two arms that
would reopen it, are on the spec's docstring), so a model that answered a
tid without recording it could answer a different one next time.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_first_call_records_the_answer (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid : word) (m' : Model) (evs : List event)
    (hspec : set_tid_address_spec i m (Ok (mkEffect tid [] []) m' evs)) :
    m' = with_tid tid m := by
  obtain ⟨x, ho, -, -⟩ := (set_tid_address_first_call_draws_a_live_tid i m h _).mp hspec
  cases ho
  rfl

/-- So a kernel reporting the answer with `m_tid` still unset is refused.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_first_call_must_record (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (tid : word) :
    ¬ set_tid_address_spec i m (Ok (mkEffect tid [] []) m []) := by
  intro hspec
  have hm : m_tid m = m_tid (with_tid tid m) :=
    congrArg m_tid (set_tid_address_first_call_records_the_answer i m h tid m [] hspec)
  have hs : m_tid (with_tid tid m) = some tid := rfl
  rw [h, hs] at hm
  cases hm

/-! ## Every later call: the recorded answer

A task that stays its own thread-group leader keeps its pid for life —
the condition is on the spec's docstring, with what would reopen it — so
the second and every later call repeats the first one's answer. -/

/-- The whole call once `m_tid` holds a tid: that tid, the model
untouched, no write, no event.  `task_pid_vnr(current)`
(kernel/fork.c:1751, Linux v6.18.46) is `__task_pid_nr_ns(tsk,
PIDTYPE_PID, NULL)` (include/linux/pid.h:244-247): the task's pid as seen
from the CALLER's active pid namespace — the `NULL` becomes
`task_active_pid_ns(current)` at kernel/pid.c:516-517, which for `current`
is its own — so the same task asks the same question each call.  The pid
it reads moves only through `exchange_tids` (kernel/pid.c:384-403), which
`de_thread` runs at fs/exec.c:995 when a NON-leader thread execs; a
single-task model whose `clone` arm declines `CLONE_THREAD`
(`clone_fork_flags_b`) has no such thread; what would reopen this is an
arm admitting a thread-creating word, which `Sys/Kernel/Fork.lean` refuses
by design.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_repeats_the_recorded_tid (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (o : outcome SyscallEffect) :
    set_tid_address_spec i m o ↔ o = Ok (mkEffect tid [] []) m [] := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_norm

/-- The `iff` above read as a forcing statement: the shape the three
refutations below project a field out of, which `sys_norm` cannot do on a
symbolic model.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_later_call_moves_nothing (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hspec : set_tid_address_spec i m (Ok eff m' evs)) :
    eff = mkEffect tid [] [] ∧ m' = m ∧ evs = [] := by
  have ho := (set_tid_address_repeats_the_recorded_tid i m tid h _).mp hspec
  cases ho
  exact ⟨rfl, rfl, rfl⟩

/-- A kernel answering a DIFFERENT tid on a later call is lying: nothing
`set_tid_address` does allocates or changes a pid — `alloc_pid`
(kernel/pid.c) is reached from `copy_process`, not from here.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_second_call_cannot_change_the_tid (i : SyscallInput) (m : Model)
    (tid tid' : word) (h : m_tid m = some tid) (hne : tid' ≠ tid) :
    ¬ set_tid_address_spec i m (Ok (mkEffect tid' [] []) m []) := by
  intro hspec
  have he := (set_tid_address_later_call_moves_nothing i m tid h _ _ _ hspec).1
  exact hne (congrArg SyscallEffect.eff_ret he)

/-- ...and one that re-records is lying too.  The first call's draw is the
task's pid for as long as it is its own thread-group leader (the spec's
docstring has the condition), and what a later `set_tid_address`
overwrites is `current->clear_child_tid` (kernel/fork.c:1749, Linux
v6.18.46), which no arm of THIS TABLE reads back.  The call that does,
`prctl(PR_GET_TID_ADDRESS)` — `prctl_get_tid_address`
(kernel/sys.c:2336-2339), compiled under `CONFIG_CHECKPOINT_RESTORE`, the
case at kernel/sys.c:2676 — has no Lean arm, and Rocq's
`Kernel.Sys.prctl_spec` answers only `PR_CAPBSET_READ` and declines every
other option.  So no later call moves state this model carries.  This
stops being true when a `PR_GET_TID_ADDRESS` arm lands: the field would
then have to be carried.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_second_call_records_nothing (i : SyscallInput) (m : Model)
    (tid tid' : word) (h : m_tid m = some tid) (hne : tid' ≠ tid) :
    ¬ set_tid_address_spec i m (Ok (mkEffect tid [] []) (with_tid tid' m) []) := by
  intro hspec
  have hm := (set_tid_address_later_call_moves_nothing i m tid h _ _ _ hspec).2.1
  have hs : some tid' = m_tid m := congrArg m_tid hm
  rw [h] at hs
  exact hne (Option.some.inj hs)

/-- ...and one that reads the four bytes at `tidptr` on a later call is
lying for the same reason as on the first: the pointer is stored, never
fetched (kernel/fork.c:1749, Linux v6.18.46).
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_later_call_copies_in_nothing (i : SyscallInput) (m : Model)
    (tid tidptr : word) (h : m_tid m = some tid) :
    ¬ set_tid_address_spec i m (Ok (with_copyins [(tidptr, 4)] (mkEffect tid [] [])) m []) := by
  simp only [set_tid_address_spec.eq_1, bind_get_model_iff, h]
  sys_refute

/-! ## The call is total

`set_tid_address` has no error path at all: its body is an assignment and
a return (kernel/fork.c:1747-1752, Linux v6.18.46). -/

/-- The call never leaves the modeled surface, whichever arm it takes.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_never_declines (i : SyscallInput) (m : Model) :
    ¬ set_tid_address_spec i m Unmodeled := by
  cases h : m_tid m with
  | none =>
      intro hspec
      obtain ⟨_, ho, _⟩ := (set_tid_address_first_call_draws_a_live_tid i m h _).mp hspec
      cases ho
  | some tid =>
      intro hspec
      have ho := (set_tid_address_repeats_the_recorded_tid i m tid h _).mp hspec
      cases ho

/-- A kernel reporting an errno on a later call is lying: there is no
error path to take.  `-EINVAL` is what `alloc_pid` returns for a bad
REQUESTED tid (kernel/pid.c:198-200, Linux v6.18.46), and `set_tid_address`
requests none.  The refutation needs only that `errno_ret EINVAL` is
`2^64 - 22`, which no tid inside `PID_MAX_ENVELOPE` can be.  The
hypothesis `henv` is the reachability fact no lemma in the tree states:
the only writer of `m_tid` is the first call, which draws inside the
envelope.  For a model outside it (`m_tid = some (2^40)`, well-typed and
unreachable) the spec really does answer the recorded value, so the pin is
stated on the models a run can be in and on no others.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_never_answers_an_errno (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (henv : bv_unsigned tid < PID_MAX_ENVELOPE) :
    ¬ set_tid_address_spec i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  intro hspec
  have he := (set_tid_address_later_call_moves_nothing i m tid h _ _ _ hspec).1
  have heq : errno_ret EINVAL = tid := congrArg SyscallEffect.eff_ret he
  rw [← heq] at henv
  exact absurd henv (by decide)

/-! ## Through the dispatcher

`set_tid_address` is `SYSCALL_DEFINE1` and DOES take an argument; the arm
hands the spec the whole input and the spec reads none of it, which is why
the pin below quantifies over every input numbered 96 and fixes no
argument. -/

/-- Syscall 96 reaches the draw: the whole first call, through the table.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem dispatch_96_draws_a_live_tid (i : SyscallInput) (m : Model)
    (hno : bv_unsigned i.in_sysno = 96) (h : m_tid m = none) (o : outcome SyscallEffect) :
    syscall_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 := by
  unfold syscall_spec dispatch
  rw [hno]
  exact set_tid_address_first_call_draws_a_live_tid i m h o

/-! ## `clone` (220) and `clone3` (435): the caller's answer, read off against Linux

Worked examples over `Sys.Kernel.Fork.clone_spec` and
`Sys.Kernel.Fork.clone3_spec`.  Rocq keeps no worked-cases file for these
arms: its statements are over the executable checker in
`Checks/ProcessCreation.v` (`clone_never_returns_zero`,
`clone3_never_returns_zero`, `clone_open_file_unmodeled`,
`clone_resolve_declines_or_sets_children`, `clone_checker_admits_a_pid`
and its companions) and in `Checks/Sys/Kernel/Fork.v`
(`clone_pid_not_errno`), so the pins below mirror no Rocq source and each
carries its own kernel citation.  Every kernel line was read at Linux
v6.18.46 (commit 1f99e9ab748f).

THE ORDER THE KERNEL DECIDES IN, which is the order of the sections below:

1. THE FLAG WORD.  `clone`, `SYSCALL_DEFINE5(clone, ...)` (kernel/fork.c:2720-2753),
   splits `lower_32_bits(clone_flags)` at `CSIGNAL` before anything is
   copied; the model answers the one word `SIGCHLD` (17) and declines every
   other, INCLUDING the words the kernel would read as 17 after discarding
   the high half, so a decline here is a modeled-surface decline and not an
   empty intersection: Linux answers these calls.
2. THE DESCRIPTOR TABLE.  `copy_files` (kernel/fork.c:1579-1607, Linux v6.18.46), called
   at :2173 inside `copy_process`, hands the child second references to the same
   `struct file`s (`dup_fd`, fs/file.c:383, Linux v6.18.46); the model declines a call
   made with a descriptor whose shared state it inlines.  Again the kernel
   answers; the model cannot represent the answer's consequences.
3. THE RESOLUTION.  `copy_process` (kernel/fork.c:1934, Linux v6.18.46) either fails
   with one of four errnos this flag word can reach, or creates a task
   whose pid `kernel_clone` returns (:2624, :2654).  The pid is drawn by
   `alloc_pid` (kernel/pid.c:163, Linux v6.18.46) from `[1, pid_max)`, and 0 — the
   CHILD's return (arch/riscv/kernel/process.c:255, Linux v6.18.46) — is never the parent's.
4. THE RECORDED CHILD.  A created task is linked onto `current->children`
   (kernel/fork.c:2398, Linux v6.18.46), which is what `__do_wait` (kernel/exit.c:1675-1710, Linux v6.18.46)
   walks; the model records that with `State.with_children` on the pid arm
   and on the pid arm only.
5. `clone3`: `copy_clone_args_from_user` (kernel/fork.c:2756, Linux v6.18.46) gates
   `size` before it copies, `copy_struct_from_user`
   (include/linux/uaccess.h:389-411, Linux v6.18.46) reads the whole struct or fails,
   `clone3_args_valid` (:2853-2879) judges the image, and `kernel_clone`
   (:2913) runs the same resolution — with the read on the ledger.

HOW A SYMBOLIC MODEL IS HANDLED.  The descriptor gate over a symbolic `m`
survives `sys_simp_pass` as an `if`, exactly as `Checks/Cases/Kernel/Exit.lean`'s
children gate does; the reading lemma `clone_resolve_reading` below
discharges it from a hypothesis on the table, and the symbolic pins go
through that lemma.  The `choose` guard `clone_pid_ok_b m pid = true` is a
Bool over a symbolic pid that no pass can decide; `clone_pid_ok_b_demo`
spells it out on the demo process so a pin can state the envelope in
numerals.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

/-! The clone specs' unfoldings, and `record_copyins`'s.  `Checks/Cases/Tactic.lean`'s
register is where these lines are owed; this ticket leaves that file
untouched, so they sit here until the register's next edit takes them.
`record_copyins reads spec` is `bind spec (fun eff => pure …)`; its
equation is already registered from `Checks/Cases/Kernel/Sched/Syscalls.lean`, and
`Checks/Cases/Fs/Stat.lean` and `Checks/Cases/Fs/Namei.lean` unfold it
through a `local sys_simp low` line, so the line here is a third copy of one
the register owes once; `bind_pure_iff` then reads it.  `clone_errnos` is unfolded so the
`errno_from` reading's membership becomes the four-way disjunction the pins
state; the gates (`clone_fork_flags_b`, `clone_no_shared_file_b`,
`clone_pid_ok_b`, `clone3_fork_args_b`) are decided, never unfolded. -/
attribute [sys_simp low] clone_spec.eq_1 clone_resolve.eq_1 clone_errnos.eq_1
  clone3_spec.eq_1 clone3_resolve.eq_1 record_copyins.eq_1

/-! ### The numbers these checks spell out -/

/-- `SIGCHLD` is 17, the numbering riscv64 takes from asm-generic.
kernel: include/uapi/asm-generic/signal.h:SIGCHLD@v6.18.46 -/
example : SIGCHLD = 17 := by decide
/-- `sizeof(struct clone_args)` is 88.  The kernel reading — `CLONE_ARGS_SIZE_VER2`
and the `BUILD_BUG_ON` that pins the struct to it — is on `Sys/Kernel/Fork.lean`'s
`CLONE_ARGS_SIZE`; a macro is not a function the evidence checker can hold a
model constant against, so this pin is marked as the model's own numeral.
model: the model's own constant at a numeral; the kernel reading behind it is on `Sys/Kernel/Fork.lean`'s `CLONE_ARGS_SIZE` -/
example : CLONE_ARGS_SIZE = 88 := by decide
/-- …and the ledger length agrees with it.
model: the model's own `Nat` mirror of `CLONE_ARGS_SIZE`, pinned by `clone_args_size_nat_ok` -/
example : CLONE_ARGS_SIZE_nat = 88 := by decide
/-- `EAGAIN` is 11.
kernel: include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
example : EAGAIN = 11 := by decide
/-- `ENOMEM` is 12.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
example : ENOMEM = 12 := by decide
/-- `EACCES` is 13.
kernel: include/uapi/asm-generic/errno-base.h:EACCES@v6.18.46 -/
example : EACCES = 13 := by decide
/-- `EMFILE` is 24, and `ENFILE`, the neighbour a refutation below names, is 23.
kernel: include/uapi/asm-generic/errno-base.h:EMFILE,ENFILE@v6.18.46 -/
example : EMFILE = 24 ∧ ENFILE = 23 := by decide

/-! ### Two readings of the gates on a concrete process

`clone_pid_ok_b` is a Bool over a symbolic pid; on the demo process, whose
tid is unobserved, it is the envelope alone.  With a tid recorded it also
excludes that tid.  Both are model computations, kept so the pins can state
the envelope in numerals. -/

/-- The pid guard on the demo process: the envelope `(0, 2^22)`, the tid
conjunct vacuous because `m_tid demo_model = none`.  The envelope is
`alloc_pid`'s: `pid_min = 1` (kernel/pid.c:226, Linux v6.18.46) below and
`idr_alloc_cyclic`'s exclusive `end` at a `pid_max` no larger than
`PID_MAX_LIMIT` above (lib/idr.c:102, Linux v6.18.46).
kernel: kernel/pid.c:alloc_pid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem clone_pid_ok_b_demo (p : word) :
    clone_pid_ok_b demo_model p = true ↔ (0 < bv_unsigned p ∧ bv_unsigned p < 4194304) := by
  simp only [clone_pid_ok_b, m_tid_demo_model, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [PID_MAX_ENVELOPE, Int.reducePow]

/-- The pid guard once a tid is recorded: the envelope, and not that tid —
`alloc_pid` hands out a FREE pid (kernel/pid.c:238-239, Linux v6.18.46),
and the caller's own is in use.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_pid_ok_b_with_tid (t p : word) (m : Model) :
    clone_pid_ok_b (with_tid t m) p = true ↔
      ((0 < bv_unsigned p ∧ bv_unsigned p < 4194304) ∧ p ≠ t) := by
  have ht : m_tid (with_tid t m) = some t := rfl
  simp only [clone_pid_ok_b, ht, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, bv_eqb, beq_eq_false_iff_ne, ne_eq]
  simp only [PID_MAX_ENVELOPE, Int.reducePow]

/-- A guard that holds puts the pid strictly above 0: `pid_min = 1`
(kernel/pid.c:226, Linux v6.18.46).
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_pid_ok_b_pos (m : Model) (p : word) (h : clone_pid_ok_b m p = true) :
    0 < bv_unsigned p := by
  simp only [clone_pid_ok_b, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- …and strictly below `2^22`: `idr_alloc_cyclic`'s `end` is exclusive
(lib/idr.c:102, Linux v6.18.46) and `pid_max` is clamped to
`PID_MAX_LIMIT` (kernel/pid.c:65, :773, :805, Linux v6.18.46).
kernel: kernel/pid.c:alloc_pid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem clone_pid_ok_b_below (m : Model) (p : word) (h : clone_pid_ok_b m p = true) :
    bv_unsigned p < 4194304 := by
  simp only [clone_pid_ok_b, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PID_MAX_ENVELOPE, Int.reducePow] at h
  exact h.1.2

/-- No admitted errno encodes 0: each is `2^64 - e` for `e ∈ {11, 12, 24, 13}`.
kernel: include/uapi/asm-generic/errno-base.h:EAGAIN,ENOMEM,EMFILE,EACCES@v6.18.46 -/
theorem clone_errno_ret_nonzero (e : Int) (he : e ∈ clone_errnos) : errno_ret e ≠ 0 := by
  simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

/-- No admitted pid encodes an admitted errno: every pid is below `2^22`
and every errno of the list reads as an unsigned value above `2^64 - 25`.
What `Checks/Sys/Kernel/Fork.v`'s `clone_pid_not_errno` says of the checker.
kernel: kernel/pid.c:alloc_pid; include/uapi/asm-generic/errno-base.h:EAGAIN,ENOMEM,EMFILE,EACCES@v6.18.46 -/
theorem clone_pid_not_errno (m : Model) (p : word) (h : clone_pid_ok_b m p = true) (e : Int)
    (he : e ∈ clone_errnos) : p ≠ errno_ret e := by
  have hb := clone_pid_ok_b_below m p h
  simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
  intro hp
  rw [hp] at hb
  rcases he with rfl | rfl | rfl | rfl <;> exact absurd hb (by decide)

/-! ### The resolution, read on any model the descriptor gate lets through -/

/-- What `clone_resolve` admits once the table passes the gate: an errno of
the list with the model untouched, or a guarded pid with the child
recorded.  The reading every symbolic pin below goes through: the two
arms of `kernel_clone`'s return (kernel/fork.c:2611-2615, :2624, :2654,
Linux v6.18.46) once `copy_files` has copied the table (:2173).
kernel: kernel/fork.c:kernel_clone,copy_process,copy_files@v6.18.46 -/
theorem clone_resolve_reading (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    clone_resolve i m o ↔
      (∃ e, e ∈ clone_errnos ∧ o = Ok (mkEffect (errno_ret e) [] []) m [])
      ∨ ∃ pid, o = Ok (mkEffect pid [] []) (with_children m) [] ∧ clone_pid_ok_b m pid = true := by
  simp only [clone_resolve.eq_1, bind_get_model_iff, hg, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, alt_iff, bind_errno_from_iff, bind_choose_outcome_iff, bind_modify_iff,
    err_ret.eq_1, ret_only.eq_1, pure_iff]

/-- …and what it does when the gate is closed: it declines, whatever the
outcome asked about — the shared `struct file` `copy_files` hands the
child (kernel/fork.c:1579-1607, Linux v6.18.46) is what the model cannot
represent.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_resolve_gate_closed (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hg : clone_no_shared_file_b (m_fds m) = false) :
    clone_resolve i m o ↔ o = Unmodeled := by
  simp only [clone_resolve.eq_1, bind_get_model_iff, hg, Bool.not_false, ↓reduceIte, unmodeled_iff]

/-! ### 1. The flag word: `SYSCALL_DEFINE5(clone, …)` → `kernel_clone`

`SYSCALL_DEFINE5(clone, unsigned long, clone_flags, unsigned long, newsp,
int __user *, parent_tidptr, unsigned long, tls, int __user *,
child_tidptr)` (kernel/fork.c:2720-2723, Linux v6.18.46, the `CLONE_BACKWARDS` prototype
riscv64 selects, arch/riscv/Kconfig:97, Linux v6.18.46) builds `.flags =
lower_32_bits(clone_flags) & ~CSIGNAL` and `.exit_signal =
lower_32_bits(clone_flags) & CSIGNAL` (:2743, :2747) and hands them to
`kernel_clone` (:2752).  The model's gate is the whole register equal to
17.  Every decline in this section is a call Linux ANSWERS — a plain fork
under another exit signal, a thread, a vfork — declined because the model
holds no child and no thread; none is an empty intersection. -/

/-- The whole call for the admitted word, over every outcome: one of the
four errnos with the model untouched, or a pid strictly inside `(0, 2^22)`
with the child recorded — no write, no zero-fill, no event, no decline.
The errnos are the error returns of `copy_process` this word can reach:
-EAGAIN at the `RLIMIT_NPROC` and `max_threads` ceilings (kernel/fork.c:2058-2073, Linux v6.18.46)
and `alloc_pid`'s -ENOSPC remap (kernel/pid.c:245, Linux v6.18.46), -ENOMEM at every
allocation on the path (:2019-2021 and the `copy_*` helpers), -EMFILE from
`alloc_fdtable` (fs/file.c:194-197, :212-213, Linux v6.18.46) under `dup_fd`, and -EACCES
from SELinux's `avc_denied` (security/selinux/avc.c:995-1005, Linux v6.18.46); the pid is
`pid_vnr` of the task created (:2624, :2654), drawn by `alloc_pid` above 0
and below `pid_max`.
kernel: kernel/fork.c:clone,kernel_clone,copy_process; kernel/pid.c:alloc_pid; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem clone_fork_answers (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EACCES) [] []) demo_model [])
      ∨ ∃ pid : word, o = Ok (mkEffect pid [] []) (with_children demo_model) []
          ∧ 0 < bv_unsigned pid ∧ bv_unsigned pid < 4194304) := by
  have hg : clone_no_shared_file_b (m_fds demo_model) = true := by decide
  have hf : clone_fork_flags_b 17 = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte, clone_resolve_reading i demo_model o hg,
    clone_pid_ok_b_demo, clone_errnos, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]

/-- The word the kernel reads as a plain fork after `lower_32_bits`
(kernel/fork.c:2743, :2747, Linux v6.18.46), `0x1_00000011`, is DECLINED: the model tests
the whole register.  Linux answers this call exactly as it answers 17, so
the decline is the model's strictness and not an empty intersection; it
costs nothing observed because musl's `_Fork` passes the literal `SIGCHLD`.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x100000011 -- clone -/
theorem clone_high_bits_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 4294967313 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A flag word of 0 — no exit signal at all, the kernel's legal
no-signal fork (`kernel_clone` reports `PTRACE_EVENT_CLONE` for it,
kernel/fork.c:2602-2605, Linux v6.18.46) — declines: the allowlist is the one word.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0 -- clone -/
theorem clone_no_signal_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The signal numbers either side of `SIGCHLD` — `SIGSTKFLT` (16) and
`SIGCONT` (18) — decline: a fork reporting another signal is not the fork
this model answers.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x10 -- clone -/
theorem clone_sigstkflt_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 16 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …and the one above.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x12 -- clone -/
theorem clone_sigcont_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 18 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_VM` (0x111): a child sharing the parent's address
space, which `copy_mm` (kernel/fork.c:1543-1545, Linux v6.18.46) hands out by reference
instead of `dup_mm`.  Linux accepts it; the model declines, because every
claim about the parent's memory would be void with a second writer in it.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x111 -- clone -/
theorem clone_vm_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 273 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_FILES` (0x411): a shared descriptor table
(`copy_files`'s `atomic_inc(&oldf->count)`, kernel/fork.c:1596-1598, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x411 -- clone -/
theorem clone_files_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 1041 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_PARENT_SETTID` (0x100011): the one word whose success
WRITES the parent's memory (`put_user(nr, args->parent_tid)`,
kernel/fork.c:2626-2627, Linux v6.18.46).  Declined, so the admitted arm carries no write.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x100011 -- clone -/
theorem clone_parent_settid_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 1048593 i m o ↔ o = Unmodeled := by
  sys_norm

/-- musl's `pthread_create` word (0x7d0f00): a THREAD, which Linux creates
and answers with a tid, and which this model cannot represent — a second
task in the address space is not a configuration it has.  Declined rather
than answered -EAGAIN: the errno would make the model REJECT the run in
which the kernel really created the thread, a false claim about Linux
(the argument on Rocq's `Kernel.Fork.clone_fork_flags_b`).
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x7d0f00 -- clone -/
theorem clone_pthread_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 8195840 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …and glibc's, the same set without `CLONE_DETACHED` (0x3d0f00).
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x3d0f00 -- clone -/
theorem clone_glibc_thread_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 4001536 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLONE_SIGHAND` alone (0x800), the word the probe's base mode really
issues: Linux answers -EINVAL before allocating anything (`copy_process`,
kernel/fork.c:1969-1970, Linux v6.18.46, `CLONE_SIGHAND` without `CLONE_VM`), an errno
outside `clone_errnos`; the model declines the word instead.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone -- clone -/
theorem clone_sighand_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 2048 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_VFORK` (0x4011): `kernel_clone` puts the parent to
sleep until the child execs or exits (kernel/fork.c:2649, Linux v6.18.46, the
wait_for_vfork_done call) — a wait this model cannot place.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x4011 -- clone -/
theorem clone_vfork_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 16401 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_FS` (0x211): a shared `fs_struct`, so the child's
`chdir` would move this process's `AT_FDCWD`.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x211 -- clone -/
theorem clone_fs_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 529 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `SIGCHLD | CLONE_PIDFD` (0x1011): a new descriptor in the PARENT's
table, which `copy_process` prepares (kernel/fork.c:2222, Linux v6.18.46, the
pidfd_prepare call) — an effect on this process the word's answer does not
name.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x1011 -- clone -/
theorem clone_pidfd_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 4113 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The gate, quantified: EVERY register value other than 17 is declined.
The sampled words above show the shape; this is the statement that a gate
admitting a second word — `bv_eqb flags 17 || bv_eqb flags 0x1011`, say —
cannot pass, since each sampled pin alone is blind to every word it does
not name.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_other_word_declines (flags : word) (hf : flags ≠ 17) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    clone_spec flags i m o ↔ o = Unmodeled := by
  have h17 : Z_to_bv 64 SIGCHLD = (17 : word) := by decide
  have hg : clone_fork_flags_b flags = false := by
    unfold clone_fork_flags_b
    rw [h17]
    exact Bool.eq_false_iff.mpr (fun h => hf ((bv_eqb_eq flags 17).mp h))
  simp only [clone_spec.eq_1, hg, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-- glibc's `fork` word, `CLONE_CHILD_SETTID | CLONE_CHILD_CLEARTID | SIGCHLD`
(0x1200011): a plain fork to Linux, declined here — one of its bits is
`CLONE_CHILD_CLEARTID`, which arms a write in the CHILD (`p->clear_child_tid`,
kernel/fork.c:2044).  So a glibc-linked program fails closed at its fork
rather than being answered.
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_glibc_fork_word_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone_spec 18874385 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The flag gate PRECEDES the resolution: a pid under a declined word is
not admitted, whatever the table holds.  The probe forks for real and
forges the word to `CLONE_VM | SIGCHLD` (0x111): the kernel created the
child and answered its pid; the model says nothing.
probe: testing/syscall-check/tests/clone_fork.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x111 -- fork -/
theorem clone_declined_word_pid_rejected (i : SyscallInput) :
    ¬ clone_spec 273 i demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) []) := by
  sys_refute

/-- …and a forged errno is not admitted either: -EAGAIN is real for the
thread word (`RLIMIT_NPROC`, kernel/fork.c:2058-2064), and the model still
says nothing rather than pick it.
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_declined_word_eagain_rejected (i : SyscallInput) :
    ¬ clone_spec 8195840 i demo_model (Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []) := by
  sys_refute

/-! ### The tables the descriptor-gate pins run on

Named here rather than spelled inline: a `fixture_of (fds := …)` inside a
statement puts a `:=` where `tools/check_lean_pins.py` and
`tools/check_lean_pin_evidence.py` cut the statement off, so the lints would
read a truncated theorem.  Each is the demo process with one more
descriptor at fd 3. -/

/-- fd 3 open on a regular file for reading.
model: a fixture, the demo process plus an `FdFile` at fd 3 -/
def open_file_model : Model := fixture_of (fds := (3, .FdFile [102] 0) :: init_fds)
/-- fd 3 open on a regular file for writing.
model: a fixture, the demo process plus an `FdFileW` at fd 3 -/
def open_wfile_model : Model := fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds)
/-- fd 3 a fresh socket.
model: a fixture, the demo process plus an `FdSocket` at fd 3 -/
def open_socket_model : Model := fixture_of (fds := (3, .FdSocket .SkFresh) :: init_fds)
/-- fd 3 the read end of a pipe.
model: a fixture, the demo process plus an `FdPipe` at fd 3 -/
def open_pipe_model : Model := fixture_of (fds := (3, .FdPipe 0 false) :: init_fds)
/-- fd 3 the WRITE end of a pipe.
model: a fixture, the demo process plus a writing `FdPipe` at fd 3 -/
def open_wpipe_model : Model := fixture_of (fds := (3, .FdPipe 0 true) :: init_fds)
/-- fd 3 a connected socket whose receive script has finished.
model: a fixture, the demo process plus a connected `FdSocket` at fd 3 -/
def open_connected_socket_model : Model :=
  fixture_of (fds := (3, .FdSocket (.SkConnected ⟨0x7f000001, 0x5000⟩ 0 NFin)) :: init_fds)
/-- fd 3 a socket its peer has reset.
model: a fixture, the demo process plus a reset `FdSocket` at fd 3 -/
def open_reset_socket_model : Model :=
  fixture_of (fds := (3, .FdSocket (.SkReset ⟨0x7f000001, 0x5000⟩ 0)) :: init_fds)
/-- fd 3 a fourth channel, `dup(1)`.
model: a fixture, the demo process plus an `FdChannel` at fd 3 -/
def open_channel_model : Model := fixture_of (fds := (3, .FdChannel 1) :: init_fds)
/-- fd 3 a directory.
model: a fixture, the demo process plus an `FdDir` at fd 3 -/
def open_dir_model : Model := fixture_of (fds := (3, .FdDir) :: init_fds)
/-- fd 3 /dev/null, read-write.
model: a fixture, the demo process plus an `FdDevNull` at fd 3 -/
def open_devnull_model : Model := fixture_of (fds := (3, .FdDevNull true true) :: init_fds)
/-- fd 3 /dev/urandom.
model: a fixture, the demo process plus an `FdUrandom` at fd 3 -/
def open_urandom_model : Model := fixture_of (fds := (3, .FdUrandom) :: init_fds)

/-! ### 2. The descriptor table

`copy_files` (kernel/fork.c:1579-1607, Linux v6.18.46) duplicates the table through `dup_fd`
(fs/file.c:383, Linux v6.18.46), whose loop takes a second reference to every open
`struct file` (`get_file(f)`, :458): the two tables share every
description, its `f_pos` included.  `State.FdEntry` inlines the offset of a
regular file and the receive script of a socket into the descriptor, so a
copied table would give the child private state where Linux gave it shared
state; the model declines instead.  The kernel answers every call in this
section, so these are modeled-surface declines, not empty intersections. -/

/-- A regular file open for reading closes the gate: its `f_pos` is
shared, and the model's `FdFile` carries the offset itself.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=17,ret=1234 -- openread -/
theorem clone_with_file_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_file_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and one open for writing.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=17,ret=1234 -- openfile -/
theorem clone_with_file_open_for_writing_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_wfile_model o ↔ o = Unmodeled := by
  sys_norm

/-- A socket closes it too: the entry inlines the connection's receive
script, and one connection cannot report a peer's reset once to each of
two processes: `sock_close` (net/socket.c:1454, Linux v6.18.46) reaches
`inet_release` (net/ipv4/af_inet.c:413, Linux v6.18.46) once per `struct
file`, which the two tables share.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_with_socket_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …in EVERY socket state, not only the fresh one: the gate matches
`FdSocket _`, so a connected socket — the state whose receive script the
argument above is about — closes it too.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_with_connected_socket_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_connected_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and a socket the peer has already reset.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_with_reset_socket_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_reset_socket_model o ↔ o = Unmodeled := by
  sys_norm

/-- A pipe end closes it: both references name one `pipe_inode_info`, and a
child's `close` of its copy does not drop the writer count `pipe_release`
keeps (fs/pipe.c:730-733) — the count `anon_pipe_read` reads to decide
between EOF and blocking (:370).
kernel: kernel/fork.c:copy_files; fs/pipe.c:pipe_release,anon_pipe_read@v6.18.46 -/
theorem clone_with_pipe_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_pipe_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the WRITE end just the same: the gate matches `FdPipe _ _`, both
ends, because the writer count `pipe_release` keeps is what the copy
would double.
kernel: kernel/fork.c:copy_files; fs/pipe.c:pipe_release,anon_pipe_read@v6.18.46 -/
theorem clone_with_pipe_write_end_open_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    clone_spec 17 i open_wpipe_model o ↔ o = Unmodeled := by
  sys_norm

/-- The descriptor gate precedes the errno alternative: with a file open
the model does not offer -EAGAIN either, although the kernel could answer
it (`RLIMIT_NPROC`, kernel/fork.c:2058-2064) — `copy_process` never gets
that far in the model.
kernel: kernel/fork.c:copy_process,copy_files@v6.18.46 -/
theorem clone_with_file_open_eagain_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i open_file_model (Ok (mkEffect (errno_ret EAGAIN) [] []) open_file_model []) := by
  sys_refute

/-- …nor a pid — the probe's read-only `FdFile`, the fixture's kind.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=17,ret=1234 -- openread -/
theorem clone_with_file_open_pid_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i open_file_model (Ok (mkEffect 1234 [] []) (with_children open_file_model) []) := by
  sys_refute

/-- A directory does NOT close the gate.  Its `f_pos` is shared on Linux
exactly as a file's is, but no modeled syscall can observe a directory
position, so there is no answer for the sharing to make wrong: the call is
answered as on the bare table.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 -- opendir -/
theorem clone_with_dir_open_answers_a_pid (i : SyscallInput) :
    clone_spec 17 i open_dir_model (Ok (mkEffect 1234 [] []) (with_children open_dir_model) []) := by
  sys_norm

/-- /dev/null does not close it either: `null_lseek` (drivers/char/mem.c:561)
pins the shared `f_pos` at 0 and `read_null`/`write_null` (:412-421) never
move it, so nothing shared can be observed.
kernel: drivers/char/mem.c:null_lseek,read_null,write_null@v6.18.46 -/
theorem clone_with_devnull_open_answers_a_pid (i : SyscallInput) :
    clone_spec 17 i open_devnull_model (Ok (mkEffect 1234 [] []) (with_children open_devnull_model) []) := by
  sys_norm

/-- Nor /dev/urandom: `urandom_fops` (drivers/char/random.c:1572-1581, Linux
v6.18.46) seats `noop_llseek` (fs/read_write.c:324, Linux v6.18.46) as its
`.llseek`, `urandom_read_iter` (drivers/char/random.c:1453, Linux v6.18.46)
reads no position, and the bytes come from the run's declared stream rather
than the file.
kernel: drivers/char/random.c:urandom_read_iter; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem clone_with_urandom_open_answers_a_pid (i : SyscallInput) :
    clone_spec 17 i open_urandom_model (Ok (mkEffect 1234 [] []) (with_children open_urandom_model) []) := by
  sys_norm

/-- …and none of the three passing kinds ever declines, which the three
admissions alone leave open: a spec admitting a pid AND `Unmodeled` on
these tables would pass them.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_with_dir_open_never_declines (i : SyscallInput) :
    ¬ clone_spec 17 i open_dir_model Unmodeled := by
  sys_refute

/-- …/dev/null.
kernel: drivers/char/mem.c:null_lseek,read_null,write_null@v6.18.46 -/
theorem clone_with_devnull_open_never_declines (i : SyscallInput) :
    ¬ clone_spec 17 i open_devnull_model Unmodeled := by
  sys_refute

/-- …/dev/urandom.
kernel: drivers/char/random.c:urandom_read_iter; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem clone_with_urandom_open_never_declines (i : SyscallInput) :
    ¬ clone_spec 17 i open_urandom_model Unmodeled := by
  sys_refute

/-- The three standard channels the demo process starts with do not close
the gate — the honest hole `Kernel.Fork.clone_no_shared_file_b` records: a
channel's position is the run's stream, not the descriptor's.  A file
CLOSED before the call is not in the table either.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 -- closedfile -/
theorem clone_with_channels_only_answers_a_pid (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) []) := by
  sys_norm

/-- A FOURTH channel, `dup(1)` at fd 3, does not close it either: the gate
is on the descriptor's KIND, and a `FdChannel` anywhere in the table is
the same hole as the three the process starts with.  `copy_files` copies
it like any other descriptor; nothing modeled can tell.
kernel: kernel/fork.c:copy_files@v6.18.46 -/
theorem clone_with_extra_channel_answers_a_pid (i : SyscallInput) :
    clone_spec 17 i open_channel_model
      (Ok (mkEffect 1234 [] []) (with_children open_channel_model) []) := by
  sys_norm

/-- The quantified form of the gate: whatever the flag word, a table the
gate closes on is declined.  What `Checks/ProcessCreation.v`'s
`clone_open_file_unmodeled` says.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_gate_closed_declines (flags : word) (i : SyscallInput) (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = false) : clone_spec flags i m Unmodeled := by
  unfold clone_spec
  by_cases hf : clone_fork_flags_b flags = true
  · simp only [hf, ↓reduceIte]
    exact (clone_resolve_gate_closed i m Unmodeled hg).mpr rfl
  · simp only [hf, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-! ### 3. The resolution: `copy_process` and `alloc_pid`

Once the gate passes, `kernel_clone` (kernel/fork.c:2611-2615, Linux v6.18.46) returns
either the error `copy_process` failed with or `pid_vnr(pid)` of the new
task (:2624, :2654).  The four errnos this word can reach, and why -EINVAL,
-EPERM, -EBUSY, -EFAULT, -ENOSPC, -EINTR and -ERESTARTNOINTR cannot, are
walked on `Sys/Kernel/Fork.lean`'s `clone_errnos`. -/

/-- -EAGAIN is admitted: `copy_process`'s `RLIMIT_NPROC` test and its
`nr_threads >= max_threads` ceiling (kernel/fork.c:2058-2073, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-EAGAIN -- clone -/
theorem clone_eagain_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []) := by
  sys_norm

/-- -ENOMEM is admitted: every allocation on the path, `dup_task_struct`
first (kernel/fork.c:2019-2021, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-ENOMEM -- clone -/
theorem clone_enomem_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []) := by
  sys_norm

/-- -EMFILE is admitted: `alloc_fdtable` under `dup_fd` against a lowered
`sysctl_nr_open` (fs/file.c:194-197, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-EMFILE -- clone -/
theorem clone_emfile_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []) := by
  sys_norm

/-- -EACCES is admitted: SELinux refusing `process:fork`
(`selinux_task_alloc`, security/selinux/hooks.c:4264-4273, Linux v6.18.46, calling
`avc_has_perm`, security/selinux/avc.c:1188, Linux v6.18.46, whose denial is
`avc_denied`, security/selinux/avc.c:995-1005, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-EACCES -- clone -/
theorem clone_eacces_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect (errno_ret EACCES) [] []) demo_model []) := by
  sys_norm

/-- -EPERM (1) is refused: every -EPERM of `copy_process` is gated on a
flag bit this word does not set (`CLONE_NEWUSER`, `CLONE_NEWPID`, …, the
namespace checks of `copy_namespaces`, kernel/nsproxy.c:161-162, Linux v6.18.46), and
no permission check remains on a plain fork.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EPERM -- clone -/
theorem clone_eperm_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret 1) [] []) demo_model []) := by
  sys_refute

/-- -EINVAL is refused: `copy_process`'s -EINVAL returns (kernel/fork.c:1951-1998, Linux v6.18.46)
are all flag-bit combinations this word does not have.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EINVAL -- clone -/
theorem clone_einval_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- -EINTR (4) is refused: `copy_process` reaches it only with a fatal
signal pending (kernel/fork.c:2362-2364, Linux v6.18.46), which group-exits the task before
it returns to userspace; and -ERESTARTNOINTR (:2015) is restarted by
`arch_do_signal_or_restart` unconditionally (arch/riscv/kernel/signal.c:417-420, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EINTR -- clone -/
theorem clone_eintr_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret 4) [] []) demo_model []) := by
  sys_refute

/-- -EBUSY (16) is refused: `cpuset_can_fork` short-circuits on `same_cs`
(kernel/cgroup/cpuset.c:3730-3734, Linux v6.18.46), so the pids controller's -EAGAIN is the
only cgroup answer a plain fork can get.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EBUSY -- clone -/
theorem clone_ebusy_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret 16) [] []) demo_model []) := by
  sys_refute

/-- -ENFILE is refused: the nearest neighbour of an admitted errno.  It is
the system-wide table's answer (`alloc_empty_file`, fs/file_table.c:278,
Linux v6.18.46), and a fork opens no file.
kernel: fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem clone_enfile_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []) := by
  sys_refute

/-- -ENOSPC (28) is refused: `alloc_pid` remaps it to -EAGAIN on the path a
plain fork takes (kernel/pid.c:245), so it never escapes.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_enospc_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret 28) [] []) demo_model []) := by
  sys_refute

/-- A pid is admitted: `pid_vnr(pid)` of the task `alloc_pid` numbered
(kernel/fork.c:2624, Linux v6.18.46), here 1234.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 -- clone -/
theorem clone_pid_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) []) := by
  sys_norm

/-- pid 1 is admitted: `pid_min` starts at 1 (kernel/pid.c:226, Linux v6.18.46).  The
kernel could not hand THIS caller pid 1: the namespace's reaper holds it,
`zap_pid_ns_processes` (kernel/pid_namespace.c:199-201, Linux v6.18.46) closes
the namespace to new pids before that slot is freed, and killing the init
namespace's reaper panics (kernel/exit.c:935-937, Linux v6.18.46).  The model
does not say so; the widening is `clone_pid_ok_b`'s on both sides and is
NOT among the ones bugs/clone-retires-no-pid.md records — a Rocq-side
follow-up.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1 -- clone -/
theorem clone_pid_one_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect 1 [] []) (with_children demo_model) []) := by
  sys_norm

/-- `2^22 - 1` is admitted: the largest pid `idr_alloc_cyclic`'s exclusive
`end` (lib/idr.c:102, Linux v6.18.46) leaves under a `pid_max` at `PID_MAX_LIMIT`.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=4194303 -- clone -/
theorem clone_pid_envelope_top_admitted (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect 4194303 [] []) (with_children demo_model) []) := by
  sys_norm

/-- ZERO IS NEVER THE PARENT'S ANSWER.  0 is what `copy_thread` seats in
the CHILD's a0 (arch/riscv/kernel/process.c:255, Linux v6.18.46); the parent gets
`pid_vnr` of a live pid (kernel/fork.c:2624, :2654, Linux v6.18.46), and `alloc_pid`
never allocates 0 (kernel/pid.c:226, Linux v6.18.46).  A kernel reporting 0 to the caller
is lying — and admitting it would make the model follow the child's branch
of the caller's own code.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=0 -- clone -/
theorem clone_zero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `2^22` itself is refused: `idr_alloc_cyclic`'s `end` is EXCLUSIVE
(lib/idr.c:102, Linux v6.18.46) and no `pid_max` exceeds `PID_MAX_LIMIT`.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=4194304 -- clone -/
theorem clone_pid_envelope_end_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 4194304 [] []) (with_children demo_model) []) := by
  sys_refute

/-- The call writes no user memory: with `CLONE_PARENT_SETTID` clear the
`put_user` of `kernel_clone` (kernel/fork.c:2626-2627, Linux v6.18.46) is skipped, and
legacy `clone` dereferences none of its pointer arguments for this word.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-write:a2:4 -- clone -/
theorem clone_writes_nothing (i : SyscallInput) (a : word) (b : byte) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 1234 [(a, [b])] []) (with_children demo_model) []) := by
  sys_refute

/-- …and zero-fills no range: `dup_mmap` copies the parent's mappings into
the CHILD's new mm (`dup_mm`, kernel/fork.c:1479-1518, Linux v6.18.46) and touches none of
the parent's pages.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-zeros:0x40000000 -- clone -/
theorem clone_zeros_nothing (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 1234 [] [(1073741824, 4096)]) (with_children demo_model) []) := by
  sys_refute

/-- …and reads no user memory: the copy-in ledger of legacy `clone` is
empty, because `SYSCALL_DEFINE5(clone, …)` copies nothing from user memory
for this word.  (`clone3`'s is not, below.)
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-copyin:a2:8 -- clone -/
theorem clone_reads_nothing (i : SyscallInput) (a : word) :
    ¬ clone_spec 17 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(a, 8)]) (with_children demo_model) []) := by
  sys_refute

/-- The call emits no event: a fork is not a read, a write or an exit of
THIS process.
kernel: kernel/fork.c:kernel_clone@v6.18.46 -/
theorem clone_emits_nothing (i : SyscallInput) (ev : event) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) [ev]) := by
  sys_refute

/-- The admitted word never declines on the demo process.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_fork_never_declines (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model Unmodeled := by
  sys_refute

/-! ### 3a. The caller's own tid

`alloc_pid` (kernel/pid.c:238-239, Linux v6.18.46) hands out a FREE pid
through `idr_alloc_cyclic` (lib/idr.c:119, Linux v6.18.46) over the
namespace's idr, where the caller's own number is allocated, so the child's
pid is never the caller's.  The model can only say so once it
knows the caller's tid — `m_tid` is `none` until `set_tid_address` or
`getpid` observes it. -/

/-- With the tid recorded as 1234, pid 1234 is refused.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate set_tid_address:ret=1234 --mutate clone:arg0=17,ret=1234 -- tid -/
theorem clone_own_tid_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i (with_tid 1234 demo_model)
        (Ok (mkEffect 1234 [] []) (with_children (with_tid 1234 demo_model)) []) := by
  sys_refute

/-- …and pid 1235 is admitted alongside it.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate set_tid_address:ret=1234 --mutate clone:arg0=17,ret=1235 -- tid -/
theorem clone_other_pid_with_tid_admitted (i : SyscallInput) :
    clone_spec 17 i (with_tid 1234 demo_model)
      (Ok (mkEffect 1235 [] []) (with_children (with_tid 1234 demo_model)) []) := by
  sys_norm

/-- The quantified form: once a tid inside the envelope is recorded, no
resolution answers it — not the pid arm, which excludes it, and not the
errno arm, whose four values read above `2^64 - 25`.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_never_answers_the_recorded_tid (t : word) (i : SyscallInput) (m : Model)
    (m' : Model) (evs : List event) (ht : bv_unsigned t < 4194304)
    (hg : clone_no_shared_file_b (m_fds (with_tid t m)) = true) :
    ¬ clone_spec 17 i (with_tid t m) (Ok (mkEffect t [] []) m' evs) := by
  intro h
  have hf : clone_fork_flags_b 17 = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
  rcases (clone_resolve_reading i (with_tid t m) _ hg).mp h with ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
  · have hte : t = errno_ret e := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    rw [hte] at ht
    simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact absurd ht (by decide)
  · have hpid : t = pid := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    subst hpid
    exact ((clone_pid_ok_b_with_tid t t m).mp hok).2 rfl

/-- Before the tid is observed EVERY pid in the envelope is admitted, the
caller's own included: a widening (the model cannot name a tid it has not
seen), recorded in bugs/clone-retires-no-pid.md.  Stated over the whole
envelope so that it says something `clone_pid_admitted` does not; the
probe shows the shape at 1234, the tid it then observes.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 --mutate set_tid_address:ret=1234 -- clonetid -/
theorem clone_unobserved_tid_widening (p : word) (hp0 : 0 < bv_unsigned p)
    (hp1 : bv_unsigned p < 4194304) (i : SyscallInput) :
    clone_spec 17 i demo_model (Ok (mkEffect p [] []) (with_children demo_model) []) :=
  (clone_fork_answers i _).mpr (Or.inr ⟨p, rfl, hp0, hp1⟩)

/-! ### 4. The recorded child: `copy_process` → `__do_wait`

The pid arm applies `State.with_children` and the errno arm does not.  The
two are SEPARATED, not merely covered: a model that recorded a child on
the errno arm would decline the `wait4` Linux answers -ECHILD after a
failed fork, and one that recorded none on the pid arm would answer
-ECHILD where Linux reaps.  `copy_process` links the new task onto
`current->children` only past every failure path (kernel/fork.c:2367-2398, Linux v6.18.46),
and unwinds everything on failure (:2438-2503). -/

/-- The pid arm records the child: a pid reported with the model unchanged
is refused.
probe: testing/syscall-check/tests/clone_fork.c#fail-closed --expect-unmodeled wait4 -- wait -/
theorem clone_pid_without_child_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect 1234 [] []) demo_model []) := by
  sys_refute

/-- The errno arm records nothing: an -EAGAIN reported with a child
recorded is refused — the `reject` case of the compose probe, where the
model must still answer -ECHILD to the `wait4` that follows.
probe: testing/syscall-check/tests/clone_wait4_compose.c#reject --mutate clone:arg0=17,ret=-EAGAIN --mutate wait4:ret=4321 -- after -/
theorem clone_errno_with_child_rejected (i : SyscallInput) :
    ¬ clone_spec 17 i demo_model (Ok (mkEffect (errno_ret EAGAIN) [] []) (with_children demo_model) []) := by
  sys_refute

/-- The quantified errno half, over every model the gate lets through: an
admitted errno leaves the model as it was.
kernel: kernel/fork.c:copy_process,kernel_clone; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem clone_errno_leaves_the_model (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (hg : clone_no_shared_file_b (m_fds m) = true)
    (h : clone_spec 17 i m (Ok eff m' evs))
    (he : eff.eff_ret = errno_ret EAGAIN ∨ eff.eff_ret = errno_ret ENOMEM
        ∨ eff.eff_ret = errno_ret EMFILE ∨ eff.eff_ret = errno_ret EACCES) :
    m' = m := by
  have hf : clone_fork_flags_b 17 = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
  rcases (clone_resolve_reading i m _ hg).mp h with ⟨e, _, ho⟩ | ⟨pid, ho, hok⟩
  · exact (outcome.Ok.inj ho).2.1
  · exfalso
    have hpid : eff.eff_ret = pid := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    have hb := clone_pid_ok_b_below m pid hok
    rw [hpid] at he
    rcases he with h1 | h1 | h1 | h1 <;> (rw [h1] at hb; exact absurd hb (by decide))

/-- …and the pid half: a return outside the errno set records the child.
kernel: kernel/fork.c:copy_process,kernel_clone; kernel/exit.c:__do_wait; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem clone_pid_records_the_child (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (hg : clone_no_shared_file_b (m_fds m) = true)
    (h : clone_spec 17 i m (Ok eff m' evs))
    (hne : eff.eff_ret ≠ errno_ret EAGAIN ∧ eff.eff_ret ≠ errno_ret ENOMEM
        ∧ eff.eff_ret ≠ errno_ret EMFILE ∧ eff.eff_ret ≠ errno_ret EACCES) :
    m_has_children m' = true := by
  have hf : clone_fork_flags_b 17 = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
  rcases (clone_resolve_reading i m _ hg).mp h with ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
  · exfalso
    have hr : eff.eff_ret = errno_ret e := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hne.1 hr
    · exact hne.2.1 hr
    · exact hne.2.2.1 hr
    · exact hne.2.2.2 hr
  · rw [(outcome.Ok.inj ho).2.1]
    rfl

/-- The same for the shared resolution on its own.
kernel: kernel/fork.c:kernel_clone; kernel/pid.c:alloc_pid; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_resolve_never_returns_zero (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : clone_resolve i m (Ok eff m' evs)) : eff.eff_ret ≠ 0 := by
  by_cases hg : clone_no_shared_file_b (m_fds m) = true
  · rcases (clone_resolve_reading i m _ hg).mp h with ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
    · have hr : eff.eff_ret = errno_ret e := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
      rw [hr]
      exact clone_errno_ret_nonzero e he
    · have hr : eff.eff_ret = pid := congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
      rw [hr]
      have hpos := clone_pid_ok_b_pos m pid hok
      intro hz
      rw [hz] at hpos
      exact absurd hpos (by decide)
  · simp only [Bool.not_eq_true] at hg
    exact absurd h (by
      rw [clone_resolve_gate_closed i m _ hg]
      exact fun h' => by cases h')

/-- ZERO IS NEVER AN ANSWER, over every flag word, every model and every
resolution: what `Checks/ProcessCreation.v`'s `clone_never_returns_zero`
says.  0 is the CHILD's a0 (arch/riscv/kernel/process.c:255, Linux v6.18.46); the parent
receives an errno or `pid_vnr` of a pid `alloc_pid` drew above 0
(kernel/pid.c:226, kernel/fork.c:2624).
kernel: kernel/fork.c:kernel_clone; kernel/pid.c:alloc_pid; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_never_returns_zero (flags : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : clone_spec flags i m (Ok eff m' evs)) : eff.eff_ret ≠ 0 := by
  unfold clone_spec at h
  by_cases hf : clone_fork_flags_b flags = true
  · simp only [hf, ↓reduceIte] at h
    exact clone_resolve_never_returns_zero i m eff m' evs h
  · simp only [hf, Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-! ### 5. `clone3`: `copy_clone_args_from_user` → `clone3_args_valid` → `kernel_clone`

The entry point `clone3` (kernel/fork.c:2892-2914, Linux v6.18.46) is `SYSCALL_DEFINE2(clone3,
struct clone_args __user *, uargs, size_t, size)`.  `copy_clone_args_from_user`
(:2756-2822) tests
`size` first — -E2BIG above `PAGE_SIZE` (:2772-2773), -EINVAL below
`CLONE_ARGS_SIZE_VER0` (:2774-2775) — then `copy_struct_from_user`
(include/linux/uaccess.h:389-411, Linux v6.18.46) reads the struct, zero-filling a short
one (:400-401) and refusing a nonzero tail with -E2BIG (:402-405), then the
field checks (:2781-2800); `clone3_args_valid` (:2853-2879) judges the
flags and the stack pair, and `kernel_clone` (:2913) runs.  The model
answers ONE size, 88, over a wholly readable image that is the plain fork
(every field 0 but `exit_signal = SIGCHLD`), and records the 88 bytes read
on the copy-in ledger.  The kernel answers every shape declined here (the
short sizes are the zero-fill path, a longer size with a zero tail is
accepted, a nonzero field is a different request), so the declines are
modeled-surface declines, not empty intersections. -/

/-- `struct clone_args` as the 88 bytes `copy_struct_from_user` reads:
eleven `__aligned_u64` fields, little-endian, in the order the header
declares them (include/uapi/linux/sched.h:92-104, Linux v6.18.46).
model: a byte image builder for the pins below -/
def clone_args_image (fields : List word) : List byte := fields.flatMap word_le8

/-- The plain-fork image: every field 0 but `exit_signal` (field 4, offset
32) equal to `SIGCHLD`.
model: the image `clone_spec.c`'s `c3` mode passes -/
def fork_args : List byte := clone_args_image [0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0]

/-- The plain-fork image with field `k` replaced by `v`: what `clone_spec.c`'s
`c3field k v` mode writes.
model: the image family the field pins range over -/
def fork_args_with (k : Nat) (v : word) : List byte :=
  clone_args_image (([0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0] : List word).set k v)

/-- The image is 88 bytes long, as the struct is.
model: `clone_args_image` over eleven fields -/
theorem fork_args_length : fork_args.length = 88 := by decide

/-- The plain-fork image passes the image gate, as it passes the kernel's
(`clone3_args_valid`, kernel/fork.c:2853-2879, Linux v6.18.46).
kernel: kernel/fork.c:clone3_args_valid,copy_clone_args_from_user@v6.18.46 -/
theorem fork_args_is_a_fork : clone3_fork_args_b fork_args = true := by decide

/-- …and every image with one other field set fails it — the eleven
fields, each at 1, and `exit_signal` at 15 (`SIGTERM`) and at 0: each is
a request the kernel would act on (`copy_clone_args_from_user`,
kernel/fork.c:2781-2800, Linux v6.18.46; then `clone3_args_valid`,
kernel/fork.c:2853-2879, Linux v6.18.46) and the model declines.
kernel: kernel/fork.c:clone3_args_valid,copy_clone_args_from_user@v6.18.46 -/
theorem fork_args_with_field_set_is_not_a_fork :
    clone3_fork_args_b (fork_args_with 0 1) = false ∧ clone3_fork_args_b (fork_args_with 1 1) = false
    ∧ clone3_fork_args_b (fork_args_with 2 1) = false ∧ clone3_fork_args_b (fork_args_with 3 1) = false
    ∧ clone3_fork_args_b (fork_args_with 4 15) = false ∧ clone3_fork_args_b (fork_args_with 4 0) = false
    ∧ clone3_fork_args_b (fork_args_with 5 1) = false ∧ clone3_fork_args_b (fork_args_with 6 1) = false
    ∧ clone3_fork_args_b (fork_args_with 7 1) = false ∧ clone3_fork_args_b (fork_args_with 8 1) = false
    ∧ clone3_fork_args_b (fork_args_with 9 1) = false ∧ clone3_fork_args_b (fork_args_with 10 1) = false := by
  decide

/-- The image at address 4096, nothing else mapped.
model: a memory fixture for the pins below -/
def fork_mem : word → Option byte := pin_mem 4096 fork_args

/-- `clone3(4096, size)` as the dispatcher sees it, over memory `mem`.
model: the input fixture for the dispatcher pins -/
def c3_input (size : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 435 [4096, size, 0, 0, 0, 0] mem mem

/-- `i`'s memory holds `bs` at 4096 for the 88-byte read `clone3` makes: the
premise the image pins quantify over.  An `abbrev`, so a concrete input
decides it and a proof unfolds it by name.
model: the read premise of the `clone3` pins -/
abbrev holds_image (i : SyscallInput) (bs : List byte) : Prop :=
  read_bytes_map i.in_mem 4096 (Z_to_bv 64 CLONE_ARGS_SIZE) = some bs

/-- …and the read fails.
model: the unreadable premise of the `clone3` pins -/
abbrev holds_no_image (i : SyscallInput) : Prop :=
  read_bytes_map i.in_mem 4096 (Z_to_bv 64 CLONE_ARGS_SIZE) = none

/-- The fixture's memory reads back as the image: what `copy_struct_from_user`
(include/linux/uaccess.h:408-409, Linux v6.18.46) hands `clone3_args_valid` once its copy
succeeds.
model: `read_bytes_map` evaluated on the fixture -/
theorem fork_mem_reads : holds_image (c3_input 88 fork_mem) fork_args := by decide

/-- The whole call for a readable plain-fork image and the right size, over
every input holding the image and every outcome: the same four errnos and
the same pid envelope as legacy `clone`, the child recorded on the pid arm
only, and EVERY arm carrying the 88 bytes read on the copy-in ledger —
`copy_struct_from_user` faults the struct in before `kernel_clone` can fail
(kernel/fork.c:2777, :2913, Linux v6.18.46), so an errno past the read read them too.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user,clone3_args_valid,kernel_clone,copy_process; kernel/pid.c:alloc_pid; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem clone3_fork_image_answers (i : SyscallInput) (o : outcome SyscallEffect)
    (hread : holds_image i fork_args) :
    clone3_spec 4096 88 i demo_model o ↔
      ((o = Ok (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret EACCES) [] [] [] [] [(4096, 88)]) demo_model [])
      ∨ ∃ pid : word,
          o = Ok (SyscallEffect.mkEffectU pid [] [] [] [] [(4096, 88)]) (with_children demo_model) []
          ∧ 0 < bv_unsigned pid ∧ bv_unsigned pid < 4194304) := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hg : clone_no_shared_file_b (m_fds demo_model) = true := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread,
    fork_args_is_a_fork, clone3_resolve.eq_1, record_copyins.eq_1, bind_bind_iff,
    clone_resolve.eq_1, bind_get_model_iff, hg, Bool.not_true, bind_alt_iff,
    bind_errno_from_iff, bind_choose_outcome_iff, bind_modify_iff, err_ret.eq_1, ret_only.eq_1,
    bind_pure_iff, pure_iff, mkEffect.eq_1, with_copyins.eq_1, List.append_nil, CLONE_ARGS_SIZE_nat,
    clone_pid_ok_b_demo, clone_errnos, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]

/-! #### The size gate: `copy_clone_args_from_user`, before any copy

`usize > PAGE_SIZE` is -E2BIG first (kernel/fork.c:2772-2773, Linux v6.18.46), `usize <
CLONE_ARGS_SIZE_VER0` is -EINVAL next (:2774-2775), and inside that range
`copy_struct_from_user` accepts every size — zero-filling a short struct
(include/linux/uaccess.h:400-401, Linux v6.18.46), requiring a longer one's tail to be zero
(:402-405).  The model answers 88 alone; every other size declines, and the
kernel's own answer to it is not given.  `size` is a `size_t`, so the
register is compared whole: `88 + 2^32` is not 88 to the kernel either. -/

/-- `CLONE_ARGS_SIZE_VER0` (64), the first published struct: the kernel
zero-fills the seven missing fields and forks; the model declines the
zero-fill path.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=64 -- c3 -/
theorem clone3_ver0_size_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 64 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLONE_ARGS_SIZE_VER1` (80), the second.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=80 -- c3 -/
theorem clone3_ver1_size_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 80 i m o ↔ o = Unmodeled := by
  sys_norm

/-- One byte short of the struct: the kernel zero-fills the last byte of
`cgroup`; the model declines.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=87 -- c3 -/
theorem clone3_short_size_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 87 i m o ↔ o = Unmodeled := by
  sys_norm

/-- One byte long: the kernel accepts it when the excess byte is zero —
`copy_struct_from_user` (include/linux/uaccess.h:403, Linux v6.18.46) asks
`check_zeroed_user` about the tail — and answers -E2BIG otherwise; the model
declines both.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=89 -- c3 -/
theorem clone3_long_size_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 89 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Size 0 is below `CLONE_ARGS_SIZE_VER0`: the kernel's -EINVAL
(kernel/fork.c:2774-2775, Linux v6.18.46) is not given; the call declines.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 -- c3 -/
theorem clone3_zero_size_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `88 + 2^32`: the size test is NOT truncated — `size_t` is 64 bits —
so a register whose low half reads 88 is not 88.  The kernel's own answer
is -E2BIG (above `PAGE_SIZE`, :2772-2773); the model declines.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=0x100000058 -- c3 -/
theorem clone3_size_high_bits_declines (uargs : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clone3_spec uargs 4294967384 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A pid is not admitted under a declined size, whatever the memory holds:
the size gate precedes the read.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=64 -- c3 -/
theorem clone3_ver0_size_pid_rejected (i : SyscallInput) :
    ¬ clone3_spec 4096 64 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 64)]) (with_children demo_model) []) := by
  sys_refute

/-! #### The read: `copy_struct_from_user`, all or nothing

`copy_from_user(dst, src, size)` call of `copy_struct_from_user`
(include/linux/uaccess.h:408-409, Linux v6.18.46) either
moves the whole struct or answers -EFAULT; a struct not wholly readable
never reaches `clone3_args_valid`.  The model declines the unreadable
struct rather than answering -EFAULT, and charges nothing to the ledger for
it. -/

/-- A struct the memory does not hold declines, over every model.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem clone3_unreadable_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_no_image i) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  simp only [holds_no_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread,
    unmodeled_iff]

/-- Nothing mapped at all: the concrete shape of the previous pin.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem clone3_nothing_mapped_declines (m : Model) (o : outcome SyscallEffect) :
    clone3_spec 4096 88 (c3_input 88 (fun _ => none)) m o ↔ o = Unmodeled :=
  clone3_unreadable_declines _ m o (by decide)

/-- The last byte unmapped: 87 readable bytes are not the struct.  A spec
reading only `CLONE_ARGS_SIZE_VER1` bytes would still accept this call; the
model reads all 88.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-hide:a0+87:1 -- c3 -/
theorem clone3_last_byte_unmapped_declines (m : Model) (o : outcome SyscallEffect) :
    clone3_spec 4096 88 (c3_input 88 (pin_mem 4096 (fork_args.take 87))) m o ↔ o = Unmodeled :=
  clone3_unreadable_declines _ m o (by decide)

/-- …and the first byte unmapped.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-hide:a0:1 -- c3 -/
theorem clone3_first_byte_unmapped_declines (m : Model) (o : outcome SyscallEffect) :
    clone3_spec 4096 88 (c3_input 88 (pin_mem 4097 (fork_args.drop 1))) m o ↔ o = Unmodeled :=
  clone3_unreadable_declines _ m o (by decide)

/-- An unreadable struct is a copy that FAILED: no pid, and no ledger
entry either — Linux charges nothing for a `copy_from_user` that faulted.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem clone3_unreadable_pid_rejected (m : Model) :
    ¬ clone3_spec 4096 88 (c3_input 88 (fun _ => none)) m
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 88)]) (with_children m) []) := by
  rw [clone3_nothing_mapped_declines]
  exact fun h => by cases h

/-! #### The image: `clone3_args_valid` and the plain-fork shape

Every field but `exit_signal` must be zero.  The kernel accepts many of
the images below — a `stack`/`stack_size` pair `clone3_stack_valid`
(kernel/fork.c:2833-2851, Linux v6.18.46) validates, a `set_tid` array, a pidfd request —
and this model declines each, because the child it would describe is not
one it steps, or the effect lands in the parent's memory (`pidfd`,
`parent_tid`, :2215-2229, :2626-2627).  `flags` is tested on all 64 bits:
`copy_clone_args_from_user` assigns it whole (:2803) and
`CLONE_CLEAR_SIGHAND` is bit 32 (include/uapi/linux/sched.h:37, Linux v6.18.46). -/

/-- The image gate closes on `flags = CLONE_VM` (0x100): a shared address
space, the same decline as the legacy word 0x111.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 0 0x100 -/
theorem clone3_flags_vm_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 0 256)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 0 256) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- Bit 56 of `flags` — the EIGHTH byte of the `__aligned_u64`, which a
seven-byte `clone_args_field` would never see: the kernel assigns the field
whole (`copy_clone_args_from_user`, kernel/fork.c:2803) and refuses the bit
(`clone3_args_valid`, :2853-2879), and the model declines it.  This is the
pin that holds `clone_args_field`'s `take 8` at eight.
kernel: kernel/fork.c:copy_clone_args_from_user,clone3_args_valid@v6.18.46 -/
theorem clone3_flags_high_byte_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 0 72057594037927936)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 0 72057594037927936) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- The same byte of the LAST field, `cgroup` (offset 80): byte 87, the
final byte of the 88 the image gate reads.  Here the kernel FORKS — without
`CLONE_INTO_CGROUP` the field is never read (:2798-2800) — and the model
declines the nonzero field with the rest of the image; the pin holds the
read at the whole struct.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem clone3_cgroup_high_byte_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 10 72057594037927936)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 10 72057594037927936) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `flags = CLONE_CLEAR_SIGHAND`, bit 32: clone3's flags field really is
64 bits wide, and the gate reads all of them.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 0 0x100000000 -/
theorem clone3_flags_clear_sighand_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 0 4294967296)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 0 4294967296) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `pidfd` set: a request to install a descriptor in the PARENT's table
(`copy_process`, kernel/fork.c:2215-2229, Linux v6.18.46; there the `CLONE_PIDFD` block
calls `pidfd_prepare` and writes the descriptor number through
`args->pidfd`) — the kernel would need `CLONE_PIDFD` to act on it, and
the model declines the shape whatever the flags.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 1 1 -/
theorem clone3_pidfd_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 1 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 1 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `child_tid` set.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 2 1 -/
theorem clone3_child_tid_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 2 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 2 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `parent_tid` set: with `CLONE_PARENT_SETTID` this is the pointer
`kernel_clone` writes the child's tid through (kernel/fork.c:2626-2627, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 3 1 -/
theorem clone3_parent_tid_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 3 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 3 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `exit_signal = SIGTERM` (15): a fork reporting another signal.  The
kernel accepts it (`copy_clone_args_from_user`, kernel/fork.c:2794-2796,
Linux v6.18.46, which asks `valid_signal`, include/linux/signal.h:272-275,
Linux v6.18.46); the model's allowlist is `SIGCHLD`.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 4 15 -/
theorem clone3_sigterm_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 4 15)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 4 15) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `exit_signal = 0`: the kernel's legal no-signal fork, declined as the
legacy word 0 is.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 4 0 -/
theorem clone3_no_signal_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 4 0)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 4 0) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- 17 in the HIGH half of the `exit_signal` field: the kernel refuses it
(-EINVAL, `args.exit_signal & ~((u64)CSIGNAL)`, kernel/fork.c:2794-2796, Linux v6.18.46);
the model reads the field whole and declines.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 4 0x1100000000 -/
theorem clone3_sigchld_high_half_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 4 73014444032)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 4 73014444032) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `stack` alone: `clone3_stack_valid` REFUSES it (`stack_size == 0`,
kernel/fork.c:2839-2840, Linux v6.18.46), so the kernel answers -EINVAL; the model
declines rather than give it.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 5 1 -/
theorem clone3_stack_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 5 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 5 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `stack_size` alone: refused by the kernel too (`stack == 0` with
`stack_size > 0`, kernel/fork.c:2835-2837, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 6 1 -/
theorem clone3_stack_size_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 6 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 6 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `stack` AND `stack_size` together — the pair `clone3_stack_valid`
ACCEPTS (kernel/fork.c:2838-2848, Linux v6.18.46), seating the stack in the child's
registers only (arch/riscv/kernel/process.c:251-252, Linux v6.18.46).  The kernel forks;
the model declines the whole shape, not just a lone half: the asymmetry
with the legacy arm's `newsp` is this model's own, and the Rocq block on
`Kernel.Fork.CLONE_ARGS_SIZE` says why neither side is moved.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3stack -/
theorem clone3_stack_pair_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (clone_args_image [0, 0, 0, 0, 17, 65536, 4096, 0, 0, 0, 0])) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (clone_args_image [0, 0, 0, 0, 17, 65536, 4096, 0, 0, 0, 0]) = false := by
    decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `tls` set: meaningful only with `CLONE_SETTLS`
(arch/riscv/kernel/process.c:253-254, Linux v6.18.46); declined as a shape.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 7 1 -/
theorem clone3_tls_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 7 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 7 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `set_tid` set without `set_tid_size`: the kernel's -EINVAL
(kernel/fork.c:2787-2788, Linux v6.18.46); declined.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 8 1 -/
theorem clone3_set_tid_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 8 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 8 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `set_tid_size` set without `set_tid`: -EINVAL too (kernel/fork.c:2784-2785, Linux v6.18.46);
declined.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 9 1 -/
theorem clone3_set_tid_size_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 9 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 9 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- `cgroup` set: read only under `CLONE_INTO_CGROUP` (kernel/fork.c:2798-2800, Linux v6.18.46);
declined as a shape.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 10 1 -/
theorem clone3_cgroup_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hread : holds_image i (fork_args_with 10 1)) :
    clone3_spec 4096 88 i m o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hgate : clone3_fork_args_b (fork_args_with 10 1) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread, hgate,
    unmodeled_iff]

/-- The image gate precedes the resolution: a pid forged over a `CLONE_VM`
image is not admitted.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88 -- c3field 0 0x100 -/
theorem clone3_flags_vm_pid_rejected (i : SyscallInput)
    (hread : holds_image i (fork_args_with 0 256)) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 88)]) (with_children demo_model) []) := by
  rw [clone3_flags_vm_declines i demo_model _ hread]
  exact fun h => by cases h

/-! #### The resolution through `clone3`: the same arms, under the ledger -/

/-- A pid is admitted, with the 88 bytes on the ledger.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=1234 -- c3 -/
theorem clone3_pid_admitted (i : SyscallInput)
    (hread : holds_image i fork_args) :
    clone3_spec 4096 88 i demo_model
      (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 88)]) (with_children demo_model) []) :=
  (clone3_fork_image_answers i _ hread).mpr (Or.inr ⟨1234, rfl, by decide, by decide⟩)

/-- -EAGAIN is admitted, and it carries the ledger too: the errno arm is
PAST the read (`copy_clone_args_from_user` returned 0 at kernel/fork.c:2777, Linux v6.18.46
before `kernel_clone` failed at :2913).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=-EAGAIN -- c3 -/
theorem clone3_eagain_admitted (i : SyscallInput)
    (hread : holds_image i fork_args) :
    clone3_spec 4096 88 i demo_model
      (Ok (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(4096, 88)]) demo_model []) :=
  (clone3_fork_image_answers i _ hread).mpr (Or.inl (Or.inl rfl))

/-- `2^22 - 1` is admitted through `clone3` as through `clone`.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=4194303 -- c3 -/
theorem clone3_pid_envelope_top_admitted (i : SyscallInput)
    (hread : holds_image i fork_args) :
    clone3_spec 4096 88 i demo_model
      (Ok (SyscallEffect.mkEffectU 4194303 [] [] [] [] [(4096, 88)]) (with_children demo_model) []) :=
  (clone3_fork_image_answers i _ hread).mpr (Or.inr ⟨4194303, rfl, by decide, by decide⟩)

/-- `2^22` is refused through `clone3` as through `clone`.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=4194304 -- c3 -/
theorem clone3_pid_envelope_end_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 4194304 [] [] [] [] [(4096, 88)]) (with_children demo_model) []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- -ENOSYS (38) is refused — LINUX's answer alone.  On the pinned kernel
the number is wired to `SYSCALL_DEFINE2(clone3, …)` (kernel/fork.c:2892-2914,
Linux v6.18.46) and every refusal of `copy_clone_args_from_user` is -EINVAL,
-E2BIG or -EFAULT (:2772-2818), none of them admitted on this image.  But
QEMU's user-mode emulation is a supported implementation too, and at
v11.1.1 — the version `testing/vm/pin.sh` pins — it has NO `clone3`
handler: `linux-user/syscall.c` carries no `TARGET_NR_clone3` case, so 435
falls to the dispatcher's `default:` (:14618-14620) and answers
-TARGET_ENOSYS with nothing read.  At this shape the intersection of the
supported implementations is empty and the refusal is a wrong modeled
behavior there, not a decline; the omission is Rocq's `clone_errnos`'s as
much as this twin's, and bugs/clone3-enosys-arm-admits-linux-alone.md
records it.  The pin holds the model's answer, not Linux's monopoly on it.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=-ENOSYS -- c3 -/
theorem clone3_enosys_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU (errno_ret 38) [] [] [] [] [(4096, 88)]) demo_model []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- THE LEDGER IS NOT OPTIONAL: a pid reported with an empty copy-in ledger
is refused.  `copy_struct_from_user` really read the 88 bytes
(include/linux/uaccess.h:408-409, Linux v6.18.46), and a model that forgot them would
accept an allocation the kernel refuses.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,drop-copyins -- c3 -/
theorem clone3_dropped_ledger_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- …and so is an errno reported without it: the errno arm is past the read.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=-EAGAIN,drop-copyins -- c3 -/
theorem clone3_errno_dropped_ledger_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model (Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- 89 bytes is not what `copy_struct_from_user` faulted in.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,grow-copyins:1 -- c3 -/
theorem clone3_grown_ledger_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 89)]) (with_children demo_model) []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- …nor is the range one byte along.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,shift-copyins:1 -- c3 -/
theorem clone3_shifted_ledger_rejected (i : SyscallInput)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4097, 88)]) (with_children demo_model) []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- The call writes nothing: `parent_tid` is zero, so `kernel_clone`'s
`put_user` (kernel/fork.c:2626-2627, Linux v6.18.46) is skipped.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,smuggle-write:a0:1 -- c3 -/
theorem clone3_writes_nothing (i : SyscallInput) (b : byte)
    (hread : holds_image i fork_args) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [(4096, [b])] [] [] [] [(4096, 88)]) (with_children demo_model) []) := by
  intro h
  have h' := (clone3_fork_image_answers i _ hread).mp h
  sys_refute at h'

/-- A copy-in ledger over a resolution that declines still declines: the
ledger goes only on outcomes the resolution admits.
model: `record_copyins` unfolded over a spec that answers `Unmodeled` alone -/
theorem record_copyins_of_declining (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (hdecl : ∀ o, spec i m o ↔ o = Unmodeled)
    (o : outcome SyscallEffect) :
    record_copyins reads spec i m o ↔ o = Unmodeled := by
  constructor
  · intro h
    cases o with
    | Unmodeled => rfl
    | Ok y m2 evs =>
      obtain ⟨x, m1, evs1, evs2, h1, -, -⟩ := h
      exact absurd ((hdecl _).mp h1) (fun h' => by cases h')
  · rintro rfl
    exact record_copyins_unmodeled reads spec i m ((hdecl _).mpr rfl)

/-- The descriptor gate is tested through `clone3` too: with a regular
file open the call declines whatever the ledger says.  What
`Checks/Sys/Kernel/Fork.v`'s `check_clone3_resolve` tests FIRST.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone3_with_file_open_declines (i : SyscallInput) (o : outcome SyscallEffect)
    (hread : holds_image i fork_args) :
    clone3_spec 4096 88 i open_file_model o ↔ o = Unmodeled := by
  have hs : (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false := by decide
  have hg : clone_no_shared_file_b (m_fds open_file_model) = false := by decide
  simp only [holds_image] at hread
  simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread,
    fork_args_is_a_fork, clone3_resolve.eq_1]
  exact record_copyins_of_declining _ _ _ _ (fun o => clone_resolve_gate_closed i _ o hg) o

/-- ZERO IS NEVER AN ANSWER through `clone3` either, over every argument,
model and resolution: what `Checks/ProcessCreation.v`'s
`clone3_never_returns_zero` says.  The ledger is the only thing
`clone3_resolve` adds (`Kernel.Fork.clone3_resolve_inv`), and the shared
resolution never answers 0.
kernel: kernel/fork.c:clone3,kernel_clone; kernel/pid.c:alloc_pid; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone3_never_returns_zero (uargs size : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : clone3_spec uargs size i m (Ok eff m' evs)) : eff.eff_ret ≠ 0 := by
  unfold clone3_spec at h
  by_cases hs : (!bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) = true
  · simp only [hs, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff] at h
    generalize hr : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) = r at h
    cases r with
    | none =>
      dsimp only at h
      simp only [unmodeled_iff, reduceCtorEq] at h
    | some bs =>
      dsimp only at h
      by_cases ha : clone3_fork_args_b bs = true
      · simp only [ha, ↓reduceIte] at h
        obtain ⟨e0, h0, hret⟩ := clone3_resolve_inv uargs i m eff m' evs h
        rw [hret]
        exact clone_resolve_never_returns_zero i m e0 m' evs h0
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- 0 is the CHILD's answer here too: what `Checks/ProcessCreation.v`'s
`clone3_never_returns_zero` says, at one forged outcome.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=0 -- c3 -/
theorem clone3_zero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ clone3_spec 4096 88 i demo_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 88)]) m' evs) := by
  intro h
  exact clone3_never_returns_zero 4096 88 i demo_model _ m' evs h rfl

/-! ### 6. Through the dispatcher

Syscall 220 reaches `clone_spec` with a0 alone — `SYSCALL_DEFINE5(clone,
…)` takes five arguments and the spec reads the flag word and nothing else,
which is the claim `clone_writes_nothing` and `clone_reads_nothing` rest on
— and 435 reaches `clone3_spec` with a0 and a1, neither narrowed:
`unsigned long clone_flags`, `struct clone_args __user *uargs` and `size_t
size` are all 64 bits wide on riscv64. -/

/-- 220 and 435 are in the modeled surface.
model: the model's own table; the numbers are the riscv rows `220 common clone` and `435 common clone3` of `scripts/syscall.tbl` -/
example : (220 : Int) ∈ modeled_sysnos ∧ (435 : Int) ∈ modeled_sysnos := by decide

/-- `clone(SIGCHLD, 0, 0, 0, 0)` through the table: the arm above.
kernel: kernel/fork.c:clone,kernel_clone,copy_process; kernel/pid.c:alloc_pid; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem sysno_220_fork_answers (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EACCES) [] []) demo_model [])
      ∨ ∃ pid : word, o = Ok (mkEffect pid [] []) (with_children demo_model) []
          ∧ 0 < bv_unsigned pid ∧ bv_unsigned pid < 4194304) := by
  unfold syscall_spec dispatch
  exact clone_fork_answers _ o

/-- `newsp` is passed through unread: a `clone(SIGCHLD, newsp)` with ANY
a1 answers exactly as with 0, because `copy_thread` seats `newsp` in the
CHILD's `sp` (arch/riscv/kernel/process.c:251-252, Linux v6.18.46) and nowhere the
caller can see.  So do a2..a5, the tid pointers and `tls`, which this word
never dereferences — quantified, so no register the arm might read is
fixed at a value that happens to pass.
kernel: kernel/fork.c:clone,kernel_clone,copy_process; kernel/pid.c:alloc_pid; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem sysno_220_newsp_unread (a1 a2 a3 a4 a5 : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 220 [17, a1, a2, a3, a4, a5] (fun _ => none) (fun _ => none))
        demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret EACCES) [] []) demo_model [])
      ∨ ∃ pid : word, o = Ok (mkEffect pid [] []) (with_children demo_model) []
          ∧ 0 < bv_unsigned pid ∧ bv_unsigned pid < 4194304) := by
  unfold syscall_spec dispatch
  exact clone_fork_answers _ o

/-- a0 = `0x1_00000011` through the table declines: the register is NOT
narrowed to `lower_32_bits` on the way to the arm.  Named `…_declines`, a
shape decline on a modeled number, for `tools/check_decline_registers.py`.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x100000011 -- clone -/
theorem sysno_220_high_bits_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 220 [4294967313, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      m Unmodeled := by
  sys_norm

/-- …and a forged pid is not given through it.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0x100000011 -- clone -/
theorem sysno_220_high_bits_pid_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 220 [4294967313, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect 1234 [] []) (with_children demo_model) []) := by
  sys_refute

/-- `clone3(&args, 88)` over memory holding the plain-fork image at 4096:
the arm above, ledger included.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user,clone3_args_valid,kernel_clone,copy_process; kernel/pid.c:alloc_pid; fs/file.c:alloc_fdtable; security/selinux/avc.c:avc_denied@v6.18.46 -/
theorem sysno_435_fork_image_answers (o : outcome SyscallEffect) :
    syscall_spec (c3_input 88 fork_mem) demo_model o ↔
      ((o = Ok (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] [] [] [(4096, 88)]) demo_model []
        ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret EACCES) [] [] [] [] [(4096, 88)]) demo_model [])
      ∨ ∃ pid : word,
          o = Ok (SyscallEffect.mkEffectU pid [] [] [] [] [(4096, 88)]) (with_children demo_model) []
          ∧ 0 < bv_unsigned pid ∧ bv_unsigned pid < 4194304) := by
  unfold syscall_spec dispatch
  exact clone3_fork_image_answers (c3_input 88 fork_mem) o fork_mem_reads

/-- a1 = 64 through the table declines, whatever the memory holds.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=64 -- c3 -/
theorem sysno_435_ver0_size_declines (m : Model) :
    syscall_spec (c3_input 64 fork_mem) m Unmodeled := by
  unfold syscall_spec dispatch
  exact (clone3_ver0_size_declines 4096 (c3_input 64 fork_mem) m Unmodeled).mpr rfl

/-- a1 = `88 + 2^32` through the table declines: `size_t` is not narrowed.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=0x100000058 -- c3 -/
theorem sysno_435_size_high_bits_declines (m : Model) :
    syscall_spec (c3_input 4294967384 fork_mem) m Unmodeled := by
  unfold syscall_spec dispatch
  exact (clone3_size_high_bits_declines 4096 (c3_input 4294967384 fork_mem) m Unmodeled).mpr rfl

/-- Nothing mapped at a0 through the table declines.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem sysno_435_nothing_mapped_declines (m : Model) :
    syscall_spec (c3_input 88 (fun _ => none)) m Unmodeled := by
  unfold syscall_spec dispatch
  exact (clone3_nothing_mapped_declines m Unmodeled).mpr rfl

/-- …and a forged pid is not given through it.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem sysno_435_nothing_mapped_pid_rejected :
    ¬ syscall_spec (c3_input 88 (fun _ => none)) demo_model
        (Ok (SyscallEffect.mkEffectU 1234 [] [] [] [] [(4096, 88)]) (with_children demo_model) []) := by
  unfold syscall_spec dispatch
  exact clone3_unreadable_pid_rejected demo_model

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `Fork.clone_no_shared_file_b`, Fork.v:636-637 at 96c2debdb.
kernel/fork.c, copy_files, Linux v6.18.46 shares every struct file via
dup_fd; independent copies of a read-write offset cannot model that.
kernel: kernel/fork.c:copy_files@v6.18.46 -/
theorem a17_rdwr_clone_declines :
    clone_no_shared_file_b [(3, .FdFileRW [102] 0)] = false := by
  rfl

/-- Rocq: `Fork.clone_no_shared_file_b`, Fork.v:636-637 at 96c2debdb.
kernel/fork.c, copy_files, Linux v6.18.46 shares every struct file via
dup_fd; independent copies of an append-mode entry would split the f_pos
an lseek reports.
kernel: kernel/fork.c:copy_files@v6.18.46 -/
theorem a17_append_clone_declines :
    clone_no_shared_file_b [(3, .FdFileA [102] 0)] = false := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork
