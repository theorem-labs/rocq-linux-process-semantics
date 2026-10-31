-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Signal.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Signal
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Signal — what the signal CHECKERS accept and their WITNESSES name, read off against Linux

Pins over `Checks.Sys.Kernel.Signal`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Signal.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Signal.v`, in two halves
written by two tickets: the rt_sigaction and rt_sigprocmask half first
(C-Kernel-Signal-mask-action) — the two checkers in the order their gates
fire, then their three witnesses — and, from the heading "The second
half" on, the sigaltstack, tkill and tgkill half
(C-Kernel-Signal-altstack-kill), in the same shape, with its own header.
Not part of the trusted specification: this file is QA on the definitions,
written to be READ, and every claim in it is a claim about what the kernel
does, with the citation beside it.  Every kernel line below was read at
Linux v6.18.46 (commit 1f99e9ab748f).  What follows in this header is the
first half's; the second half's header restates what differs.

WHAT A CHECKER PIN IS.  `Checks/Cases/Kernel/Signal.lean` states, for each
decision of the two specs, an `iff` over every outcome and refutes the lie
a kernel could not tell.  The checker is that spec made executable — the
four `_sound_`/`_complete_` lemmas beside it say the two agree on every
input — so a pin here does not restate those `iff`s.  It hands the checker
a concrete `(input, effect)` pair, the shape a trace hands it, and states
the verdict: `CheckOk` on the kernel's answer, `CheckReject` on the lie,
`CheckUnmodeled` where the spec declines.  That is the question a trace
asks, and the one the four lemmas cannot: soundness and completeness are
biconditionals between two definitions of this tree, and hold as well of
a wrong spec beside a matching wrong checker.  Only a verdict on a value
named from outside tells the two apart, which is what each pin below is.

THE MODEL IS AN OUTPUT.  rt_sigprocmask is the one arm of this half that
returns a model other than the one it was given (the second half has two
more, sigaltstack's install and the SIGABRT delivery), and a trace offers
the checker an effect, never a model: a lie about the mask installed is
therefore not a `CheckReject` but a `CheckOk` with the RIGHT model, and
the pins say which model that is.  Where Rocq refutes a wrong post-state (`… =
CheckOk (with_sigmask 65543 …) [] -> False`) the twin here is a `≠` on the
same `CheckOk`, closed by the two models differing in the mask.

WHAT THIS RESTATES.  Rocq keeps the worked examples for these checkers in
`Checks/Cases/Kernel/Signal.v`, beside the spec's, as `Example`s over
`check_syscall`.  The dispatcher twin and the arm record are the
registration step's, so each is restated here on `check_rt_sigaction i sig
act oact ss eff m` or `check_rt_sigprocmask i how nset oset ss eff m`
directly — the body of the arm the checked table will hold for 134 and
135 — and is one line over `check_syscall` once the registration lands.
For rt_sigaction: `rt_sigaction_sigint_accepted` is
`check_rt_sigaction_sigint_accepts_zero`; `rt_sigaction_sigsegv_unmodeled`,
`rt_sigaction_sigpipe_unmodeled`, `rt_sigaction_sigchld_unmodeled` and
`rt_sigaction_sigabrt_unmodeled` are the conjuncts of
`check_rt_sigaction_declined_signals`; `rt_sigaction_oact_read_back_declined`
is `check_rt_sigaction_oact_read_back_declines`.  For rt_sigprocmask:
`rt_sigprocmask_block_sigsegv_accepted` is
`check_rt_sigprocmask_block_sigsegv_accepts_the_install`;
`rt_sigprocmask_kill_stop_stripped_not_refused` is
`check_rt_sigprocmask_kill_stop_stripped_not_refused`;
`rt_sigprocmask_block_unions` and `rt_sigprocmask_unblock_clears` keep
their names with `check_` in front; `rt_sigprocmask_unblock_is_not_block`
is `check_rt_sigprocmask_unblock_is_not_block`;
`rt_sigprocmask_oldset_unmodeled` is the second conjunct of
`check_rt_sigprocmask_install_with_unwritable_oset_declines`;
`rt_sigprocmask_oldset_reports_entry_mask`,
`rt_sigprocmask_oldset_impossible_mask_rejected`,
`rt_sigprocmask_oldset_is_not_the_new_mask`,
`rt_sigprocmask_oldset_snapshot_precedes_install`,
`rt_sigprocmask_oldset_efault_still_installs` and
`rt_sigprocmask_oldset_over_task_size_never_succeeds` keep their names
with `check_` in front; `rt_sigprocmask_null_set_ignores_how` is
`check_rt_sigprocmask_null_set_ignores_how_on_the_fixture`;
`rt_sigprocmask_bad_size_beats_unreadable_set` and
`rt_sigprocmask_bad_size_beats_oldset_decline` keep their names with
`check_` in front;
`rt_sigprocmask_efault_beats_bad_how` is
`check_rt_sigprocmask_efault_beats_bad_how` with
`check_rt_sigprocmask_efault_beats_bad_how_einval_rejected`;
`rt_sigprocmask_copyins_separate_the_two_einvals` is the `BadHow` section's
`check_rt_sigprocmask_two_einvals_differ_in_the_ledger`;
`rt_sigprocmask_efault_records_no_copyin` is
`check_rt_sigprocmask_efault_records_no_copyin`;
`rt_sigprocmask_success_admits_no_write` is
`check_rt_sigprocmask_install_rejects_a_write`;
`rt_sigprocmask_unblock_pending_sigabrt_kills` and
`rt_sigprocmask_unblock_nothing_pending_lives` keep their names with
`check_` in front; `one_sided_unblock_kills` is
`check_rt_sigprocmask_one_sided_unblock_kills`, and the rt_sigprocmask
conjunct of `decl_off_frame_hypotheses_inhabited` — its first two are
facts about the fixture, pinned beside it in `Checks/Cases/Kernel/Signal.lean`
— is `check_rt_sigprocmask_declaration_off_nothing_pending_installs`.
Two Rocq examples are NOT restated here because they are dispatcher facts:
`rt_sigprocmask_how_truncates_size_does_not` is about which register bits
the ARM hands the checker as `how` — the `int` narrowing happens in the
row, before `check_rt_sigprocmask` sees the value, so a pin on the
checker alone at `how = 2^32 + 1` would state the narrowing's absence, not
the kernel's; rt_sigaction's `sig` is narrowed the same way in its row,
so no pin here reads either above 32 bits — and goes with the
registration, all but its size third,
which `check_rt_sigprocmask_size_is_not_narrowed` states here; and
`sig_mask_windows_all_declined`, with `rt_sigreturn_unmodeled` and
`kill_unmodeled`, are about numbers with no arm, which the decline
registers hold.  What a restatement loses is the register file — which of
a0..a3 an arm reads, and where the table sends each number — and those
facts are the registration's to pin, and go with it.
That list is prose: nothing reads it, and it goes stale on a rename with
nothing going red.  Its mechanical home would be the coverage header
`check_lean_cases_parity.py` reads, but that header lives on
`Checks/Cases/Kernel/Signal.lean`, the Lean mirror of the Rocq file that
holds these examples; this file mirrors no Rocq Cases file — Rocq keeps no
worked cases over these checkers apart from the ones above — so it
carries no such header and that checker would refuse one here.

NO PROBE REACHES THIS FILE.  The harness runs the EXTRACTED ROCQ model
(`check.sh` extracts it), so no Lean definition is ever evaluated against
a trace.  The probe cases that state the same facts of the Rocq side are
`testing/syscall-check/tests/rt_sigaction_spec.c`,
`testing/syscall-check/tests/rt_sigprocmask_spec.c`,
`testing/syscall-check/tests/rt_sigprocmask_mask.c`,
`testing/syscall-check/tests/sigaltstack_spec.c` and, for the SIGABRT
delivery under tkill and tgkill, `testing/syscall-check/tests/abort_terminal.c`,
each with its `conform`, `reject --mutate` and `fail-closed` cases.  Each pin below
cites the kernel line and not the probe, because the probe's verdict is
about the Rocq checker and this file is about the Lean one.

WHAT IS PINNED BEYOND THE SPEC'S FIXTURES.  Three things the spec pins
state over a fixture are stated here over a symbolic model, an
arbitrary input, or both, because at the checker they are ORDER facts —
which gate is decided first — and a fixture could pass them by luck:
the size test answers -EINVAL on EVERY input and model, the memory it
never reads included; a NULL `nset` answers on every model whatever `how`
holds, since the `how` test sits inside `if (nset)`; and the -EFAULT of
`copy_from_user` records nothing on every model, where the -EINVAL of a
bad `how` and the -EFAULT of `copy_to_user` both carry the eight-byte
ledger.  The other order fact — a not-wholly-writable `oset` DECLINES,
whatever effect the trace offers, -EFAULT and 0 alike — is stated over
the effect, which the spec pins cannot quantify over.

HOW THE PINS ARE PROVED.  A closed pin runs `check_norm`, the two
passes of the spec pins' `sys_norm` with the checker opened in the
first: one `simp +decide only` pass that opens the checker and the
acceptors, decides every closed gate and reads the fixture memories with
the `sys_simp` set — the spec pins' `sigaction_flags_*`, `sigset_at_*`
and `wmem_oldset_walk` rewrites are members — and then, if a goal is
left, the ground pass of `sys_norm` (`sys_simp_pass +ground +decide`),
which evaluates the reads no rewrite covers: an `act` eight bytes into
the address space, a set at an unmapped 8192, the all-ones set.  The
ground pass comes second for the reason `Checks/Cases/Tactic.lean` gives
`sys_norm`'s order: the readings must fire before ground evaluation
opens the fixtures they read.  The acceptors with a wildcard arm
(`check_ret_only`, `check_one_write` and the two `_copyins` forms) enter
the set by name, and a mismatched effect lands in the wildcard arm by
the same pass — which is why `sig_copyin` is opened there too: a ledger
left folded is neither `[]` nor a cons, and the match on it is stuck.
A `≠` pin runs `check_refute`, which is `check_norm` and then `done`;
`ne_eq` is in the first pass so the verdicts' injectivity is reached
under the negation.  The closed witness pins run `witness_norm`, the
same two passes over the witnesses.  None is `rfl`: the unifier behind
`rfl` walks into `Int.pow 2 64` and the fixture models and does not come
back, where the kernel-routed `decide` does.  The symbolic pins open the
checker by hand and close by the `_ok_iff` lemma of the acceptor they
land in.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Signal

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Signal
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-- Evaluate a closed call of one of the two checkers: open the checker
and the acceptors, decide every closed gate, read the fixture memories
and models with the `sys_simp` set, and finish with `sys_norm` if a read
is left.  The header says why this and not `rfl`. -/
macro "check_norm" : tactic =>
  `(tactic| (simp +decide only [check_rt_sigaction, check_rt_sigprocmask, check_write_oset,
              check_write_oset_copyins, check_one_write, check_ret_only_copyins, check_ret_only,
              clear_copyins, sig_copyin, Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq,
              access_ranges_eqb_eq, check_result.CheckOk.injEq, ne_eq, sys_simp, ↓reduceIte];
             first | done | sys_simp_pass +ground +decide -failIfUnchanged))

/-- Refute: `check_norm`, and the goal must be closed by it. -/
macro "check_refute" : tactic => `(tactic| (check_norm; done))

/-- Seven of the eight `oset` bytes writable at 8192: the eighth is not,
so the copy-out faults after the forward copy may have stored the first
seven — the partially writable range the spec's fixtures do not carry
(`wmem_oldset` is all eight, `mem_none` none).  Lean-only, and local:
this file mirrors no Rocq Cases file. -/
def wmem_oldset_short : word → Option byte := bytes_at 8192 (List.replicate 7 0)

/-- The short destination walks to nothing: the eighth byte is missing, so
the eight-byte read is `none`, as over `mem_none`.  A rewrite because the
ground pass leaves the missing byte's lookup stuck, as the fixture file
says of `wmem_oldset_walk`.
model: a closed `read_bytes_map` walk over the fixture, a rewrite for `check_norm`. -/
theorem wmem_oldset_short_walk :
    read_bytes_map wmem_oldset_short 8192 (Z_to_bv 64 NSIG_BYTES) = none := by decide

attribute [sys_simp] wmem_oldset_short_walk

section SigactionSize

/-! ## `rt_sigaction` (134): `sigsetsize` first

`if (sigsetsize != sizeof(sigset_t)) return -EINVAL;` is the first
statement of `SYSCALL_DEFINE4(rt_sigaction)` (kernel/signal.c:4647-4648,
Linux v6.18.46), ahead of the `act` copy-in (:4650-4651) and the `oact`
copy-out (:4657-4658) alike.  `sigsetsize` is a `size_t`, compared
full-width, so a register whose low half is 8 is the wrong size. -/

/-- Every size but 8 is -EINVAL on EVERY input and model — nothing else
has been looked at — with the model untouched and no event: 0, 16, and
2^32 + 8, whose low word is 8.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_bad_size_accepts_einval_on_every_input (i : SyscallInput) (m : Model) :
    check_rt_sigaction i 2 4096 0 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 2 4096 0 16 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 2 4096 0 4294967304 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies at a bad size, on every model: a success, the -EFAULT a
kernel reading `act` first would raise, -EINVAL beside a store, and
-EINVAL beside the 24-byte ledger of a copy-in that never ran (:4647
returns before :4650).
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_bad_size_rejects_the_lies (i : SyscallInput) (m : Model) :
    check_rt_sigaction i 2 4096 0 16 (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigaction i 2 4096 0 16 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject
    ∧ check_rt_sigaction i 2 4096 0 16 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) m
        = CheckReject
    ∧ check_rt_sigaction i 2 4096 0 16
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 24)]) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A bad size beats an unreadable `act` (nothing mapped at 8192): -EINVAL
is accepted and -EFAULT refused, because :4647 runs before :4650.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_bad_size_beats_unreadable_act (m : Model) :
    check_rt_sigaction (sigaction_in mem_none mem_none) 2 8192 0 0
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_none mem_none) 2 8192 0 0
        (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A bad size beats the `oact` decline and the SIGSEGV decline: both
calls are ANSWERED, with -EINVAL, where at size 8 each would be
`CheckUnmodeled`.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_bad_size_beats_the_declines (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 4096 0
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 11 4096 0 0
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

end SigactionSize

section SigactionOact

/-! ## A non-NULL `oact` declines, whatever else the call carries

`if (oact && copy_to_user(oact, &old_sa.sa, sizeof(old_sa.sa)))`
(kernel/signal.c:4657-4658, Linux v6.18.46) would report the stored
disposition, which the model does not carry.  The spec declines EARLIER
than the kernel copies: before `act` is read, so an unreadable `act`
beside a non-NULL `oact` is a decline and not -EFAULT.  The argument is on
`Signal.rt_sigaction_spec`. -/

/-- With `oact` set the checker declines on EVERY effect, input and model:
a query, an install with a query, SIGSEGV, SIGKILL, an out-of-range
signal, and an unreadable `act`.  Nothing a kernel answers here is
checked, -EINVAL and -EFAULT included.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_oact_declines_on_every_effect (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    check_rt_sigaction i 2 0 4096 8 eff m = CheckUnmodeled
    ∧ check_rt_sigaction i 2 4096 4096 8 eff m = CheckUnmodeled
    ∧ check_rt_sigaction i 11 0 4096 8 eff m = CheckUnmodeled
    ∧ check_rt_sigaction i 9 4096 4096 8 eff m = CheckUnmodeled
    ∧ check_rt_sigaction i 65 4096 4096 8 eff m = CheckUnmodeled
    ∧ check_rt_sigaction i 2 8192 4096 8 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigaction_oact_read_back_declined`, on the fixture: SIGINT
with a readable `act` and `oact` at the same page declines.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_oact_read_back_declines :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 4096 8
        (mkEffect 0 [] []) demo_model = CheckUnmodeled := by
  check_norm

/-- The control: the same call with `oact` NULL is answered, 0, so it is
the `oact` alone that declines.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_oact_control_is_answered :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect 0 [] []) demo_model = CheckOk demo_model [] := by
  check_norm

end SigactionOact

section SigactionNullAct

/-! ## `act == NULL`: a query with no read-back is answered by the signal number alone

With `act` NULL the copy-in at kernel/signal.c:4650 is skipped and
`do_sigaction(sig, NULL, NULL)` runs its guard: `if (!valid_signal(sig)
|| sig < 1 || (act && sig_kernel_only(sig))) return -EINVAL;` (:4317-4318,
Linux v6.18.46), whose third disjunct is off with `act` NULL — so SIGKILL
and SIGSTOP are VALID here — and then, under the lock, the SA_IMMUTABLE
test on the stored disposition (:4323-4326), whose -EINVAL the spec
argues no process the model runs can meet (the `rt_sigaction_spec`
header in `Sys/Kernel/Signal.lean`); so the answer with `act` NULL is
the guard's alone.  `valid_signal` is `sig <= _NSIG`
(include/linux/signal.h:272-275, Linux v6.18.46), `_NSIG` 64. -/

/-- Every valid signal is 0 on every input and model — SIGINT, SIGSEGV,
SIGKILL, SIGSTOP, SIGHUP and 64 — with the model untouched.
kernel: kernel/signal.c:rt_sigaction,do_sigaction; include/linux/signal.h:valid_signal@v6.18.46 -/
theorem check_rt_sigaction_null_act_valid_accepts_zero (i : SyscallInput) (m : Model) :
    check_rt_sigaction i 2 0 0 8 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 11 0 0 8 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 9 0 0 8 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 19 0 0 8 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 1 0 0 8 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 64 0 0 8 (mkEffect 0 [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Every invalid signal is -EINVAL on every input and model: 0, 65, and
2^32 - 1, which the `int` cast makes -1 and `valid_signal` refuses first,
after widening it to `unsigned long` (include/linux/signal.h:272-275,
Linux v6.18.46); the `sig < 1` disjunct behind it is never reached.
kernel: kernel/signal.c:rt_sigaction,do_sigaction; include/linux/signal.h:valid_signal@v6.18.46 -/
theorem check_rt_sigaction_null_act_invalid_accepts_einval (i : SyscallInput) (m : Model) :
    check_rt_sigaction i 0 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 65 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction i 4294967295 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies: -EINVAL on SIGSEGV and on SIGKILL — the kernel-only test is
gated on `act` — and a success on signal 0 and on 65.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_null_act_rejects_the_lies (i : SyscallInput) (m : Model) :
    check_rt_sigaction i 11 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigaction i 9 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigaction i 0 0 0 8 (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigaction i 65 0 0 8 (mkEffect 0 [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A query is NEVER declined, whatever the signal: with `act` NULL the
checker reaches no `CheckUnmodeled` arm, because the flags and the
accepted-signal list are read only on an install.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_null_act_never_declines (sig : word) (i : SyscallInput)
    (eff : SyscallEffect) (m : Model) :
    check_rt_sigaction i sig 0 0 8 eff m ≠ CheckUnmodeled := by
  unfold check_rt_sigaction
  have hss : (!(bv_eqb (8 : word) (Z_to_bv 64 8))) = false := by decide
  have hact : w_is0 (0 : word) = true := by decide
  simp only [hss, hact, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases sig_valid sig <;> simp only [Bool.false_eq_true, ↓reduceIte]
    <;> exact check_ret_only_no_unmodeled _ _ _ _

end SigactionNullAct

section SigactionCopyIn

/-! ## `copy_from_user(&new_sa.sa, act, sizeof(new_sa.sa))`: 24 bytes, all or nothing

`if (act && copy_from_user(&new_sa.sa, act, sizeof(new_sa.sa))) return
-EFAULT;` (kernel/signal.c:4650-4651, Linux v6.18.46) runs BEFORE
`do_sigaction` (:4653), so an unreadable `act` is -EFAULT ahead of the
guard's -EINVAL and ahead of every decline.  riscv's `struct sigaction`
is 24 bytes (handler, flags, mask); the model reads exactly that many. -/

/-- An unreadable `act` is -EFAULT on every model: nothing mapped, a
pointer below the mapped page, and a page 23 bytes long.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_unreadable_act_accepts_efault (m : Model) :
    check_rt_sigaction (sigaction_in mem_none mem_none) 2 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 8 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_short mem_none) 2 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies: a success and -EINVAL where the copy faulted, and a -EFAULT
that carries a copy-in ledger — rt_sigaction records no copy-in on any
path (the spec does not ledger its copy of `act`, kernel/signal.c:4650-4651,
Linux v6.18.46), so the ledger is a lie on the fault path exactly as on
the success path.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_unreadable_act_rejects_the_lies (m : Model) :
    check_rt_sigaction (sigaction_in mem_none mem_none) 2 4096 0 8 (mkEffect 0 [] []) m
        = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_short mem_none) 2 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_none mem_none) 2 4096 0 8
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(4096, 24)]) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- 24 bytes are enough: the zero disposition for SIGINT is accepted, and
-EFAULT there is refused.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_24_bytes_are_enough (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- -EFAULT beats the guard: an unreadable `act` for SIGKILL and for
signal 65 is -EFAULT, and -EINVAL is refused, because :4650 runs before
:4653.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_efault_beats_the_guard (m : Model) :
    check_rt_sigaction (sigaction_in mem_none mem_none) 9 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_none mem_none) 9 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_none mem_none) 65 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- -EFAULT beats the declines: SIGSEGV with an unreadable `act`, and
SIGINT with SA_RESTART on a page one byte short, are ANSWERED with
-EFAULT where a readable `act` would decline.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem check_rt_sigaction_efault_beats_the_declines (m : Model) :
    check_rt_sigaction (sigaction_in mem_none mem_none) 11 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_restart_short mem_none) 2 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

end SigactionCopyIn

section SigactionGuard

/-! ## `do_sigaction`'s guard on an install

`if (!valid_signal(sig) || sig < 1 || (act && sig_kernel_only(sig))) return
-EINVAL;` (kernel/signal.c:4317-4318, Linux v6.18.46), reached from :4653
with `act` set, so `sig_kernel_only` — SIGKILL and SIGSTOP
(include/linux/signal.h:445) — is now live, and it fires before the flags
are looked at. -/

/-- Installing on SIGKILL or SIGSTOP is -EINVAL on every model, with a
zero disposition and with SA_RESTART alike — the guard runs before the
flags — and the same for signal 65 with SA_RESTART.
kernel: kernel/signal.c:rt_sigaction,do_sigaction; include/linux/signal.h:sig_kernel_only@v6.18.46 -/
theorem check_rt_sigaction_kernel_only_install_accepts_einval (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 9 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 19 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_restart mem_none) 9 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_restart mem_none) 65 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- An out-of-range signal with a readable `act` is -EINVAL on every model:
0, 65, -1 and INT_MIN after the `int` cast.
kernel: kernel/signal.c:rt_sigaction,do_sigaction; include/linux/signal.h:valid_signal@v6.18.46 -/
theorem check_rt_sigaction_out_of_range_install_accepts_einval (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 0 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 65 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 4294967295 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2147483648 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The lies: a success installing on SIGKILL, on SIGSTOP, on signal 0
and on 65, each refused.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_guard_rejects_success (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 9 4096 0 8
        (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 19 4096 0 8
        (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 0 4096 0 8
        (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 65 4096 0 8
        (mkEffect 0 [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end SigactionGuard

section SigactionFlags

/-! ## The flags: an allowlist, and a decline outside it

Past the guard the kernel masks the flags word to `UAPI_SA_FLAGS`
(`act->sa.sa_flags &= UAPI_SA_FLAGS`, kernel/signal.c:4341-4342, Linux
v6.18.46), strips SIGKILL and SIGSTOP from `sa_mask` (`sigdelsetmask`,
:4351-4352) and installs the result (`*k = *act`, :4353): a bit outside
`UAPI_SA_FLAGS` is silently cleared and the call returns 0 (:4377), never
refused.  The model declines, rather than installs, any flag it does not
interpret: `Signal.sa_flags_ok` is the allowlist,
`Signal.sa_flags_accepted` its mask, and the reason each bit is in or out
is on the spec.  SA_RESTART (0x10000000) is out; SA_NOCLDSTOP,
SA_NOCLDWAIT, SA_SIGINFO, SA_EXPOSE_TAGBITS, SA_ONSTACK, SA_NODEFER and
SA_RESETHAND (the allowlist fixture, 0xC8000807) are in; bit 32 of
`sa_flags` — an `unsigned long` on riscv64, though every flag constant
fits 32 bits — is out, and is a bit Linux would clear and answer 0 to
where the model answers `unmodeled`. -/

/-- SA_RESTART on SIGINT declines on every effect and model, and so does
a flags word with bit 32 set.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_flags_outside_the_allowlist_decline (eff : SyscallEffect) (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_restart mem_none) 2 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_bit32 mem_none) 2 4096 0 8 eff m
        = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The whole allowlist at once on SIGINT is accepted, 0, and -EINVAL
there is refused.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_allowlist_accepts_zero (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_allowlist mem_none) 2 4096 0 8
        (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_allowlist mem_none) 2 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

end SigactionFlags

section SigactionAccepted

/-! ## The accepted signals: 0, with nothing recorded

An install on a signal the model's runs never deliver
(`Signal.sigaction_accepted`) is answered 0 (`return 0`,
kernel/signal.c:4660, Linux v6.18.46), the model untouched: the checker
records no disposition.  Every other signal declines, because a later
delivery would read the disposition the model does not hold. -/

/-- Rocq's `rt_sigaction_sigint_accepted`: SIGINT with the zero
disposition on `demo_model` is `CheckOk demo_model []`, and SIGTERM the
same.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_sigint_accepts_zero :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect 0 [] []) demo_model = CheckOk demo_model []
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 15 4096 0 8
        (mkEffect 0 [] []) demo_model = CheckOk demo_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and on every model: the install reads nothing from the model and
changes nothing in it.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_sigint_accepts_zero_on_every_model (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect 0 [] []) m = CheckOk m [] := by
  check_norm

/-- The lies on an accepted install: -EINVAL, a success beside a store at
`act`, a success carrying a copy-in ledger, and a success claiming a
zero-fill.  rt_sigaction records nothing, so every ledger must be empty.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_sigint_rejects_the_lies (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (mkEffect 0 [(4096, [0])] []) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 24)]) m = CheckReject
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 2 4096 0 8
        (SyscallEffect.mkEffectU 0 [] [(4096, 24)] [] [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Every other signal declines on every effect and model, with the zero
disposition: the four Rocq examples — SIGSEGV (11), SIGPIPE (13), SIGCHLD
(17), SIGABRT (6) — and the rest of the class: SIGHUP (1), SIGILL (4),
SIGTRAP (5), SIGBUS (7), SIGXFSZ (25), SIGWINCH (28), the first real-time
signal (32) and the last (64).
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_declined_signals (eff : SyscallEffect) (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 11 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 13 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 17 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 6 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 1 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 4 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 5 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 7 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 25 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 28 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 32 4096 0 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 64 4096 0 8 eff m
        = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- SIGCHLD with SA_NOCLDSTOP — an allowlisted flag on a declined signal —
still declines: the flags gate is passed and the signal's arm is what
declines.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem check_rt_sigaction_sigchld_nocldstop_declines (eff : SyscallEffect) (m : Model) :
    check_rt_sigaction
        (sigaction_in (bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
                                      0, 0, 0, 0, 0, 0, 0, 0]) mem_none)
        17 4096 0 8 eff m = CheckUnmodeled := by
  check_norm

end SigactionAccepted

section ProcmaskSize

/-! ## `rt_sigprocmask` (135): `sigsetsize` first

`if (sigsetsize != sizeof(sigset_t)) return -EINVAL;` (kernel/signal.c:3334-3335,
Linux v6.18.46) is the first statement of `SYSCALL_DEFINE4(rt_sigprocmask)`,
ahead of the `nset` copy-in (:3340) and the `oset` copy-out (:3350), and
`sigsetsize` is a `size_t` compared full-width. -/

/-- Every size but 8 is -EINVAL on EVERY input and model, the model
untouched and nothing recorded: 0, 7, 9, 128 and 2^32 + 8.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_size_accepts_einval_on_every_input (i : SyscallInput)
    (m : Model) :
    check_rt_sigprocmask i 1 4096 0 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask i 1 4096 0 7 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask i 1 4096 0 9 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask i 1 4096 0 128 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask i 1 4096 0 4294967304 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The size third of Rocq's `rt_sigprocmask_how_truncates_size_does_not`:
`sigsetsize` is a `size_t`, so a register of 2^32 + 8 is not 8 and the
call is -EINVAL, where a checker narrowing it to `int` would install.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_size_is_not_narrowed (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 0 4294967304
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 0 4294967304
        (with_copyins sig_copyin (mkEffect 0 [] [])) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The lies at a bad size, on every model: a success, -EFAULT, and
-EINVAL carrying the ledger the copy-in would have left — nothing was
copied, so the ledger is empty.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_size_rejects_the_lies (i : SyscallInput) (m : Model) :
    check_rt_sigprocmask i 1 4096 0 128 (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigprocmask i 1 4096 0 128 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject
    ∧ check_rt_sigprocmask i 0 4096 0 0 (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_bad_size_beats_unreadable_set`: a bad size with
nothing mapped at `nset` is -EINVAL, and -EFAULT is refused, since :3334
runs before :3340.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_size_beats_unreadable_set (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 0
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 0
        (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_bad_size_beats_oldset_decline`: a bad size with
an unwritable `oset` is ANSWERED, -EINVAL, where at size 8 the same call
declines.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_size_beats_oldset_decline (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 0 8192 0
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 0 8192 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The size gate is not nested under `if (nset)`: with BOTH pointers NULL
a wrong size is still -EINVAL on every input and model, and the 0 that
the null-set path would answer is refused.  kernel/signal.c:3334-3335
(Linux v6.18.46) precedes the `if (nset)` at :3339 and the `if (oset)` at
:3349.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_size_with_no_sets (i : SyscallInput) (m : Model) :
    check_rt_sigprocmask i 1 0 0 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask i 1 0 0 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_rt_sigprocmask i 1 0 0 7 (mkEffect 0 [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

end ProcmaskSize

section ProcmaskNullSet

/-! ## `nset == NULL`: `how` is never looked at

`if (nset)` (kernel/signal.c:3339, Linux v6.18.46) encloses the copy-in,
the `sigdelsetmask` and the `sigprocmask` call that tests `how`
(:3340-3346), so a NULL set skips all three and the call is a pure query
of the mask: 0 with `oset` NULL too, the eight bytes otherwise. -/

/-- A NULL set with a NULL `oset` is 0 on every `how`, input and model,
the model untouched: nothing is read and nothing installed.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_null_set_ignores_how (how : word) (i : SyscallInput) (m : Model) :
    check_rt_sigprocmask i how 0 0 8 (mkEffect 0 [] []) m = CheckOk m [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_null_set_ignores_how`, on the fixture, with the
wild values beside it: 999, 3, -1 and INT64_MAX.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_null_set_ignores_how_on_the_fixture :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 999 0 0 8 (mkEffect 0 [] [])
        demo_model = CheckOk demo_model []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 3 0 0 8 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 4294967295 0 0 8
        (mkEffect 0 [] []) demo_model = CheckOk demo_model []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 9223372036854775807 0 0 8
        (mkEffect 0 [] []) demo_model = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The lies: -EINVAL on a bad `how` with a NULL set — the test at :3253
is never reached — a success beside a store, and a success carrying a
copy-in ledger.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_null_set_rejects_the_lies (i : SyscallInput) (m : Model) :
    check_rt_sigprocmask i 3 0 0 8 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigprocmask i 0 0 0 8 (mkEffect 0 [(4096, [0])] []) m = CheckReject
    ∧ check_rt_sigprocmask i 0 0 0 8 (with_copyins sig_copyin (mkEffect 0 [] [])) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

end ProcmaskNullSet

section ProcmaskQuery

/-! ## The pure query: `oset` gets the mask, eight bytes, all or nothing

`old_set = current->blocked` (kernel/signal.c:3337, Linux v6.18.46) and
`if (oset) { if (copy_to_user(oset, &old_set, sizeof(sigset_t))) return
-EFAULT; }` (:3349-3352).  `copy_to_user` is -EFAULT outright when
`access_ok` refuses the range (`__access_ok`,
include/asm-generic/access_ok.h:31-41), which is how an `oset` ending
past `TASK_SIZE` is answered; a range inside the address space whose
eight bytes are not all writable DECLINES, because riscv's
`raw_copy_to_user` copies forward and may have stored the leading bytes
before faulting, a partial store the model does not represent. -/

/-- On EVERY model the query is accepted with the model's own mask as
eight little-endian bytes at `oset`, whatever `how` holds, the model
untouched.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_query_accepts_the_mask_on_every_model (how : word) (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) how 0 8192 8
        (mkEffect 0 [(8192, Z_to_le_bytes 8 (bv_unsigned (m_sigmask m)))] []) m
      = CheckOk m [] := by
  unfold check_rt_sigprocmask check_write_oset
  simp +decide only [sigprocmask_in, wmem_oldset_walk, ↓reduceIte]
  exact (check_one_write_ok_iff _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq's `rt_sigprocmask_oldset_reports_entry_mask`: over the blocked
fixture the eight bytes are 6, 0, 1, 0, 0, 0, 0, 0 — 0x10006
little-endian.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_reports_entry_mask :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 0 0 8192 8
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked
      = CheckOk sig_model_blocked [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_oldset_impossible_mask_rejected`: a mask the
process could not have had — {SIGKILL, SIGSTOP}, 0x40100 — is refused,
by the byte-for-byte equality against the mask the model carries.
kernel: kernel/signal.c:rt_sigprocmask,set_current_blocked@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_impossible_mask_rejected :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 0 0 8192 8
        (mkEffect 0 [(8192, [0, 1, 4, 0, 0, 0, 0, 0])] []) sig_model_blocked
      = CheckReject := by
  check_norm

/-- A query owes exactly its eight bytes: a 0 that wrote nothing, -EINVAL,
the right bytes at the wrong address, seven bytes, a return of 1 beside
the right store, and the right store beside a copy-in ledger are all
refused.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_query_rejects_the_lies :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 0 [] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 0 [(8193, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0])] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 1 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (SyscallEffect.mkEffectU 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] [] [] [] [(8192, 8)])
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The store owes an otherwise EMPTY effect: the right eight bytes beside
a zero-fill, an unmap, a copy, a ninth byte or a second store are all
refused — `rt_sigprocmask`'s copy-out at kernel/signal.c:3350 (Linux
v6.18.46) is the only thing the query does to memory, and
`check_one_write` matches the other four ledgers empty rather than
ignoring them.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_query_store_admits_nothing_beside_it :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (SyscallEffect.mkEffectU 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] [(8192, 8)] [] [] [])
        sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (SyscallEffect.mkEffectU 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] [] [(8192, 4096)] [] [])
        sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (SyscallEffect.mkEffectU 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] [] []
          [MemCopy.mkCopy 8192 8192 8] [])
        sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0, 0])] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 8192 8
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0]), (8200, [0])] []) sig_model_blocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A query whose `oset` is not wholly writable — nothing writable at
8192 — DECLINES on every effect and model: the -EFAULT of :3351 is
certain, but the bytes the forward copy stored before it faulted are
not, and the model represents no partial store (the section header).
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_query_unwritable_oset_declines (eff : SyscallEffect) (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 0 8192 8 eff m = CheckUnmodeled := by
  check_norm

/-- The same decline with SEVEN of the eight bytes writable at 8192, on
the query and after an install: the walk is all eight bytes or nothing,
so a checker that walked seven, or looked at the first byte alone, would
have accepted a store here that the copy-out (:3350-3351) faults on.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_partly_writable_oset_declines (eff : SyscallEffect) (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset_short) 1 0 8192 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset_short) 1 4096 8192 8
        eff sig_model_blocked = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A query whose eight bytes run past `TASK_SIZE` — `oset` = 2^64 - 8 —
is -EFAULT outright on every model, `access_ok` refusing the range
before any byte is looked at; and a success there is refused.
kernel: kernel/signal.c:rt_sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_rt_sigprocmask_query_over_task_size_is_efault (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 0 (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (mkEffect 0 [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The `access_ok` edge, where an off-by-one in the port's `≤` would hide
at 2^64 - 8: `oset = TASK_SIZE - 8` (0x7FFFFFFFFFF8) is the LAST address
eight bytes fit under `TASK_SIZE_MAX` (`__access_ok`,
include/asm-generic/access_ok.h:31-41, Linux v6.18.46: `ptr <= limit -
size`, with `TASK_SIZE_MAX = TASK_SIZE` at :15-16 and 2^47 on Sv48), so
the walk is reached — declined on a map with no bytes there, and the
entry mask stored on a writable one; `oset = TASK_SIZE - 7` is one past
it, -EFAULT on every model with success refused.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oset_at_the_task_size_edge (eff : SyscallEffect) (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 0 140737488355320 8 eff m
        = CheckUnmodeled
    ∧ check_rt_sigprocmask
        (sigprocmask_in mem_none (bytes_at 140737488355320 [0, 0, 0, 0, 0, 0, 0, 0]))
        1 0 140737488355320 8
        (mkEffect 0 [(140737488355320, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked
        = CheckOk sig_model_blocked []
    ∧ check_rt_sigprocmask
        (sigprocmask_in mem_none (bytes_at 140737488355321 [0, 0, 0, 0, 0, 0, 0, 0]))
        1 0 140737488355321 8 (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask
        (sigprocmask_in mem_none (bytes_at 140737488355321 [0, 0, 0, 0, 0, 0, 0, 0]))
        1 0 140737488355321 8
        (mkEffect 0 [(140737488355321, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end ProcmaskQuery

section ProcmaskCopyIn

/-! ## `copy_from_user(&new_set, nset, sizeof(sigset_t))`: eight bytes, all or nothing

Inside `if (nset)`, `if (copy_from_user(&new_set, nset, sizeof(sigset_t)))
return -EFAULT;` (kernel/signal.c:3340-3341, Linux v6.18.46) runs before
`sigprocmask` (:3344), so an unreadable set is -EFAULT ahead of a bad
`how`'s -EINVAL, and a failed copy records nothing: this -EFAULT carries
an EMPTY ledger, where the -EFAULT of the copy-out (`ProcmaskAfterInstall`)
carries the eight bytes it had already read. -/

/-- An unreadable set is -EFAULT on every model: nothing mapped at 8192,
a page seven bytes long, and a pointer below the mapped page.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unreadable_set_accepts_efault (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_short mem_none) 1 4096 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 1 8 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies: a success and -EINVAL where the copy faulted.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unreadable_set_rejects_the_lies (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 8 (mkEffect 0 [] []) m
        = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_short mem_none) 1 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_efault_beats_bad_how`: an unreadable set with
`how` = 3 is -EFAULT, because :3340 runs before `sigprocmask`'s `switch`.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_efault_beats_bad_how (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 3 8192 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  check_norm

/-- …and its -EINVAL is refused, bare and ledgered alike.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_efault_beats_bad_how_einval_rejected (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 3 8192 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 3 8192 0 8
        (with_copyins [(8192, 8)] (mkEffect (errno_ret EINVAL) [] [])) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- All three at once — an invalid `how`, an unreadable `nset` and a
writable `oset`: the copy-in's bare -EFAULT wins, nothing is written and
nothing is ledgered.  kernel/signal.c:3340-3341 (Linux v6.18.46) returns
before the `switch` at :3253-3264 and before the `copy_to_user` at :3350;
the pairs are pinned above and in `ProcmaskAfterInstall`, this is the
triple.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_efault_beats_bad_how_and_oset (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 3 4096 8192 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 3 4096 8192 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 3 4096 8192 8
        (mkEffect (errno_ret EFAULT) [(8192, [0, 0, 0, 0, 0, 0, 0, 0])] []) m = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 3 4096 8192 8
        (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_efault_records_no_copyin`: the copy-in's
-EFAULT carries an EMPTY ledger, on every model — the bare -EFAULT is
accepted and the same -EFAULT claiming the eight bytes were read is
refused.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_efault_records_no_copyin (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 8192 0 8
        (with_copyins [(8192, 8)] (mkEffect (errno_ret EFAULT) [] [])) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- An unreadable set beside a writable `oset` is -EFAULT with NOTHING
written — the copy-out at :3350 is never reached — so the same -EFAULT
beside the mask's eight bytes is refused.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unreadable_set_writes_nothing (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 4096 8192 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none wmem_oldset) 1 4096 8192 8
        (mkEffect (errno_ret EFAULT) [(8192, Z_to_le_bytes 8 (bv_unsigned (m_sigmask m)))] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

end ProcmaskCopyIn

section ProcmaskBadHow

/-! ## `sigprocmask`'s `switch (how)`: -EINVAL AFTER the copy, so the ledger is carried

`sigprocmask` (kernel/signal.c:3244-3269, Linux v6.18.46) is called at
:3344 with the set already copied; its `switch (how)` (:3253-3265) takes
SIG_BLOCK, SIG_UNBLOCK and SIG_SETMASK and answers `default: return
-EINVAL;` (:3263-3264) for anything else, `__set_current_blocked` (:3267)
never running.  The model records the eight-byte read whether or not the
`how` is good, so this -EINVAL carries the ledger the size test's -EINVAL
does not: two -EINVALs the checker tells apart by the ledger alone. -/

/-- `how` = 3 with a readable set is -EINVAL carrying the eight-byte
ledger, on every model, the model untouched; so are -1 and INT_MAX.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_how_accepts_einval_with_ledger (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 4294967295 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 2147483647 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies: -EINVAL WITHOUT the ledger, a ledgered success, and the
right -EINVAL beside a ledger of nine bytes.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_how_rejects_the_lies (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) m = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (with_copyins [(4096, 9)] (mkEffect (errno_ret EINVAL) [] [])) m = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_copyins_separate_the_two_einvals`, all four
conjuncts: the size test's -EINVAL is bare and the bad-`how` -EINVAL is
ledgered, and each with the other's ledger is refused.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_two_einvals_differ_in_the_ledger :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 0
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model
        = CheckOk demo_model []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 0
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A bad `how` with a writable `oset` is the same ledgered -EINVAL with
NOTHING written — `sigprocmask` returned before the copy-out at :3350 —
and the same -EINVAL beside the mask's eight bytes is refused.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_bad_how_writes_nothing :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv wmem_oldset) 3 4096 8192 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model_blocked
        = CheckOk sig_model_blocked []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv wmem_oldset) 3 4096 8192 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The two errors before the copy-out are ANSWERED beside an `oset` that
would DECLINE: a bad `how` with nothing writable at 8192 is the ledgered
-EINVAL (`sigprocmask` returned at :3264 before :3350 was reached), and
an unreadable `nset` with the same `oset` is the bare -EFAULT (:3341
before :3350), both on every model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_errors_beat_the_oset_decline (m : Model) :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 3 4096 8192 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_none mem_none) 1 4096 8192 8
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

end ProcmaskBadHow

section ProcmaskInstall

/-! ## The install: strip, combine, store

`sigdelsetmask(&new_set, sigmask(SIGKILL) | sigmask(SIGSTOP))`
(kernel/signal.c:3342, Linux v6.18.46) STRIPS the two before
`sigprocmask` combines: `sigorsets` for SIG_BLOCK (:3254-3255),
`sigandnsets` for SIG_UNBLOCK (:3257-3258), assignment for SIG_SETMASK
(:3260-3261); then the store, `__set_current_blocked`
(kernel/signal.c:3220-3234, Linux v6.18.46) called from `sigprocmask` at
:3267, and `return 0` (:3268, :3354).  The new model is the checker's
OUTPUT: each pin states it. -/

/-- Rocq's `rt_sigprocmask_block_sigsegv_accepted`: SIG_BLOCK {SIGSEGV} on
`demo_model` installs 0x400, returns 0 with the eight-byte ledger.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_block_sigsegv_accepts_the_install :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model
      = CheckOk (with_sigmask 1024 demo_model) [] := by
  check_norm

/-- The lies on an install: -EINVAL with the ledger, a success WITHOUT the
ledger, a ledger of nine bytes, the right eight at the wrong address, and
a success carrying a zero-fill.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_install_rejects_the_lies :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins [(4096, 9)] (mkEffect 0 [] [])) demo_model = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins [(4097, 8)] (mkEffect 0 [] [])) demo_model = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (SyscallEffect.mkEffectU 0 [] [(4096, 8)] [] [] [(4096, 8)]) demo_model
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_success_admits_no_write`: WRITING NOTHING IS AN
OBLIGATION — an install claiming a one-byte store at the set's own
address is refused, so a target cannot smuggle a write through a call
whose only visible answer is 0.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_install_rejects_a_write :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [(4096, [0])] [])) demo_model = CheckReject := by
  check_norm

/-- Rocq's `rt_sigprocmask_kill_stop_stripped_not_refused`: SIG_SETMASK of
0x40105 on the blocked fixture installs 0x5 — SIGKILL and SIGSTOP
stripped, not -EINVAL — and the -EINVAL is refused.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask; include/linux/signal.h:sigdelsetmask@v6.18.46 -/
theorem check_rt_sigprocmask_kill_stop_stripped_not_refused :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 2 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      = CheckOk (with_sigmask 5 sig_model_blocked) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 2 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model_blocked
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_block_unions`: SIG_BLOCK of the same set on the
blocked fixture is 0x10006 ∪ 0x5 = 0x10007.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_block_unions :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      = CheckOk (with_sigmask 65543 sig_model_blocked) [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_unblock_clears`: SIG_UNBLOCK of the same set is
0x10006 ∖ 0x5 = 0x10002.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_clears :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      = CheckOk (with_sigmask 65538 sig_model_blocked) [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_unblock_is_not_block`: the UNBLOCK verdict is not
the BLOCK's post-state, and not the SETMASK's either — three `how`s, three
masks.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_is_not_block :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      ≠ CheckOk (with_sigmask 65543 sig_model_blocked) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      ≠ CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  refine ⟨?_, ?_⟩ <;> check_refute

/-- …and the BLOCK verdict is not the SETMASK's: SIG_BLOCK keeps the entry
bits where SIG_SETMASK drops them.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_block_is_not_setmask :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
      ≠ CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  check_refute

/-- SIG_SETMASK of every bit installs everything but the two: 2^64 - 1
minus 0x40100.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask; include/linux/signal.h:sigdelsetmask@v6.18.46 -/
theorem check_rt_sigprocmask_setmask_all_bits :
    check_rt_sigprocmask (sigprocmask_in (bytes_at 4096 (List.replicate 8 255)) mem_none) 2 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model
      = CheckOk (with_sigmask (Z_to_bv 64 (2 ^ 64 - 1 - 262400)) demo_model) [] := by
  check_norm

end ProcmaskInstall

section ProcmaskAfterInstall

/-! ## The copy-out after an install: the ENTRY mask, last, with no rollback

`old_set` was snapshotted at kernel/signal.c:3337 (Linux v6.18.46), before
`sigprocmask` ran, and is what `copy_to_user` writes at :3350; a fault
there returns -EFAULT with the new mask already installed (:3351), and
that -EFAULT carries the copy-in's ledger. -/

/-- Rocq's `rt_sigprocmask_oldset_snapshot_precedes_install`: `oset` gets
0x10006, the installed mask is the stripped 0x5, the ledger carries the
eight bytes.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_snapshot_precedes_install :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096 8192 8
        (with_copyins sig_copyin (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked
      = CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  check_norm

/-- `oset == nset`: the same eight bytes are read at kernel/signal.c:3340
(Linux v6.18.46) and written at :3350, in that order, so the OLD mask
lands over the new set's bytes and the install is still the stripped
0x5; the ledger names the read, the write names the store, both at the
one address.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oset_aliasing_nset_gets_the_old_mask :
    check_rt_sigprocmask
        (sigprocmask_in mem_sigset_kill_stop (bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0]))
        2 4096 4096 8
        (with_copyins sig_copyin (mkEffect 0 [(4096, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked
      = CheckOk (with_sigmask 5 sig_model_blocked) []
    ∧ check_rt_sigprocmask
        (sigprocmask_in mem_sigset_kill_stop (bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0]))
        2 4096 4096 8
        (with_copyins sig_copyin (mkEffect 0 [(4096, [5, 0, 0, 0, 0, 0, 0, 0])] []))
        sig_model_blocked
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_oldset_is_not_the_new_mask`: a kernel reporting
the INSTALLED mask instead — the post-install snapshot a
reimplementation makes — is refused.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_is_not_the_new_mask :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096 8192 8
        (with_copyins sig_copyin (mkEffect 0 [(8192, [5, 0, 0, 0, 0, 0, 0, 0])] []))
        sig_model_blocked = CheckReject := by
  check_norm

/-- The other lies after an install with `oset`: a success that reported
no mask, the right store without the ledger, -EINVAL, and the right
store beside a ledger of nine bytes or at the wrong address — the
ledger beside a store is compared whole, as it is beside a bare return.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_install_with_oset_rejects_the_lies :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 0 4096 8192 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 0 4096 8192 8
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 0 4096 8192 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 0 4096 8192 8
        (with_copyins [(4096, 9)] (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 0 4096 8192 8
        (with_copyins [(4097, 8)] (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `rt_sigprocmask_oldset_efault_still_installs`, THE NO-ROLLBACK
CORNER: an `oset` whose eight bytes end past `TASK_SIZE` returns -EFAULT
WITH THE NEW MASK INSTALLED and the copy-in recorded.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_efault_still_installs :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096
        (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) sig_model_blocked
      = CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_oldset_over_task_size_never_succeeds`: a success
there would owe a write `__access_ok` forbids, and is refused; so is the
-EFAULT without its ledger, and the -EFAULT with a nine-byte one.
kernel: kernel/signal.c:rt_sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_over_task_size_never_succeeds :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096
        (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096
        (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096
        (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (with_copyins [(4096, 9)] (mkEffect (errno_ret EFAULT) [] [])) sig_model_blocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- …and a rollback — -EFAULT with the entry mask kept — is not the verdict:
the model the checker returns has 0x5 installed, not 0x10006.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_oldset_efault_rollback_refuted :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop wmem_oldset) 2 4096
        (Z_to_bv 64 (2 ^ 64 - 8)) 8
        (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) sig_model_blocked
      ≠ CheckOk sig_model_blocked [] := by
  check_refute

/-- An `oset` below `TASK_SIZE` that is not wholly writable DECLINES after
the install, on every effect: SIG_UNBLOCK on the blocked fixture, and
Rocq's `rt_sigprocmask_oldset_unmodeled` — SIG_BLOCK {SIGSEGV} on
`demo_model` with nothing writable at 8192.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_install_with_unwritable_oset_declines (eff : SyscallEffect) :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_kill_stop mem_none) 1 4096 8192 8 eff
        sig_model_blocked = CheckUnmodeled
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 8192 8 eff
        demo_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

end ProcmaskAfterInstall

section ProcmaskAbort

/-! ## Unblocking a pending SIGABRT delivers it

`__set_task_blocked` (kernel/signal.c:3195-3205, Linux v6.18.46), reached
from `__set_current_blocked` (:3220-3234, which returns early at
:3228-3229 when the mask is unchanged — harmless here, since an unchanged
mask unblocks nothing), stores the NEW mask (:3203) and calls
`recalc_sigpending` (:177-183), whose `recalc_sigpending_tsk` (:159-175)
finds the SIGABRT that `tkill` left pending while it was blocked; on the
way back to user space `get_signal` delivers it and the default action
kills.  `Signal.sigmask_deliver_model` reads two things and nothing else:
the model's SIGABRT pending bit and bit 5 of the NEW mask — so the
delivery is keyed on the mask installed, not on `how`, and the pins
below vary both.  The abort-terminal declaration gates the pending bit's
only writer, `tkill`, not this arm; the return is still 0 with its
ledger, and `Run.sstep_killed` discards it. -/

/-- Rocq's `rt_sigprocmask_unblock_pending_sigabrt_kills`: SIG_UNBLOCK
{SIGABRT} on the pending, blocked fixture returns 0 with its ledger, and
the model is `with_killed 6` over the install.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_pending_sigabrt_kills :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      = CheckOk (with_killed 6 (with_sigmask 0 (with_sigabrt_pending abort_model_blocked))) [] := by
  check_norm

/-- Rocq's `rt_sigprocmask_unblock_nothing_pending_lives`: with nothing
pending the same call is the plain install, the control for the one
above.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_nothing_pending_lives :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_blocked
      = CheckOk (with_sigmask 0 abort_model_blocked) [] := by
  check_norm

/-- A pending SIGABRT that STAYS blocked is not delivered: SIG_BLOCK
{SIGSEGV} on top installs 0x420 and the process lives.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_pending_still_blocked_lives :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 0 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      = CheckOk (with_sigmask 1056 (with_sigabrt_pending abort_model_blocked)) [] := by
  check_norm

/-- The delivery is keyed on the mask INSTALLED, not on `how` or on the
set named: SIG_SETMASK with the empty set unblocks the pending SIGABRT
and kills just as SIG_UNBLOCK {SIGABRT} does, and SIG_UNBLOCK {SIGSEGV}
leaves SIGABRT blocked (0x20 stays 0x20) and the process lives — a
checker keyed on `how` alone would answer both wrongly, and one that also
asked whether SIGABRT was in the set would still get the first wrong.
`recalc_sigpending_tsk` tests `PENDING(&t->pending,
&t->blocked)` (kernel/signal.c:162, Linux v6.18.46) against the mask
`__set_task_blocked` stored at :3203, whatever `sigprocmask` did to build it.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_delivery_follows_the_new_mask :
    check_rt_sigprocmask (sigprocmask_in (bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0]) mem_none)
        2 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      = CheckOk (with_killed 6 (with_sigmask 0 (with_sigabrt_pending abort_model_blocked))) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      = CheckOk (with_sigmask 32 (with_sigabrt_pending abort_model_blocked)) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      ≠ CheckOk (with_killed 6 (with_sigmask 32 (with_sigabrt_pending abort_model_blocked))) [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The lies about the kill the effect can carry: -EINVAL on the restore,
and a return of 6 — the death is not reported through a0.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_pending_sigabrt_rejects_the_lies :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] []))
        (with_sigabrt_pending abort_model_blocked) = CheckReject
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 6 [] []))
        (with_sigabrt_pending abort_model_blocked) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The lies about the kill the MODEL would carry, refuted on the verdict:
an install that did not die, and a death that did not install.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_unblock_pending_sigabrt_model_lies_refuted :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      ≠ CheckOk (with_sigmask 0 (with_sigabrt_pending abort_model_blocked)) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigabrt_pending abort_model_blocked)
      ≠ CheckOk (with_killed 6 (with_sigabrt_pending abort_model_blocked)) [] := by
  refine ⟨?_, ?_⟩ <;> check_refute

/-- Rocq's `one_sided_unblock_kills`: the delivery reads the pending bit
and the new mask, NOT the declaration — on `one_sided_model`, SIGABRT
pending with the abort terminal undeclared, SIG_UNBLOCK {SIGABRT} names
the killed model, and the plain install a checker gating the delivery on
`m_abort_terminal` would answer is refuted.  The declaration gates
`tkill`, the pending bit's only writer, not this arm.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_one_sided_unblock_kills :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) one_sided_model
      = CheckOk (with_killed 6 (with_sigmask 0 one_sided_model)) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) one_sided_model
      ≠ CheckOk (with_sigmask 0 one_sided_model) [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The rt_sigprocmask conjunct of Rocq's `decl_off_frame_hypotheses_inhabited`:
with the declaration off AND nothing pending, the same call is the plain
install on `abort_model_undeclared`, and the kill is refuted — the
control for the one above, from the model with both bits clear.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem check_rt_sigprocmask_declaration_off_nothing_pending_installs :
    check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_undeclared
      = CheckOk (with_sigmask 0 abort_model_undeclared) []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigabrt mem_none) 1 4096 0 8
        (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_undeclared
      ≠ CheckOk (with_killed 6 (with_sigmask 0 abort_model_undeclared)) [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

end ProcmaskAbort

section TheWitnesses

/-! ## The witnesses: which outcome each names

A witness is one outcome the spec admits, computed from the arguments,
the input and the model with no effect to check; `rt_sigaction_witness_ok`,
`write_oset_witness_ok` and `rt_sigprocmask_witness_ok` say each one is
admitted, which is the receptiveness field of the arm the registration
step builds.  What that lemma cannot say is WHICH outcome the witness
names, so each pin below names it on a fixture: the kernel's return on
the path the model answers, `Unmodeled` on the path it declines.  A
witness that named a different admitted outcome — there is none, both
specs are deterministic where they answer, but a lemma does not know that
— would pass `_ok` and fail here. -/

/-- Evaluate a closed witness: open it, decide every closed gate, read the
fixture memories and models with the `sys_simp` set, and finish with
`sys_norm` if a read is left.  The header says why this and not `rfl`. -/
macro "witness_norm" : tactic =>
  `(tactic| (simp +decide only [rt_sigaction_witness, rt_sigprocmask_witness,
              write_oset_witness, ret_outcome, sig_copyin, sys_simp, ↓reduceIte];
             first | done | sys_simp_pass +ground +decide -failIfUnchanged))

/-- rt_sigaction: the size test on every input and model, then `oact`.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_witness_size_then_oact (i : SyscallInput) (m : Model) :
    rt_sigaction_witness 2 4096 0 16 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ rt_sigaction_witness 2 4096 4096 8 i m = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- rt_sigaction with `act` NULL: 0 on a valid signal, SIGKILL included,
-EINVAL on 65, on every input and model.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_witness_null_act (i : SyscallInput) (m : Model) :
    rt_sigaction_witness 9 0 0 8 i m = Ok (mkEffect 0 [] []) m []
    ∧ rt_sigaction_witness 65 0 0 8 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- rt_sigaction on an install: -EFAULT on an unreadable `act`, -EINVAL on
SIGKILL, `Unmodeled` on SA_RESTART, 0 on SIGINT with the zero
disposition, `Unmodeled` on SIGSEGV.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_witness_install_paths :
    rt_sigaction_witness 2 4096 0 8 (sigaction_in mem_none mem_none) demo_model
        = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []
    ∧ rt_sigaction_witness 9 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []
    ∧ rt_sigaction_witness 2 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) demo_model
        = Unmodeled
    ∧ rt_sigaction_witness 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        = Ok (mkEffect 0 [] []) demo_model []
    ∧ rt_sigaction_witness 11 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        = Unmodeled
    ∧ rt_sigaction_witness 65 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- The witness decides its gates in the checker's order, pinned where
both conditions of a neighbouring pair hold at once: size before `oact`,
`oact` before the NULL-`act` split, the read before the signal tests,
SIGKILL and 65 before the flags.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_witness_gate_order (i : SyscallInput) (m : Model) :
    rt_sigaction_witness 2 4096 4096 16 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ rt_sigaction_witness 2 0 4096 8 i m = Unmodeled
    ∧ rt_sigaction_witness 65 4096 0 8 (sigaction_in mem_none mem_none) m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ rt_sigaction_witness 9 4096 0 8 (sigaction_in mem_none mem_none) m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ rt_sigaction_witness 9 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m
        = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ rt_sigaction_witness 65 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- The copy-out witness: -EFAULT past `TASK_SIZE` on every model,
`Unmodeled` on an unwritable page, the eight bytes on a writable one.
kernel: kernel/signal.c:rt_sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem write_oset_witness_paths (m : Model) :
    write_oset_witness (Z_to_bv 64 (2 ^ 64 - 8)) 65542 (sigprocmask_in mem_none wmem_oldset) m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ write_oset_witness 8192 65542 (sigprocmask_in mem_none mem_none) m = Unmodeled
    ∧ write_oset_witness 8192 65542 (sigprocmask_in mem_none wmem_oldset_short) m = Unmodeled
    ∧ write_oset_witness 8192 65542 (sigprocmask_in mem_none wmem_oldset) m
        = Ok (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) m [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- rt_sigprocmask before the install: -EINVAL at a bad size, 0 on a NULL
set whatever `how`, -EFAULT on an unreadable set, all on every input or
model as stated.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_witness_before_the_install (how : word) (i : SyscallInput) (m : Model) :
    rt_sigprocmask_witness 1 4096 0 16 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ rt_sigprocmask_witness how 0 0 8 i m = Ok (mkEffect 0 [] []) m []
    ∧ rt_sigprocmask_witness 1 8192 0 8 (sigprocmask_in mem_none mem_none) m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> witness_norm

/-- The witness's gate order where both conditions hold: a bad size with
a NULL set is -EINVAL, an unreadable set with a bad `how` is the bare
-EFAULT, and a bad `how` with an unwritable `oset` is the ledgered
-EINVAL rather than `Unmodeled`.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_witness_gate_order (how : word) (i : SyscallInput) (m : Model) :
    rt_sigprocmask_witness how 0 0 16 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ rt_sigprocmask_witness 3 4096 0 8 (sigprocmask_in mem_none mem_none) m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ rt_sigprocmask_witness 3 4096 8192 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m
        = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> witness_norm

/-- rt_sigprocmask's query: the blocked fixture's eight bytes, and
`Unmodeled` on an unwritable `oset`.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_witness_query :
    rt_sigprocmask_witness 0 0 8192 8 (sigprocmask_in mem_none wmem_oldset) sig_model_blocked
        = Ok (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked []
    ∧ rt_sigprocmask_witness 0 0 8192 8 (sigprocmask_in mem_none mem_none) sig_model_blocked
        = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- rt_sigprocmask's install: the ledgered -EINVAL on a bad `how`, SIG_BLOCK
{SIGSEGV} on `demo_model`, the snapshot-then-install with `oset`, the
no-rollback -EFAULT, and `Unmodeled` on an unwritable `oset` after the
install.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_witness_install_paths :
    rt_sigprocmask_witness 3 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model []
    ∧ rt_sigprocmask_witness 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 1024 demo_model) []
    ∧ rt_sigprocmask_witness 2 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset)
          sig_model_blocked
        = Ok (with_copyins sig_copyin (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
            (with_sigmask 5 sig_model_blocked) []
    ∧ rt_sigprocmask_witness 2 4096 (Z_to_bv 64 (2 ^ 64 - 8)) 8
          (sigprocmask_in mem_sigset_kill_stop wmem_oldset) sig_model_blocked
        = Ok (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] []))
            (with_sigmask 5 sig_model_blocked) []
    ∧ rt_sigprocmask_witness 1 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop mem_none)
          sig_model_blocked = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- rt_sigprocmask's delivery: unblocking a pending SIGABRT names the
killed model, and with nothing pending the plain install.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem rt_sigprocmask_witness_delivers_pending_sigabrt :
    rt_sigprocmask_witness 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
          (with_sigabrt_pending abort_model_blocked)
        = Ok (with_copyins sig_copyin (mkEffect 0 [] []))
            (with_killed 6 (with_sigmask 0 (with_sigabrt_pending abort_model_blocked))) []
    ∧ rt_sigprocmask_witness 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
          abort_model_blocked
        = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 abort_model_blocked) [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

end TheWitnesses

-- lean-port sentinel: ticket V-Kernel-Signal-mask-action appends below this line

section V_Kernel_Signal_mask_action

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Signal-mask-action — `rt_sigaction` and `rt_sigprocmask` over the real table

WHAT IS TWINNED HERE.  The sections above state the Rocq examples about 134
and 135 on `check_rt_sigaction` and `check_rt_sigprocmask` themselves,
because `checked_table` carried no row for either when they were written,
and the file's header leaves the restatement through `check_syscall` to
the registration.  This is the registration.  Each example
`theories/LinuxProcessSem/Checks/Cases/Kernel/Signal.v` states about 134 or
135 through `check_syscall` is restated here through the Lean
`check_syscall`, over `checked_table` itself, at Rocq's input and model,
under its Rocq name with `_over_the_real_table` after it.  The rt_sigaction
ones hold at every model, and its declines at every effect too, as their
checker-level twins do.  Each verdict pin is proved by computing the
dispatch once (`check_syscall_rt_sigaction`, `check_syscall_rt_sigprocmask`)
and then the checker, as `check_norm` does above.

WHAT A PIN HERE ADDS to its checker-level twin is the ARM's claim: that the
lookups at 134 and 135 find `arm_rt_sigaction` and `arm_rt_sigprocmask`
rather than the dispatcher's own decline, and that each arm hands its
checker `a0` narrowed to its low 32 bits, and `a1`, `a2` and `a3` whole.
`rt_sigprocmask_how_truncates_size_does_not_over_the_real_table` is the
Rocq example the header leaves to the registration and carries that for
rt_sigprocmask's `how` and `sigsetsize`; the pins after the Rocq examples
carry it for rt_sigaction's `sig` and `sigsetsize`, for the four pointers,
and for `a4` and `a5`, which neither arm reads.

POLARITY: `model:` is on the table's own contents (the lookups and
`check_syscall`'s reduction at 134 and 135), on the closed rewrites the
ground pass needs, and on `the_checkers_themselves_read_whole_words` (which
says why); `kernel:` is on every verdict of the table and outcome of its
witness, `CheckUnmodeled` included, and on the witness's reduction, which
states the arm's reading of the registers. -/

/-- Reading a register from the six-word input.
model: `in_arg` on a six-word list, a rewrite for the ground pass. -/
theorem in_arg_six_0 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- Reading a register from the six-word input.
model: `in_arg` on a six-word list, a rewrite for the ground pass. -/
theorem in_arg_six_1 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- Reading a register from the six-word input.
model: `in_arg` on a six-word list, a rewrite for the ground pass. -/
theorem in_arg_six_2 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 2 = a2 := rfl
/-- Reading a register from the six-word input.
model: `in_arg` on a six-word list, a rewrite for the ground pass. -/
theorem in_arg_six_3 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 3 = a3 := rfl
attribute [local sys_simp] in_arg_six_0 in_arg_six_1 in_arg_six_2 in_arg_six_3

/-- The literal narrowing values used by these pins.
model: a closed evaluation of the narrowing `abi_low32`, a rewrite for the ground pass. -/
theorem how32_on_the_table :
    how32 0 = 0 ∧ how32 1 = 1 ∧ how32 2 = 2 ∧ how32 3 = 3 ∧ how32 999 = 999
    ∧ how32 4294967297 = 1 ∧ how32 4294967299 = 3 := by decide
/-- The literal narrowing values used by these pins.
model: a closed evaluation of the narrowing `abi_low32`, a rewrite for the ground pass. -/
theorem sig32_on_the_table :
    sig32 2 = 2 ∧ sig32 6 = 6 ∧ sig32 11 = 11 ∧ sig32 13 = 13 ∧ sig32 17 = 17
    ∧ sig32 4294967298 = 2 ∧ sig32 4294967307 = 11 := by decide
attribute [local sys_simp] how32_on_the_table sig32_on_the_table

/-- The checked table selects this signal arm.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_rt_sigaction (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 134 args mem wmem).in_sysno)
      = some arm_rt_sigaction :=
  lookup_ca_checked_table_rt_sigaction

/-- The checked table selects this signal arm.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_rt_sigprocmask (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 135 args mem wmem).in_sysno)
      = some arm_rt_sigprocmask :=
  lookup_ca_checked_table_rt_sigprocmask

/-- The checker selected by the real table.
model: `check_syscall` through `arm_rt_sigaction`, unfolded; the table's own contents, not a kernel claim. -/
theorem check_syscall_rt_sigaction (args : List word) (mem wmem : word → Option byte) (eff : SyscallEffect)
    (m : Model) :
    check_syscall (SyscallInput.mkInput 134 args mem wmem) eff m
      = check_rt_sigaction (SyscallInput.mkInput 134 args mem wmem)
          (sig32 (in_arg (SyscallInput.mkInput 134 args mem wmem) 0))
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 1)
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 2)
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 3) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_rt_sigaction args mem wmem)

/-- The checker selected by the real table.
model: `check_syscall` through `arm_rt_sigprocmask`, unfolded; the table's own contents, not a kernel claim. -/
theorem check_syscall_rt_sigprocmask (args : List word) (mem wmem : word → Option byte) (eff : SyscallEffect)
    (m : Model) :
    check_syscall (SyscallInput.mkInput 135 args mem wmem) eff m
      = check_rt_sigprocmask (SyscallInput.mkInput 135 args mem wmem)
          (how32 (in_arg (SyscallInput.mkInput 135 args mem wmem) 0))
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 1)
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 2)
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 3) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_rt_sigprocmask args mem wmem)

/-- What the table hands the witness at 134: the arm's reading, `a0`
narrowed and `a1` to `a3` whole.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem syscall_spec_witness_rt_sigaction (args : List word) (mem wmem : word → Option byte) (m : Model) :
    syscall_spec_witness (SyscallInput.mkInput 134 args mem wmem) m
      = rt_sigaction_witness (sig32 (in_arg (SyscallInput.mkInput 134 args mem wmem) 0))
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 1)
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 2)
          (in_arg (SyscallInput.mkInput 134 args mem wmem) 3)
          (SyscallInput.mkInput 134 args mem wmem) m := by
  unfold syscall_spec_witness table_witness
  rw [lookup_rt_sigaction]
  rfl

/-- What the table hands the witness at 135: the arm's reading, `a0`
narrowed and `a1` to `a3` whole.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem syscall_spec_witness_rt_sigprocmask (args : List word) (mem wmem : word → Option byte) (m : Model) :
    syscall_spec_witness (SyscallInput.mkInput 135 args mem wmem) m
      = rt_sigprocmask_witness (how32 (in_arg (SyscallInput.mkInput 135 args mem wmem) 0))
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 1)
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 2)
          (in_arg (SyscallInput.mkInput 135 args mem wmem) 3)
          (SyscallInput.mkInput 135 args mem wmem) m := by
  unfold syscall_spec_witness table_witness
  rw [lookup_rt_sigprocmask]
  rfl

/-- `mem_sigaction_zero` holds no flags word at `2^32 + 4096`, the `act`
the pointer pin below hands the table.
model: a closed `sigaction_flags` read of the fixture, a rewrite for the ground pass. -/
theorem sigaction_flags_above_the_fixture :
    sigaction_flags mem_sigaction_zero 4294971392 = none := by decide
attribute [local sys_simp] sigaction_flags_above_the_fixture List.get?Internal

macro "table_norm_mask_action" : tactic =>
  `(tactic| (simp only [check_syscall_rt_sigaction, check_syscall_rt_sigprocmask]; check_norm))

macro "table_refute_mask_action" : tactic =>
  `(tactic| (table_norm_mask_action; done))

/-- Rocq's `rt_sigaction_sigsegv_unmodeled` over the real table.
Restates the corresponding conjunct of `check_rt_sigaction_declined_signals`, already general in effect and model.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigsegv_unmodeled_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [11, 4096, 0, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      eff m
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigaction_sigpipe_unmodeled` over the real table.
Restates the corresponding conjunct of `check_rt_sigaction_declined_signals`, already general in effect and model.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigpipe_unmodeled_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [13, 4096, 0, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      eff m
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigaction_sigchld_unmodeled` over the real table.
Restates the corresponding conjunct of `check_rt_sigaction_declined_signals`, already general in effect and model.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigchld_unmodeled_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [17, 4096, 0, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      eff m
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigaction_sigabrt_unmodeled` over the real table.
Restates the corresponding conjunct of `check_rt_sigaction_declined_signals`, already general in effect and model.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigabrt_unmodeled_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [6, 4096, 0, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      eff m
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigaction_sigint_accepted` over the real table.
Restates `check_rt_sigaction_sigint_accepts_zero_on_every_model`.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigint_accepted_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [2, 4096, 0, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      (mkEffect 0 [] []) m
    = CheckOk m [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_block_sigsegv_accepted` over the real table.
Restates `check_rt_sigprocmask_block_sigsegv_accepts_the_install` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_block_sigsegv_accepted_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 8, 0, 0] mem_sigset_sigsegv
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model
    = CheckOk (with_sigmask 1024 demo_model) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_kill_stop_stripped_not_refused` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_kill_stop_stripped_not_refused`.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask; include/linux/signal.h:sigdelsetmask@v6.18.46 -/
theorem rt_sigprocmask_kill_stop_stripped_not_refused_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [2, 4096, 0, 8, 0, 0] mem_sigset_kill_stop
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
    = CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_block_unions` over the real table.
Restates `check_rt_sigprocmask_block_unions` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_block_unions_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 8, 0, 0] mem_sigset_kill_stop
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
    = CheckOk (with_sigmask 65543 sig_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_unblock_clears` over the real table.
Restates `check_rt_sigprocmask_unblock_clears` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_unblock_clears_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_kill_stop
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
    = CheckOk (with_sigmask 65538 sig_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_unblock_is_not_block` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_unblock_is_not_block`.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_unblock_is_not_block_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_kill_stop
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
    ≠ CheckOk (with_sigmask 65543 sig_model_blocked) [] := by
  table_refute_mask_action

/-- Rocq's `rt_sigprocmask_oldset_unmodeled` over the real table.
Restates the second conjunct of `check_rt_sigprocmask_install_with_unwritable_oset_declines`,
at Rocq's effect.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_unmodeled_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4096, 8192, 8, 0, 0] mem_sigset_sigsegv
                     mem_none)
      (mkEffect 0 [] []) demo_model
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_reports_entry_mask` over the real table.
Restates `check_rt_sigprocmask_oldset_reports_entry_mask` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_reports_entry_mask_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 0, 8192, 8, 0, 0] mem_none
                     wmem_oldset)
      (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked
    = CheckOk sig_model_blocked [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_impossible_mask_rejected` over the real table.
Restates `check_rt_sigprocmask_oldset_impossible_mask_rejected` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,set_current_blocked@v6.18.46 -/
theorem rt_sigprocmask_oldset_impossible_mask_rejected_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 0, 8192, 8, 0, 0] mem_none
                     wmem_oldset)
      (mkEffect 0 [(8192, [0, 1, 4, 0, 0, 0, 0, 0])] []) sig_model_blocked
    = CheckReject := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_is_not_the_new_mask` over the real table.
Restates `check_rt_sigprocmask_oldset_is_not_the_new_mask` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_is_not_the_new_mask_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [2, 4096, 8192, 8, 0, 0] mem_sigset_kill_stop
                     wmem_oldset)
      (with_copyins sig_copyin (mkEffect 0 [(8192, [5, 0, 0, 0, 0, 0, 0, 0])] []))
      sig_model_blocked
    = CheckReject := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_snapshot_precedes_install` over the real table.
Restates `check_rt_sigprocmask_oldset_snapshot_precedes_install` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_snapshot_precedes_install_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [2, 4096, 8192, 8, 0, 0] mem_sigset_kill_stop
                     wmem_oldset)
      (with_copyins sig_copyin (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
      sig_model_blocked
    = CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_efault_still_installs` over the real table.
Restates `check_rt_sigprocmask_oldset_efault_still_installs` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem rt_sigprocmask_oldset_efault_still_installs_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [2, 4096, Z_to_bv 64 (2 ^ 64 - 8), 8, 0, 0]
                     mem_sigset_kill_stop wmem_oldset)
      (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] []))
      sig_model_blocked
    = CheckOk (with_sigmask 5 sig_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_oldset_over_task_size_never_succeeds` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_oldset_over_task_size_never_succeeds`.
kernel: kernel/signal.c:rt_sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem rt_sigprocmask_oldset_over_task_size_never_succeeds_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [2, 4096, Z_to_bv 64 (2 ^ 64 - 8), 8, 0, 0]
                     mem_sigset_kill_stop wmem_oldset)
      (with_copyins sig_copyin (mkEffect 0 [] []))
      sig_model_blocked
    = CheckReject := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_null_set_ignores_how` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_null_set_ignores_how_on_the_fixture`.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_null_set_ignores_how_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [999, 0, 0, 8, 0, 0] mem_none
                     mem_none)
      (mkEffect 0 [] []) demo_model
    = CheckOk demo_model [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_bad_size_beats_unreadable_set` over the real table.
Restates `check_rt_sigprocmask_bad_size_beats_unreadable_set` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_bad_size_beats_unreadable_set_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 8192, 0, 0, 0, 0] mem_none
                     mem_none)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
    = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [1, 8192, 0, 0, 0, 0] mem_none
                       mem_none)
         (mkEffect (errno_ret EFAULT) [] []) demo_model
       = CheckReject := by
  refine ⟨?_, ?_⟩ <;> table_norm_mask_action

/-- Rocq's `rt_sigprocmask_bad_size_beats_oldset_decline` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_bad_size_beats_oldset_decline`.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_bad_size_beats_oldset_decline_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 0, 8192, 0, 0, 0] mem_none
                     mem_none)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
    = CheckOk demo_model [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_efault_beats_bad_how` over the real table.
Restates `check_rt_sigprocmask_efault_beats_bad_how` and the first conjunct of
`check_rt_sigprocmask_efault_beats_bad_how_einval_rejected`.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_efault_beats_bad_how_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [3, 8192, 0, 8, 0, 0] mem_none
                     mem_none)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
    = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [3, 8192, 0, 8, 0, 0] mem_none
                       mem_none)
         (mkEffect (errno_ret EINVAL) [] []) demo_model
       = CheckReject := by
  refine ⟨?_, ?_⟩ <;> table_norm_mask_action

/-- Rocq's `rt_sigprocmask_how_truncates_size_does_not` over the real table:
the arm's reading, which the checker-level sections leave to the
registration.  `how` is an `int` and `sigsetsize` a `size_t`
(kernel/signal.c:3327-3328, Linux v6.18.46), narrowed through `__SC_CAST`
(include/linux/syscalls.h:132).  So `2^32 + 1` is SIG_UNBLOCK and `2^32 + 3`
an unknown `how`, while `2^32 + 8` fails the size test (:3334-3335).  The
third conjunct is what the first conjunct of
`check_rt_sigprocmask_size_is_not_narrowed` states on the checker, at
Rocq's fixture.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_how_truncates_size_does_not_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [4294967297, 4096, 0, 8, 0, 0]
                     mem_sigset_sigsegv mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model
    = CheckOk (with_sigmask 0 demo_model) []
    ∧ check_syscall (SyscallInput.mkInput 135 [4294967299, 4096, 0, 8, 0, 0]
                       mem_sigset_sigsegv mem_none)
         (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model
       = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 4294967304, 0, 0]
                       mem_sigset_sigsegv mem_none)
         (mkEffect (errno_ret EINVAL) [] []) demo_model
       = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> table_norm_mask_action

/-- Rocq's `rt_sigprocmask_copyins_separate_the_two_einvals` over the real table.
Restates `check_rt_sigprocmask_two_einvals_differ_in_the_ledger` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_copyins_separate_the_two_einvals_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 0, 0, 0] mem_sigset_sigsegv
                     mem_none)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
    = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [3, 4096, 0, 8, 0, 0] mem_sigset_sigsegv
                       mem_none)
         (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model
       = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 0, 0, 0] mem_sigset_sigsegv
                       mem_none)
         (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model
       = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 135 [3, 4096, 0, 8, 0, 0] mem_sigset_sigsegv
                       mem_none)
         (mkEffect (errno_ret EINVAL) [] []) demo_model
       = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> table_norm_mask_action

/-- Rocq's `rt_sigprocmask_efault_records_no_copyin` over the real table.
Restates `check_rt_sigprocmask_efault_records_no_copyin` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_efault_records_no_copyin_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 8192, 0, 8, 0, 0] mem_none
                     mem_none)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
    = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [1, 8192, 0, 8, 0, 0] mem_none
                       mem_none)
         (with_copyins [(8192, 8)] (mkEffect (errno_ret EFAULT) [] []))
         demo_model
       = CheckReject := by
  refine ⟨?_, ?_⟩ <;> table_norm_mask_action

/-- Rocq's `rt_sigprocmask_success_admits_no_write` over the real table.
Restates `check_rt_sigprocmask_install_rejects_a_write` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_success_admits_no_write_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 8, 0, 0] mem_sigset_sigsegv
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [(4096, [0])] [])) demo_model
    = CheckReject := by
  table_norm_mask_action

/-- Rocq's `rt_sigaction_oact_read_back_declined` over the real table.
Restates the second conjunct of `check_rt_sigaction_oact_declines_on_every_effect`,
at Rocq's input.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_oact_read_back_declined_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [2, 4096, 4096, 8, 0, 0] mem_sigaction_zero
                     mem_none)
      eff m
    = CheckUnmodeled := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_unblock_pending_sigabrt_kills` over the real table.
Restates `check_rt_sigprocmask_unblock_pending_sigabrt_kills` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem rt_sigprocmask_unblock_pending_sigabrt_kills_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] []))
      (with_sigabrt_pending abort_model_blocked)
    = CheckOk (with_killed 6
                 (with_sigmask 0
                    (with_sigabrt_pending abort_model_blocked))) [] := by
  table_norm_mask_action

/-- Rocq's `rt_sigprocmask_unblock_nothing_pending_lives` over the real table.
Restates `check_rt_sigprocmask_unblock_nothing_pending_lives` with the same effect and model.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem rt_sigprocmask_unblock_nothing_pending_lives_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_blocked
    = CheckOk (with_sigmask 0 abort_model_blocked) [] := by
  table_norm_mask_action

/-- Rocq's `one_sided_unblock_kills` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_one_sided_unblock_kills`.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem one_sided_unblock_kills_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt
                     mem_none)
      (with_copyins sig_copyin (mkEffect 0 [] [])) one_sided_model
    = CheckOk (with_killed 6
                 (with_sigmask 0 one_sided_model)) [] := by
  table_norm_mask_action

/-- Rocq's `decl_off_frame_one_sided_refuted` over the real table: the
table's answer to the unblock just above, carried to the spec by
`check_syscall_sound_ok`, meets `Run.decl_off_frame_one_sided`'s hypotheses
and breaks its `m_killed m' = none` conclusion.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem decl_off_frame_one_sided_refuted_over_the_real_table :
    ¬ LinuxProcessSem.Run.decl_off_frame_one_sided := by
  intro H
  have h := H (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt mem_none)
    one_sided_model (with_copyins sig_copyin (mkEffect 0 [] []))
    (with_killed 6 (with_sigmask 0 one_sided_model)) []
    (check_syscall_sound_ok _ _ _ _ _ one_sided_unblock_kills_over_the_real_table) (by decide)
  exact nomatch (h.2.1 : (some (6 : word) : Option word) = none)

/-- Rocq's `decl_off_frame_hypotheses_inhabited` over the real table.
Restates the first conjunct of `check_rt_sigprocmask_declaration_off_nothing_pending_installs`
and adds the two fixture hypotheses.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem decl_off_frame_hypotheses_inhabited_over_the_real_table :
    m_abort_terminal abort_model_undeclared = false
    ∧ m_sigabrt_pending abort_model_undeclared = false
    ∧ check_syscall (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt
                       mem_none)
         (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_undeclared
       = CheckOk (with_sigmask 0 abort_model_undeclared) [] := by
  refine ⟨rfl, rfl, ?_⟩
  table_norm_mask_action

/-- `sig` is an `int` and `sigsetsize` a `size_t`
(`SYSCALL_DEFINE4(rt_sigaction, …)`, kernel/signal.c:4638-4641, Linux
v6.18.46), and riscv64's `__SYSCALL_DEFINEx` hands each register to
`__do_sys_rt_sigaction` through `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88).  So bit 32 of `a0`
is not a bit of `sig`, and every bit of `a3` is a bit of `sigsetsize`.
`2^32 + 2` in `a0` is SIGINT, and its 0 is accepted as at 2.  `2^32 + 11` is
SIGSEGV, declined as at 11.  `2^32 + 8` in `a3` fails the size test
(:4647-4648), so its -EINVAL is accepted and 0 refused.  An arm handing the
checker the whole `a0` would refuse the first 0
(`the_checkers_themselves_read_whole_words`); one narrowing `a3` would
accept the last.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_sig_is_the_low_half_of_a0_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [4294967298, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_syscall (SyscallInput.mkInput 134 [4294967307, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckUnmodeled
    ∧ check_syscall (SyscallInput.mkInput 134 [2, 4096, 0, 4294967304, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (SyscallInput.mkInput 134 [2, 4096, 0, 4294967304, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> table_norm_mask_action

/-- `act` and `oact` are pointers, and `__SC_CAST` to a pointer type keeps
all 64 bits of the register (include/linux/syscalls.h:132, Linux v6.18.46).
`2^32 + 4096` in `a1` is not the readable 24 bytes at 4096, so
`copy_from_user` faults (kernel/signal.c:4650-4651).  Its -EFAULT is
accepted and 0 refused, where an arm reading 4096 would accept the 0.
`2^32` in `a2` is a non-NULL `oact`, the read-back the spec declines;
read as NULL it would have been answered.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_pointers_are_whole_registers_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [2, 4294971392, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m []
    ∧ check_syscall (SyscallInput.mkInput 134 [2, 4294971392, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 134 [2, 4096, 4294967296, 8, 0, 0] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> table_norm_mask_action

/-- `nset` and `oset` are pointers too (`SYSCALL_DEFINE4(rt_sigprocmask,
…)`, kernel/signal.c:3327-3328, Linux v6.18.46), whole registers after
`__SC_CAST`.  `2^32 + 4096` in `a1` is not the readable set at 4096, so the
copy faults (:3339-3341).  Its -EFAULT is accepted with no copy-in, and the
install is refused.  `2^32 + 8192` in `a2` is not the writable eight bytes
at 8192, so the query declines, even for the store at 8192 that an arm
reading 8192 would accept.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_pointers_are_whole_registers_over_the_real_table :
    check_syscall (SyscallInput.mkInput 135 [0, 4294971392, 0, 8, 0, 0] mem_sigset_sigsegv mem_none)
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 135 [0, 4294971392, 0, 8, 0, 0] mem_sigset_sigsegv mem_none)
        (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 135 [0, 0, 4294975488, 8, 0, 0] mem_none wmem_oldset)
        (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> table_norm_mask_action

/-- Both entry points take four arguments (`SYSCALL_DEFINE4`,
kernel/signal.c:3327 and :4638, Linux v6.18.46), so
`SC_RISCV_REGS_TO_ARGS` reads `orig_a0` and `a1` to `a3`, never `a4` or `a5`
(arch/riscv/include/asm/syscall_wrapper.h:21-24).  With 7 and 9 there, both
calls are answered as with zeros.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/signal.c:rt_sigaction,rt_sigprocmask@v6.18.46 -/
theorem upper_registers_are_not_read_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 134 [2, 4096, 0, 8, 7, 9] mem_sigaction_zero mem_none)
        (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_syscall (SyscallInput.mkInput 135 [0, 4096, 0, 8, 7, 9] mem_sigset_sigsegv mem_none)
        (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model
      = CheckOk (with_sigmask 1024 demo_model) [] := by
  refine ⟨?_, ?_⟩ <;> table_norm_mask_action

/-- The checkers' side of the narrowing.  Handed the whole words the table
pins above hand the arms, each answers -EINVAL: rt_sigaction's for a signal
past `_NSIG`, and rt_sigprocmask's for a `how` its switch does not know.
So the narrowing lives in the arms' `sig32` and `how32` reading, not in the
checkers.  This is not the kernel's answer at those registers: Linux
narrows before it tests (`__SC_CAST`, include/linux/syscalls.h:132, Linux
v6.18.46), and both calls return 0.  That is why the evidence line is
`model:`.
model: the checkers' contract with the arms' reading; Linux narrows first (__SC_CAST, cited above) and does not answer -EINVAL at these register words -/
theorem the_checkers_themselves_read_whole_words (m : Model) :
    check_rt_sigaction (sigaction_in mem_sigaction_zero mem_none) 4294967298 4096 0 8
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_rt_sigprocmask (sigprocmask_in mem_sigset_sigsegv mem_none) 4294967297 4096 0 8
        (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The witness at 134 gets the arm's reading too.  At `2^32 + 2` in `a0`
it gives SIGINT's 0, and at `2^32 + 11` it declines, as at 11 and as the
checker does.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_witness_reads_the_low_half_over_the_real_table :
    syscall_spec_witness (SyscallInput.mkInput 134 [4294967298, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        demo_model = Ok (mkEffect 0 [] []) demo_model []
    ∧ syscall_spec_witness (SyscallInput.mkInput 134 [4294967307, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none)
        demo_model = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> (rw [syscall_spec_witness_rt_sigaction]; witness_norm)

/-- The witness at 135 gets the arm's reading too.  `2^32 + 1` is
SIG_UNBLOCK: the eight-byte copy-in, and `demo_model`'s empty mask less
SIGSEGV installed, which is still 0.  `2^32 + 3` is past SIG_SETMASK, so it
is the -EINVAL of `sigprocmask`'s switch, with the same copy-in.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_witness_reads_the_low_half_over_the_real_table :
    syscall_spec_witness (SyscallInput.mkInput 135 [4294967297, 4096, 0, 8, 0, 0] mem_sigset_sigsegv mem_none)
        demo_model = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 demo_model) []
    ∧ syscall_spec_witness (SyscallInput.mkInput 135 [4294967299, 4096, 0, 8, 0, 0] mem_sigset_sigsegv mem_none)
        demo_model = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model [] := by
  refine ⟨?_, ?_⟩ <;> (rw [syscall_spec_witness_rt_sigprocmask]; witness_norm)

end V_Kernel_Signal_mask_action


/-! # The second half: what the `sigaltstack`, `tkill` and `tgkill` CHECKERS accept and their WITNESSES name

Appended by C-Kernel-Signal-altstack-kill after the mask/action half above
had merged.  Pins over the second half of `Checks.Sys.Kernel.Signal`, the
twin of the sigaltstack/tkill/tgkill half of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Signal.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Signal.v`, in the same
reading as the first half: a concrete `(input, effect)` pair to
`check_sigaltstack i uss uoss eff m`, `check_tkill pid sig eff m` or
`check_tgkill tgid pid sig eff m` — the body of the arm the checked table
will hold for 132, 130 and 131 — and the verdict, `CheckOk` on the
kernel's answer, `CheckReject` on the lie, `CheckUnmodeled` where the spec
declines.  Every kernel line below was read at Linux v6.18.46 (commit
1f99e9ab748f).  The delivery acceptor `check_send_sigabrt eff m` is pinned
directly as well, on both models, because the two kill checkers reach it
only through their gates and a reader of the pending-or-dead answer
should not have to walk them.

THE MODEL IS AN OUTPUT here twice over.  sigaltstack's install answers
`CheckOk (with_sigaltstack_installed m) []` and the SIGABRT delivery
`CheckOk (with_sigabrt_pending m) []` or `CheckOk (with_killed 6 m) []`,
and a trace offers an effect, never a model: so the lie "the install left
the bit clear" or "the unblocked send left the process alive" is a
`CheckOk` with the RIGHT model, which the pins state by refuting the wrong
one as a `≠` on the same `CheckOk`, closed by the two models differing in
the one field.

WHAT THIS RESTATES.  Rocq keeps the worked examples for these checkers in
`Checks/Cases/Kernel/Signal.v` as `Example`s over `check_syscall`; each is
restated here on the checker directly, one line over `check_syscall` once
the registration lands.  For sigaltstack:
`sigaltstack_leaves_the_mask_alone` is
`check_sigaltstack_install_leaves_the_mask_alone`;
`sigaltstack_after_an_install_declined` is
`check_sigaltstack_installed_declines_every_shape`'s first conjunct;
`sigaltstack_enomem_keeps_the_record` is
`check_sigaltstack_enomem_keeps_the_record`;
`sigaltstack_success_admits_no_write` is the first conjunct of
`check_sigaltstack_install_rejects_a_write_or_a_ledger`;
`sigaltstack_disable_leaves_the_record_answerable` is
`check_sigaltstack_disable_leaves_the_record_answerable`;
`sigaltstack_install_still_sets_the_bit` is
`check_sigaltstack_install_still_sets_the_bit`;
`sigaltstack_after_a_disable_rejects_a_false_success` is
`check_sigaltstack_after_a_disable_rejects_a_false_success`.  For tkill and
tgkill: `tkill_sigabrt_unblocked_kills`, `tkill_sigabrt_blocked_pends`
and `tgkill_self_sigabrt_kills` are the first, second and third conjuncts
of `check_tkill_sigabrt_kills_or_pends`; `tkill_off_declined` and
`tgkill_off_declined` the first two of `check_tkill_off_declined`;
`tkill_signal_zero_declined` and `tkill_other_signal_declined` the first
two of `check_tkill_other_signal_declined`; `tkill_other_pid_declined`,
`tkill_nonpositive_pid_einval`, `tgkill_wrong_tgid_esrch`,
`tkill_forged_write_rejected` and `tkill_forged_return_rejected` the
first conjunct each of the theorem of the same name with `check_` in
front; and `tkill_reads_the_mask_and_writes_none` is
`check_tkill_reads_the_mask_and_writes_none`, its two mask equalities
read as the values 0 and 32.  The Rocq admission reasons (the list at
the top of `Checks/Examples.v`) are three: the sigaltstack examples and
the declined kill shapes cite the third (the fact is about model-internal
state a probe cannot observe — the bit, the pending flag, the mask read)
or the fourth (a `CheckReject` needs a kernel answer no kernel gives);
the three positive kill examples cite, in Rocq's words, the first — a
conformance probe reaches the shape (`abort_terminal.c` does) but cannot
run under the declaration, which the harness builds from a launch rather
than from a task's statement.  Not restated: `sig_mask_windows_all_declined`'s
sigaltstack, tkill and tgkill conjuncts are dispatcher facts, the decline
registers' before the arms landed and the registration's after.  The name
map is prose, for the reason the first half gives.

WHAT IS PINNED BEYOND THE SPEC'S FIXTURES.  Six facts are stated over a
symbolic model, an arbitrary effect, or both, because at the checker a
fixture could pass them by luck: the installed bit declines on EVERY
input, argument and effect; a non-NULL `uoss` declines on every
uninstalled model whatever effect is offered; `sigaltstack(NULL, NULL)`
answers 0 on every uninstalled model with any input; so does the
`SS_DISABLE` record over the Rocq fixture map; the install on that map
answers `CheckOk (with_sigaltstack_installed m) []` on every uninstalled
model; and the declaration off declines all three kill checkers on every
model, argument and effect.  A seventh, that the delivery acceptor does
not read the declaration, is on the two undeclared fixtures, with the
effect quantified only in the conjunct that reaches the acceptor through
`check_tkill`.  The effect is quantified where the spec pins cannot
quantify it: a decline is a decline for the forged write, the forged
errno and the forged success alike.

HOW THE PINS ARE PROVED.  As the first half's, with the second half's
checkers and witnesses in the set: `check_norm_altstack_kill` is
`check_norm` over `check_sigaltstack`, `check_tkill`, `check_tgkill`,
`check_tkill_self` and `check_send_sigabrt`, `check_refute_altstack_kill`
is it followed by `done`, and `witness_norm_altstack_kill` is
`witness_norm` over the five witnesses.  The `sys_simp` readings the first
pass leans on are the spec pins' `sigaltstack_at_reads_*`,
`ss_fields_read*` and `rocq_sigaltstack_fixtures_read_as_described`; the
model fixtures (`abort_model_*`, `installed_model`) are read by the ground
pass.  The symbolic pins open the checker by hand and close by the gate
hypothesis alone, or by unfolding `check_ret_only` and deciding.  Where a pin
compares two models (`≠ CheckOk … []`), the ground pass opens both to
their fields and the injectivity set finds the one that differs — the bit,
the pending flag, the halt — so no `DecidableEq Model` is needed and none
exists. -/

/-- Evaluate a closed call of one of the second half's checkers, or of the
delivery acceptor: `check_norm` with those five in the set. -/
macro "check_norm_altstack_kill" : tactic =>
  `(tactic| (simp +decide only [check_sigaltstack, check_tkill, check_tgkill, check_tkill_self,
              check_send_sigabrt, check_ret_only, Bool.and_eq_true, bv_eqb_eq,
              check_result.CheckOk.injEq, ne_eq, sys_simp, ↓reduceIte];
             first | done | sys_simp_pass +ground +decide -failIfUnchanged))

/-- Refute: `check_norm_altstack_kill`, and the goal must be closed by it. -/
macro "check_refute_altstack_kill" : tactic => `(tactic| (check_norm_altstack_kill; done))

/-! ### The verdict's injectivity, in the ground pass

The ground pass splits every constructor the normalizer knows — outcome,
effect, model, event — and not this file's verdict type.  A refutation whose
checker call is opened only by the ground pass (the kill checkers' `match` on
the recorded tid is one: the fixture models are not `sys_simp` readings, so
the first pass leaves the `match` standing) reaches
`CheckOk M [] = CheckOk M' [] → False` there and needs the verdict's
injectivity in the same pass to go on into the two models.  Local, so the
first half's pins above are proved as they were. -/
attribute [local sys_simp] check_result.CheckOk.injEq

section AltstackInstalled

/-! ## `sigaltstack` (132): the recorded stack, ahead of everything

`sigaltstack_spec`'s first gate is the model's own: once an install has
raised `sas_ss_size`, `do_sigaltstack`'s `on_sig_stack(sp)` test
(kernel/signal.c:4418-4419, Linux v6.18.46) turns on the user stack
pointer and the stored record, and the fast path (:4430-4433) on the
stored record alone, neither of which the model tracks, so every call on
such a model declines —
before the copy-in, before the mode test, whatever the effect offered. -/

/-- On the installed model every shape declines: the good install, the
disable, the query, the NULL/NULL no-op, the unreadable `uss`, the
non-NULL `uoss` — whatever effect is offered.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_installed_declines_every_shape (eff : SyscallEffect) :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 eff installed_model
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0 eff installed_model
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0 eff installed_model
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 0 0 eff installed_model = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 eff installed_model
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 8192 eff installed_model
        = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The bit is the FIRST gate, on every input, every argument pair and
every effect: a symbolic model with the bit set declines before anything
is read.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_installed_declines_symbolically (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model) (hin : m_sigaltstack_installed m = true) :
    check_sigaltstack i uss uoss eff m = CheckUnmodeled := by
  simp only [check_sigaltstack, hin, ↓reduceIte]

/-- The answers a kernel would give — 0 on the install, 0 on the disable,
-ENOMEM on the small one, -EFAULT on the unreadable one — are NOT
`CheckOk` on the installed model, and not `CheckReject` either: the arm
declines rather than judges.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_installed_answers_neither_accepted_nor_rejected :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        installed_model ≠ CheckOk installed_model []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        installed_model ≠ CheckOk (with_sigaltstack_installed installed_model) []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        installed_model ≠ CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0
        (mkEffect 0 [] []) installed_model ≠ CheckOk installed_model []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) installed_model ≠ CheckOk installed_model []
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret EFAULT) [] [])
        installed_model ≠ CheckOk installed_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

end AltstackInstalled

section AltstackUoss

/-! ## `do_sigaltstack` with `oss`: the inherited flags word

`oss->ss_flags = sas_ss_flags(sp) | (current->sas_ss_flags & SS_FLAG_BITS)`
(kernel/signal.c:4408-4409, Linux v6.18.46): the second half is the bit
`begin_new_exec` never resets (fs/exec.c:1211 clears the pointer and the
size only), so the answer depends on what called `execve`, and a non-NULL
`uoss` declines whatever `uss` says and whatever effect is offered. -/

/-- A non-NULL `uoss` declines on every effect: with `uss` NULL (the pure
query), with a good install beside it, with an unreadable `uss`, and at
`uoss = 2^32` — a pointer whose low half is 0 is still not NULL.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_uoss_declines (eff : SyscallEffect) :
    check_sigaltstack (sigaltstack_in mem_none mem_none) 0 8192 eff sig_model_blocked
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 8192 eff
        sig_model_blocked = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 8192 eff sig_model_blocked
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 0 4294967296 eff sig_model_blocked
        = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The `uoss` gate is second, on every uninstalled model, every input,
every `uss` and every effect.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_uoss_declines_symbolically (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model) (hin : m_sigaltstack_installed m = false)
    (ho : w_is0 uoss = false) :
    check_sigaltstack i uss uoss eff m = CheckUnmodeled := by
  simp only [check_sigaltstack, hin, ho, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

/-- The two answers a kernel would give the query — 0 with the record an
empty stack reads back (`ss_sp` 0, `ss_flags` SS_DISABLE by `sas_ss_flags`,
include/linux/sched/signal.h:604-610, Linux v6.18.46, bit 31 inherited or
not, `ss_size` 0), or -EFAULT on an unwritable `uoss` — are neither
accepted nor rejected: the decline is not a verdict on them.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_uoss_answers_neither_accepted_nor_rejected :
    check_sigaltstack (sigaltstack_in mem_none mem_none) 0 8192
        (mkEffect 0 [(8192, [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
                             0, 0, 0, 0, 0, 0, 0, 0])] []) sig_model_blocked
        ≠ CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 0 8192
        (mkEffect 0 [(8192, [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
                             0, 0, 0, 0, 0, 0, 0, 0])] []) sig_model_blocked ≠ CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 0 8192
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked ≠ CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 0 8192
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked ≠ CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

end AltstackUoss

section AltstackNullNull

/-! ## `sigaltstack(NULL, NULL)`: nothing to do

With `uss` NULL the syscall copies nothing (kernel/signal.c:4459, Linux
v6.18.46) and `do_sigaltstack` with both arguments NULL runs neither
branch and returns its initial 0 (:4402, :4452): 0, the model unchanged,
on every input. -/

/-- NULL/NULL is 0 with the model untouched, on both spec fixtures and on
any input at all — the memory is never read.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_null_null_accepts_zero (i : SyscallInput) :
    check_sigaltstack i 0 0 (mkEffect 0 [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack i 0 0 (mkEffect 0 [] []) demo_model = CheckOk demo_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm_altstack_kill

/-- NULL/NULL is 0 on every uninstalled model.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_null_null_accepts_zero_symbolically (i : SyscallInput) (m : Model)
    (hin : m_sigaltstack_installed m = false) :
    check_sigaltstack i 0 0 (mkEffect 0 [] []) m = CheckOk m [] := by
  simp +decide only [check_sigaltstack, check_ret_only, hin, Bool.false_eq_true, ↓reduceIte]

/-- The lies at NULL/NULL: -EFAULT (nothing was copied), -EINVAL, a store,
and a 0 that claims the bit was set.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem check_sigaltstack_null_null_rejects_the_lies (i : SyscallInput) :
    check_sigaltstack i 0 0 (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack i 0 0 (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack i 0 0 (mkEffect 0 [(4096, [0])] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack i 0 0 (mkEffect 0 [] []) sig_model_blocked
        ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

end AltstackNullNull

section AltstackCopyIn

/-! ## `copy_from_user(&new, uss, sizeof(stack_t))`: 24 bytes, all or nothing

`if (uss && copy_from_user(&new, uss, sizeof(stack_t))) return -EFAULT;`
(kernel/signal.c:4459-4460, Linux v6.18.46), before `do_sigaltstack` sees
anything: -EFAULT precedes -EINVAL and -ENOMEM, and 24 bytes are the
struct (include/uapi/asm-generic/signal.h:85-89). -/

/-- -EFAULT, model untouched, on every unreadable `uss`: nothing mapped,
23 of 24 bytes mapped, the low address 8, a `uss` at 2^32 over a map at
4096, and the top of memory, whose 24-byte walk wraps.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem check_sigaltstack_unreadable_uss_accepts_efault :
    check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret EFAULT) [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_short mem_none) 4096 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 8 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4294967296 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 18446744073709551608 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckOk sig_model_blocked [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies on an unreadable `uss`: 0, -EINVAL, -ENOMEM, -EFAULT beside
a store, -EFAULT beside the 24-byte ledger, and a 0 with the bit set.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem check_sigaltstack_unreadable_uss_rejects_the_lies :
    check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret EINVAL) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret ENOMEM) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0
        (mkEffect (errno_ret EFAULT) [(4096, [0])] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(4096, 24)]) sig_model_blocked
        = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_short mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- 24 bytes are enough: the same list mapped at 4294971392 (2^32 + 4096)
installs when `uss` names it and is -EFAULT when `uss` is 4096.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem check_sigaltstack_24_bytes_are_enough :
    check_sigaltstack (sigaltstack_in mem_ss_ok_high mem_none) 4294971392 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_ok_high mem_none) 4096 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_ok_high mem_none) 4294971392 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- -EFAULT beats -EINVAL: the mode-3 struct in an unreadable `uss` is
-EFAULT, and -EINVAL is refused, because :4459 runs before :4421.
kernel: kernel/signal.c:sigaltstack,do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_efault_beats_einval :
    check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret EFAULT) [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect (errno_ret EINVAL) [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_none mem_none) 4096 0 (mkEffect (errno_ret EINVAL) [] [])
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end AltstackCopyIn

section AltstackMode

/-! ## `do_sigaltstack`: the mode, after the copy and before the fast path

`ss_mode = ss_flags & ~SS_FLAG_BITS; if (ss_mode != SS_DISABLE && ss_mode
!= SS_ONSTACK && ss_mode != 0) return -EINVAL;` (kernel/signal.c:4421-4424,
Linux v6.18.46), on the `unsigned ss_flags = ss->ss_flags` read four bytes
wide (:4415).  The -EPERM ahead of it (:4418-4419) cannot fire while the
recorded size is zero. -/

/-- -EINVAL, model untouched, on every mode outside {0, SS_ONSTACK,
SS_DISABLE}: 3, 4, 0x7fffffff, 0xffffffff (mode 0x7fffffff once bit 31 is
masked), SS_AUTODISARM over 3, the top flags byte alone, and mode 3 with
the padding byte at offset 12 set.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_bad_mode_accepts_einval :
    check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect (errno_ret EINVAL) [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode4 mem_none) 4096 0 (mkEffect (errno_ret EINVAL) [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode_7fffffff mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode_ffffffff mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm_mode3 mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_flags_top_byte mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_bit32_mode3 mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies on a bad mode: 0, -ENOMEM, -EFAULT (the copy succeeded),
-EPERM, -EINVAL beside a store, 22 (the errno with its sign lost), and a
0 that installs.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_bad_mode_rejects_the_lies :
    check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect 22 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect (errno_ret ENOMEM) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect (errno_ret EFAULT) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect (errno_ret EPERM) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [(4096, [0])] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode_ffffffff mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3 mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- -EINVAL beats -ENOMEM: mode 3 over a 1-byte size is -EINVAL and
-ENOMEM is refused, because :4421 runs before :4440.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_einval_beats_enomem :
    check_sigaltstack (sigaltstack_in mem_ss_mode3_small mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_mode3_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm_altstack_kill

/-- The accepted modes with a real stack install: SS_ONSTACK, SS_AUTODISARM
alone (mode 0 once bit 31 is masked), the two together, and mode 0 with
the padding byte at offset 12 set — `ss_flags` is four bytes wide and
that byte is not one of them.  -EINVAL is refused on each.  The two
SS_AUTODISARM shapes are Linux's answer alone: qemu-user's
`target_restore_altstack` switches on the raw flags word and answers
-EINVAL to every value with bit 31 set (linux-user/signal.c:317-319,
QEMU v11.1.1), and `linux-process-semantics@ff0313ba4f:bugs/sigaltstack-autodisarm-mode-admits-linux-alone.md`
records that the spec's arm, which this checker restates, proves as
certain an answer outside the supported intersection there.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_accepted_modes_install :
    check_sigaltstack (sigaltstack_in mem_ss_onstack mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm_onstack mem_none) 4096 0
        (mkEffect 0 [] []) sig_model_blocked
        = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_bit32 mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_onstack mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_bit32 mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end AltstackMode

section AltstackDisable

/-! ## `do_sigaltstack`'s SS_DISABLE branch: a write that does not shut the door

`if (ss_mode == SS_DISABLE) { ss_size = 0; ss_sp = NULL; }`
(kernel/signal.c:4436-4438, Linux v6.18.46) before the store (:4445-4448):
the record it leaves is (NULL, 0, ss_flags), the zero-size shape whose two
readers are constant in sp, so the bit stays clear and the checker keeps
answering. -/

/-- Rocq's `sigaltstack_disable_leaves_the_record_answerable`: the disable
is 0 with the model UNCHANGED; the undersized install after it is still
-ENOMEM on the same model; and the same undersized install on the
installed model declines.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_disable_leaves_the_record_answerable :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) installed_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- Rocq's `sigaltstack_install_still_sets_the_bit`: the install answers
with the bit set, and the disable does NOT answer with it set.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_still_sets_the_bit :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_⟩
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- Rocq's `sigaltstack_after_a_disable_rejects_a_false_success`: the
undersized install offered a 0 is refused, and a store smuggled through
the disable is refused too.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_after_a_disable_rejects_a_false_success :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0
        (mkEffect 0 [(4096, [0])] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm_altstack_kill

/-- SS_DISABLE ignores the size and rides with SS_AUTODISARM: the 1-byte
disable and the autodisarm disable are both 0 with the model unchanged,
-ENOMEM is refused on the first, and neither sets the bit.  The
autodisarm disable is Linux's answer alone, for the reason
`check_sigaltstack_accepted_modes_install` gives (qemu-user, QEMU v11.1.1,
answers -EINVAL to bit 31 at linux-user/signal.c:317-319) and
`linux-process-semantics@ff0313ba4f:bugs/sigaltstack-autodisarm-mode-admits-linux-alone.md` records.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_disable_ignores_the_size_and_autodisarm :
    check_sigaltstack (sigaltstack_in mem_ss_disable_small mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm_disable mem_none) 4096 0
        (mkEffect 0 [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_disable_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_autodisarm_disable mem_none) 4096 0
        (mkEffect 0 [] []) sig_model_blocked
        ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- The disable is 0 with the model unchanged on every uninstalled model.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_disable_accepts_zero_symbolically (m : Model)
    (hin : m_sigaltstack_installed m = false) :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_disable mem_none) 4096 0 (mkEffect 0 [] []) m
        = CheckOk m [] := by
  simp +decide only [check_sigaltstack, check_ret_only, hin, Bool.false_eq_true, ↓reduceIte,
    sys_simp]

end AltstackDisable

section AltstackShadow

/-! ## The fast path's shadow: `ss_sp` and `ss_size` both zero

`if (t->sas_ss_sp == ss_sp && t->sas_ss_size == ss_size && t->sas_ss_flags
== ss_flags) return 0;` (kernel/signal.c:4430-4433, Linux v6.18.46) is the
only kernel answer whose value turns on the stored flags word the model
does not track: from the starting record (NULL, 0, F) it fires exactly
when the caller's `ss_flags` equals F, and otherwise the zero size is
-ENOMEM (:4440-4441).  The all-zero struct under a non-disabling mode
declines; the two shapes beside it are answered. -/

/-- The shadow declines on every effect: the all-zero struct, and the same
under SS_ONSTACK and under SS_AUTODISARM.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_fast_path_shadow_declines (eff : SyscallEffect) :
    check_sigaltstack (sigaltstack_in mem_ss_zero mem_none) 4096 0 eff sig_model_blocked
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_ss_zero_onstack mem_none) 4096 0 eff sig_model_blocked
        = CheckUnmodeled
    ∧ check_sigaltstack (sigaltstack_in mem_ss_zero_autodisarm mem_none) 4096 0 eff
        sig_model_blocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- Beside the shadow, both answered: size 0 with a non-zero `ss_sp` is
-ENOMEM (the fast path cannot fire against a NULL record), `ss_sp` 0 with
a 16 KiB size installs, and the far pointer over size 0 is -ENOMEM; the
0 is refused where -ENOMEM is accepted.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_beside_the_shadow_answers :
    check_sigaltstack (sigaltstack_in mem_ss_size_zero mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_size_zero mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_sp_zero mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_far_size_zero mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_far_size_zero mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end AltstackShadow

section AltstackMinsigstksz

/-! ## `ss_size < min_ss_size`: MINSIGSTKSZ, from both sides

`if (unlikely(ss_size < min_ss_size)) ret = -ENOMEM;` (kernel/signal.c:4440-4441,
Linux v6.18.46) with `min_ss_size` the MINSIGSTKSZ the syscall passes
(:4461-4463), 2048 on riscv64; `sigaltstack_size_valid` beside it
(:4442-4443) never decides a case this bound has not — under the ISA
premise the spec header carries (`Sys/Kernel/Signal.lean`, on
`sigaltstack_spec`): on riscv it is `ss_size > get_rt_frame_size(false)`
(arch/riscv/kernel/signal.c:479-482, Linux v6.18.46), 1088 bytes while
the task's vector state is off, and no modeled instruction turns it on.
The day the ISA model decodes a V instruction, "2048 installs" below
stops being Linux's answer on a hart whose vector context pushes the
frame past 2048 bytes. -/

/-- Rocq's `sigaltstack_enomem_keeps_the_record`: the 1 KiB stack is
-ENOMEM with the model UNCHANGED — the bit stays clear, so the next call
is still answered.  Beside it, both sides of the bound: 2048 installs and
2047 is -ENOMEM.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_enomem_keeps_the_record :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_min mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_below_min mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies at the bound: 0 on 1 KiB and on 2047, -ENOMEM on 2048,
-ENOMEM beside a store, and an -ENOMEM that claims the bit.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_enomem_rejects_the_lies :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_below_min mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_min mem_none) 4096 0 (mkEffect (errno_ret ENOMEM) [] [])
        sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [(4096, [0])] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_small mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked
        ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- No upper bound this side of `sigaltstack_size_valid`: 2^32 and
`(size_t)-1` both install, and -ENOMEM is refused on each.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_large_sizes_install :
    check_sigaltstack (sigaltstack_in mem_ss_size_2_32 mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_huge mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_size_2_32 mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_ss_huge mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end AltstackMinsigstksz

section AltstackInstall

/-! ## The install: the one arm that raises `sas_ss_size`

`t->sas_ss_sp = ss_sp; t->sas_ss_size = ss_size; t->sas_ss_flags = ss_flags;`
(kernel/signal.c:4445-4448, Linux v6.18.46), reached with a non-zero
`ss_size`: the bit is set, the return is 0, and no user memory is written
or recorded — the 24 bytes went into a kernel local (:4457). -/

/-- Rocq's `sigaltstack_leaves_the_mask_alone`: the install answers
`CheckOk (with_sigaltstack_installed sig_model_blocked) []`, and that
model's mask is still the entry mask — the install touches the record and
nothing else.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_leaves_the_mask_alone :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ m_sigmask (with_sigaltstack_installed sig_model_blocked) = sig_entry_mask := by
  refine ⟨?_, rfl⟩
  check_norm_altstack_kill

/-- Rocq's `sigaltstack_success_admits_no_write`, and the ledger beside
it: a store smuggled through the install, a zero-fill, an unmap, a
pre-effect copy and the 24-byte copy-in record are each refused — the
effect is a bare return.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_rejects_a_write_or_a_ledger :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect 0 [(4096, [0])] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect 0 [] [(4096, 24)]) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (SyscallEffect.mkEffectU 0 [] [] [(4096, 24)] [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (SyscallEffect.mkEffectU 0 [] [] [] [⟨4096, 8192, 24⟩] []) sig_model_blocked
        = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 24)]) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The install's return is 0 and nothing else: -ENOMEM, -EPERM, -EINVAL,
-EFAULT and 1 are refused on the 16 KiB stack.
kernel: kernel/signal.c:sigaltstack,do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_rejects_every_other_return :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect (errno_ret EPERM) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckReject
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 1 [] [])
        sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The install without the bit is not the answer, and neither is the
install on a different model or with an event beside it: the model that
comes back is the given one with the bit set and nothing else changed,
and the event list is empty.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_answers_exactly_the_bit (ev : event) :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk sig_model_blocked []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk (with_sigaltstack_installed demo_model) []
    ∧ check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [ev] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_refute_altstack_kill

/-- An `ss_sp` nothing maps (0x7f0000000000) installs all the same: the
kernel stores the pointer and never dereferences it here.
kernel: kernel/signal.c:sigaltstack,do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_far_sp_installs :
    check_sigaltstack (sigaltstack_in mem_ss_far mem_none) 4096 0 (mkEffect 0 [] [])
        sig_model_blocked = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_sigaltstack (sigaltstack_in mem_ss_far mem_none) 4096 0
        (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm_altstack_kill

/-- The install on the Rocq fixture map answers with the bit set on EVERY
uninstalled model, whatever else the model holds.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem check_sigaltstack_install_symbolically (m : Model)
    (hin : m_sigaltstack_installed m = false) :
    check_sigaltstack (sigaltstack_in mem_sigaltstack_ok mem_none) 4096 0 (mkEffect 0 [] []) m
        = CheckOk (with_sigaltstack_installed m) [] := by
  simp +decide only [check_sigaltstack, check_ret_only, hin, Bool.false_eq_true, ↓reduceIte,
    sys_simp]

end AltstackInstall

section KillDeclaration

/-! ## `tkill` (130) and `tgkill` (131): the declaration, ahead of the kernel

`State.in_abort_terminal` is the task's stance, and with it clear all
three checkers answer `CheckUnmodeled` for EVERY argument shape and every
effect — before the -EINVAL `SYSCALL_DEFINE2(tkill)` (kernel/signal.c:4195-4196,
Linux v6.18.46) would answer first — because a coverage gate is not a
kernel test.  `abort_model_undeclared` has the tid pinned and the
declaration off; `one_sided_model` has SIGABRT blocked and pending with
the declaration off. -/

/-- Rocq's `tkill_off_declined` and `tgkill_off_declined`, on every
effect: the well-formed self-abort under the declaration off declines,
and so does `check_tkill_self` reached directly.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem check_tkill_off_declined (eff : SyscallEffect) :
    check_tkill 4242 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tgkill 4242 4242 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tkill_self 4242 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tkill 4242 6 eff one_sided_model = CheckUnmodeled
    ∧ check_tgkill 4242 4242 6 eff one_sided_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The declaration beats every kernel test: pid 0, signal 65, a wrong
tgid and a pid the model does not know all decline with it off, where
each would be answered or declined for its own reason with it on.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem check_tkill_off_beats_every_kernel_test (eff : SyscallEffect) :
    check_tkill 0 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tkill 4242 65 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tgkill 7 4242 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tgkill 0 0 6 eff abort_model_undeclared = CheckUnmodeled
    ∧ check_tkill 4243 6 eff abort_model_undeclared = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The declaration is the FIRST gate of all three checkers, on every
model with it off, every argument and every effect: the worked case of
`tkill_spec_off_unmodeled` at the checker.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem check_tkill_off_declines_symbolically (pid tgid sig : word) (eff : SyscallEffect)
    (m : Model) (hoff : m_abort_terminal m = false) :
    check_tkill pid sig eff m = CheckUnmodeled
    ∧ check_tgkill tgid pid sig eff m = CheckUnmodeled
    ∧ check_tkill_self pid sig eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [check_tkill, hoff, Bool.not_false, ↓reduceIte]
  · simp only [check_tgkill, hoff, Bool.not_false, ↓reduceIte]
  · simp only [check_tkill_self, hoff, Bool.not_false, ↓reduceIte]

/-- The kernel's own answers under the declaration off are neither
accepted nor rejected: the -EINVAL at pid 0, the death at 4242/6 and the
pending bit on the one-sided model.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem check_tkill_off_answers_neither_accepted_nor_rejected :
    check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_undeclared
        ≠ CheckOk abort_model_undeclared []
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_undeclared ≠ CheckReject
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_undeclared
        ≠ CheckOk (with_killed 6 abort_model_undeclared) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_undeclared ≠ CheckReject
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) one_sided_model ≠ CheckOk one_sided_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

end KillDeclaration

section KillPid

/-! ## The two `SYSCALL_DEFINE`s: `pid <= 0`

`SYSCALL_DEFINE2(tkill)` refuses `pid <= 0` with -EINVAL
(kernel/signal.c:4195-4196, Linux v6.18.46) and `SYSCALL_DEFINE3(tgkill)`
refuses `pid <= 0 || tgid <= 0` (:4179-4180), on the `pid_t` — an `int`,
so every negative value is at or above 2^31 after the table's `pid32` —
before any task is looked up.  `abort_model_unblocked` has the declaration
on, the tid 4242 pinned and nothing blocked. -/

/-- Rocq's `tkill_nonpositive_pid_einval`, and the negatives beside it:
pid 0, 2^31 (INT_MIN) and 2^32 - 1 (-1) are -EINVAL with the model
untouched — on the tid-pinned model and on the one with no tid at all,
since the test precedes the lookup.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem check_tkill_nonpositive_pid_einval :
    check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 2147483648 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 4294967295 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned
        = CheckOk abort_model_unpinned [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies at a non-positive pid: 0, -ESRCH (no task was looked up),
22 (the errno with its sign lost), -EINVAL beside a store, and an -EINVAL
that pends or kills.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem check_tkill_nonpositive_pid_rejects_the_lies :
    check_tkill 0 6 (mkEffect 0 [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 0 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 0 6 (mkEffect 22 [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) abort_model_unblocked
        = CheckReject
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 6 abort_model_unblocked) []
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_blocked
        ≠ CheckOk (with_sigabrt_pending abort_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill
  · check_refute_altstack_kill

/-- The pid test beats the signal: pid 0 with signal 10 is -EINVAL and
ANSWERED, where 4242 with signal 10 declines; and every positive pid
passes the gate — 1, 4242 and 2^31 - 1 reach the lookup, where the two
that are not the caller decline.
kernel: kernel/signal.c:tkill,do_send_specific@v6.18.46 -/
theorem check_tkill_nonpositive_pid_beats_the_signal (eff : SyscallEffect) :
    check_tkill 0 10 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 4242 10 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 1 6 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 2147483647 6 eff abort_model_unblocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- tgkill's gate reads both: (0, 4242), (4242, 0), (2^31, 4242) and
(4242, 2^32 - 1) are each -EINVAL, and the -EINVAL is the answer even
where the tgid would be wrong — (0, 0) is -EINVAL and not -ESRCH.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem check_tgkill_nonpositive_einval :
    check_tgkill 0 4242 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 4242 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 2147483648 4242 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 4242 4294967295 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 0 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 0 0 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked = CheckReject
    ∧ check_tgkill 0 4242 6 (mkEffect 0 [] []) abort_model_unblocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end KillPid

section KillLookup

/-! ## `find_task_by_vpid`: a task this model does not know

`p = find_task_by_vpid(pid); if (p && …)` (kernel/signal.c:4134-4135,
Linux v6.18.46) searches the whole pid namespace; the model knows one
task, its own, and only once something has pinned its tid.  Every other
positive pid declines — -ESRCH would be a claim about every other process
on the machine — and so does a call before the tid is pinned. -/

/-- Rocq's `tkill_other_pid_declined`, on every effect: 4243 and 1 decline
under tkill, and under tgkill with the caller's own tgid or with 4243 as
tgid; a bad signal beside the unknown pid still declines, since the
lookup precedes `check_kill_permission`.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tkill_other_pid_declined (eff : SyscallEffect) :
    check_tkill 4243 6 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 1 6 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tgkill 4242 4243 6 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tgkill 4243 4243 6 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 4243 65 eff abort_model_unblocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- A tid the model has not pinned declines on every effect, under both
arms — and a non-positive pid or tgid is STILL -EINVAL there under both,
since `SYSCALL_DEFINE2(tkill)`'s and `SYSCALL_DEFINE3(tgkill)`'s tests
(kernel/signal.c:4195-4196 and :4179-4180, Linux v6.18.46) precede the
lookup (:4134): tgkill with tgid 0, with pid 0 and with both 0 is -EINVAL
before the tid is pinned, and the -ESRCH a lookup would earn is a lie
there.  A checker that looked the tid up first would decline these four
where Linux answers.
kernel: kernel/signal.c:tkill,tgkill,do_send_specific@v6.18.46 -/
theorem check_tkill_unpinned_tid_declined (eff : SyscallEffect) :
    check_tkill 4242 6 eff abort_model_unpinned = CheckUnmodeled
    ∧ check_tgkill 4242 4242 6 eff abort_model_unpinned = CheckUnmodeled
    ∧ check_tkill 4242 65 eff abort_model_unpinned = CheckUnmodeled
    ∧ check_tkill 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned
        = CheckOk abort_model_unpinned []
    ∧ check_tgkill 0 4242 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned
        = CheckOk abort_model_unpinned []
    ∧ check_tgkill 4242 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned
        = CheckOk abort_model_unpinned []
    ∧ check_tgkill 0 0 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned
        = CheckOk abort_model_unpinned []
    ∧ check_tgkill 0 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unpinned
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The answers a kernel might give about another task — -ESRCH, -EPERM,
0 — are neither accepted nor rejected for 4243.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tkill_other_pid_answers_neither_accepted_nor_rejected :
    check_tkill 4243 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        ≠ CheckOk abort_model_unblocked []
    ∧ check_tkill 4243 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked ≠ CheckReject
    ∧ check_tkill 4243 6 (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked ≠ CheckReject
    ∧ check_tkill 4243 6 (mkEffect 0 [] []) abort_model_unblocked ≠ CheckReject
    ∧ check_tkill 4243 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 6 abort_model_unblocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

end KillLookup

section KillTgid

/-! ## `do_send_specific`'s tgid test: -ESRCH for the caller under another group

`int error = -ESRCH; … if (p && (tgid <= 0 || task_tgid_vnr(p) == tgid))`
(kernel/signal.c:4131, :4135, Linux v6.18.46): the task is found and its
thread-group id does not match, so the seeded -ESRCH stands and
`check_kill_permission` never runs.  One thread, one group: the caller's
tgid is its tid. -/

/-- Rocq's `tgkill_wrong_tgid_esrch`: tgid 7 for the caller's own tid is
-ESRCH with the model untouched; so is INT_MAX, and so is 7 beside a bad
signal or a foreign one, since the tgid test precedes `valid_signal`.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tgkill_wrong_tgid_esrch :
    check_tgkill 7 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 2147483647 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 7 4242 65 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 7 4242 10 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies at a wrong tgid: 0, -EINVAL (the signal was never tested),
-EPERM, -ESRCH beside a store, and an -ESRCH that kills; and -ESRCH at
the caller's OWN tgid, where the send goes through.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tgkill_wrong_tgid_rejects_the_lies :
    check_tgkill 7 4242 6 (mkEffect 0 [] []) abort_model_unblocked = CheckReject
    ∧ check_tgkill 7 4242 65 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked = CheckReject
    ∧ check_tgkill 7 4242 6 (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked = CheckReject
    ∧ check_tgkill 7 4242 6 (mkEffect (errno_ret ESRCH) [(4096, [0])] []) abort_model_unblocked
        = CheckReject
    ∧ check_tgkill 7 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 6 abort_model_unblocked) []
    ∧ check_tgkill 4242 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill
  · check_norm_altstack_kill

end KillTgid

section KillValidSignal

/-! ## `check_kill_permission`: `valid_signal`

`check_kill_permission`'s first test (kernel/signal.c:805-806, Linux
v6.18.46) is reached because the task lookup succeeded, and it is
`valid_signal` (include/linux/signal.h:272-275, Linux v6.18.46): `sig <=
_NSIG` on the widened `unsigned long`, 64 included.  A negative `int`
widens to something enormous and fails. -/

/-- 65 and 2^32 - 1 (-1) are -EINVAL with the model untouched, under tkill
and under tgkill with the caller's own tgid; 64 passes the test and
declines as a signal the model has no disposition for.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem check_tkill_bad_signal_einval (eff : SyscallEffect) :
    check_tkill 4242 65 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 4242 4294967295 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tgkill 4242 4242 65 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        = CheckOk abort_model_unblocked []
    ∧ check_tkill 4242 64 eff abort_model_unblocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The lies at signal 65: 0, -ESRCH, -EPERM, -EINVAL beside a store, and
an -EINVAL that kills.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem check_tkill_bad_signal_rejects_the_lies :
    check_tkill 4242 65 (mkEffect 0 [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 65 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 65 (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 65 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) abort_model_unblocked
        = CheckReject
    ∧ check_tkill 4242 65 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 6 abort_model_unblocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill

end KillValidSignal

section KillOtherSignals

/-! ## The null signal, and every signal but SIGABRT

`if (!error && sig)` (kernel/signal.c:4141, Linux v6.18.46): signal 0 is a
permission-and-existence probe whose answer is `security_task_kill`'s
(:832), an LSM question; every other signal in 1..64 would be delivered,
and the model has a disposition for SIGABRT and for no other. -/

/-- Rocq's `tkill_signal_zero_declined` and `tkill_other_signal_declined`,
on every effect: 0, SIGUSR1 (10), SIGKILL (9), SIGSEGV (11) and 64 decline
under tkill, and 0 and 10 under tgkill with the caller's own tgid.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tkill_other_signal_declined (eff : SyscallEffect) :
    check_tkill 4242 0 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 4242 10 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 4242 9 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 4242 11 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tkill 4242 64 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tgkill 4242 4242 0 eff abort_model_unblocked = CheckUnmodeled
    ∧ check_tgkill 4242 4242 10 eff abort_model_unblocked = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The kernel's likely answers — 0 to the null signal, 0 and a death to
SIGUSR1 — are neither accepted nor rejected: the decline is not a
verdict.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tkill_other_signal_answers_neither_accepted_nor_rejected :
    check_tkill 4242 0 (mkEffect 0 [] []) abort_model_unblocked ≠ CheckOk abort_model_unblocked []
    ∧ check_tkill 4242 0 (mkEffect 0 [] []) abort_model_unblocked ≠ CheckReject
    ∧ check_tkill 4242 10 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 10 abort_model_unblocked) []
    ∧ check_tkill 4242 10 (mkEffect 0 [] []) abort_model_unblocked ≠ CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

end KillOtherSignals

section KillSigabrt

/-! ## SIGABRT to oneself: pending under the mask, fatal without it

`__send_signal_locked` adds the signal to the pending set
(`sigaddset(&pending->signal, sig)`, kernel/signal.c:1137, Linux v6.18.46),
and `complete_signal` does not flag a task whose mask covers it —
`wants_signal` returns false on `sigismember(&p->blocked, sig)` (:946-949)
— so it stays pending until a mask change lets `recalc_sigpending_tsk`
(:159-175) find it; an unblocked one is taken on the way back to user
space, where `get_signal` finds SIG_DFL (:2942) for a coredumping signal
and reaches the fatal branch (:3016-3043).  That it finds SIG_DFL is the
launch premise `linux-process-semantics@ff0313ba4f:bugs/tkill-assumes-sigabrt-not-ignored-at-launch.md`
records and Rocq's `Run.v` cites: `flush_signal_handlers` (:519-534,
called from `begin_new_exec`, fs/exec.c:1252, Linux v6.18.46) resets a
handler to SIG_DFL but keeps a SIG_IGN across execve, and the model has no
state for the disposition the process inherits.  `abort_model_blocked` has
SIGABRT (bit 5, so 32) blocked; the `abort_model_*_others` fixtures set
other bits beside or instead of it, because the kernel tests the one bit
and a predicate reading "any bit" or "exactly 32" must not pass. -/

/-- Rocq's `tkill_sigabrt_unblocked_kills`, `tkill_sigabrt_blocked_pends`
and `tgkill_self_sigabrt_kills`: the unblocked send answers 0 with the
process killed by 6, the blocked one 0 with the signal pending, and tgkill
with the caller's own tgid and tid reaches the same two places.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem check_tkill_sigabrt_kills_or_pends :
    check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        = CheckOk (with_killed 6 abort_model_unblocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked
        = CheckOk (with_sigabrt_pending abort_model_blocked) []
    ∧ check_tgkill 4242 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        = CheckOk (with_killed 6 abort_model_unblocked) []
    ∧ check_tgkill 4242 4242 6 (mkEffect 0 [] []) abort_model_blocked
        = CheckOk (with_sigabrt_pending abort_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The mask is read at ONE bit: SIGABRT unblocked among other blocked
signals (0x10006) kills, SIGABRT blocked among others (0x10026) pends, and
every blockable signal but SIGABRT blocked (0xfffffffffffbfedf) kills —
with the wrong answer refuted on each, so a `sigabrt_blocked` reading
"any bit", "exactly 32" or another bit fails here.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem check_tkill_reads_one_bit_of_the_mask :
    check_tkill 4242 6 (mkEffect 0 [] []) abort_model_others_blocked
        = CheckOk (with_killed 6 abort_model_others_blocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked_among_others
        = CheckOk (with_sigabrt_pending abort_model_blocked_among_others) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_all_but_sigabrt_blocked
        = CheckOk (with_killed 6 abort_model_all_but_sigabrt_blocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_others_blocked
        ≠ CheckOk (with_sigabrt_pending abort_model_others_blocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked_among_others
        ≠ CheckOk (with_killed 6 abort_model_blocked_among_others) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_all_but_sigabrt_blocked
        ≠ CheckOk (with_sigabrt_pending abort_model_all_but_sigabrt_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill
  · check_refute_altstack_kill
  · check_refute_altstack_kill

/-- A second blocked send finds the bit already set and leaves it set:
`__send_signal_locked` drops a standard signal that is already pending
(`legacy_queue`, kernel/signal.c:1037-1040, tested at :1062-1064) before
`sigaddset` (:1137) is reached, and the model's setter is idempotent.
kernel: kernel/signal.c:__send_signal_locked,legacy_queue@v6.18.46 -/
theorem check_tkill_pending_twice_stays_pending :
    check_tkill 4242 6 (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked)
        = CheckOk (with_sigabrt_pending (with_sigabrt_pending abort_model_blocked)) []
    ∧ with_sigabrt_pending (with_sigabrt_pending abort_model_blocked)
        = with_sigabrt_pending abort_model_blocked
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked)
        ≠ CheckOk (with_killed 6 (with_sigabrt_pending abort_model_blocked)) [] := by
  refine ⟨?_, rfl, ?_⟩
  · check_norm_altstack_kill
  · check_refute_altstack_kill

/-- Rocq's `tkill_reads_the_mask_and_writes_none`: the two fixtures differ
in the mask alone, the send WRITES no mask — both answers keep the mask
they were given — and the two answers differ.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem check_tkill_reads_the_mask_and_writes_none :
    m_sigmask abort_model_unblocked = 0 ∧ m_sigmask abort_model_blocked = 32
    ∧ m_sigmask (with_killed 6 abort_model_unblocked) = 0
    ∧ m_sigmask (with_sigabrt_pending abort_model_blocked) = 32
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  check_refute_altstack_kill

/-- The lies about the two sends, as the spec pins
`tkill_blocked_lies_rejected` and `tkill_unblocked_lies_rejected`
(`Checks/Cases/Kernel/Signal.lean`, with no Rocq twin) state them: a
death where the signal pends, a pending bit where the process died, a
process left as it was on either side, and — on the two right models —
an event list forged beside the bare return.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem check_tkill_wrong_model_rejected (ev : event) :
    check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked
        ≠ CheckOk (with_killed 6 abort_model_blocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked ≠ CheckOk abort_model_blocked []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_sigabrt_pending abort_model_unblocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk abort_model_unblocked []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 9 abort_model_unblocked) []
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_blocked
        ≠ CheckOk (with_sigabrt_pending abort_model_blocked) [ev]
    ∧ check_tkill 4242 6 (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_killed 6 abort_model_unblocked) [ev] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_refute_altstack_kill

/-- Rocq's `tkill_forged_write_rejected`, and the ledger and zero-fill
beside it: neither send writes user memory, zeroes, unmaps or copies
anything, or copies anything in, on either side of the mask.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem check_tkill_forged_write_rejected :
    check_tkill 4242 6 (mkEffect 0 [(4096, [0])] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect 0 [(4096, [0])] []) abort_model_blocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect 0 [] [(4096, 8)]) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (SyscallEffect.mkEffectU 0 [] [] [(4096, 8)] [] []) abort_model_unblocked
        = CheckReject
    ∧ check_tkill 4242 6 (SyscallEffect.mkEffectU 0 [] [] [] [⟨4096, 8192, 8⟩] [])
        abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 8)]) abort_model_unblocked
        = CheckReject
    ∧ check_tgkill 4242 4242 6 (mkEffect 0 [(4096, [0])] []) abort_model_unblocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- Rocq's `tkill_forged_return_rejected`, and every other non-zero return:
an LSM's -EPERM (linux-process-semantics@ff0313ba4f:bugs/tkill-lsm-denial-not-admitted.md), -ESRCH for the
caller itself, -EINVAL for a valid signal, and 1 — on both sides of the
mask.  The fatal branch still claims 0.
kernel: kernel/signal.c:do_send_specific,check_kill_permission@v6.18.46 -/
theorem check_tkill_forged_return_rejected :
    check_tkill 4242 6 (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect 1 [] []) abort_model_unblocked = CheckReject
    ∧ check_tkill 4242 6 (mkEffect (errno_ret EPERM) [] []) abort_model_blocked = CheckReject
    ∧ check_tgkill 4242 4242 6 (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The delivery acceptor directly: a bare 0 on each model, with the
pending bit or the kill, and the two lies refuted on each.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem check_send_sigabrt_pends_or_kills :
    check_send_sigabrt (mkEffect 0 [] []) abort_model_blocked
        = CheckOk (with_sigabrt_pending abort_model_blocked) []
    ∧ check_send_sigabrt (mkEffect 0 [] []) abort_model_unblocked
        = CheckOk (with_killed 6 abort_model_unblocked) []
    ∧ check_send_sigabrt (mkEffect 0 [] []) abort_model_blocked
        ≠ CheckOk (with_killed 6 abort_model_blocked) []
    ∧ check_send_sigabrt (mkEffect 0 [] []) abort_model_unblocked
        ≠ CheckOk (with_sigabrt_pending abort_model_unblocked) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · check_norm_altstack_kill
  · check_norm_altstack_kill
  · check_refute_altstack_kill
  · check_refute_altstack_kill

/-- The delivery acceptor rejects every effect but the bare 0, and never
declines: -EPERM, a store, the ledger, and 1.
kernel: kernel/signal.c:do_send_specific,check_kill_permission@v6.18.46 -/
theorem check_send_sigabrt_rejects_the_lies :
    check_send_sigabrt (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked = CheckReject
    ∧ check_send_sigabrt (mkEffect 0 [(4096, [0])] []) abort_model_unblocked = CheckReject
    ∧ check_send_sigabrt (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 8)]) abort_model_unblocked
        = CheckReject
    ∧ check_send_sigabrt (mkEffect 1 [] []) abort_model_blocked = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm_altstack_kill

/-- The delivery acceptor does not read the declaration: reached
directly on the undeclared model it answers, where `check_tkill` on the
same model declines — the gate is the callers', not the delivery's.
model: `send_sigabrt` reads `m_sigmask` alone; the declaration is tested by `tkill_self`, `tkill_spec` and `tgkill_spec` before it -/
theorem check_send_sigabrt_does_not_read_the_declaration (eff : SyscallEffect) :
    check_send_sigabrt (mkEffect 0 [] []) abort_model_undeclared
        = CheckOk (with_killed 6 abort_model_undeclared) []
    ∧ check_send_sigabrt (mkEffect 0 [] []) one_sided_model
        = CheckOk (with_sigabrt_pending one_sided_model) []
    ∧ check_tkill 4242 6 eff abort_model_undeclared = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm_altstack_kill

end KillSigabrt

section TheWitnessesContinued

/-! ## The witnesses, continued: which outcome each names

As above: `sigaltstack_witness_ok`, `send_sigabrt_witness_ok`,
`tkill_self_witness_ok`, `tkill_witness_ok` and `tgkill_witness_ok` say
each witness is admitted; the pins below say WHICH outcome each names on
a fixture — the kernel's return on the path the model answers,
`Unmodeled` on the path it declines, the declaration off included. -/

/-- Evaluate a closed witness of the second half: open it, decide every
closed gate, read the fixture memories and models, and finish with the
ground pass if a read is left. -/
macro "witness_norm_altstack_kill" : tactic =>
  `(tactic| (simp +decide only [sigaltstack_witness, send_sigabrt_witness, tkill_self_witness,
              tkill_witness, tgkill_witness, ret_outcome, sys_simp, ↓reduceIte];
             first | done | sys_simp_pass +ground +decide -failIfUnchanged))

/-- sigaltstack: the installed bit on every input and argument pair, then
`uoss`, then the NULL/NULL no-op on every input.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_witness_installed_then_uoss_then_null (i : SyscallInput) (uss uoss : word) :
    sigaltstack_witness uss uoss i installed_model = Unmodeled
    ∧ sigaltstack_witness 0 8192 i sig_model_blocked = Unmodeled
    ∧ sigaltstack_witness 4096 8192 i sig_model_blocked = Unmodeled
    ∧ sigaltstack_witness 0 0 i sig_model_blocked = Ok (mkEffect 0 [] []) sig_model_blocked [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

/-- sigaltstack through the copy: -EFAULT on nothing mapped, -EINVAL on
mode 3, 0 on the disable with the model kept, `Unmodeled` on the shadow,
-ENOMEM on 1 KiB, and 0 with the bit set on 16 KiB.
kernel: kernel/signal.c:sigaltstack,do_sigaltstack@v6.18.46 -/
theorem sigaltstack_witness_paths :
    sigaltstack_witness 4096 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked []
    ∧ sigaltstack_witness 4096 0 (sigaltstack_in mem_ss_mode3 mem_none) sig_model_blocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []
    ∧ sigaltstack_witness 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) sig_model_blocked
        = Ok (mkEffect 0 [] []) sig_model_blocked []
    ∧ sigaltstack_witness 4096 0 (sigaltstack_in mem_ss_zero mem_none) sig_model_blocked
        = Unmodeled
    ∧ sigaltstack_witness 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) sig_model_blocked
        = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []
    ∧ sigaltstack_witness 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        = Ok (mkEffect 0 [] []) (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

/-- The delivery: pending on the blocked model, dead on the unblocked one,
and the one-bit read on the two mixed masks.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem send_sigabrt_witness_paths :
    send_sigabrt_witness abort_model_blocked
        = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) []
    ∧ send_sigabrt_witness abort_model_unblocked
        = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []
    ∧ send_sigabrt_witness abort_model_others_blocked
        = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_others_blocked) []
    ∧ send_sigabrt_witness abort_model_blocked_among_others
        = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked_among_others) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

/-- tkill: `Unmodeled` on every argument pair with the declaration off,
then -EINVAL at pid 0, `Unmodeled` at a foreign pid and at signal 10,
-EINVAL at 65, and the two SIGABRT outcomes.
kernel: kernel/signal.c:tkill,do_send_specific@v6.18.46 -/
theorem tkill_witness_paths (pid sig : word) :
    tkill_witness pid sig abort_model_undeclared = Unmodeled
    ∧ tkill_witness 0 6 abort_model_unblocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []
    ∧ tkill_witness 4243 6 abort_model_unblocked = Unmodeled
    ∧ tkill_witness 4242 10 abort_model_unblocked = Unmodeled
    ∧ tkill_witness 4242 65 abort_model_unblocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []
    ∧ tkill_witness 4242 6 abort_model_unblocked
        = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []
    ∧ tkill_witness 4242 6 abort_model_blocked
        = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

/-- tgkill: `Unmodeled` with the declaration off on every triple, -EINVAL
on a non-positive tgid or pid, -ESRCH on the wrong tgid, `Unmodeled` on a
foreign pid and before the tid is pinned — where the non-positive tgid or
pid is still -EINVAL, the gate preceding the lookup (kernel/signal.c:4179-4180
before :4134, Linux v6.18.46) — and the two SIGABRT outcomes.
kernel: kernel/signal.c:tgkill,do_send_specific@v6.18.46 -/
theorem tgkill_witness_paths (tgid pid sig : word) :
    tgkill_witness tgid pid sig abort_model_undeclared = Unmodeled
    ∧ tgkill_witness 0 4242 6 abort_model_unblocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []
    ∧ tgkill_witness 4242 0 6 abort_model_unblocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []
    ∧ tgkill_witness 7 4242 6 abort_model_unblocked
        = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked []
    ∧ tgkill_witness 4242 4243 6 abort_model_unblocked = Unmodeled
    ∧ tgkill_witness 4242 4242 6 abort_model_unpinned = Unmodeled
    ∧ tgkill_witness 0 4242 6 abort_model_unpinned
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned []
    ∧ tgkill_witness 4242 0 6 abort_model_unpinned
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned []
    ∧ tgkill_witness 4242 4242 6 abort_model_unblocked
        = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []
    ∧ tgkill_witness 4242 4242 6 abort_model_blocked
        = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

/-- The shared tail directly: `Unmodeled` with the declaration off and
before the tid is pinned, then the foreign pid, the bad signal and the
delivery.
kernel: kernel/signal.c:do_send_specific,check_kill_permission@v6.18.46 -/
theorem tkill_self_witness_paths (pid sig : word) :
    tkill_self_witness pid sig abort_model_undeclared = Unmodeled
    ∧ tkill_self_witness pid sig abort_model_unpinned = Unmodeled
    ∧ tkill_self_witness 4243 6 abort_model_unblocked = Unmodeled
    ∧ tkill_self_witness 4242 65 abort_model_unblocked
        = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []
    ∧ tkill_self_witness 4242 0 abort_model_unblocked = Unmodeled
    ∧ tkill_self_witness 4242 6 abort_model_unblocked
        = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm_altstack_kill

end TheWitnessesContinued

-- lean-port sentinel: ticket V-Kernel-Signal-altstack-kill appends below this line

section V_Kernel_Signal_altstack_kill

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Signal-altstack-kill — `sigaltstack`, `tkill` and `tgkill` over the real table

WHAT IS TWINNED HERE.  Rocq states its worked examples for these three
arms through `check_syscall`, in `Checks/Cases/Kernel/Signal.v` (933-1094
and 1151-1321, at a71fd38a).  `Checks/Cases/Kernel/Signal.lean` twins
each over `syscall_spec` under its Rocq name, and the second half's header
above names the checker-level pin each was restated as before the arms
were registered.  Each is restated here once more, over `checked_table` itself, under its
Rocq name with `_over_the_real_table` after it (K6a's convention, from
`Checks/Cases/Checks/Sys/Kernel/Exit.lean`), on Rocq's own input and
model: `mkInput 132 [4096, 0, 0, 0, 0, 0] mem mem_none`,
`mkInput 130 [pid, sig, 0, 0, 0, 0] mem_none mem_none` and
`mkInput 131 [tgid, pid, sig, 0, 0, 0] mem_none mem_none`.  That the
lookups at 130, 131 and 132 find the three arms is pinned by
`lookups_agree_at_arm_tkill` and its two siblings, which
`tools/gen_lean_checked.py` renders for every arm, and not again here.
They sit in the checker's Cases file, and not in the spec's
`Checks/Cases/Kernel/Signal.lean`, for the reason #1234 gave for eventfd2:
that file is the spec's mutation twin, and the checked table entering its
import closure would make a spec mutant that breaks the checker's proofs
read as stillborn rather than as killed by a spec pin.

WHAT A PIN HERE ADDS to its checker-level neighbour is the ARM's claim,
in two halves.  The table answers each call with the arm and not with the
dispatcher's own decline: a table with no row for the number answers
`CheckUnmodeled` to every call, so each `CheckOk` and `CheckReject` below
fails on such a table.  And the arm hands the checker the registers the
kernel reads, narrowed as the kernel narrows them: `SC_RISCV_REGS_TO_ARGS`
passes `a0`, `a1` and `a2` in that order
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
`__SC_CAST` (include/linux/syscalls.h:132, applied at
syscall_wrapper.h:88, Linux v6.18.46) narrows each to the `pid_t` or `int`
the definition declares (kernel/signal.c:4176, 4192 and 4455, Linux
v6.18.46).  The three bridge pins state that reading at every input of
the number and every model; each of the four pins after the Rocq twins
answers differently if the arm reads one register whole where the kernel
narrows it, or swaps two arguments.

EVIDENCE is as in the second half above: a `CheckReject` or
`CheckUnmodeled` pin is POSITIVE to `tools/check_lean_pin_evidence.py`, so
each pin cites the kernel function whose lines make its verdict the
kernel's. -/

/-! ### The arms' register reading -/

/-- 130 is `tkill` with `pid` from `a0` and `sig` from `a1`, each the low
32 bits: `SYSCALL_DEFINE2(tkill, pid_t, pid, int, sig)`
(kernel/signal.c:4192, Linux v6.18.46), at every input numbered 130,
every effect and every model.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_reads_a0_a1_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 130) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  exact ca_check_arm_tkill i eff m

/-- 131 is `tgkill` with `tgid` from `a0`, `pid` from `a1` and `sig` from
`a2`, each the low 32 bits: `SYSCALL_DEFINE3(tgkill, pid_t, tgid, pid_t,
pid, int, sig)` (kernel/signal.c:4176, Linux v6.18.46), at every input
numbered 131, every effect and every model.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem tgkill_reads_a0_a1_a2_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 131) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m
      = check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  exact ca_check_arm_tgkill i eff m

/-- 132 is `sigaltstack` with `uss` from `a0` and `uoss` from `a1`, both
pointers and so read whole: `SYSCALL_DEFINE2(sigaltstack, const stack_t
__user *, uss, stack_t __user *, uoss)` (kernel/signal.c:4455, Linux
v6.18.46), at every input numbered 132, every effect and every model.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_reads_a0_a1_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 132) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  exact ca_check_arm_sigaltstack i eff m

/-! ### `sigaltstack` (132): Rocq's examples over the real table -/

/-- Rocq's `sigaltstack_leaves_the_mask_alone`: the 16 KiB install answers
0 with the record installed and the entry mask kept: the install stores
`t->sas_ss_sp`, `t->sas_ss_size` and `t->sas_ss_flags`
(kernel/signal.c:4445-4449, Linux v6.18.46), and the mask is not among
them.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_leaves_the_mask_alone_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        (mkEffect 0 [] []) sig_model_blocked
      = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ m_sigmask (with_sigaltstack_installed sig_model_blocked) = sig_entry_mask := by
  refine ⟨?_, ?_⟩
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill
  · rfl

/-- Rocq's `sigaltstack_after_an_install_declined`: the same call on the
model the install left declines: after an install, `on_sig_stack(sp)`
(kernel/signal.c:4418-4419, Linux v6.18.46) turns on the user stack
pointer, which no `SyscallInput` carries.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_after_an_install_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        (mkEffect 0 [] []) (with_sigaltstack_installed sig_model_blocked) = CheckUnmodeled := by
  rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `sigaltstack_enomem_keeps_the_record`: the 1 KiB stack is
-ENOMEM with the model unchanged: `ss_size < min_ss_size` sets -ENOMEM
and the three stores are skipped (kernel/signal.c:4440-4449, Linux
v6.18.46).
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_enomem_keeps_the_record_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_small mem_none)
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked [] := by
  rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `sigaltstack_success_admits_no_write`: a store smuggled through
the install is refused.  With `uoss` NULL the call copies nothing out
(kernel/signal.c:4464, Linux v6.18.46), and `do_sigaltstack` writes no
user memory.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_success_admits_no_write_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        (mkEffect 0 [(4096, [0])] []) sig_model_blocked = CheckReject := by
  rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `sigaltstack_disable_leaves_the_record_answerable`: the disable
answers 0 with the model unchanged, the undersized install after it is
still -ENOMEM, and the same undersized install on the installed model
declines.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_disable_leaves_the_record_answerable_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_disable mem_none)
        (mkEffect 0 [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_small mem_none)
        (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked = CheckOk sig_model_blocked []
    ∧ check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_small mem_none)
        (mkEffect (errno_ret ENOMEM) [] []) (with_sigaltstack_installed sig_model_blocked)
        = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill

/-- Rocq's `sigaltstack_install_still_sets_the_bit`: the install answers
with the bit set, and the disable does not.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_install_still_sets_the_bit_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        (mkEffect 0 [] []) sig_model_blocked
      = CheckOk (with_sigaltstack_installed sig_model_blocked) []
    ∧ check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_disable mem_none)
        (mkEffect 0 [] []) sig_model_blocked
      ≠ CheckOk (with_sigaltstack_installed sig_model_blocked) [] := by
  refine ⟨?_, ?_⟩
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_refute_altstack_kill

/-- Rocq's `sigaltstack_after_a_disable_rejects_a_false_success`: the
undersized install offered a 0 is refused, and a store smuggled through
the disable is refused too.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_after_a_disable_rejects_a_false_success_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_small mem_none)
        (mkEffect 0 [] []) sig_model_blocked = CheckReject
    ∧ check_syscall (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_disable mem_none)
        (mkEffect 0 [(4096, [0])] []) sig_model_blocked = CheckReject := by
  refine ⟨?_, ?_⟩
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill
  · rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
    check_norm_altstack_kill

/-! ### `tkill` (130) and `tgkill` (131): Rocq's examples over the real table -/

/-- Rocq's `tkill_sigabrt_unblocked_kills`: SIGABRT to the caller's own
tid, unblocked, answers 0 with the process killed by 6.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem tkill_sigabrt_unblocked_kills_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked
      = CheckOk (with_killed 6 abort_model_unblocked) [] := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_sigabrt_blocked_pends`: blocked, the same send answers 0
with the signal pending.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem tkill_sigabrt_blocked_pends_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_blocked
      = CheckOk (with_sigabrt_pending abort_model_blocked) [] := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tgkill_self_sigabrt_kills`: tgkill with the caller's own tgid
and tid reaches the same kill.
kernel: kernel/signal.c:wants_signal,get_signal@v6.18.46 -/
theorem tgkill_self_sigabrt_kills_over_the_real_table :
    check_syscall (SyscallInput.mkInput 131 [4242, 4242, 6, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked
      = CheckOk (with_killed 6 abort_model_unblocked) [] := by
  rw [tgkill_reads_a0_a1_a2_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_nonpositive_pid_einval`: pid 0 is -EINVAL with the model
untouched (kernel/signal.c:4195-4196, Linux v6.18.46).
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_nonpositive_pid_einval_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [0, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
      = CheckOk abort_model_unblocked [] := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tgkill_wrong_tgid_esrch`: tgid 7 for the caller's own tid is
-ESRCH with the model untouched, `error = -ESRCH` standing when
`task_tgid_vnr(p) == tgid` fails (kernel/signal.c:4131-4135, Linux
v6.18.46).
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_wrong_tgid_esrch_over_the_real_table :
    check_syscall (SyscallInput.mkInput 131 [7, 4242, 6, 0, 0, 0] mem_none mem_none)
        (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
      = CheckOk abort_model_unblocked [] := by
  rw [tgkill_reads_a0_a1_a2_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_off_declined`: with the abort declaration off, the
self-abort declines.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem tkill_off_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_undeclared = CheckUnmodeled := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tgkill_off_declined`: the same under tgkill.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem tgkill_off_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 131 [4242, 4242, 6, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_undeclared = CheckUnmodeled := by
  rw [tgkill_reads_a0_a1_a2_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_other_signal_declined`: SIGUSR1 (10) to the caller
declines.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_other_signal_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 10, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked = CheckUnmodeled := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_other_pid_declined`: SIGABRT to a tid other than the
caller's declines.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_other_pid_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4243, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked = CheckUnmodeled := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_signal_zero_declined`: signal 0 to the caller declines.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_signal_zero_declined_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 0, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked = CheckUnmodeled := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_forged_write_rejected`: a store smuggled through the
send is refused.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_forged_write_rejected_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [(4096, [0])] []) abort_model_unblocked = CheckReject := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_forged_return_rejected`: an LSM's -EPERM is refused
(linux-process-semantics@ff0313ba4f:bugs/tkill-lsm-denial-not-admitted.md).
kernel: kernel/signal.c:do_send_specific,check_kill_permission@v6.18.46 -/
theorem tkill_forged_return_rejected_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked = CheckReject := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- Rocq's `tkill_reads_the_mask_and_writes_none`: both answers keep the
mask they were given, and the two answers differ.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem tkill_reads_the_mask_and_writes_none_over_the_real_table :
    m_sigmask (with_killed 6 abort_model_unblocked) = m_sigmask abort_model_unblocked
    ∧ m_sigmask (with_sigabrt_pending abort_model_blocked) = m_sigmask abort_model_blocked
    ∧ check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked
      ≠ check_syscall (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_blocked := by
  refine ⟨rfl, rfl, ?_⟩
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_refute_altstack_kill

/-! ### Where a misread register answers differently -/

/-- `(1 << 32) | 4242` in `a0` kills as 4242 does: `__SC_CAST` keeps the
low 32 bits.  Read whole, `a0` fails `pid_positive`, the model's
`pid <= 0` test (kernel/signal.c:4195-4196, Linux v6.18.46), so an arm
doing so answers -EINVAL and refuses this 0.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_a0_high_half_dropped_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4294971538, 6, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked
      = CheckOk (with_killed 6 abort_model_unblocked) [] := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- `(1 << 32) | 6` in `a1` is SIGABRT: `__SC_CAST` keeps the low 32
bits.  Read whole, `a1` is above 64, which `valid_signal` refuses
(include/linux/signal.h:272-275, Linux v6.18.46), so an arm doing so
answers -EINVAL and refuses this 0.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_a1_high_half_dropped_over_the_real_table :
    check_syscall (SyscallInput.mkInput 130 [4242, 4294967302, 0, 0, 0, 0] mem_none mem_none)
        (mkEffect 0 [] []) abort_model_unblocked
      = CheckOk (with_killed 6 abort_model_unblocked) [] := by
  rw [tkill_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- `tgkill(4242, 7, 6)` names tid 7 in thread group 4242: `pid` is the
second argument (kernel/signal.c:4176, Linux v6.18.46), so the lookup is
of tid 7, which is not the caller, and the call declines.  An arm swapping
`a0` and `a1` would read `tgkill(7, 4242, 6)`, which
`tgkill_wrong_tgid_esrch_over_the_real_table` answers -ESRCH.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_pid_is_a1_over_the_real_table :
    check_syscall (SyscallInput.mkInput 131 [4242, 7, 6, 0, 0, 0] mem_none mem_none)
        (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked = CheckUnmodeled := by
  rw [tgkill_reads_a0_a1_a2_over_the_real_table _ rfl]
  check_norm_altstack_kill

/-- `sigaltstack(NULL, 4096)` over the 16 KiB record at 4096 installs
nothing: `uss` is `a0` (kernel/signal.c:4455, Linux v6.18.46), NULL here,
and the non-NULL `uoss` declines on a model with no stack installed.  An
arm swapping the two would read the record at 4096 as `uss` and install
it.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_uss_is_a0_over_the_real_table :
    check_syscall (SyscallInput.mkInput 132 [0, 4096, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        (mkEffect 0 [] []) sig_model_blocked = CheckUnmodeled := by
  rw [sigaltstack_reads_a0_a1_over_the_real_table _ rfl]
  check_norm_altstack_kill

end V_Kernel_Signal_altstack_kill

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Signal
