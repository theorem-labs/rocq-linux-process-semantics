import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-cases: a71fd38a08571d519b9cfc5f66308db5c26da570
covers: rt_sigreturn_unmodeled -- sysno_139_is_unmodeled
covers: kill_unmodeled -- sysno_129_is_unmodeled
covers: rt_sigaction_sigsegv_unmodeled -- rt_sigaction_sigsegv_unmodeled
covers: rt_sigaction_sigpipe_unmodeled -- rt_sigaction_sigpipe_unmodeled
covers: rt_sigaction_sigchld_unmodeled -- rt_sigaction_sigchld_unmodeled
covers: rt_sigaction_sigabrt_unmodeled -- rt_sigaction_sigabrt_unmodeled
covers: rt_sigaction_sigint_accepted -- rt_sigaction_sigint_accepted
covers: rt_sigprocmask_block_sigsegv_accepted -- rt_sigprocmask_block_sigsegv_accepted
covers: rt_sigprocmask_kill_stop_stripped_not_refused -- rt_sigprocmask_kill_stop_stripped_not_refused
covers: rt_sigprocmask_block_unions -- rt_sigprocmask_block_unions
covers: rt_sigprocmask_unblock_clears -- rt_sigprocmask_unblock_clears
covers: rt_sigprocmask_unblock_is_not_block -- rt_sigprocmask_unblock_is_not_block
covers: rt_sigprocmask_oldset_unmodeled -- rt_sigprocmask_oldset_unmodeled, rt_sigprocmask_install_unwritable_oset_declines, sysno_135_unwritable_oset_declines
covers: rt_sigprocmask_oldset_reports_entry_mask -- rt_sigprocmask_oldset_reports_entry_mask
covers: rt_sigprocmask_oldset_impossible_mask_rejected -- rt_sigprocmask_oldset_impossible_mask_rejected
covers: rt_sigprocmask_oldset_is_not_the_new_mask -- rt_sigprocmask_oldset_is_not_the_new_mask
covers: rt_sigprocmask_oldset_snapshot_precedes_install -- rt_sigprocmask_oldset_snapshot_precedes_install
covers: rt_sigprocmask_oldset_efault_still_installs -- rt_sigprocmask_oldset_efault_still_installs
covers: rt_sigprocmask_oldset_over_task_size_never_succeeds -- rt_sigprocmask_oldset_over_task_size_never_succeeds
covers: rt_sigprocmask_null_set_ignores_how -- rt_sigprocmask_null_set_ignores_how
covers: rt_sigprocmask_bad_size_beats_unreadable_set -- rt_sigprocmask_bad_size_beats_unreadable_set
covers: rt_sigprocmask_bad_size_beats_oldset_decline -- rt_sigprocmask_bad_size_beats_oldset_decline
covers: rt_sigprocmask_efault_beats_bad_how -- rt_sigprocmask_efault_beats_bad_how
covers: rt_sigprocmask_how_truncates_size_does_not -- sysno_135_size_not_narrowed, sysno_135_how_high_half_dropped, sysno_135_bad_how_high_half
covers: rt_sigprocmask_copyins_separate_the_two_einvals -- rt_sigprocmask_bad_how_is_einval_with_ledger, rt_sigprocmask_sizes_are_einval, rt_sigprocmask_bad_size_ledger_rejected
covers: rt_sigprocmask_efault_records_no_copyin -- rt_sigprocmask_efault_records_no_copyin, rt_sigprocmask_unreadable_set_is_efault
covers: rt_sigprocmask_success_admits_no_write -- rt_sigprocmask_success_admits_no_write
covers: sig_mask_windows_all_declined -- sig_mask_windows_all_declined
covers: rt_sigaction_oact_read_back_declined -- rt_sigaction_oact_declines
unpinned: pselect6_real_mask_declined -- 72's set_user_sigmask decline is Fs/Select's pselect6 spec, not this file's; pinned in Checks/Cases/Fs/Select.lean (the Select port), where the spec it reads lives
unpinned: pselect6_no_mask_is_not_declined -- 72's NULL-mask acceptance is Fs/Select's pselect6 spec; pinned in Checks/Cases/Fs/Select.lean, where the spec it reads lives
unpinned: epoll_pwait_real_mask_declined -- 22 has no Lean arm yet (Checks/Cases/SyscallTable.lean pins lookup_arm spec_table 22 = none), so its set_user_sigmask window is shut by absence from the table; the pin belongs to the Fs/EventPoll port that gives 22 a spec
unpinned: epoll_pwait_no_mask_is_not_declined -- 22 has no Lean arm yet; the acceptance it pins is the Fs/EventPoll port's to state once 22 has a spec
unpinned: ppoll_real_mask_declined -- 73's set_user_sigmask decline is Fs/Select's ppoll spec (its PpSigReal arm answers unmodeled); the real-mask pin is owed in Checks/Cases/Fs/Select.lean by the Select ticket, whose spec it reads
unpinned: ppoll_no_mask_is_not_declined -- 73's NULL-mask acceptance is Fs/Select's ppoll spec; pinned in Checks/Cases/Fs/Select.lean, where the spec it reads lives
covers: sig_mask_windows_not_vacuous -- sig_mask_windows_not_vacuous
covers: sigaltstack_leaves_the_mask_alone -- sigaltstack_leaves_the_mask_alone
covers: sigaltstack_after_an_install_declined -- sigaltstack_after_an_install_declined
covers: sigaltstack_enomem_keeps_the_record -- sigaltstack_enomem_keeps_the_record
covers: sigaltstack_success_admits_no_write -- sigaltstack_success_admits_no_write
covers: sigaltstack_disable_leaves_the_record_answerable -- sigaltstack_disable_leaves_the_record_answerable
covers: sigaltstack_install_still_sets_the_bit -- sigaltstack_install_still_sets_the_bit
covers: sigaltstack_after_a_disable_rejects_a_false_success -- sigaltstack_after_a_disable_rejects_a_false_success
covers: tkill_sigabrt_unblocked_kills -- tkill_sigabrt_unblocked_kills
covers: tkill_sigabrt_blocked_pends -- tkill_sigabrt_blocked_pends
covers: rt_sigprocmask_unblock_pending_sigabrt_kills -- rt_sigprocmask_unblock_pending_sigabrt_kills
covers: rt_sigprocmask_unblock_nothing_pending_lives -- rt_sigprocmask_unblock_nothing_pending_lives
covers: tgkill_self_sigabrt_kills -- tgkill_self_sigabrt_kills
covers: tkill_nonpositive_pid_einval -- tkill_nonpositive_pid_einval
covers: tgkill_wrong_tgid_esrch -- tgkill_wrong_tgid_esrch
covers: tkill_off_declined -- tkill_off_declined
covers: tgkill_off_declined -- tgkill_off_declined
covers: tkill_other_signal_declined -- tkill_other_signal_declined
covers: tkill_other_pid_declined -- tkill_other_pid_declined
covers: tkill_signal_zero_declined -- tkill_signal_zero_declined
covers: tkill_forged_write_rejected -- tkill_forged_write_rejected
covers: tkill_forged_return_rejected -- tkill_forged_return_rejected
covers: tkill_reads_the_mask_and_writes_none -- tkill_reads_the_mask_and_writes_none
covers: one_sided_model_is_declaration_off -- one_sided_model_is_declaration_off
covers: one_sided_unblock_kills -- one_sided_unblock_kills
covers: decl_off_frame_one_sided_refuted -- decl_off_frame_one_sided_refuted
covers: decl_off_frame_hypotheses_inhabited -- decl_off_frame_hypotheses_inhabited_at_a_mask_install -/

/-! # Checks.Cases.Kernel.Signal — what `kernel/signal.c`'s five arms answer, read off against Linux

Worked examples over `Sys.Kernel.Signal.rt_sigaction_spec`,
`Sys.Kernel.Signal.rt_sigprocmask_spec`, `Sys.Kernel.Signal.sigaltstack_spec`,
`Sys.Kernel.Signal.tkill_spec` and `Sys.Kernel.Signal.tgkill_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Signal.v` as it stands at
Rocq commit a71fd38a08571d519b9cfc5f66308db5c26da570 (the squash the spec
twin's `rocq-baseline` names): that file differs from the plan baseline
f44244ad only in how it spells `mkProcInput`, and the fixtures below
follow the spelling at the squash.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  Each decision of a spec gets an `iff` over EVERY
outcome `o` — what is admitted and that nothing else is, in one
statement — and beside it the concrete lie a kernel could report, refuted
on its own.  Both close by the tactics of `Checks/Cases/Tactic.lean`:
`sys_norm` reads the call off its monad primitives and decides the closed
gates, `sys_refute` is `sys_norm` that must close the goal.  A gate that
is decided before the input or the model is looked at is pinned over a
SYMBOLIC input and model; an arm that reads user memory is pinned over a
concrete `SyscallInput` carrying one of the byte maps below, and an arm
that installs a mask over one of the fixtures, because a model rebuilt
from a symbolic `m` is never syntactically `m` (the `Tactic.lean` header
says why).  A symbolic gate is stated as the spec has it — `sys_simp_pass
+decide` leaves it standing, `split` cases on it and the hypothesis closes
the excluded branch — the way `Checks/Cases/Kernel/Exit.lean` reads the
`wait4` children gate.

WHAT THE rt_sigprocmask CASES PIN, AND WHERE THEIR LIMIT IS.  The call
keeps a mask and answers `oset` out of it, so these cases are about a
VALUE and not only a return code: the ORDER the error conditions are
decided in, that a NULL new set makes `how` unreachable, that the
copy-out reports the ENTRY mask after the install, and that an effect
claiming a write the arm did not make is refused.  What no case here can
catch is the mask's MEANING: nothing in the model delivers a signal, so
two programs that block different signals differ only where one of them
reads the mask back.  That is the premise the spec's header states, not a
gap in these examples.

THE ROCQ WORKED CASES NOT TWINNED HERE, and why.  The `rocq-cases:` block
at the top of this file is the register `check_lean_cases_parity.py` reads
and is the claim; what follows is the argument behind its `unpinned:` lines
and the twins whose Lean name differs from the Rocq one:

- `pselect6_real_mask_declined`, `pselect6_no_mask_is_not_declined`,
  `epoll_pwait_real_mask_declined`, `epoll_pwait_no_mask_is_not_declined`,
  `ppoll_real_mask_declined`, `ppoll_no_mask_is_not_declined`: 72 and 73
  have Lean arms whose `set_user_sigmask` window is shut by `Fs/Select`'s
  spec (pselect6's real-mask decline is pinned in
  `Checks/Cases/Fs/Select.lean`; ppoll's is owed there); 22 has no Lean arm
  yet, so its window is shut by absence from the table; the pins belong to
  those ports, whose specs they read.
- `decl_off_frame_hypotheses_inhabited`'s two Bool conjuncts are
  `Checks/Cases/Run.lean`'s theorem of that name (ticket A12); the
  `rt_sigprocmask` conjunct is `decl_off_frame_hypotheses_inhabited_at_a_mask_install`
  below.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding and the unfolding of each builder its post-states are spelled
with, at low priority.  `write_oset`, `set_sigmask_deliver` and
`sigmask_deliver_model` are the builders; `record_copyins` is the
`Sys/Syscall.lean` wrapper this is the first ported spec to use, so its
line sits here until that register's next edit takes it.  The gates
(`sig_valid`, `sig_kernel_only`, `sa_flags_ok`, `sigaction_accepted`,
`how_valid`, `sigabrt_blocked`) are decided, never unfolded; the two
memory readers (`sigaction_flags`, `sigset_at`) and the mask arithmetic
(`sigmask_strip`, `sigmask_apply`) are evaluated closed by the second
pass, and the rewrites below spell out what each fixture reads as.  The
lines live here rather than in `Tactic.lean`'s register on purpose: a
port PR creates its own files and edits no shared one, so that ports
merge in any order (docs/merge-commutativity.md). -/

attribute [sys_simp low] rt_sigaction_spec.eq_1 rt_sigprocmask_spec.eq_1 write_oset.eq_1
  set_sigmask_deliver.eq_1 sigmask_deliver_model.eq_1 record_copyins.eq_1

/-! ## The numbers these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- `EINVAL` is 22.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
example : EINVAL = 22 := by decide
/-- `EFAULT` is 14.
kernel: include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
example : EFAULT = 14 := by decide
/-- `sizeof(sigset_t)` is 8 on riscv64: `_NSIG` 64 over a 64-bit word.
model: the model's own constant at a numeral; the kernel reading of `_NSIG` is on the `Sys/Uapi/Signal.lean` twin and its pins -/
example : NSIG_BYTES = 8 ∧ NSIG_BYTES * 8 = 64 := by decide
/-- `rt_sigprocmask`'s three `how` values, in the order `sigprocmask`'s
`switch` names them.
kernel: include/uapi/asm-generic/signal-defs.h:SIG_BLOCK,SIG_UNBLOCK,SIG_SETMASK@v6.18.46 -/
example : SIG_BLOCK = 0 ∧ SIG_UNBLOCK = 1 ∧ SIG_SETMASK = 2 := by decide
/-- The two bits `rt_sigprocmask` strips: SIGKILL (9) and SIGSTOP (19) as
`1UL << (sig - 1)`, 0x40100.
kernel: include/uapi/asm-generic/signal.h:SIGKILL,SIGSTOP@v6.18.46 -/
example : sig_kernel_only_mask = 262400 ∧ 262400 = ((1 <<< (9 - 1)) ||| (1 <<< (19 - 1)) : Nat) := by
  decide
/-- SIGABRT is 6 and its mask bit is `1 << 5`.
kernel: include/uapi/asm-generic/signal.h:SIGABRT@v6.18.46 -/
example : SIGABRT = 6 ∧ sigabrt_mask = 32 := by decide
/-- The two accepted signals are SIGINT (2) and SIGTERM (15), and the four
fault signals are not.
kernel: include/uapi/asm-generic/signal.h:SIGINT,SIGTERM,SIGILL,SIGTRAP,SIGBUS,SIGSEGV@v6.18.46 -/
example : sigaction_accepted 2 = true ∧ sigaction_accepted 15 = true
    ∧ sigaction_accepted 4 = false ∧ sigaction_accepted 5 = false
    ∧ sigaction_accepted 7 = false ∧ sigaction_accepted 11 = false := by decide
/-- The flags allowlist is the seven delivery-only bits of `UAPI_SA_FLAGS`:
1, 2, 4, 0x800, 0x08000000, 0x40000000 and 0x80000000.
kernel: include/uapi/asm-generic/signal-defs.h:SA_NOCLDSTOP,SA_NOCLDWAIT,SA_SIGINFO,SA_EXPOSE_TAGBITS,SA_ONSTACK,SA_NODEFER,SA_RESETHAND@v6.18.46 -/
example : sa_flags_accepted = 1 + 2 + 4 + 2048 + 134217728 + 1073741824 + 2147483648 := by decide
/-- ...and SA_RESTART, 0x10000000, is the one retained flag left out of it.
kernel: include/uapi/asm-generic/signal-defs.h:SA_RESTART@v6.18.46 -/
example : sa_flags_ok 268435456 = false ∧ sa_flags_accepted ≠ 1 + 2 + 4 + 2048 + 268435456
    + 134217728 + 1073741824 + 2147483648 := by decide
/-- `valid_signal` is inclusive at `_NSIG`: 64 is valid, 65 is not, and so
is 0 through the explicit `sig < 1`.
kernel: include/linux/signal.h:valid_signal@v6.18.46 -/
example : sig_valid 1 = true ∧ sig_valid 64 = true ∧ sig_valid 65 = false ∧ sig_valid 0 = false := by
  decide
/-- `sig_kernel_only` is exactly SIGKILL and SIGSTOP.
kernel: include/linux/signal.h:sig_kernel_only@v6.18.46 -/
example : sig_kernel_only 9 = true ∧ sig_kernel_only 19 = true ∧ sig_kernel_only 2 = false
    ∧ sig_kernel_only 11 = false := by decide
/-- `int sig` is the low 32 bits of the register: `(1 << 32) | 2` is
SIGINT, `(1 << 32) | 0` is signal 0, and -1 sign-extended is 0xffffffff.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
example : bv_unsigned (sig32 4294967298) = 2 ∧ bv_unsigned (sig32 4294967296) = 0
    ∧ bv_unsigned (sig32 (Z_to_bv 64 (-1))) = 4294967295 := by decide
/-- `int how` likewise: `(1 << 32) | 1` is SIG_UNBLOCK and `(1 << 32) | 3`
is the 3 that is -EINVAL.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
example : bv_unsigned (how32 4294967297) = 1 ∧ bv_unsigned (how32 4294967299) = 3 := by decide

/-! ## The fixtures

The byte maps are Rocq's, spelled through `Prelude.bytes_at`: the bytes
laid out from the address and nothing readable on either side, so the
extent of a read is part of what each case pins.  The models are Rocq's
`init_model` fixtures written as the setter they differ from `demo_model`
by; the `rfl` pins below say the two spellings are one record. -/

/-- Nothing readable, nothing writable. -/
def mem_none : word → Option byte := fun _ => none

/-- A syscall input carrying its arm's number and its two byte maps, for a
pin that hands the spec its arguments directly.  Neither spec reads
`in_sysno`; the number is there so the evidence checker matches a pin's
probe to runs that issue rt_sigaction (134). -/
def sigaction_in (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 134 [] mem wmem

/-- The same for rt_sigprocmask (135) and the helpers only it reaches. -/
def sigprocmask_in (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 135 [] mem wmem

attribute [sys_simp low] sigaction_in.eq_1 sigprocmask_in.eq_1

/-- A fully readable 24-byte `struct sigaction` at 4096: handler SIG_DFL,
flags 0, an empty mask. -/
def mem_sigaction_zero : word → Option byte := bytes_at 4096 (List.replicate 24 0)
/-- The same struct with `sa_flags` = SA_RESTART (0x10000000): byte 11 is
0x10. -/
def mem_sigaction_restart : word → Option byte :=
  bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The same struct with `sa_flags` = 0xC8000807, the whole allowlist. -/
def mem_sigaction_allowlist : word → Option byte :=
  bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 7, 8, 0, 200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The same struct with bit 32 of `sa_flags` set: `sa_flags` is an
`unsigned long`, so a 32-bit read would see 0 here. -/
def mem_sigaction_bit32 : word → Option byte :=
  bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Only the first 23 bytes of the struct readable: byte 23, the last of
`sa_mask`, is absent. -/
def mem_sigaction_short : word → Option byte := bytes_at 4096 (List.replicate 23 0)
/-- The SA_RESTART struct with its last byte absent: the flags word is
readable and the copy still fails. -/
def mem_sigaction_restart_short : word → Option byte :=
  bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Eight readable bytes at 4096 holding `sigmask(SIGSEGV)` = 1 << 10,
little-endian: byte 1 is 4. -/
def mem_sigset_sigsegv : word → Option byte := bytes_at 4096 [0, 4, 0, 0, 0, 0, 0, 0]
/-- Eight bytes at 4096 holding `sigmask(SIGABRT)` = 1 << 5 = 32, the set
musl's `raise` unblocks. -/
def mem_sigset_sigabrt : word → Option byte := bytes_at 4096 [32, 0, 0, 0, 0, 0, 0, 0]
/-- Eight bytes at 4096 holding 0x40105: SIGKILL (bit 8) and SIGSTOP (bit
18) with SIGHUP (bit 0) and SIGQUIT (bit 2) riding along, so the strip
leaves 0x5 rather than 0 and the three `how` arithmetics land on three
different numbers. -/
def mem_sigset_kill_stop : word → Option byte := bytes_at 4096 [5, 1, 4, 0, 0, 0, 0, 0]
/-- Seven readable bytes at 4096: one short of a `sigset_t`. -/
def mem_sigset_short : word → Option byte := bytes_at 4096 [0, 4, 0, 0, 0, 0, 0]
/-- A writable eight bytes at 8192 for the `oset` copy-out. -/
def wmem_oldset : word → Option byte := bytes_at 8192 (List.replicate 8 0)

/-- The entry mask of the blocked fixture: 0x10006, SIGINT (2), SIGQUIT (3)
and SIGCHLD (17).  Non-zero so an install is told from no install, and
with a bit above byte 0 so a copy-out of one byte, or a strip applied to
the value going OUT, is told from the right answer. -/
def sig_entry_mask : word := 65542
/-- The copy-from-user ledger every arm PAST the copy must carry: the eight
bytes of `sigset_t` at `nset`. -/
def sig_copyin : List (word × Nat) := [(4096, 8)]

/-- Rocq's `sig_model_blocked`: the demo process launched with
`sig_entry_mask` blocked. -/
def sig_model_blocked : Model := with_sigmask sig_entry_mask demo_model

/-- The tid the abort fixtures pin, so a `tkill` twin has something to
compare against once ported. -/
def abort_tid : word := 4242
/-- Rocq's `abort_model_unblocked`: the abort path declared, nothing
blocked. -/
def abort_model_unblocked : Model := with_tid abort_tid (with_abort_terminal true demo_model)
/-- Rocq's `abort_model_blocked`: the abort path declared and SIGABRT
blocked — the state musl's `__block_app_sigs` leaves, restricted to the
one bit this model reads. -/
def abort_model_blocked : Model :=
  with_tid abort_tid (with_abort_terminal true (with_sigmask 32 demo_model))
/-- Rocq's `abort_model_undeclared`: the same launch with the declaration
off. -/
def abort_model_undeclared : Model := with_tid abort_tid demo_model
/-- Rocq's `one_sided_model`: the declaration OFF and SIGABRT both blocked
and pending — the state the one-sided frame claims cannot be killed. -/
def one_sided_model : Model :=
  with_sigabrt_pending (with_tid abort_tid (with_sigmask 32 demo_model))

/-! ### The fixtures are Rocq's, pinned -/

/-- `sig_model_blocked` is the `init_model` of a launch whose only
difference from `demo_input` is the blocked mask.
model: the fixture equals its Rocq `init_model` spelling -/
theorem sig_model_blocked_is_init_model :
    sig_model_blocked = init_model [] 0 0 demo_sp demo_limit
      (ProcInput.mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
        default_nofile sig_entry_mask demo_hwcap false .Sv48) := rfl
/-- ...and its mask is 0x10006, not 0: the whole reason the fixture exists.
model: the fixture's entry mask, read back -/
theorem sig_model_blocked_mask : m_sigmask sig_model_blocked = 65542 ∧ m_sigmask demo_model = 0 :=
  ⟨rfl, rfl⟩
/-- The three abort fixtures are the `init_model`s of Rocq's `abort_input`
launches, tid pinned.
model: the fixtures equal their Rocq `init_model` spellings -/
theorem abort_models_are_init_models :
    abort_model_unblocked = with_tid abort_tid (init_model [] 0 0 demo_sp demo_limit
      (ProcInput.mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
        default_nofile 0 demo_hwcap true .Sv48))
    ∧ abort_model_blocked = with_tid abort_tid (init_model [] 0 0 demo_sp demo_limit
      (ProcInput.mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
        default_nofile 32 demo_hwcap true .Sv48))
    ∧ abort_model_undeclared = with_tid abort_tid (init_model [] 0 0 demo_sp demo_limit
      (ProcInput.mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
        default_nofile 0 demo_hwcap false .Sv48)) := ⟨rfl, rfl, rfl⟩
/-- `one_sided_model` is Rocq's: the declaration clear, SIGABRT blocked and
pending.
rocq-twin: one_sided_model_is_declaration_off -/
theorem one_sided_model_is_declaration_off :
    m_abort_terminal one_sided_model = false ∧ m_sigabrt_pending one_sided_model = true
    ∧ m_sigmask one_sided_model = 32 := ⟨rfl, rfl, rfl⟩

/-! ### What each fixture reads as

Closed reads of the fixtures, kept as rewrites so the first pass of
`sys_norm` sees the value where the spec reads the map; each is what the
Rocq docstring of the fixture asserts in prose. -/

/-- The zero struct is fully readable and its flags word is 0.
model: a closed `sigaction_flags` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigaction_flags_zero : sigaction_flags mem_sigaction_zero 4096 = some 0 := by decide
/-- The SA_RESTART struct reads as 0x10000000.
model: a closed `sigaction_flags` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigaction_flags_restart : sigaction_flags mem_sigaction_restart 4096 = some 268435456 := by
  decide
/-- The allowlist struct reads as 0xC8000807.
model: a closed `sigaction_flags` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigaction_flags_allowlist :
    sigaction_flags mem_sigaction_allowlist 4096 = some 3355445255 := by decide
/-- The bit-32 struct reads as 0x100000000.
model: a closed `sigaction_flags` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigaction_flags_bit32 : sigaction_flags mem_sigaction_bit32 4096 = some 4294967296 := by
  decide
/-- Twenty-three readable bytes are not a struct: `none`, and so is an
unmapped `act`.
model: a closed `sigaction_flags` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigaction_flags_short :
    sigaction_flags mem_sigaction_short 4096 = none ∧ sigaction_flags mem_none 4096 = none
    ∧ sigaction_flags mem_sigaction_restart_short 4096 = none := by
  decide
/-- The SIGSEGV set reads as 1 << 10.
model: a closed `sigset_at` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigset_at_sigsegv : sigset_at mem_sigset_sigsegv 4096 = some 1024 := by decide
/-- The SIGABRT set reads as 32.
model: a closed `sigset_at` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigset_at_sigabrt : sigset_at mem_sigset_sigabrt 4096 = some 32 := by decide
/-- The kill/stop set reads as 0x40105.
model: a closed `sigset_at` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigset_at_kill_stop : sigset_at mem_sigset_kill_stop 4096 = some 262405 := by decide
/-- Seven bytes are not a set, nor is unmapped memory.
model: a closed `sigset_at` read of the fixture, a rewrite for `sys_norm`. -/
theorem sigset_at_short : sigset_at mem_sigset_short 4096 = none ∧ sigset_at mem_none 4096 = none := by
  decide
/-- The copy-out's destination: eight writable bytes at 8192, none at all
in `mem_none`.
model: a closed `read_bytes_map` walk over the fixture, a rewrite for `sys_norm`. -/
theorem wmem_oldset_walk :
    read_bytes_map wmem_oldset 8192 (Z_to_bv 64 NSIG_BYTES) = some [0, 0, 0, 0, 0, 0, 0, 0]
    ∧ read_bytes_map mem_none 8192 (Z_to_bv 64 NSIG_BYTES) = none := by decide
/-- The blocked fixture's entry mask, 0x10006, as the eight little-endian
bytes `copy_to_user` stores: 6, 0, 1 and five zeros.  A rewrite because the
second pass of `sys_norm` has no `Int.shiftRight` evaluation and would
leave the tail of `Z_to_le_bytes` as stuck shifts.
model: a closed `Z_to_le_bytes` of the fixture's mask, a rewrite for `sys_norm`. -/
theorem le_bytes_of_entry_mask : Z_to_le_bytes 8 65542 = [6, 0, 1, 0, 0, 0, 0, 0] := by decide

attribute [sys_simp]
  sigaction_flags_zero sigaction_flags_restart sigaction_flags_allowlist sigaction_flags_bit32
  sigaction_flags_short sigset_at_sigsegv sigset_at_sigabrt sigset_at_kill_stop sigset_at_short
  wmem_oldset_walk le_bytes_of_entry_mask

/-! ## `SYSCALL_DEFINE4(rt_sigaction)`: `sigsetsize` first

`if (sigsetsize != sizeof(sigset_t)) return -EINVAL;` is the first
statement (kernel/signal.c:4647-4648, Linux v6.18.46), ahead of the `act` copy-in
(:4650-4651) and the `oact` copy-out (:4657-4658) alike, so a bad size
beats a wild `act` pointer and the `oact` decline.  `sigsetsize` is a
`size_t`: compared full-width, so a register whose low half is 8 is the
wrong size. -/

/-- Every size but 8 is -EINVAL, whatever the other three arguments, the
memory or the model: nothing else has been looked at.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem rt_sigaction_bad_size_is_einval (sig act oact ss : word) (h : ss ≠ 8)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec sig act oact ss i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exfalso
    apply h
    have hb : bv_eqb ss (Z_to_bv 64 8) = true := by
      revert hc
      cases bv_eqb ss (Z_to_bv 64 8) <;> decide
    have hss : ss = Z_to_bv 64 8 := by simpa only [bv_eqb, beq_iff_eq] using hb
    rw [hss]
    decide

/-- Size 0.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x2 0x1 0x0 0x0 -22 -/
theorem rt_sigaction_size_0_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- Size 16.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x0 0x10 -22 -/
theorem rt_sigaction_size_16_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 16 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- A `size_t` does not truncate: 0x100000008 is the wrong size although
its low half is 8.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x0 0x100000008 -22 -/
theorem rt_sigaction_size_high_half_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 4294967304 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and is never the accepted 8.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act ok 0x2 0x1 0x0 0x100000008 -22 -/
theorem rt_sigaction_size_high_half_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 4294967304 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- The size test precedes the copy-in: an unreadable `act` with size 0 is
-EINVAL, not -EFAULT — stated over EVERY input, since no memory is read.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- act h0 0x2 0x1 0x0 0x0 -22 -/
theorem rt_sigaction_bad_size_beats_unreadable_act (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 8192 0 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...so -EFAULT is not admissible there.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EFAULT -- act h0 0x2 0x1 0x0 0x0 -22 -/
theorem rt_sigaction_bad_size_efault_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 2 8192 0 0 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  sys_refute
/-- The size test precedes the `oact` decline: nothing about `oact` is
reached, and the answer is -EINVAL, not a decline.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- oact ok ok 0x2 0x0 -22 -/
theorem rt_sigaction_bad_size_beats_oact_decline (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 4096 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and 0 is not admissible there either.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- oact ok ok 0x2 0x0 -22 -/
theorem rt_sigaction_bad_size_oact_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 2 4096 4096 0 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- The size test precedes the SIGSEGV decline too: -EINVAL, not a decline.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- act ok 0xb 0x0 0x0 0x0 -22 -/
theorem rt_sigaction_bad_size_beats_sigsegv_decline (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 11 4096 0 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ## A non-NULL `oact`: the read-back the model cannot answer

`do_sigaction` copies the previous disposition into `old_sa` (`*oact = *k`,
kernel/signal.c:4327-4328, Linux v6.18.46) and the syscall writes it out (:4657-4658).
The model stores no disposition and cannot invent one — `execve`'s
`flush_signal_handlers` (kernel/signal.c, Linux v6.18.46; `begin_new_exec` calls it at
fs/exec.c:1252) preserves an inherited SIG_IGN,
so the initial disposition is the launcher's — and it declines every
non-NULL `oact` outright, whatever `act` or `sig` says.  This is the one
place the spec's order is EARLIER than the kernel's: Linux copies `act` in
first (:4650-4651) and would answer -EFAULT to an unreadable `act` here;
the decline is a decline where the kernel gives an answer, which
fail-closed permits.  These are pinned over EVERY input and model: the
gate is decided before either is looked at. -/

/-- An install with a read-back declines: the one way to read an `sa_mask`
back, and the window the spec twin's header says 134 shuts one level down.
rocq-twin: rt_sigaction_oact_read_back_declined
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact ok ok 0x2 0x8 any -/
theorem rt_sigaction_oact_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- A pure query — `act` NULL, `oact` set — declines too: it is the same
read-back.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact null ok 0x2 0x8 any -/
theorem rt_sigaction_query_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 0 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and a pure query about SIGSEGV, which the NULL-`oact` no-op arm
answers 0 for, declines with a read-back.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact null ok 0xb 0x8 any -/
theorem rt_sigaction_sigsegv_query_declines (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 11 0 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- The decline precedes SIGKILL's -EINVAL...
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact ok ok 0x9 0x8 any -/
theorem rt_sigaction_oact_beats_sigkill_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 9 4096 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- ...signal 65's...
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact ok ok 0x41 0x8 any -/
theorem rt_sigaction_oact_beats_sig65_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigaction_spec 65 4096 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and an unreadable `act`'s -EFAULT, the one answer Linux would give
ahead of it.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact h0 ok 0x2 0x8 any -/
theorem rt_sigaction_oact_beats_efault (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 8192 4096 8 i m o ↔ o = Unmodeled := by
  sys_norm
/-- No errno rescues the decline: -EINVAL is not admitted...
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=-EINVAL -- oact ok ok 0x2 0x8 any -/
theorem rt_sigaction_oact_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 2 4096 4096 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- ...nor a success, nor the -EFAULT of an unmapped `oact`, which Linux
returns with the install already committed.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=0 -- oact ok hole 0x2 0x8 any -/
theorem rt_sigaction_oact_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 2 4096 8192 8 i m (Ok (mkEffect 0 [] []) m [])
    ∧ ¬ rt_sigaction_spec 2 4096 8192 8 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  constructor <;> sys_refute
/-- The anti-vacuity control: the SAME signal and struct with `oact` NULL is
answered 0, so the declines above measure `oact` and not a spec that
declines everything.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_oact_control_is_answered (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model o
      ↔ o = Ok (mkEffect 0 [] []) demo_model [] := by
  sys_norm

/-! ## `act` NULL: a no-op for every valid signal

With nothing to install, `do_sigaction`'s guard (kernel/signal.c:4317-4318, Linux v6.18.46)
has only its `!valid_signal(sig) || sig < 1` half — 1..64 passes — and
the `act && sig_kernel_only(sig)` half is off, so SIGKILL and SIGSTOP are
answered 0 like every other signal, the fault signals included; nothing
in the model changes.  The extremes of the range are pinned on both
sides. -/

/-- Every valid signal is a plain 0 with `act` NULL: over every input and
model, since nothing is read or written.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_null_act_valid_is_zero (sig : word) (h : sig_valid sig = true)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec sig 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exact absurd h hc
/-- ...and every other signal number is -EINVAL.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_null_act_invalid_is_einval (sig : word) (h : sig_valid sig = false)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec sig 0 0 8 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_simp_pass +decide
  split
  · rename_i hc
    exact absurd (h.symm.trans hc) Bool.false_ne_true
  · sys_norm
/-- SIGINT, `act` NULL: 0.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x2 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigint (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- SIGSEGV, `act` NULL: 0, NOT a decline — the fault signal's decline is
on the install, and there is none.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0xb 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigsegv (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 11 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...and its -EINVAL is refused.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act null 0xb 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigsegv_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 11 0 0 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- SIGKILL, `act` NULL: 0 — no `sig_kernel_only` gate without `act`.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x9 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigkill (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 9 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...so SIGKILL's install-time -EINVAL is refused here.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act null 0x9 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigkill_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 9 0 0 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- SIGSTOP and SIGHUP likewise.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x13 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sigstop_sighup (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (rt_sigaction_spec 19 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [])
    ∧ (rt_sigaction_spec 1 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m []) := by
  constructor <;> sys_norm
/-- Signal 64 is the inclusive ceiling: valid.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x40 0x0 0x0 0x8 0 -/
theorem rt_sigaction_null_act_sig64 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 64 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- Signal 0 is below `valid_signal`'s floor: -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x0 0x0 0x0 0x8 -22 -/
theorem rt_sigaction_null_act_sig0 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 0 0 0 8 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and is not a no-op success.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act null 0x0 0x0 0x0 0x8 -22 -/
theorem rt_sigaction_null_act_sig0_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec 0 0 0 8 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- Signal 65, one past the ceiling, and -1 as a 32-bit `int` (0xffffffff):
-EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act null 0x41 0x0 0x0 0x8 -22 -/
theorem rt_sigaction_null_act_sig65_and_minus1 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (rt_sigaction_spec 65 0 0 8 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigaction_spec 4294967295 0 0 8 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  constructor <;> sys_norm
/-- The no-op arm never declines: a decline here would be a spec that
declined everything, which the SIGSEGV query above already refuses.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_null_act_never_unmodeled (sig : word) (i : SyscallInput) (m : Model) :
    ¬ rt_sigaction_spec sig 0 0 8 i m Unmodeled := by
  intro h
  sys_simp_pass +decide at h
  split at h <;> sys_refute at h

/-! ## `copy_from_user(&new_sa.sa, act, sizeof(new_sa.sa))`: 24 bytes, all or nothing

The copy (kernel/signal.c:4650-4651, Linux v6.18.46) precedes `do_sigaction` (:4653), so
-EFAULT beats every -EINVAL of the guard and every decline of the model;
the struct is 24 bytes on riscv64 (`struct sigaction`,
include/linux/signal_types.h:37-49, Linux v6.18.46, no `sa_restorer`), so 23 readable
bytes are a fault and 24 are enough. -/

/-- A wholly unmapped `act` is -EFAULT.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h0 0x2 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_unreadable_act_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...never a success, never -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act h0 0x2 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_unreadable_act_lies_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_none mem_none) m (Ok (mkEffect 0 [] []) m [])
    ∧ ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_none mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  constructor <;> sys_refute
/-- `act = 8`: non-NULL and unmapped, so -EFAULT and not the no-op 0 —
NULL-ness is `act == 0`, not "unreadable".
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act low 0x2 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_low_act_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 8 0 8 (sigaction_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- Twenty-three readable bytes: byte 23 absent, so -EFAULT.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h23 0x2 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_23_bytes_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_short mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...and a partial copy is never a success.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act h23 0x2 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_23_bytes_success_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_short mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- Twenty-four readable bytes with nothing beyond them are enough: a spec
reading musl's 32-byte struct would answer -EFAULT here.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h24 0x2 0x1 0x0 0x8 0 -/
theorem rt_sigaction_24_bytes_are_enough (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...so a 32-byte read's -EFAULT is not admissible.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EFAULT -- act h24 0x2 0x1 0x0 0x8 0 -/
theorem rt_sigaction_24_bytes_efault_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  sys_refute
/-- -EFAULT precedes `sig_kernel_only`: an unreadable `act` with SIGKILL is
-EFAULT, not -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h0 0x9 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_efault_beats_sigkill_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 9 4096 0 8 (sigaction_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...so the honest -EINVAL is refused there.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act h0 0x9 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_efault_beats_sigkill_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 9 4096 0 8 (sigaction_in mem_none mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- -EFAULT precedes the invalid-signal -EINVAL: signal 65, unreadable.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h0 0x41 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_efault_beats_sig65_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 65 4096 0 8 (sigaction_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- -EFAULT precedes the SIGSEGV decline: an unreadable `act` for SIGSEGV
is ANSWERED -EFAULT, not declined.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act h0 0xb 0x1 0x0 0x8 -14 -/
theorem rt_sigaction_efault_beats_sigsegv_decline (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 11 4096 0 8 (sigaction_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- -EFAULT precedes the SA_RESTART decline as well.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:mem-hide:a1:1,ret=-EFAULT -- act ok 0x2 0x1 0x10000000 0x8 0 -/
theorem rt_sigaction_efault_beats_restart_decline (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_restart_short mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-! ## `do_sigaction`'s guard with `act`: the range, then `sig_kernel_only`

`if (!valid_signal(sig) || sig < 1 || (act && sig_kernel_only(sig)))
return -EINVAL;` (kernel/signal.c:4317-4318, Linux v6.18.46): one -EINVAL for three
conditions, so no ordering among them is observable; what IS observable
is that all three come after the copy-in and before the flags are
consulted. -/

/-- SIGKILL with something to install: -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x9 0x1 0x0 0x8 -22 -/
theorem rt_sigaction_sigkill_install_is_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 9 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and never a success.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act ok 0x9 0x1 0x0 0x8 -22 -/
theorem rt_sigaction_sigkill_install_success_rejected (m : Model) :
    ¬ rt_sigaction_spec 9 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- SIGSTOP likewise.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x13 0x1 0x0 0x8 -22 -/
theorem rt_sigaction_sigstop_install_is_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 19 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- The guard precedes the flags: SIGKILL with SA_RESTART is -EINVAL, not
the SA_RESTART decline...
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x9 0x1 0x10000000 0x8 -22 -/
theorem rt_sigaction_sigkill_restart_is_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 9 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and so is signal 65 with SA_RESTART.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x41 0x1 0x10000000 0x8 -22 -/
theorem rt_sigaction_sig65_restart_is_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 65 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- Signal 0, 65, -1 and INT_MIN (0x80000000: negative as an `int`, huge as
`valid_signal`'s `unsigned long`) with an install: -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x80000000 0x1 0x0 0x8 -22 -/
theorem rt_sigaction_out_of_range_install_is_einval (m : Model) (o : outcome SyscallEffect) :
    (rt_sigaction_spec 0 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigaction_spec 65 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigaction_spec 4294967295 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigaction_spec 2147483648 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm
/-- ...none of them a success.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=0 -- act ok 0x80000000 0x1 0x0 0x8 -22 -/
theorem rt_sigaction_out_of_range_install_success_rejected (m : Model) :
    ¬ rt_sigaction_spec 0 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m (Ok (mkEffect 0 [] []) m [])
    ∧ ¬ rt_sigaction_spec 65 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m (Ok (mkEffect 0 [] []) m [])
    ∧ ¬ rt_sigaction_spec 2147483648 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

/-! ## The flags: SA_RESTART and anything outside the allowlist decline

`do_sigaction` masks the flags with `UAPI_SA_FLAGS`
(kernel/signal.c:4341-4342, Linux v6.18.46) and installs (:4353); the model declines
SA_RESTART because it is the one flag that changes a syscall's return
value, and every bit outside `UAPI_SA_FLAGS` because nothing needs the
shape.  Both are declines where Linux answers 0, and the spec twin's
`sa_flags_accepted` docstring carries the argument. -/

/-- SA_RESTART alone declines.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x2 0x1 0x10000000 0x8 0 -/
theorem rt_sigaction_restart_declines (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and no errno rescues it.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x10000000 0x8 0 -/
theorem rt_sigaction_restart_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_restart mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  constructor <;> sys_refute
/-- The whole allowlist at once is accepted: 0 for SIGINT.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x2 0x1 0xc8000807 0x8 0 -/
theorem rt_sigaction_allowlist_is_zero (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_allowlist mem_none) m o
      ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...and is not -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0xc8000807 0x8 0 -/
theorem rt_sigaction_allowlist_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_allowlist mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- Bit 32 of `sa_flags`: `unsigned long`, not `u32`, so a bit a 32-bit
read would lose declines.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x2 0x1 0x100000000 0x8 0 -/
theorem rt_sigaction_bit32_declines (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_bit32 mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and no errno rescues it.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x100000000 0x8 0 -/
theorem rt_sigaction_bit32_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_bit32 mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute

/-! ## `sigaction_accepted`: the case the whole spec exists for

The same call, at the same fully readable 24-byte struct, differing only
in the signal number: SIGINT and SIGTERM are accepted and answer 0
recording nothing; SIGSEGV, SIGILL, SIGBUS and SIGTRAP fail closed because
every `MachineFault` site raises them; SIGPIPE and SIGXFSZ because a
modeled `write` can cause a real kernel to raise them; SIGCHLD because it
left the set ahead of the model acquiring a child; SIGABRT because the
abort arm delivers it with the default disposition and never asks
whether a handler is installed; and every other signal because nothing
argues for it.  Linux answers 0 to all of them (`do_sigaction`,
kernel/signal.c:4348-4377, Linux v6.18.46), so each decline is a decline where the
kernel gives an answer. -/

/-- SIGINT is accepted: 0, nothing recorded, the model untouched.
rocq-twin: rt_sigaction_sigint_accepted
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x2 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigint_accepted (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...and neither -EINVAL nor -EFAULT is admitted for it.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigint_lies_rejected (m : Model) :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  constructor <;> sys_refute
/-- SIGTERM is accepted.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0xf 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigterm_accepted (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 15 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...and is not -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#reject --mutate 134:ret=-EINVAL -- act ok 0xf 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigterm_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 15 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- An accepted install records NOTHING: a success that changed the mask,
or claimed a write, is refused — on the model and on the effect.
kernel: kernel/signal.c:rt_sigaction,do_sigaction@v6.18.46 -/
theorem rt_sigaction_sigint_records_nothing :
    ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        (Ok (mkEffect 0 [] []) (with_sigmask 1024 demo_model) [])
    ∧ ¬ rt_sigaction_spec 2 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) demo_model
        (Ok (mkEffect 0 [(4096, [0])] []) demo_model []) := by
  constructor <;> sys_refute
/-- SIGSEGV declines.
rocq-twin: rt_sigaction_sigsegv_unmodeled
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0xb 0x0 0x0 0x8 0 -/
theorem rt_sigaction_sigsegv_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 11 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and neither -EINVAL nor -EFAULT rescues it.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=-EINVAL -- act ok 0xb 0x0 0x0 0x8 0 -/
theorem rt_sigaction_sigsegv_errnos_rejected (m : Model) :
    ¬ rt_sigaction_spec 11 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ ¬ rt_sigaction_spec 11 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m [])
    ∧ ¬ rt_sigaction_spec 11 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- SIGILL, SIGTRAP and SIGBUS, the other three fault signals.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x4 0x0 0x0 0x8 0 -/
theorem rt_sigaction_fault_signals_unmodeled (m : Model) (o : outcome SyscallEffect) :
    (rt_sigaction_spec 4 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled)
    ∧ (rt_sigaction_spec 5 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled)
    ∧ (rt_sigaction_spec 7 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- SIGPIPE: a modeled `write` on a channel whose reader has gone raises it
on a real kernel.
rocq-twin: rt_sigaction_sigpipe_unmodeled
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0xd 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigpipe_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 13 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- SIGXFSZ: neither the modeled `write` nor the modeled `ftruncate`
consults RLIMIT_FSIZE.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x19 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigxfsz_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 25 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- SIGCHLD left the accepted set ahead of the model acquiring a child, so
that neither landing order could open a window; nothing else in the tree
fails if it comes back.
rocq-twin: rt_sigaction_sigchld_unmodeled
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x11 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sigchld_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 17 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- ...including the dropbear word, SIGCHLD with SA_NOCLDSTOP: the flag is
inside the allowlist, so the SIGNAL is what refuses.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x11 0x1 0x1 0x8 0 -/
theorem rt_sigaction_sigchld_nocldstop_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 17 4096 0 8
        (sigaction_in (bytes_at 4096 [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
          mem_none) m o
      ↔ o = Unmodeled := by
  sys_norm
/-- SIGABRT, LOAD-BEARING FOR THE ABORT ARM: `tkill_self` delivers SIGABRT
with the default disposition and never asks whether a handler is
installed, and this decline is what makes that sound — no run the model
covers reaches the abort path with a handler in place.  Same struct and
shape as the SIGINT acceptance above, differing in the signal alone.
rocq-twin: rt_sigaction_sigabrt_unmodeled
probe: testing/syscall-check/tests/musl_abort.c#fail-closed --expect-unmodeled rt_sigaction --abort-terminal --guest-signal 6 -- handler -/
theorem rt_sigaction_sigabrt_unmodeled (m : Model) (o : outcome SyscallEffect) :
    rt_sigaction_spec 6 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- SIGHUP, SIGWINCH, 32 and 64: declined for want of a motivating program,
the ceiling included.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x40 0x1 0x0 0x8 0 -/
theorem rt_sigaction_other_signals_unmodeled (m : Model) (o : outcome SyscallEffect) :
    (rt_sigaction_spec 1 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled)
    ∧ (rt_sigaction_spec 28 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled)
    ∧ (rt_sigaction_spec 32 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled)
    ∧ (rt_sigaction_spec 64 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm
/-- ...and signal 64's -EINVAL is not given: 64 is valid, and the decline
is on the acceptance, not the range.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=-EINVAL -- act ok 0x40 0x1 0x0 0x8 0 -/
theorem rt_sigaction_sig64_einval_rejected (m : Model) :
    ¬ rt_sigaction_spec 64 4096 0 8 (sigaction_in mem_sigaction_zero mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute

/-! ## `SYSCALL_DEFINE4(rt_sigprocmask)`: `sigsetsize` first

`if (sigsetsize != sizeof(sigset_t)) return -EINVAL;` (kernel/signal.c:3334-3335, Linux v6.18.46)
is the first statement, before the `old_set` snapshot (:3337) and the
`if (nset)` (:3339) that holds the only `copy_from_user`.  A `size_t`,
compared full-width.  Pinned over EVERY input and model: nothing has been
read. -/

/-- Every size but 8 is -EINVAL, whatever `how`, `nset`, `oset`, the memory
or the model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_bad_size_is_einval (how nset oset ss : word) (h : ss ≠ 8)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec how nset oset ss i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exfalso
    apply h
    have hb : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) = true := by
      revert hc
      cases bv_eqb ss (Z_to_bv 64 NSIG_BYTES) <;> decide
    have hss : ss = Z_to_bv 64 NSIG_BYTES := by simpa only [bv_eqb, beq_iff_eq] using hb
    rw [hss]
    decide
/-- Size 0, 7, 9 and 128 — musl's userspace `sigset_t` — are -EINVAL.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x1 0x0 0x80 -22 -/
theorem rt_sigprocmask_sizes_are_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (rt_sigprocmask_spec 1 4096 0 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigprocmask_spec 1 4096 0 7 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigprocmask_spec 1 4096 0 9 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (rt_sigprocmask_spec 1 4096 0 128 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm
/-- ...and 128 is never the accepted size.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- set ok 0x1 0x0 0x80 -22 -/
theorem rt_sigprocmask_size_128_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 1 4096 0 128 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- `size_t` does not truncate: 0x100000008 is the wrong size.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x1 0x0 0x100000008 -22 -/
theorem rt_sigprocmask_size_high_half_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 0 4294967304 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and is not the accepted 8.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- set ok 0x1 0x0 0x100000008 -22 -/
theorem rt_sigprocmask_size_high_half_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 1 4096 0 4294967304 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- A wrong size beats a wild `nset`: -EINVAL, NOT -EFAULT, over every
input.
rocq-twin: rt_sigprocmask_bad_size_beats_unreadable_set
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform --mutate 135:ret=-EINVAL -- set h0 0x1 0x0 0x0 -22 -/
theorem rt_sigprocmask_bad_size_beats_unreadable_set (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 8192 0 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...so -EFAULT is not admissible there.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=-EFAULT -- set h0 0x1 0x0 0x0 -22 -/
theorem rt_sigprocmask_bad_size_efault_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 1 8192 0 0 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  sys_refute
/-- A wrong size beats the `oset` decline too — the one pair where the model
is narrower than Linux in the other direction, and the size is answered
before `oset` is reached.
rocq-twin: rt_sigprocmask_bad_size_beats_oldset_decline
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform --mutate 135:ret=-EINVAL -- old ok ok 0x1 0x0 -22 -/
theorem rt_sigprocmask_bad_size_beats_oldset_decline (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 0 8192 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- ...and 0 is not admissible there either.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- old ok ok 0x1 0x0 -22 -/
theorem rt_sigprocmask_bad_size_oldset_success_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 1 0 8192 0 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- The arm-1 -EINVAL read NO user memory: a ledger on it is refused.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_bad_size_ledger_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 0 4096 0 0 i m
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m []) := by
  sys_refute

/-! ## `if (nset)`: with a NULL set, `how` is never looked at

`sigprocmask`, and with it the `switch (how)` and its -EINVAL, is reached
only from inside `if (nset)` (kernel/signal.c:3339-3346, Linux v6.18.46), so a NULL `nset`
with an out-of-range `how` is 0, not -EINVAL.  The call is not a no-op even
so: the `oset` copy-out (:3349-3351) still runs, so a query WRITES. -/

/-- Any `how` at all with a NULL set and a NULL `oset`: 0, the model
untouched — over every `how`, input and model.
rocq-twin: rt_sigprocmask_null_set_ignores_how
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set null 0x3 0x0 0x8 0 -/
theorem rt_sigprocmask_null_set_ignores_how (how : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    rt_sigprocmask_spec how 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- `how` = 999, -1 as a 32-bit `int`, and a wild 64-bit `how`: 0.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set null 0x7fffffffffffffff 0x0 0x8 0 -/
theorem rt_sigprocmask_null_set_wild_how (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (rt_sigprocmask_spec 999 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [])
    ∧ (rt_sigprocmask_spec 4294967295 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m [])
    ∧ (rt_sigprocmask_spec 9223372036854775807 0 0 8 i m o ↔ o = Ok (mkEffect 0 [] []) m []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- ...and -EINVAL is not admissible on any of them.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=-EINVAL -- set null 0x3 0x0 0x8 0 -/
theorem rt_sigprocmask_null_set_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ rt_sigprocmask_spec 3 0 0 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ ¬ rt_sigprocmask_spec 4294967295 0 0 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  constructor <;> sys_refute
/-- A NULL set installs nothing: a 0 that changed the mask is refused, on
the model.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_null_set_installs_nothing (i : SyscallInput) :
    ¬ rt_sigprocmask_spec 0 0 0 8 i sig_model_blocked (Ok (mkEffect 0 [] []) (with_sigmask 0 sig_model_blocked) []) := by
  sys_refute

/-! ## The pure query: `oset` reports the ENTRY mask

`old_set = current->blocked` is taken at kernel/signal.c:3337 (Linux v6.18.46) and copied out
at :3349-3351.  A query — NULL `nset`, non-NULL `oset` — hands the mask the
process is holding back as eight little-endian bytes and installs nothing.
Not reachable by a probe: the value asserted is the launch's
`in_sigmask`, which a probe cannot choose, so it is pinned here against
the two fixtures. -/

/-- The entry mask goes out for EVERY model and every `how`: eight bytes of
`Z_to_le_bytes`, the model untouched.
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_query_reports_entry_mask (how : word) (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec how 0 8192 8 (sigprocmask_in mem_none wmem_oldset) m o
      ↔ o = Ok (mkEffect 0 [(8192, Z_to_le_bytes 8 (bv_unsigned (m_sigmask m)))] []) m [] := by
  sys_norm
/-- Over the blocked fixture the eight bytes are 6, 0, 1, 0, 0, 0, 0, 0 —
0x10006 little-endian — so a spec that wrote one byte, or stripped the
value going OUT, is told apart.
rocq-twin: rt_sigprocmask_oldset_reports_entry_mask
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_reports_entry_mask (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 0 0 8192 8 (sigprocmask_in mem_none wmem_oldset) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []) sig_model_blocked [] := by
  sys_norm
/-- A mask the process could not have had — {SIGKILL, SIGSTOP}, 0x40100 —
is refused: not by an invariant about possible masks, which the spec holds
none of, but by the byte-for-byte equality against the mask the model
carries.
rocq-twin: rt_sigprocmask_oldset_impossible_mask_rejected
kernel: kernel/signal.c:rt_sigprocmask,set_current_blocked@v6.18.46 -/
theorem rt_sigprocmask_oldset_impossible_mask_rejected :
    ¬ rt_sigprocmask_spec 0 0 8192 8 (sigprocmask_in mem_none wmem_oldset) sig_model_blocked
        (Ok (mkEffect 0 [(8192, [0, 1, 4, 0, 0, 0, 0, 0])] []) sig_model_blocked []) := by
  sys_refute
/-- A query owes its eight bytes: a 0 that wrote nothing is refused...
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:drop-writes -- old null ok 0x1 0x8 0 -/
theorem rt_sigprocmask_query_drop_writes_rejected :
    ¬ rt_sigprocmask_spec 1 0 8192 8 (sigprocmask_in mem_none wmem_oldset) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- ...and so is -EINVAL on a valid size with a NULL set.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=-EINVAL -- old null ok 0x1 0x8 0 -/
theorem rt_sigprocmask_query_einval_rejected :
    ¬ rt_sigprocmask_spec 1 0 8192 8 (sigprocmask_in mem_none wmem_oldset) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute
/-- A query whose destination is not wholly writable — nothing writable at
8192 — DECLINES rather than answering -EFAULT: riscv's forward-copying
`raw_copy_to_user` may have stored the leading bytes before faulting, a
partial store this model does not represent.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#fail-closed --expect-unmodeled rt_sigprocmask -- old null far 0x1 0x8 -14 -/
theorem rt_sigprocmask_query_unwritable_oset_declines (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 0 8192 8 (sigprocmask_in mem_none mem_none) m o ↔ o = Unmodeled := by
  sys_norm
/-- ...and its -EFAULT is not admitted: a decline answers nothing.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#fail-closed --expect-unmodeled rt_sigprocmask -- decline far-pure -/
theorem rt_sigprocmask_query_unwritable_efault_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 1 0 8192 8 (sigprocmask_in mem_none mem_none) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  sys_refute
/-- A query whose eight bytes run past `TASK_SIZE` — `oset` = 2^64 - 8 — is
-EFAULT outright: `access_ok` refuses the range before any byte is looked
at, for every model and whatever the writable map says.
kernel: kernel/signal.c:rt_sigprocmask; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem rt_sigprocmask_query_over_task_size_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 0 (Z_to_bv 64 (2 ^ 64 - 8)) 8 (sigprocmask_in mem_none wmem_oldset) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-! ## `copy_from_user(&new_set, nset, sizeof(sigset_t))`: eight bytes, all or nothing

Inside `if (nset)`, the copy (kernel/signal.c:3340-3341, Linux v6.18.46) runs two statements
before `sigprocmask` (:3344), so an unreadable set is -EFAULT ahead of a
bad `how`'s -EINVAL, and a failed copy records nothing. -/

/-- An unreadable set is -EFAULT, for every model.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set h0 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_unreadable_set_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 8192 0 8 (sigprocmask_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...never a success, never -EINVAL.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- set h0 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_unreadable_set_lies_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 1 8192 0 8 (sigprocmask_in mem_none mem_none) m (Ok (mkEffect 0 [] []) m [])
    ∧ ¬ rt_sigprocmask_spec 1 8192 0 8 (sigprocmask_in mem_none mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  constructor <;> sys_refute
/-- Seven readable bytes are one short: -EFAULT.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set h7 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_7_bytes_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_short mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...and a partial copy is never a success.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- set h7 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_7_bytes_success_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_short mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- `nset = 8`: non-NULL and unmapped, so -EFAULT and not the no-op 0.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set low 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_low_set_is_efault (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 8 0 8 (sigprocmask_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- An unreadable set beats a bad `how`: -EFAULT.
rocq-twin: rt_sigprocmask_efault_beats_bad_how
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set h0 0x3 0x0 0x8 -14 -/
theorem rt_sigprocmask_efault_beats_bad_how (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 3 8192 0 8 (sigprocmask_in mem_none mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm
/-- ...so the honest -EINVAL is refused there.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=-EINVAL -- set h0 0x3 0x0 0x8 -14 -/
theorem rt_sigprocmask_efault_beats_bad_how_einval_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 3 8192 0 8 (sigprocmask_in mem_none mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute
/-- A failed copy has no range to record: a ledger on the -EFAULT is
refused.
rocq-twin: rt_sigprocmask_efault_records_no_copyin
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:smuggle-copyin:a1:8 -- set h0 0x1 0x0 0x8 -14 -/
theorem rt_sigprocmask_efault_records_no_copyin (m : Model) :
    ¬ rt_sigprocmask_spec 1 8192 0 8 (sigprocmask_in mem_none mem_none) m
        (Ok (with_copyins [(8192, 8)] (mkEffect (errno_ret EFAULT) [] [])) m []) := by
  sys_refute
/-- An unreadable set with a writable `oset` is still -EFAULT with no write:
the copy-out is never reached.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform --mutate 135:mem-none,ret=-EFAULT,drop-writes -- old ok ok 0x1 0x8 0 -/
theorem rt_sigprocmask_unreadable_set_writes_nothing (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 8192 8 (sigprocmask_in mem_none wmem_oldset) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-! ## `sigprocmask`'s `switch (how)`: -EINVAL after the copy, with the ledger

`default: return -EINVAL` (kernel/signal.c:3263-3264, Linux v6.18.46) is reached after
the eight bytes were copied, so this -EINVAL carries the copy-in ledger
that the `sigsetsize` -EINVAL does not — the one thing that tells the two
apart, and the pair the ledger exists for. -/

/-- `how` = 3 with a readable set: -EINVAL with the eight bytes recorded,
for every model.
rocq-twin: rt_sigprocmask_copyins_separate_the_two_einvals
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x3 0x0 0x8 -22 -/
theorem rt_sigprocmask_bad_how_is_einval_with_ledger (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 3 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm
/-- ...and neither a success nor an EMPTY ledger is admissible for it.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:drop-copyins -- set ok 0x3 0x0 0x8 -22 -/
theorem rt_sigprocmask_bad_how_lies_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 3 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ ¬ rt_sigprocmask_spec 3 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) m []) := by
  constructor <;> sys_refute
/-- `how` = -1 as an `int` (0xffffffff), INT_MAX and INT_MIN: -EINVAL.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0xffffffff 0x0 0x8 -22 -/
theorem rt_sigprocmask_wild_how_is_einval (m : Model) (o : outcome SyscallEffect) :
    (rt_sigprocmask_spec 4294967295 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [])
    ∧ (rt_sigprocmask_spec 2147483647 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [])
    ∧ (rt_sigprocmask_spec 2147483648 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- ...never a success.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=0 -- set ok 0xffffffff 0x0 0x8 -22 -/
theorem rt_sigprocmask_wild_how_success_rejected (m : Model) :
    ¬ rt_sigprocmask_spec 4294967295 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) m
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) m []) := by
  sys_refute
/-- A bad `how` returns before the copy-out: with a writable `oset` the answer
is still -EINVAL with the ledger and no write, for every model.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#conform -- noop badhow -/
theorem rt_sigprocmask_bad_how_with_oset_is_einval (m : Model) (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 3 4096 8192 8 (sigprocmask_in mem_sigset_sigsegv wmem_oldset) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm
/-- ...so a write to that `oset` is refused.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:smuggle-write:a2:8 -- noop badhow -/
theorem rt_sigprocmask_bad_how_writes_nothing (m : Model) :
    ¬ rt_sigprocmask_spec 3 4096 8192 8 (sigprocmask_in mem_sigset_sigsegv wmem_oldset) m
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL)
              [(8192, Z_to_le_bytes 8 (bv_unsigned (m_sigmask m)))] [])) m []) := by
  sys_refute

/-! ## The install: strip, then one of three arithmetics

`sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))`
(kernel/signal.c:3342, Linux v6.18.46) says nothing and the call SUCCEEDS; then
`sigorsets` (:3255), `sigandnsets` (:3258) or assignment (:3261) over the
entry mask, installed by `__set_task_blocked` (:3203).  Every case is
stated over a fixture, and the three arithmetics over the BLOCKED one,
because over an entry mask of 0 an install of 0 and no install at all are
the same record. -/

/-- BLOCKING SIGSEGV IS ACCEPTED, and installs: `force_sig_info_to_task`
resets the disposition and clears the bit before sending
(kernel/signal.c:1305-1311, Linux v6.18.46), so a blocked fault signal still kills and
there is no accepted-signal list here.
rocq-twin: rt_sigprocmask_block_sigsegv_accepted
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x0 0x400 0x8 0 -/
theorem rt_sigprocmask_block_sigsegv_accepted (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 1024 demo_model) [] := by
  sys_norm
/-- ...and blocking a fault signal is not -EINVAL.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:ret=-EINVAL -- set ok 0x0 0x400 0x8 0 -/
theorem rt_sigprocmask_block_sigsegv_einval_rejected :
    ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  sys_refute
/-- A success that did NOT install is refused, on the model.
kernel: kernel/signal.c:rt_sigprocmask,__set_task_blocked@v6.18.46 -/
theorem rt_sigprocmask_block_sigsegv_no_install_rejected :
    ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) demo_model []) := by
  sys_refute
/-- WRITING NOTHING IS AN OBLIGATION: an install that claims a store — one
byte at the new set's own address — is refused, so a target cannot smuggle
a write through a call whose only visible answer is 0.
rocq-twin: rt_sigprocmask_success_admits_no_write
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_success_admits_no_write :
    ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (with_copyins sig_copyin (mkEffect 0 [(4096, [0])] [])) (with_sigmask 1024 demo_model) []) := by
  sys_refute
/-- An install owes its ledger: a success that claims it read nothing, or
nine bytes, or the right eight at the wrong address, is refused.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#reject --mutate 135:drop-copyins -- set ok 0x1 0x0 0x8 0 -/
theorem rt_sigprocmask_install_ledger_lies_rejected :
    ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (mkEffect 0 [] []) (with_sigmask 1024 demo_model) [])
    ∧ ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (with_copyins [(4096, 9)] (mkEffect 0 [] [])) (with_sigmask 1024 demo_model) [])
    ∧ ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model
        (Ok (with_copyins [(4097, 8)] (mkEffect 0 [] [])) (with_sigmask 1024 demo_model) []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- SIGKILL and SIGSTOP are STRIPPED, not refused: SIG_SETMASK of 0x40105
over the blocked fixture installs 0x5 — not 0x40105 (no strip), not 0 (a
strip that took the survivors too), not 0x10006 (no install).
rocq-twin: rt_sigprocmask_kill_stop_stripped_not_refused
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_kill_stop_stripped_not_refused (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 5 sig_model_blocked) [] := by
  sys_norm
/-- ...and blocking SIGKILL is not the -EINVAL an `rt_sigaction` install
would give.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:ret=-EINVAL -- strip -/
theorem rt_sigprocmask_kill_stop_einval_rejected :
    ¬ rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model_blocked []) := by
  sys_refute
/-- The unstripped install and the no-install are refused, on the model.
kernel: kernel/signal.c:rt_sigprocmask,sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_kill_stop_wrong_installs_rejected :
    ¬ rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 262405 sig_model_blocked) [])
    ∧ ¬ rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked [])
    ∧ ¬ rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 sig_model_blocked) []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- SIG_BLOCK is `sigorsets`: 0x10006 | 0x5 = 0x10007.
rocq-twin: rt_sigprocmask_block_unions
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#conform -- arith block -/
theorem rt_sigprocmask_block_unions (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 65543 sig_model_blocked) [] := by
  sys_norm
/-- SIG_UNBLOCK is `sigandnsets`: 0x10006 & ~0x5 = 0x10002.
rocq-twin: rt_sigprocmask_unblock_clears
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#conform -- arith unblock -/
theorem rt_sigprocmask_unblock_clears (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 65538 sig_model_blocked) [] := by
  sys_norm
/-- ...and SIG_UNBLOCK is not SIG_BLOCK's answer, nor `old & new`'s — 0x10006 &
0x5 = 0x4, the one bit they share — so the pair cannot both be satisfied by a
spec that confuses `sigandnsets` with `sigorsets` or with a plain and.
rocq-twin: rt_sigprocmask_unblock_is_not_block
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:arg0=0 -- arith unblock -/
theorem rt_sigprocmask_unblock_is_not_block :
    ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 65543 sig_model_blocked) [])
    ∧ ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 4 sig_model_blocked) []) := by
  constructor <;> sys_refute
/-- ...and SIG_BLOCK is not SIG_SETMASK's.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:arg0=2 -- arith block -/
theorem rt_sigprocmask_block_is_not_setmask :
    ¬ rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 5 sig_model_blocked) []) := by
  sys_refute
/-- SIG_SETMASK to every bit set installs everything but the two: 2^64 - 1
minus 0x40100.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x2 0xffffffffffffffff 0x8 0 -/
theorem rt_sigprocmask_setmask_all_bits (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 2 4096 0 8 (sigprocmask_in (bytes_at 4096 (List.replicate 8 255)) mem_none) demo_model o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] []))
              (with_sigmask (Z_to_bv 64 (2 ^ 64 - 1 - 262400)) demo_model) [] := by
  sys_norm

/-! ## The copy-out after an install: the ENTRY mask, last, with no rollback

`old_set` was snapshotted at kernel/signal.c:3337 (Linux v6.18.46), before `sigprocmask`
ran, and is what `copy_to_user` writes at :3350; a fault there returns
-EFAULT with the new mask already installed. -/

/-- The snapshot precedes the install: `oset` gets 0x10006, the installed
mask is the stripped 0x5, and the ledger carries the eight bytes.
rocq-twin: rt_sigprocmask_oldset_snapshot_precedes_install
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#conform -- arith setmask -/
theorem rt_sigprocmask_oldset_snapshot_precedes_install (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 2 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset) sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
              (with_sigmask 5 sig_model_blocked) [] := by
  sys_norm
/-- A kernel reporting the INSTALLED mask instead — the post-install
snapshot a reimplementation makes — is refused: two orderings, not two
values.
rocq-twin: rt_sigprocmask_oldset_is_not_the_new_mask
kernel: kernel/signal.c:rt_sigprocmask@v6.18.46 -/
theorem rt_sigprocmask_oldset_is_not_the_new_mask :
    ¬ rt_sigprocmask_spec 2 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [(8192, [5, 0, 0, 0, 0, 0, 0, 0])] []))
          (with_sigmask 5 sig_model_blocked) []) := by
  sys_refute
/-- ...and so is a success that reported no mask.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:drop-writes -- arith block -/
theorem rt_sigprocmask_install_drop_writes_rejected :
    ¬ rt_sigprocmask_spec 0 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset) sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 65543 sig_model_blocked) []) := by
  sys_refute
/-- THE NO-ROLLBACK CORNER: an `oset` whose eight bytes end past `TASK_SIZE`
returns -EFAULT WITH THE NEW MASK INSTALLED, and the copy-in recorded.
rocq-twin: rt_sigprocmask_oldset_efault_still_installs
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#conform -- faultout -/
theorem rt_sigprocmask_oldset_efault_still_installs (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 2 4096 (Z_to_bv 64 (2 ^ 64 - 8)) 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset)
        sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) (with_sigmask 5 sig_model_blocked) [] := by
  sys_norm
/-- ...a success there would owe a write `__access_ok` forbids, and is
refused.
rocq-twin: rt_sigprocmask_oldset_over_task_size_never_succeeds
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#2:ret=0 -- faultout -/
theorem rt_sigprocmask_oldset_over_task_size_never_succeeds :
    ¬ rt_sigprocmask_spec 2 4096 (Z_to_bv 64 (2 ^ 64 - 8)) 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset)
        sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 5 sig_model_blocked) []) := by
  sys_refute
/-- ...and a rollback — -EFAULT with the entry mask kept — is refused too.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#reject --mutate 135#3:poison-writes:0 -- faultout -/
theorem rt_sigprocmask_oldset_efault_rollback_rejected :
    ¬ rt_sigprocmask_spec 2 4096 (Z_to_bv 64 (2 ^ 64 - 8)) 8 (sigprocmask_in mem_sigset_kill_stop wmem_oldset)
        sig_model_blocked
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) sig_model_blocked []) := by
  sys_refute
/-- An `oset` below `TASK_SIZE` that is not wholly writable declines after
the install: the same class as the pure query's, on the install arm — the
class Rocq's `rt_sigprocmask_oldset_unmodeled` pins (a readable set at 4096,
an unwritable `oset` at 8192), under SIG_UNBLOCK on the blocked model.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#fail-closed --expect-unmodeled rt_sigprocmask -- old ok far 0x1 0x8 -14 -/
theorem rt_sigprocmask_install_unwritable_oset_declines (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 8192 8 (sigprocmask_in mem_sigset_kill_stop mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- The Rocq case itself, shape for shape: SIG_BLOCK of the SIGSEGV byte at
4096 with an `oset` at 8192 no byte of the writable map covers, on the entry
model (Rocq's `sig_model` is `demo_model` here) — declined, for the reason
above.  The two pins beside it carry the same class on other shapes; this one
is the case the register names.
rocq-twin: rt_sigprocmask_oldset_unmodeled -/
theorem rt_sigprocmask_oldset_unmodeled (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 0 4096 8192 8 (sigprocmask_in mem_sigset_sigsegv mem_none) demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## The abort path: the install that kills

musl's `raise` blocks, sends SIGABRT to itself and restores; with SIGABRT
blocked the send only makes it pending, and the RESTORE is fatal:
`__set_task_blocked` installs (kernel/signal.c:3203, Linux v6.18.46) and `recalc_sigpending`
(:3204) finds the now-unblocked pending signal, so `get_signal` takes the
fatal path (:3016-3043).  The order is the kernel's: the mask is installed
first and the process dies afterwards, the syscall's return still 0.  The
pending bit is `State.with_sigabrt_pending`, the setter the `tkill` arm
calls once ported; `abort_model_blocked` has SIGABRT (32) blocked. -/

/-- Unblocking a PENDING SIGABRT kills: the model is `with_killed 6` over
the install, the return still 0 with its ledger.
rocq-twin: rt_sigprocmask_unblock_pending_sigabrt_kills
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -/
theorem rt_sigprocmask_unblock_pending_sigabrt_kills (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
        (with_sigabrt_pending abort_model_blocked) o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] []))
              (with_killed 6 (with_sigmask 0 (with_sigabrt_pending abort_model_blocked))) [] := by
  sys_norm
/-- With nothing pending the same call is the plain install it always was:
the control for the one above.
rocq-twin: rt_sigprocmask_unblock_nothing_pending_lives
kernel: kernel/signal.c:__set_task_blocked,recalc_sigpending@v6.18.46 -/
theorem rt_sigprocmask_unblock_nothing_pending_lives (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none) abort_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 abort_model_blocked) [] := by
  sys_norm
/-- And a pending SIGABRT that STAYS blocked is not delivered: blocking
SIGSEGV on top installs 0x420 and the process lives, because
`recalc_sigpending_tsk` tests the pending set against the new mask.
kernel: kernel/signal.c:__set_task_blocked,recalc_sigpending_tsk@v6.18.46 -/
theorem rt_sigprocmask_pending_still_blocked_lives (o : outcome SyscallEffect) :
    rt_sigprocmask_spec 0 4096 0 8 (sigprocmask_in mem_sigset_sigsegv mem_none)
        (with_sigabrt_pending abort_model_blocked) o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] []))
              (with_sigmask 1056 (with_sigabrt_pending abort_model_blocked)) [] := by
  sys_norm
/-- The lies about the kill: an install that did not die, a death that did
not install, and -EINVAL on the restore.
probe: testing/syscall-check/tests/abort_terminal.c#reject --mutate rt_sigprocmask#3:ret=-EINVAL --abort-terminal --guest-signal 6 -/
theorem rt_sigprocmask_unblock_pending_sigabrt_lies_rejected :
    ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
        (with_sigabrt_pending abort_model_blocked)
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 (with_sigabrt_pending abort_model_blocked)) [])
    ∧ ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
        (with_sigabrt_pending abort_model_blocked)
        (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_killed 6 (with_sigabrt_pending abort_model_blocked)) [])
    ∧ ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
        (with_sigabrt_pending abort_model_blocked)
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] []))
          (with_sigabrt_pending abort_model_blocked) []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- The death is not reported through the return: a kernel answering
anything but 0 to the fatal restore is refused (the value is unobservable
— `Run.sstep_killed` discards the effect — but the relation is total on
the shape).
kernel: kernel/signal.c:rt_sigprocmask,get_signal@v6.18.46 -/
theorem rt_sigprocmask_kill_forged_return_rejected :
    ¬ rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none)
        (with_sigabrt_pending abort_model_blocked)
        (Ok (with_copyins sig_copyin (mkEffect 6 [] []))
          (with_killed 6 (with_sigmask 0 (with_sigabrt_pending abort_model_blocked))) []) := by
  sys_refute

/-! ## The one-sided frame, refuted

`Run.decl_off_frame_one_sided` quantifies over the declaration alone; the
delivery inside `rt_sigprocmask` branches on the PENDING bit and never
looks at the declaration, so a model with the declaration clear and the
bit set is killed by an ordinary `rt_sigprocmask(SIG_UNBLOCK, {SIGABRT})`.
`State.with_sigabrt_pending` is total, so that model is constructible
even though no run with the declaration off reaches it — which is exactly
why the frame the tree consumes, `Run.decl_off_frame`, carries the bit. -/

/-- An ordinary unblock kills `one_sided_model`, through the dispatcher.
rocq-twin: one_sided_unblock_kills
kernel: kernel/signal.c:__set_task_blocked,recalc_sigpending@v6.18.46 -/
theorem one_sided_unblock_kills :
    syscall_spec (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt mem_none)
      one_sided_model
      (Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_killed 6 (with_sigmask 0 one_sided_model)) []) := by
  sys_norm

/-- The one-sided frame is FALSE: the call above satisfies its hypotheses
and violates its `m_killed m' = none` conclusion.
rocq-twin: decl_off_frame_one_sided_refuted -/
theorem decl_off_frame_one_sided_refuted : ¬ LinuxProcessSem.Run.decl_off_frame_one_sided := by
  intro H
  have h := H (SyscallInput.mkInput 135 [1, 4096, 0, 8, 0, 0] mem_sigset_sigabrt mem_none)
    one_sided_model (with_copyins sig_copyin (mkEffect 0 [] []))
    (with_killed 6 (with_sigmask 0 one_sided_model)) [] one_sided_unblock_kills (by decide)
  exact nomatch (h.2.1 : (some (6 : word) : Option word) = none)

/-- ...and the invariant form's hypotheses are inhabited at a mask install
from a model with BOTH bits clear, which the frame then obliges to stay
that way, and it does.
rocq-twin: decl_off_frame_hypotheses_inhabited -/
theorem decl_off_frame_hypotheses_inhabited_at_a_mask_install (o : outcome SyscallEffect) :
    m_abort_terminal abort_model_undeclared = false
    ∧ m_sigabrt_pending abort_model_undeclared = false
    ∧ (rt_sigprocmask_spec 1 4096 0 8 (sigprocmask_in mem_sigset_sigabrt mem_none) abort_model_undeclared o
        ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 abort_model_undeclared) [])
    ∧ m_killed (with_sigmask 0 abort_model_undeclared) = none := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  sys_norm

/-! ## The closed-surface enumeration, machine-checked

The spec twin's header argues that the mask this model tracks is the one
Linux would have, and discharges the in-model half by enumerating every
syscall that reads `->blocked`, installs a mask, or can deliver or send a
signal, and asserting none has an arm.  The list is Rocq's; 74 (signalfd4)
is on it as a DELIVERY window, not a mask installer, and 220/435 (clone,
clone3) are deliberately NOT — their window is shut by `Run.sstep` having
no transition that starts a second task, not by the table.  In Rocq 134,
72, 22, 73, 130, 131 and 132 have arms and their windows are shut one level
down by their specs (`rt_sigaction_oact_declines` above is 134's,
`sigaltstack_leaves_the_mask_alone` below is 132's,
`tkill_reads_the_mask_and_writes_none` and the `*_off_declined` pins below
are 130's and 131's, and `Fs/Select`'s spec shuts 72's and 73's, pinned for
72 in `Checks/Cases/Fs/Select.lean`); 22 has no Lean arm yet,
so here it is shut by absence and NOT listed, because listing it would fail
the build the day its port lands with a message blaming the wrong thing.  `tools/check_decline_registers.py`
reads this list as register L1 and compares it against the Lean table. -/
def sig_mask_windows : List Int :=
  [ 74, 117, 129, 133, 136, 137, 138, 139, 240, 292, 424, 426, 441 ]

/-- Every window in the list is outside `modeled_sysnos`: adding an arm for
any of them fails HERE, which is the point.
rocq-twin: sig_mask_windows_all_declined
model: pins a model constant, `Specs.modeled_sysnos`, that no observation of one execution reveals -/
theorem sig_mask_windows_all_declined : ∀ n ∈ sig_mask_windows, n ∉ modeled_sysnos := by decide

/-- The list with the arm this file exists for planted in it. -/
def sig_mask_windows_wrong : List Int := 135 :: sig_mask_windows

/-- NEGATIVE: the same computation is FALSE the moment a number on the
modeled surface joins the list — without this an empty table would satisfy
the check above and prove nothing.
rocq-twin: sig_mask_windows_not_vacuous
model: the register's check run over a list made wrong, and 135's own membership -/
theorem sig_mask_windows_not_vacuous :
    (135 : Int) ∈ modeled_sysnos ∧ ¬ (∀ n ∈ sig_mask_windows_wrong, n ∉ modeled_sysnos) := by
  decide

/-! ## The dispatcher, read through the table

Syscall 134 reaches `rt_sigaction_spec` with a0 through `sig32`, and 135
reaches `rt_sigprocmask_spec` with a0 through `how32`; the pointer and size
arguments arrive untruncated. -/

/-- 134: SIGINT with the high half of a0 set is still SIGINT: 0.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x100000002 0x1 0x0 0x8 0 -/
theorem sysno_134_sig_high_half_dropped (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 134 [4294967298, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm
/-- ...and `(1 << 32) | 0` is still signal 0: -EINVAL.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform -- act ok 0x100000000 0x1 0x0 0x8 -22 -/
theorem sysno_134_sig_zero_high_half (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 134 [4294967296, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- `(1 << 32) | 13` fails closed exactly as SIGPIPE does.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- act ok 0x10000000d 0x1 0x0 0x8 0 -/
theorem sysno_134_sigpipe_high_half_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 134 [4294967309, 4096, 0, 8, 0, 0] mem_sigaction_zero mem_none) m
      Unmodeled := by
  sys_norm
/-- a3 is NOT narrowed: 0x100000008 is the wrong size through the table.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#conform --mutate 134:ret=-EINVAL -- act ok 0x2 0x1 0x0 0x100000008 -22 -/
theorem sysno_134_size_not_narrowed (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 134 [2, 4096, 0, 4294967304, 0, 0] mem_sigaction_zero mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- A non-NULL `oact` declines through the table.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed -- oact ok ok 0x2 0x8 any -/
theorem sysno_134_oact_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 134 [2, 4096, 4096, 8, 0, 0] mem_sigaction_zero mem_none) m
      Unmodeled := by
  sys_norm
/-- ...and a2 is a pointer, `struct sigaction __user *oact`, never narrowed:
bit 32 alone is non-NULL through the table as it is to the kernel.
kernel: kernel/signal.c:rt_sigaction@v6.18.46 -/
theorem sysno_134_oact_bit32_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 134 [2, 4096, 4294967296, 8, 0, 0] mem_sigaction_zero mem_none) m
      Unmodeled := by
  sys_norm
/-- ...and its 0 is not given.
probe: testing/syscall-check/tests/rt_sigaction_spec.c#fail-closed --mutate 134:ret=0 -- oact ok hole 0x2 0x8 any -/
theorem sysno_134_oact_success_rejected (m : Model) :
    ¬ syscall_spec (SyscallInput.mkInput 134 [2, 4096, 4294967296, 8, 0, 0] mem_sigaction_zero mem_none) m
        (Ok (mkEffect 0 [] []) m []) := by
  sys_refute
/-- 135: `(1 << 32) | 1` is SIG_UNBLOCK — over the demo fixture's empty mask
it installs 0, which this case cannot tell from no install; what it
separates is the truncated `how`, which decides success against -EINVAL.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x100000001 0x0 0x8 0 -/
theorem sysno_135_how_high_half_dropped (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 135 [4294967297, 4096, 0, 8, 0, 0] mem_sigset_sigsegv mem_none)
        demo_model o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [] [])) (with_sigmask 0 demo_model) [] := by
  sys_norm
/-- ...`(1 << 32) | 3` is the -EINVAL that 3 is, with the ledger...
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x100000003 0x0 0x8 -22 -/
theorem sysno_135_bad_how_high_half (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 135 [4294967299, 4096, 0, 8, 0, 0] mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm
/-- ...and a3 is NOT narrowed: 0x100000008 is the wrong size, with no
ledger.
rocq-twin: rt_sigprocmask_how_truncates_size_does_not
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- set ok 0x1 0x0 0x100000008 -22 -/
theorem sysno_135_size_not_narrowed (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 135 [1, 4096, 0, 4294967304, 0, 0] mem_sigset_sigsegv mem_none) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm
/-- The install with a read-back, through the table.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#conform -- old ok ok 0x1 0x8 0 -/
theorem sysno_135_install_and_read_back (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 135 [1, 4096, 8192, 8, 0, 0] mem_sigset_kill_stop wmem_oldset)
        sig_model_blocked o
      ↔ o = Ok (with_copyins sig_copyin (mkEffect 0 [(8192, [6, 0, 1, 0, 0, 0, 0, 0])] []))
              (with_sigmask 65538 sig_model_blocked) [] := by
  sys_norm
/-- An unwritable `oset` declines through the table.
probe: testing/syscall-check/tests/rt_sigprocmask_mask.c#fail-closed --expect-unmodeled rt_sigprocmask -- decline far -/
theorem sysno_135_unwritable_oset_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 135 [1, 4096, 8192, 8, 0, 0] mem_sigset_sigsegv mem_none) m
      Unmodeled := by
  sys_norm
/-- ...and -EFAULT is not given for it.
probe: testing/syscall-check/tests/rt_sigprocmask_spec.c#fail-closed --expect-unmodeled rt_sigprocmask -- old ok far 0x1 0x8 -14 -/
theorem sysno_135_unwritable_oset_efault_rejected (m : Model) :
    ¬ syscall_spec (SyscallInput.mkInput 135 [1, 4096, 8192, 8, 0, 0] mem_sigset_sigsegv mem_none) m
        (Ok (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] [])) (with_sigmask 1024 m) []) := by
  sys_refute

/-! The two number declines below are register L3's claims on 129 and 139
(`tools/check_decline_registers.py` reads a theorem named `…_unmodeled`
in this shape as "the number has no arm"); both are on `sig_mask_windows`
above, so the two registers agree with each other and with the table. -/

/-- `kill` (129) has no arm: it declines by absence, whatever the pid and
signal.  A process cannot even signal itself.
rocq-twin: kill_unmodeled
probe: testing/syscall-check/tests/signal_unmodeled.c#fail-closed --expect-unmodeled kill -- kill 0 0 -/
theorem sysno_129_is_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 129 [0, 0, 0, 0, 0, 0] mem_none mem_none) m Unmodeled := rfl

/-- `rt_sigreturn` (139) has no arm: it declines by absence.  No probe
reaches it — a bare `rt_sigreturn` restores every register from whatever
the stack holds, so the guest does not survive the call.
rocq-twin: rt_sigreturn_unmodeled
kernel: arch/riscv/kernel/signal.c:rt_sigreturn@v6.18.46 -/
theorem sysno_139_is_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 139 [0, 0, 0, 0, 0, 0] mem_none mem_none) m Unmodeled := rfl


/-! # sigaltstack (132), tkill (130) and tgkill (131)

The second half of the file: the worked cases of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Signal.v` over
`sigaltstack_spec`, `tkill_spec` and `tgkill_spec`, twinned, and the pins
each decision of the three arms owes, in the kernel's order.  Every kernel
line below was read at Linux v6.18.46 (commit 1f99e9ab748f); the section
headers name the function that decides each group.  The three specs are
gated on model state a symbolic `m` leaves undecided — the alternate-stack
bit, the abort declaration, the pinned tid — so every pin here runs on a
named fixture, and the fixtures are pinned to Rocq's `init_model`
spellings below. -/

/-! ## The register, continued

The three specs and the two builders their post-states are spelled with;
the gates (`ss_mode_ok`, `ss_disabling`, `pid_positive`, `tkill_sig_valid`)
are decided, never unfolded, and the three field decoders (`ss_sp_of`,
`ss_flags_of`, `ss_size_of`) and the struct reader (`sigaltstack_at`) are
read off each fixture by the rewrites below. -/

attribute [sys_simp low] sigaltstack_spec.eq_1 tkill_spec.eq_1 tgkill_spec.eq_1
  tkill_self.eq_1 send_sigabrt.eq_1

/-! ## The numbers these checks spell out, continued -/

/-- `ENOMEM` is 12 and `ESRCH` is 3.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM,ESRCH@v6.18.46 -/
example : ENOMEM = 12 ∧ ESRCH = 3 := by decide
/-- The two `sigaltstack` modes and the one flag bit: SS_ONSTACK 1,
SS_DISABLE 2, SS_AUTODISARM `1U << 31`.
kernel: include/uapi/linux/signal.h:SS_ONSTACK,SS_DISABLE,SS_AUTODISARM@v6.18.46 -/
example : SS_ONSTACK = 1 ∧ SS_DISABLE = 2 ∧ SS_AUTODISARM = 2147483648
    ∧ 2147483648 = ((1 <<< 31) : Nat) := by decide
/-- The smallest stack `sigaltstack` installs: 2048 bytes.
kernel: include/uapi/asm-generic/signal.h:MINSIGSTKSZ@v6.18.46 -/
example : MINSIGSTKSZ = 2048 := by decide
/-- The riscv64 `stack_t`: 24 bytes, `ss_flags` at 8, `ss_size` at 16.
model: the model's own layout constants at numerals; the kernel reading of `struct sigaltstack` is on the `Sys/Uapi/Signal.lean` twin -/
example : SIGALTSTACK_BYTES = 24 ∧ SS_FLAGS_OFF = 8 ∧ SS_SIZE_OFF = 16 := by decide
/-- `ss_mode` strips exactly bit 31, and the three accepted modes are 0,
SS_ONSTACK and SS_DISABLE; 3, 4 and every-bit-but-31 are refused, and bit 31
alone is mode 0.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
example : ss_mode 2147483648 = 0 ∧ ss_mode 2147483650 = 2 ∧ ss_mode 4294967295 = 2147483647
    ∧ ss_mode_ok 0 = true ∧ ss_mode_ok 1 = true ∧ ss_mode_ok 2 = true
    ∧ ss_mode_ok 3 = false ∧ ss_mode_ok 4 = false ∧ ss_mode_ok 2147483647 = false
    ∧ ss_mode_ok 2147483648 = true ∧ ss_disabling 2 = true ∧ ss_disabling 2147483650 = true
    ∧ ss_disabling 0 = false ∧ ss_disabling 1 = false := by decide
/-- `pid_positive` is 1..2^31-1 on the truncated `pid_t`: 0 and every
value at or above 2^31 (a negative `int`) fail it.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
example : pid_positive 0 = false ∧ pid_positive 1 = true ∧ pid_positive 2147483647 = true
    ∧ pid_positive 2147483648 = false ∧ pid_positive 4294967295 = false := by decide
/-- `valid_signal` is `sig <= 64` on the widened `int`, 0 included and 65
excluded — the bound is inclusive and there is no `sig < 1` half here.
kernel: include/linux/signal.h:valid_signal@v6.18.46 -/
example : tkill_sig_valid 0 = true ∧ tkill_sig_valid 6 = true ∧ tkill_sig_valid 64 = true
    ∧ tkill_sig_valid 65 = false ∧ tkill_sig_valid 4294967295 = false := by decide

/-! ## The fixtures, continued

Each `stack_t` is a 24-byte list laid out at 4096 by `Prelude.bytes_at`,
so exactly 24 bytes are readable and nothing on either side is
(`mem_sigaltstack_ok_maps_exactly_24` below pins both ends): a spec that
read the 32-byte struct some libcs declare would answer -EFAULT on every one
of them.  Two maps are named for how they differ: `mem_sigaltstack_short`
has 23 of the bytes, and `mem_ss_ok_high` has all 24 at `(1 << 32) + 4096`.
The names say what the kernel would make of the struct. -/

/-- A syscall input carrying its arm's number and its two byte maps.
Neither spec reads `in_sysno`; the number is there so the evidence checker
matches a pin's probe to runs that issue that syscall. -/
def sigaltstack_in (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 132 [] mem wmem
/-- The same for 130.  `tkill_spec` reads no memory, so every use below
passes `mem_none` twice; the builder keeps its siblings' shape so a pin
reads the same across the three arms. -/
def tkill_in (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 130 [] mem wmem
/-- The same for 131, with the same two `mem_none`s at every use. -/
def tgkill_in (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 131 [] mem wmem

attribute [sys_simp low] sigaltstack_in.eq_1 tkill_in.eq_1 tgkill_in.eq_1

/-- Rocq's `mem_sigaltstack_ok`: `ss_sp` 0x2000, `ss_flags` 0, `ss_size`
0x4000 (16 KiB, above MINSIGSTKSZ) — the Zig shape, the one the model
records as installed. -/
def ss_ok_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Rocq's `mem_sigaltstack_small`: the same with `ss_size` 0x400 (1 KiB),
below MINSIGSTKSZ. -/
def ss_small_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 4, 0, 0, 0, 0, 0, 0]
/-- Rocq's `mem_sigaltstack_disable`: the ordinary disable, `ss_sp` 0,
`ss_flags` SS_DISABLE, `ss_size` 0. -/
def ss_disable_bytes : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0,  2, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0]
/-- The all-zero struct: `ss_sp` 0, `ss_flags` 0, `ss_size` 0 — the shape
of the fast path's shadow. -/
def ss_zero_bytes : List byte := List.replicate 24 0
/-- The all-zero struct under SS_ONSTACK. -/
def ss_zero_onstack_bytes : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0]
/-- The all-zero struct under SS_AUTODISARM alone (byte 11 is 0x80). -/
def ss_zero_autodisarm_bytes : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 128, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0]
/-- Mode 3 over the 16 KiB stack. -/
def ss_mode3_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  3, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Mode 3 over a 1-byte stack: the order pair, -EINVAL before -ENOMEM. -/
def ss_mode3_small_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  3, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0]
/-- Mode 4 over the 16 KiB stack. -/
def ss_mode4_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  4, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Every bit of `ss_flags` but 31: 0x7fffffff, mode 0x7fffffff. -/
def ss_mode_7fffffff_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  255, 255, 255, 127, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Every bit of `ss_flags`: 0xffffffff, mode 0x7fffffff once bit 31 is
masked. -/
def ss_mode_ffffffff_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  255, 255, 255, 255, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- `ss_size` exactly MINSIGSTKSZ (0x800). -/
def ss_min_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 8, 0, 0, 0, 0, 0, 0]
/-- `ss_size` one byte below MINSIGSTKSZ (0x7ff). -/
def ss_below_min_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  255, 7, 0, 0, 0, 0, 0, 0]
/-- The 16 KiB stack under SS_ONSTACK. -/
def ss_onstack_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The 16 KiB stack under SS_AUTODISARM alone (0x80000000; byte 11 is
0x80). -/
def ss_autodisarm_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 128, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The 16 KiB stack under SS_AUTODISARM|SS_DISABLE (0x80000002). -/
def ss_autodisarm_disable_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  2, 0, 0, 128, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The 16 KiB stack under SS_AUTODISARM|SS_ONSTACK (0x80000001): bit 31
riding with bit 0. -/
def ss_autodisarm_onstack_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  1, 0, 0, 128, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The 16 KiB stack under SS_AUTODISARM with mode 3 (0x80000003): the
one bit-31 shape every implementation answers alike. -/
def ss_autodisarm_mode3_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  3, 0, 0, 128, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Bit 32 of the eight bytes at offset 8 set under mode 0: byte 12 is
PADDING, copied and never read. -/
def ss_bit32_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 1, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The same padding byte under mode 3. -/
def ss_bit32_mode3_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  3, 0, 0, 0, 1, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- Byte 11 of the struct alone — the top byte of `ss_flags`, 0x01000000 — over
the 16 KiB stack: a mode outside the three, which a reader of fewer than
four flag bytes would take for mode 0. -/
def ss_flags_top_byte_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 1, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- `ss_sp` 0 with a 16 KiB size. -/
def ss_sp_zero_bytes : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- `ss_sp` 0x2000 with size 0. -/
def ss_size_zero_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0]
/-- The largest size there is, `(size_t)-1`. -/
def ss_huge_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  255, 255, 255, 255, 255, 255, 255, 255]
/-- `ss_size` 2^32: byte 20, the fifth of the eight, is the only one set. -/
def ss_size_2_32_bytes : List byte :=
  [0, 32, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 1, 0, 0, 0]
/-- An `ss_sp` (0x7f0000000000) nothing maps, with the 16 KiB size. -/
def ss_far_bytes : List byte :=
  [0, 0, 0, 0, 0, 127, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 64, 0, 0, 0, 0, 0, 0]
/-- The far `ss_sp` with size 0: not the shadow, since the pointer is not 0,
and the pointer's only non-zero byte is its sixth. -/
def ss_far_size_zero_bytes : List byte :=
  [0, 0, 0, 0, 0, 127, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0]
/-- SS_DISABLE over a 1-byte size. -/
def ss_disable_small_bytes : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0,  2, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0]

/-- `ss_ok_bytes` at 4096. -/
def mem_sigaltstack_ok : word → Option byte := bytes_at 4096 ss_ok_bytes
/-- `ss_small_bytes` at 4096. -/
def mem_sigaltstack_small : word → Option byte := bytes_at 4096 ss_small_bytes
/-- `ss_disable_bytes` at 4096. -/
def mem_sigaltstack_disable : word → Option byte := bytes_at 4096 ss_disable_bytes
/-- The all-zero `stack_t` at 4096.  Byte for byte the same map as
`mem_sigaction_zero`, kept as its own definition so a `stack_t` fixture is
never coupled to a `struct sigaction` one. -/
def mem_ss_zero : word → Option byte := bytes_at 4096 ss_zero_bytes
/-- `ss_zero_onstack_bytes` at 4096. -/
def mem_ss_zero_onstack : word → Option byte := bytes_at 4096 ss_zero_onstack_bytes
/-- `ss_zero_autodisarm_bytes` at 4096. -/
def mem_ss_zero_autodisarm : word → Option byte := bytes_at 4096 ss_zero_autodisarm_bytes
/-- `ss_mode3_bytes` at 4096. -/
def mem_ss_mode3 : word → Option byte := bytes_at 4096 ss_mode3_bytes
/-- `ss_mode3_small_bytes` at 4096. -/
def mem_ss_mode3_small : word → Option byte := bytes_at 4096 ss_mode3_small_bytes
/-- `ss_mode4_bytes` at 4096. -/
def mem_ss_mode4 : word → Option byte := bytes_at 4096 ss_mode4_bytes
/-- `ss_mode_7fffffff_bytes` at 4096. -/
def mem_ss_mode_7fffffff : word → Option byte := bytes_at 4096 ss_mode_7fffffff_bytes
/-- `ss_mode_ffffffff_bytes` at 4096. -/
def mem_ss_mode_ffffffff : word → Option byte := bytes_at 4096 ss_mode_ffffffff_bytes
/-- `ss_min_bytes` at 4096. -/
def mem_ss_min : word → Option byte := bytes_at 4096 ss_min_bytes
/-- `ss_below_min_bytes` at 4096. -/
def mem_ss_below_min : word → Option byte := bytes_at 4096 ss_below_min_bytes
/-- `ss_onstack_bytes` at 4096. -/
def mem_ss_onstack : word → Option byte := bytes_at 4096 ss_onstack_bytes
/-- `ss_autodisarm_bytes` at 4096. -/
def mem_ss_autodisarm : word → Option byte := bytes_at 4096 ss_autodisarm_bytes
/-- `ss_autodisarm_disable_bytes` at 4096. -/
def mem_ss_autodisarm_disable : word → Option byte := bytes_at 4096 ss_autodisarm_disable_bytes
/-- `ss_autodisarm_onstack_bytes` at 4096. -/
def mem_ss_autodisarm_onstack : word → Option byte := bytes_at 4096 ss_autodisarm_onstack_bytes
/-- `ss_autodisarm_mode3_bytes` at 4096. -/
def mem_ss_autodisarm_mode3 : word → Option byte := bytes_at 4096 ss_autodisarm_mode3_bytes
/-- `ss_bit32_bytes` at 4096. -/
def mem_ss_bit32 : word → Option byte := bytes_at 4096 ss_bit32_bytes
/-- `ss_bit32_mode3_bytes` at 4096. -/
def mem_ss_bit32_mode3 : word → Option byte := bytes_at 4096 ss_bit32_mode3_bytes
/-- `ss_flags_top_byte_bytes` at 4096. -/
def mem_ss_flags_top_byte : word → Option byte := bytes_at 4096 ss_flags_top_byte_bytes
/-- `ss_sp_zero_bytes` at 4096. -/
def mem_ss_sp_zero : word → Option byte := bytes_at 4096 ss_sp_zero_bytes
/-- `ss_size_zero_bytes` at 4096. -/
def mem_ss_size_zero : word → Option byte := bytes_at 4096 ss_size_zero_bytes
/-- `ss_huge_bytes` at 4096. -/
def mem_ss_huge : word → Option byte := bytes_at 4096 ss_huge_bytes
/-- `ss_far_bytes` at 4096. -/
def mem_ss_far : word → Option byte := bytes_at 4096 ss_far_bytes
/-- `ss_far_size_zero_bytes` at 4096. -/
def mem_ss_far_size_zero : word → Option byte := bytes_at 4096 ss_far_size_zero_bytes
/-- `ss_size_2_32_bytes` at 4096. -/
def mem_ss_size_2_32 : word → Option byte := bytes_at 4096 ss_size_2_32_bytes
/-- `ss_disable_small_bytes` at 4096. -/
def mem_ss_disable_small : word → Option byte := bytes_at 4096 ss_disable_small_bytes
/-- Only the first 23 bytes of the 16 KiB struct readable: byte 23, the last
of `ss_size`, is absent. -/
def mem_sigaltstack_short : word → Option byte := bytes_at 4096 (List.take 23 ss_ok_bytes)
/-- The 16 KiB struct mapped at `(1 << 32) + 4096` and nowhere else, for the
dispatcher pin that a0 keeps its high half. -/
def mem_ss_ok_high : word → Option byte := bytes_at 4294971392 ss_ok_bytes

/-- The model after Rocq's `with_sigaltstack_installed sig_model_blocked`:
a stack recorded as installed. -/
def installed_model : Model := with_sigaltstack_installed sig_model_blocked
/-- The abort path declared and NO tid pinned: `tkill_self` has nothing to
compare `pid` against. -/
def abort_model_unpinned : Model := with_abort_terminal true demo_model
/-- SIGABRT UNBLOCKED while other signals are blocked: `sig_entry_mask`
(0x10006, bits 1, 2 and 16) on the abort fixture.  What tells a
`sigabrt_blocked` that reads bit 5 from one that reads "any bit". -/
def abort_model_others_blocked : Model := with_sigmask sig_entry_mask abort_model_unblocked
/-- SIGABRT blocked AMONG others: bit 5 on top of `sig_entry_mask`
(0x10026).  What tells bit 5 from a mask equal to 32 exactly. -/
def abort_model_blocked_among_others : Model := with_sigmask 65574 abort_model_unblocked
/-- Every blockable signal but SIGABRT: all 64 bits set except bit 5 and
the two `sigprocmask` never lets in, bit 8 (SIGKILL) and bit 18 (SIGSTOP)
(the mask `rt_sigprocmask_setmask_all_bits` installs, less
32).  The strongest fixture for the read of bit 5: any `sigabrt_blocked`
that consults another bit, alone or as well, pends where this kills. -/
def abort_model_all_but_sigabrt_blocked : Model :=
  with_sigmask 18446744073709289183 abort_model_unblocked

/-! ### The fixtures are Rocq's, pinned, continued -/

/-- Rocq's three `stack_t` maps read as the structs their docstrings
describe: (0x2000, 0, 0x4000), (0x2000, 0, 0x400) and (0, SS_DISABLE, 0).
model: the fixtures' fields, read back -/
theorem rocq_sigaltstack_fixtures_read_as_described :
    ss_sp_of ss_ok_bytes = 8192 ∧ ss_flags_of ss_ok_bytes = 0 ∧ ss_size_of ss_ok_bytes = 16384
    ∧ ss_sp_of ss_small_bytes = 8192 ∧ ss_flags_of ss_small_bytes = 0
    ∧ ss_size_of ss_small_bytes = 1024
    ∧ ss_sp_of ss_disable_bytes = 0 ∧ ss_flags_of ss_disable_bytes = 2
    ∧ ss_size_of ss_disable_bytes = 0 := by decide
/-- The two extra models are `demo_model` with one setter each, and the
installed one has the bit the other fixtures lack.
model: the fixtures' fields, read back -/
theorem extra_models_read_as_described :
    m_sigaltstack_installed installed_model = true
    ∧ m_sigaltstack_installed sig_model_blocked = false
    ∧ m_sigmask installed_model = sig_entry_mask
    ∧ m_abort_terminal abort_model_unpinned = true ∧ m_tid abort_model_unpinned = none
    ∧ m_tid abort_model_unblocked = some 4242 ∧ m_abort_terminal abort_model_unblocked = true
    ∧ m_abort_terminal abort_model_undeclared = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### What each fixture reads as, continued

The struct reads and the field decodes, kept as rewrites so the first pass
of `sys_norm` sees the value where the spec reads the map. -/

/-- The first eight 24-byte maps read as their lists.
model: closed `sigaltstack_at` reads of the fixtures, rewrites for `sys_norm`. -/
theorem sigaltstack_at_reads_1 :
    sigaltstack_at mem_sigaltstack_ok 4096 = some ss_ok_bytes
    ∧ sigaltstack_at mem_sigaltstack_small 4096 = some ss_small_bytes
    ∧ sigaltstack_at mem_sigaltstack_disable 4096 = some ss_disable_bytes
    ∧ sigaltstack_at mem_ss_zero 4096 = some ss_zero_bytes
    ∧ sigaltstack_at mem_ss_zero_onstack 4096 = some ss_zero_onstack_bytes
    ∧ sigaltstack_at mem_ss_zero_autodisarm 4096 = some ss_zero_autodisarm_bytes
    ∧ sigaltstack_at mem_ss_mode3 4096 = some ss_mode3_bytes
    ∧ sigaltstack_at mem_ss_mode3_small 4096 = some ss_mode3_small_bytes := by decide
/-- The next eight.
model: closed `sigaltstack_at` reads of the fixtures, rewrites for `sys_norm`. -/
theorem sigaltstack_at_reads_2 :
    sigaltstack_at mem_ss_mode4 4096 = some ss_mode4_bytes
    ∧ sigaltstack_at mem_ss_mode_7fffffff 4096 = some ss_mode_7fffffff_bytes
    ∧ sigaltstack_at mem_ss_mode_ffffffff 4096 = some ss_mode_ffffffff_bytes
    ∧ sigaltstack_at mem_ss_min 4096 = some ss_min_bytes
    ∧ sigaltstack_at mem_ss_below_min 4096 = some ss_below_min_bytes
    ∧ sigaltstack_at mem_ss_onstack 4096 = some ss_onstack_bytes
    ∧ sigaltstack_at mem_ss_autodisarm 4096 = some ss_autodisarm_bytes
    ∧ sigaltstack_at mem_ss_autodisarm_disable 4096 = some ss_autodisarm_disable_bytes := by decide
/-- The rest, and the reads that fail: the 23-byte map, unmapped memory, the
low address 8, and the two addresses on the wrong side of `mem_ss_ok_high`.
model: closed `sigaltstack_at` reads of the fixtures, rewrites for `sys_norm`. -/
theorem sigaltstack_at_reads_3 :
    sigaltstack_at mem_ss_bit32 4096 = some ss_bit32_bytes
    ∧ sigaltstack_at mem_ss_bit32_mode3 4096 = some ss_bit32_mode3_bytes
    ∧ sigaltstack_at mem_ss_sp_zero 4096 = some ss_sp_zero_bytes
    ∧ sigaltstack_at mem_ss_size_zero 4096 = some ss_size_zero_bytes
    ∧ sigaltstack_at mem_ss_huge 4096 = some ss_huge_bytes
    ∧ sigaltstack_at mem_ss_far 4096 = some ss_far_bytes
    ∧ sigaltstack_at mem_ss_disable_small 4096 = some ss_disable_small_bytes
    ∧ sigaltstack_at mem_ss_ok_high 4294971392 = some ss_ok_bytes
    ∧ sigaltstack_at mem_ss_ok_high 4096 = none
    ∧ sigaltstack_at mem_sigaltstack_short 4096 = none
    ∧ sigaltstack_at mem_none 4096 = none
    ∧ sigaltstack_at mem_sigaltstack_ok 8 = none
    ∧ sigaltstack_at mem_sigaltstack_ok 4294967296 = none := by decide
/-- The field decodes of every list: `ss_flags` is the four bytes at 8, so
bit 32 (byte 12) is not part of it, and 0xffffffff decodes to the full word
whose mode is 0x7fffffff.
model: closed `ss_sp_of`/`ss_flags_of`/`ss_size_of` reads of the fixtures, rewrites for `sys_norm`. -/
theorem ss_fields_read :
    ss_sp_of ss_zero_bytes = 0 ∧ ss_flags_of ss_zero_bytes = 0 ∧ ss_size_of ss_zero_bytes = 0
    ∧ ss_sp_of ss_zero_onstack_bytes = 0 ∧ ss_flags_of ss_zero_onstack_bytes = 1
    ∧ ss_size_of ss_zero_onstack_bytes = 0
    ∧ ss_sp_of ss_zero_autodisarm_bytes = 0 ∧ ss_flags_of ss_zero_autodisarm_bytes = 2147483648
    ∧ ss_size_of ss_zero_autodisarm_bytes = 0
    ∧ ss_sp_of ss_mode3_bytes = 8192 ∧ ss_flags_of ss_mode3_bytes = 3 ∧ ss_size_of ss_mode3_bytes = 16384
    ∧ ss_sp_of ss_mode3_small_bytes = 8192 ∧ ss_flags_of ss_mode3_small_bytes = 3
    ∧ ss_size_of ss_mode3_small_bytes = 1
    ∧ ss_sp_of ss_mode4_bytes = 8192 ∧ ss_flags_of ss_mode4_bytes = 4 ∧ ss_size_of ss_mode4_bytes = 16384
    ∧ ss_sp_of ss_mode_7fffffff_bytes = 8192 ∧ ss_flags_of ss_mode_7fffffff_bytes = 2147483647
    ∧ ss_size_of ss_mode_7fffffff_bytes = 16384
    ∧ ss_sp_of ss_mode_ffffffff_bytes = 8192 ∧ ss_flags_of ss_mode_ffffffff_bytes = 4294967295
    ∧ ss_size_of ss_mode_ffffffff_bytes = 16384
    ∧ ss_sp_of ss_min_bytes = 8192 ∧ ss_flags_of ss_min_bytes = 0 ∧ ss_size_of ss_min_bytes = 2048
    ∧ ss_sp_of ss_below_min_bytes = 8192 ∧ ss_flags_of ss_below_min_bytes = 0
    ∧ ss_size_of ss_below_min_bytes = 2047
    ∧ ss_sp_of ss_onstack_bytes = 8192 ∧ ss_flags_of ss_onstack_bytes = 1
    ∧ ss_size_of ss_onstack_bytes = 16384
    ∧ ss_sp_of ss_autodisarm_bytes = 8192 ∧ ss_flags_of ss_autodisarm_bytes = 2147483648
    ∧ ss_size_of ss_autodisarm_bytes = 16384
    ∧ ss_sp_of ss_autodisarm_disable_bytes = 8192
    ∧ ss_flags_of ss_autodisarm_disable_bytes = 2147483650
    ∧ ss_size_of ss_autodisarm_disable_bytes = 16384
    ∧ ss_sp_of ss_bit32_bytes = 8192 ∧ ss_flags_of ss_bit32_bytes = 0 ∧ ss_size_of ss_bit32_bytes = 16384
    ∧ ss_sp_of ss_bit32_mode3_bytes = 8192 ∧ ss_flags_of ss_bit32_mode3_bytes = 3
    ∧ ss_size_of ss_bit32_mode3_bytes = 16384
    ∧ ss_sp_of ss_sp_zero_bytes = 0 ∧ ss_flags_of ss_sp_zero_bytes = 0 ∧ ss_size_of ss_sp_zero_bytes = 16384
    ∧ ss_sp_of ss_size_zero_bytes = 8192 ∧ ss_flags_of ss_size_zero_bytes = 0
    ∧ ss_size_of ss_size_zero_bytes = 0
    ∧ ss_sp_of ss_huge_bytes = 8192 ∧ ss_flags_of ss_huge_bytes = 0
    ∧ ss_size_of ss_huge_bytes = 18446744073709551615
    ∧ ss_sp_of ss_far_bytes = 139637976727552 ∧ ss_flags_of ss_far_bytes = 0
    ∧ ss_size_of ss_far_bytes = 16384
    ∧ ss_sp_of ss_disable_small_bytes = 0 ∧ ss_flags_of ss_disable_small_bytes = 2
    ∧ ss_size_of ss_disable_small_bytes = 1 := by decide

/-- The five maps added by the deep review, and the read that WRAPS: the
walk from `2^64 - 8` steps through the top eight addresses and on to
0..15, none of which `mem_sigaltstack_ok` maps.
model: closed `sigaltstack_at` reads of the fixtures, rewrites for `sys_norm`. -/
theorem sigaltstack_at_reads_4 :
    sigaltstack_at mem_ss_autodisarm_onstack 4096 = some ss_autodisarm_onstack_bytes
    ∧ sigaltstack_at mem_ss_autodisarm_mode3 4096 = some ss_autodisarm_mode3_bytes
    ∧ sigaltstack_at mem_ss_flags_top_byte 4096 = some ss_flags_top_byte_bytes
    ∧ sigaltstack_at mem_ss_far_size_zero 4096 = some ss_far_size_zero_bytes
    ∧ sigaltstack_at mem_ss_size_2_32 4096 = some ss_size_2_32_bytes
    ∧ sigaltstack_at mem_sigaltstack_ok 18446744073709551608 = none := by decide
/-- Their field decodes: bit 31 riding with bit 0 and with mode 3, the top
flags byte alone, the far pointer over size 0, and the size with only
byte 20 set.
model: closed `ss_sp_of`/`ss_flags_of`/`ss_size_of` reads of the fixtures, rewrites for `sys_norm`. -/
theorem ss_fields_read_2 :
    ss_sp_of ss_autodisarm_onstack_bytes = 8192
    ∧ ss_flags_of ss_autodisarm_onstack_bytes = 2147483649
    ∧ ss_size_of ss_autodisarm_onstack_bytes = 16384
    ∧ ss_sp_of ss_autodisarm_mode3_bytes = 8192
    ∧ ss_flags_of ss_autodisarm_mode3_bytes = 2147483651
    ∧ ss_size_of ss_autodisarm_mode3_bytes = 16384
    ∧ ss_sp_of ss_flags_top_byte_bytes = 8192 ∧ ss_flags_of ss_flags_top_byte_bytes = 16777216
    ∧ ss_size_of ss_flags_top_byte_bytes = 16384
    ∧ ss_sp_of ss_far_size_zero_bytes = 139637976727552 ∧ ss_flags_of ss_far_size_zero_bytes = 0
    ∧ ss_size_of ss_far_size_zero_bytes = 0
    ∧ ss_sp_of ss_size_2_32_bytes = 8192 ∧ ss_flags_of ss_size_2_32_bytes = 0
    ∧ ss_size_of ss_size_2_32_bytes = 4294967296 := by decide
/-- `mem_sigaltstack_ok` maps its 24 bytes and nothing on either side: the
claim the fixtures section makes, as a check.
model: the fixture's extent, read back at both ends -/
theorem mem_sigaltstack_ok_maps_exactly_24 :
    mem_sigaltstack_ok 4095 = none ∧ mem_sigaltstack_ok 4096 = some 0
    ∧ mem_sigaltstack_ok 4119 = some 0 ∧ mem_sigaltstack_ok 4120 = none := by decide
/-- The three mask fixtures read as described, and `sigabrt_blocked` reads
bit 5 of each: clear in 0x10006 and in 0xfffffffffffbfedf, set in 0x10026,
as in 32 and not in 0 — the `sigismember(&t->blocked, sig)` of `wants_signal`
(kernel/signal.c:946-949, Linux v6.18.46) asks about the one bit.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem mask_models_read_as_described :
    m_sigmask abort_model_others_blocked = 65542
    ∧ m_sigmask abort_model_blocked_among_others = 65574
    ∧ m_tid abort_model_others_blocked = some 4242
    ∧ m_abort_terminal abort_model_blocked_among_others = true
    ∧ m_sigmask abort_model_all_but_sigabrt_blocked = 18446744073709289183
    ∧ sigabrt_blocked 65542 = false ∧ sigabrt_blocked 65574 = true
    ∧ sigabrt_blocked 18446744073709289183 = false
    ∧ sigabrt_blocked 32 = true ∧ sigabrt_blocked 0 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

attribute [sys_simp] sigaltstack_at_reads_1 sigaltstack_at_reads_2 sigaltstack_at_reads_3
  sigaltstack_at_reads_4 ss_fields_read ss_fields_read_2
  rocq_sigaltstack_fixtures_read_as_described

/-! ## sigaltstack: the recorded stack, ahead of everything

`sigaltstack_spec`'s first gate is the model's own: once a call has left
`sas_ss_size` non-zero, `on_sig_stack(sp)` (kernel/signal.c:4418, Linux
v6.18.46) and `sas_ss_flags(sp)` (:4408) both read a stack pointer no
`SyscallInput` carries, so every later call declines — the kernel's answer
to each shape below is known and is not given, which fail-closed permits.
`installed_model` is the state the install leaves. -/

/-- The install that succeeded once declines when asked again: same input,
same memory, and the only difference is the bit.
rocq-twin: sigaltstack_after_an_install_declined
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- twice -/
theorem sigaltstack_after_an_install_declined (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) installed_model o
      ↔ o = Unmodeled := by
  sys_norm
/-- ...and so does every other shape on that model: the NULL/NULL no-op the
kernel answers 0 (`do_sigaltstack` with both arguments NULL, kernel/signal.c:4461
and :4452), the disable it answers 0 (:4436-4438), and the unreadable
struct it answers -EFAULT (:4459-4460).  The bit is tested first, so none
of those answers is given.
kernel: kernel/signal.c:do_sigaltstack,sigaltstack@v6.18.46 -/
theorem sigaltstack_installed_declines_every_shape (o : outcome SyscallEffect) :
    (sigaltstack_spec 0 0 (sigaltstack_in mem_none mem_none) installed_model o ↔ o = Unmodeled)
    ∧ (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) installed_model o
        ↔ o = Unmodeled)
    ∧ (sigaltstack_spec 4096 0 (sigaltstack_in mem_none mem_none) installed_model o
        ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- The kernel's 0 to a second install is not given, nor the -EPERM a stack
pointer inside the installed stack would earn (:4418-4419).
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- disable install2 -/
theorem sigaltstack_installed_answers_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) installed_model
        (Ok (mkEffect 0 [] []) installed_model [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) installed_model
        (Ok (mkEffect (errno_ret EPERM) [] []) installed_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## `do_sigaltstack` with `oss`: the inherited flags word

`oss->ss_flags = sas_ss_flags(sp) | (current->sas_ss_flags & SS_FLAG_BITS)`
(kernel/signal.c:4408-4409, Linux v6.18.46): the second half is the bit
`begin_new_exec` never resets (fs/exec.c:1211 clears the pointer and the
size only), so the answer depends on what called `execve`, and a non-NULL
`uoss` declines whatever `uss` says. -/

/-- The pure query, `sigaltstack(NULL, &oss)`, declines.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- oss null any -/
theorem sigaltstack_uoss_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 0 8192 (sigaltstack_in mem_none mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- An install WITH a read-back declines too: the `uoss` half decides before
the install is looked at.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- oss ok any -/
theorem sigaltstack_uoss_with_install_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 8192 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- ...and it beats the -EFAULT of an unreadable `uss`: the kernel copies
`uss` first (kernel/signal.c:4459-4460, Linux v6.18.46) and would answer
-EFAULT here, one step the model does not take.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- oss h0 any -/
theorem sigaltstack_uoss_beats_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 8192 (sigaltstack_in mem_none mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- No errno rescues the decline: not the 0 of a query, nor -EINVAL.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed --mutate sigaltstack:ret=-EINVAL -- oss null any -/
theorem sigaltstack_uoss_query_lies_rejected :
    ¬ sigaltstack_spec 0 8192 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 0 8192 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- Nor the -EFAULT a faulting `oss` copy-out gives with the install
already committed (kernel/signal.c:4464-4465, Linux v6.18.46), nor the
committed install.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed --mutate sigaltstack:ret=-EFAULT -- oss ok any -/
theorem sigaltstack_uoss_install_lies_rejected :
    ¬ sigaltstack_spec 4096 8192 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EFAULT) [] []) installed_model [])
    ∧ ¬ sigaltstack_spec 4096 8192 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- `uoss` is a pointer, `stack_t __user *uoss`, never narrowed: bit 32
alone is non-NULL to the kernel and declines here.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_uoss_bit32_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 4294967296 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## `sigaltstack(NULL, NULL)`: nothing to do

With `uss` NULL the syscall copies nothing (kernel/signal.c:4459, Linux
v6.18.46) and `do_sigaltstack` with both arguments NULL runs neither branch
and returns its initial 0 (:4402, :4452). -/

/-- Both pointers NULL is 0 with the model untouched, on either fixture.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss null zero 0x0 0x0 0 -/
theorem sigaltstack_null_null_is_zero (o : outcome SyscallEffect) :
    (sigaltstack_spec 0 0 (sigaltstack_in mem_none mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ (sigaltstack_spec 0 0 (sigaltstack_in mem_none mem_none) demo_model o
      ↔ o = Ok (mkEffect 0 [] []) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- A NULL `uss` reads nothing, so it cannot fault.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EFAULT -- ss null zero 0x0 0x0 0 -/
theorem sigaltstack_null_null_efault_rejected :
    ¬ sigaltstack_spec 0 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked []) := by
  sys_refute
/-- ...and it installs nothing: the model with the bit set is not an answer.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_null_null_installs_nothing :
    ¬ sigaltstack_spec 0 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  sys_refute

/-! ## `copy_from_user(&new, uss, sizeof(stack_t))`: 24 bytes, all or nothing

`if (uss && copy_from_user(&new, uss, sizeof(stack_t))) return -EFAULT;`
(kernel/signal.c:4459-4460, Linux v6.18.46), before `do_sigaltstack` sees
anything: -EFAULT precedes -EINVAL and -ENOMEM, and 24 bytes are the
struct (include/uapi/asm-generic/signal.h:85-89). -/

/-- An unmapped `uss` is -EFAULT with the model untouched.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss h0 buf 0x0 0x4000 -14 -/
theorem sigaltstack_unreadable_uss_is_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_none mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and a partial copy is never a success.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss h0 buf 0x0 0x4000 -14 -/
theorem sigaltstack_unreadable_uss_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- `uss` = 8 is non-NULL and unmapped: -EFAULT, not the NULL no-op —
NULL-ness is `uss == 0`, not "unreadable".
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss low buf 0x0 0x4000 -14 -/
theorem sigaltstack_low_uss_is_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 8 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and its 0 is refused.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss low buf 0x0 0x4000 -14 -/
theorem sigaltstack_low_uss_success_rejected :
    ¬ sigaltstack_spec 8 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- `uss` is a pointer, never narrowed: bit 32 alone is non-NULL and, mapped
by nothing, -EFAULT.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_uss_bit32_is_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 4294967296 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked [] := by
  sys_norm
/-- Bytes 0..22 mapped and byte 23 absent: one short of the struct, -EFAULT.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss h23 buf 0x0 0x4000 -14 -/
theorem sigaltstack_23_bytes_is_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_short mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...never a success.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss h23 buf 0x0 0x4000 -14 -/
theorem sigaltstack_23_bytes_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_short mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- A `uss` eight bytes below the top of memory is -EFAULT: the 24-byte walk
runs off the end of the address space and wraps to 0, and nothing is mapped
on either side of the wrap.  `copy_from_user` refuses the range before it
reads a byte (kernel/signal.c:4459-4460, Linux v6.18.46); the model reads
and finds nothing, the same answer by another route, and the fixture's
mapped bytes are nowhere near.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_top_of_memory_is_efault (o : outcome SyscallEffect) :
    sigaltstack_spec 18446744073709551608 0 (sigaltstack_in mem_sigaltstack_ok mem_none)
        sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and no install is given there.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sigaltstack_top_of_memory_success_rejected :
    ¬ sigaltstack_spec 18446744073709551608 0 (sigaltstack_in mem_sigaltstack_ok mem_none)
        sig_model_blocked (Ok (mkEffect 0 [] []) installed_model []) := by
  sys_refute
/-- Exactly 24 readable bytes are enough (`mem_sigaltstack_ok` maps 24 and
nothing on either side, `mem_sigaltstack_ok_maps_exactly_24`), so a spec
reading a 32-byte struct would answer -EFAULT here and is wrong.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss h24 buf 0x0 0x4000 0 -/
theorem sigaltstack_24_bytes_are_enough (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...so a 32-byte read's -EFAULT is not admissible.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EFAULT -- ss h24 buf 0x0 0x4000 0 -/
theorem sigaltstack_24_bytes_efault_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked []) := by
  sys_refute
/-- An unreadable struct beats both later errnos: the mode and the size
are never read, so the -EINVAL a mode-3 struct would earn is not answered.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EINVAL -- ss h0 buf 0x3 0x1 -14 -/
theorem sigaltstack_efault_beats_einval :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_none mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## `do_sigaltstack`: the mode, after the copy and before the fast path

`ss_mode = ss_flags & ~SS_FLAG_BITS; if (ss_mode != SS_DISABLE && ss_mode
!= SS_ONSTACK && ss_mode != 0) return -EINVAL;` (kernel/signal.c:4421-4424,
Linux v6.18.46), on the `unsigned ss_flags = ss->ss_flags` read four bytes
wide (:4415).  The -EPERM ahead of it (:4418-4419) cannot fire while the
recorded size is zero. -/

/-- Mode 3 is not a mode: -EINVAL, the model untouched.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x3 0x4000 -22 -/
theorem sigaltstack_mode3_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode3 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and never succeeds.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss ok buf 0x3 0x4000 -22 -/
theorem sigaltstack_mode3_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode3 mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode3 mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- Mode 4 likewise.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x4 0x4000 -22 -/
theorem sigaltstack_mode4_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode4 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- Every bit but SS_AUTODISARM is mode 0x7fffffff: -EINVAL.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x7fffffff 0x4000 -22 -/
theorem sigaltstack_every_bit_but_31_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode_7fffffff mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and with it too: the mode is still 0x7fffffff.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0xffffffff 0x4000 -22 -/
theorem sigaltstack_every_bit_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode_ffffffff mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...never a success.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss ok buf 0xffffffff 0x4000 -22 -/
theorem sigaltstack_every_bit_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode_ffffffff mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  sys_refute
/-- A bad mode with an undersized stack is -EINVAL, not -ENOMEM: the mode is
decided at :4422 and the size at :4440.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x3 0x1 -22 -/
theorem sigaltstack_einval_beats_enomem (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode3_small mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...so the size answer is not admissible there.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-ENOMEM -- ss ok buf 0x3 0x1 -22 -/
theorem sigaltstack_einval_beats_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_mode3_small mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- The low half still decides under a set bit 32: `0x100000003` is mode 3.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x100000003 0x4000 -22 -/
theorem sigaltstack_bit32_mode3_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_bit32_mode3 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- SS_ONSTACK is an accepted INPUT mode: the install goes through.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x1 0x4000 0 -/
theorem sigaltstack_onstack_is_an_accepted_mode (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_onstack mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...and is not refused.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EINVAL -- ss ok buf 0x1 0x4000 0 -/
theorem sigaltstack_onstack_einval_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_onstack mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute
/-- SS_AUTODISARM alone masks to mode 0: an ordinary install.  That is
Linux's answer (`ss_mode = ss_flags & ~SS_FLAG_BITS`, kernel/signal.c:4421,
Linux v6.18.46) and only Linux's: qemu-user's `target_restore_altstack`
switches on the raw flags word and answers -EINVAL to every value with bit
31 set (linux-user/signal.c:317-319, QEMU v11.1.1).  The arm is Rocq's, and
`bugs/sigaltstack-autodisarm-mode-admits-linux-alone.md` records that at
this shape it proves as certain an answer outside the intersection of the
supported implementations, and what closes it.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x80000000 0x4000 0 -/
theorem sigaltstack_autodisarm_alone_is_mode_0 (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...and the -EINVAL is refused — which is exactly qemu-user's real answer
(linux-user/signal.c:319, QEMU v11.1.1).  This pin fixes what Rocq's arm
decides; the bugs/ entry above says why that is a defect and what moves.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EINVAL -- ss ok buf 0x80000000 0x4000 0 -/
theorem sigaltstack_autodisarm_einval_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute
/-- SS_AUTODISARM|SS_ONSTACK is mode SS_ONSTACK: the install goes through —
under Linux, whose mask leaves bit 0 (kernel/signal.c:4421-4424, Linux
v6.18.46); qemu-user answers -EINVAL here too (linux-user/signal.c:317-319,
QEMU v11.1.1), the second of the three shapes the bugs/ entry records.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x80000001 0x4000 0 -/
theorem sigaltstack_autodisarm_onstack_installs (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm_onstack mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...so bit 31 does not make SS_ONSTACK an invalid mode, and the refused
-EINVAL is again qemu-user's answer.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_autodisarm_onstack_einval_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm_onstack mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute
/-- SS_AUTODISARM over mode 3 is -EINVAL: the mask leaves 3, which is not a
mode.  The one bit-31 shape on which Linux (kernel/signal.c:4421-4424,
Linux v6.18.46) and qemu-user (`default:`, linux-user/signal.c:318-319,
QEMU v11.1.1) agree.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_autodisarm_mode3_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm_mode3 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and bit 31 does not rescue mode 3 into an install.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_autodisarm_mode3_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm_mode3 mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  sys_refute
/-- `ss_flags` is four bytes wide from BELOW as well: byte 11 alone
(0x01000000) is a mode outside the three, -EINVAL (kernel/signal.c:4415,
`unsigned ss_flags = ss->ss_flags`, and :4422-4424, Linux v6.18.46), where a
reader of one, two or three flag bytes would see mode 0 and install.  The
pin beside it fixes the width from above.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_flags_top_byte_is_einval (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_flags_top_byte mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...so the install a narrower reader would give is refused.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_flags_top_byte_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_flags_top_byte mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  sys_refute
/-- `ss_flags` is a 4-byte `int`: bit 32 of the word at offset 8 is padding,
so the mode is 0 and the stack installs.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x100000000 0x4000 0 -/
theorem sigaltstack_ss_flags_is_four_bytes (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_bit32 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...and reading 8 bytes there would call it an invalid mode.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EINVAL -- ss ok buf 0x100000000 0x4000 0 -/
theorem sigaltstack_ss_flags_bit32_einval_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_bit32 mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute

/-! ## `do_sigaltstack`'s SS_DISABLE branch: a write that does not shut the door

`if (ss_mode == SS_DISABLE) { ss_size = 0; ss_sp = NULL; }`
(kernel/signal.c:4436-4438, Linux v6.18.46) before the store (:4445-4448):
the record it leaves is (NULL, 0, ss_flags), the zero-size shape whose two
readers are constant in sp, so the bit stays clear and the model keeps
answering. -/

/-- The disable answers 0 and hands the model back unchanged; a later
undersized install against that model is still ANSWERED, with -ENOMEM; and
the very same call against the model the arm used to hand back — the bit
set — is declined, so a suite that lost the first conjunct would not keep
passing.
rocq-twin: sigaltstack_disable_leaves_the_record_answerable
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_disable_leaves_the_record_answerable (o : outcome SyscallEffect) :
    (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked [])
    ∧ (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) installed_model o
      ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- The install still shuts it: the 16 KiB struct sets the bit and the
disable does not, on the same fixture pair.
rocq-twin: sigaltstack_install_still_sets_the_bit
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_install_still_sets_the_bit (o : outcome SyscallEffect) :
    (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  refine ⟨?_, ?_⟩
  · sys_norm
  · sys_refute
/-- A disable is not a licence: the undersized install offered a 0 is
refused, and a store smuggled through the disable is refused too.
rocq-twin: sigaltstack_after_a_disable_rejects_a_false_success
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack#2:ret=0 -- disable small -/
theorem sigaltstack_after_a_disable_rejects_a_false_success :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) sig_model_blocked
        (Ok (mkEffect 0 [(4096, [0])] []) sig_model_blocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- SS_DISABLE ignores the size: a 1-byte disable is 0, since `ss_size` is
zeroed before any bound is applied.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x2 0x1 0 -/
theorem sigaltstack_disable_ignores_the_size (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_disable_small mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) sig_model_blocked [] := by
  sys_norm
/-- ...so a 1-byte disable is not -ENOMEM.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-ENOMEM -- ss ok buf 0x2 0x1 0 -/
theorem sigaltstack_disable_small_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_disable_small mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- SS_AUTODISARM|SS_DISABLE is a disable: 0, and the bit stays clear
although a 16 KiB size rides along.  Linux's answer once more (the mask
leaves SS_DISABLE, kernel/signal.c:4421 and :4436-4438, Linux v6.18.46);
qemu-user's is -EINVAL (linux-user/signal.c:317-319, QEMU v11.1.1), the
third shape `bugs/sigaltstack-autodisarm-mode-admits-linux-alone.md`
records.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x80000002 0x4000 0 -/
theorem sigaltstack_autodisarm_disable_is_a_disable (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_autodisarm_disable mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) sig_model_blocked [] := by
  sys_norm
/-- A second disable takes the kernel's fast path (all three fields match,
kernel/signal.c:4430-4433, Linux v6.18.46) and is 0 all the same: the model's answer does
not depend on which of the two paths the kernel took, since both leave the
same zero-size record.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- disable disable -/
theorem sigaltstack_second_disable_is_zero (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) demo_model o
      ↔ o = Ok (mkEffect 0 [] []) demo_model [] := by
  sys_norm
/-- ...and nothing is on a stack that was just disabled, nor is SS_DISABLE
an invalid mode the second time.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack#2:ret=-EPERM -- disable disable -/
theorem sigaltstack_second_disable_lies_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) demo_model
        (Ok (mkEffect (errno_ret EPERM) [] []) demo_model [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_disable mem_none) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## The fast path's shadow: `ss_sp` and `ss_size` both zero

`if (t->sas_ss_sp == ss_sp && t->sas_ss_size == ss_size && t->sas_ss_flags
== ss_flags) return 0;` (kernel/signal.c:4430-4433, Linux v6.18.46) is the
only kernel answer whose value turns on the stored flags word the model
does not track: from the starting record (NULL, 0, F) it fires exactly
when the caller's `ss_flags` equals F, and otherwise the zero size is
-ENOMEM (:4440-4441).  The all-zero struct under a non-disabling mode
declines; the two shapes beside it are answered. -/

/-- The all-zero struct under mode 0 declines: 0 if the inherited word is 0,
-ENOMEM otherwise, and the model knows neither.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- ss ok zero 0x0 0x0 fastpath -/
theorem sigaltstack_fast_path_shadow_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_zero mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- Neither answer rescues it: not the -ENOMEM…
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed --mutate sigaltstack:ret=-ENOMEM -- ss ok zero 0x0 0x0 fastpath -/
theorem sigaltstack_fast_path_shadow_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_zero mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- …nor the 0 a fresh process gets.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed --mutate sigaltstack:ret=0 -- ss ok zero 0x0 0x0 fastpath -/
theorem sigaltstack_fast_path_shadow_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_zero mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- The same under SS_ONSTACK…
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- ss ok zero 0x1 0x0 fastpath -/
theorem sigaltstack_fast_path_shadow_under_onstack_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_zero_onstack mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- …and under SS_AUTODISARM alone.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- ss ok zero 0x80000000 0x0 fastpath -/
theorem sigaltstack_fast_path_shadow_under_autodisarm_declines (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_zero_autodisarm mem_none) sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm
/-- Size 0 under a real `ss_sp` is NOT the shadow: the stored pointer is
NULL, so the fast path cannot fire and the zero size is -ENOMEM.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0x0 -12 -/
theorem sigaltstack_size_zero_with_sp_is_enomem (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_size_zero mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and never a success.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss ok buf 0x0 0x0 -12 -/
theorem sigaltstack_size_zero_with_sp_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_size_zero mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- A NULL `ss_sp` under a 16 KiB size is not the shadow either: the stored
size is 0 and this one is not, so the fast path cannot fire, and `ss_sp` is
stored without being validated (kernel/signal.c:4446) — the install
succeeds.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_sp_zero_with_size_installs (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_sp_zero mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm

/-- `ss_sp` is eight bytes wide: the far pointer, whose only non-zero byte
is its sixth, over size 0 is NOT the shadow — the stored pointer is NULL
and this one is not, so the fast path cannot fire (kernel/signal.c:4430,
Linux v6.18.46) and the zero size is -ENOMEM (:4440-4441).  A reader of
four pointer bytes would see 0, take the shape for the shadow, and decline.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_far_sp_size_zero_is_enomem (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_far_size_zero mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and neither a success nor an install is given for it.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_far_sp_size_zero_lies_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_far_size_zero mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_far_size_zero mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## `ss_size < min_ss_size`: MINSIGSTKSZ, from both sides

`if (unlikely(ss_size < min_ss_size)) ret = -ENOMEM;` (kernel/signal.c:4440-4441,
Linux v6.18.46) with `min_ss_size` the MINSIGSTKSZ the syscall passes
(:4463), 2048 on riscv64; `sigaltstack_size_valid` beside it (:4442-4443)
never decides a case this bound has not (the spec's section header). -/

/-- Exactly MINSIGSTKSZ installs: the bound is `<`, not `<=`.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0x800 0 -/
theorem sigaltstack_minsigstksz_is_enough (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_min mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...so 2048 is not too small.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-ENOMEM -- ss ok buf 0x0 0x800 0 -/
theorem sigaltstack_minsigstksz_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_min mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- One byte below it is -ENOMEM, the model untouched.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0x7ff -12 -/
theorem sigaltstack_below_minsigstksz_is_enomem (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_below_min mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...and an undersized stack never succeeds.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=0 -- ss ok buf 0x0 0x7ff -12 -/
theorem sigaltstack_below_minsigstksz_success_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_below_min mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked [])
    ∧ ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_below_min mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) installed_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- An errno leaves the record alone: `do_sigaltstack` stores under
`if (!ret)` (kernel/signal.c:4445), so the 1 KiB install answers -ENOMEM
from, and to, the same model.
rocq-twin: sigaltstack_enomem_keeps_the_record
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_enomem_keeps_the_record (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked [] := by
  sys_norm
/-- ...so an -ENOMEM that set the bit is refused.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_enomem_sets_no_bit :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_small mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) installed_model []) := by
  sys_refute
/-- ...and an -ENOMEM carrying a store is refused.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:smuggle-write:a0:8 -- ss ok buf 0x0 0x7ff -12 -/
theorem sigaltstack_enomem_admits_no_write :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_below_min mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [(4096, [0])] []) sig_model_blocked []) := by
  sys_refute
/-- `ss_size` is eight bytes wide: a size whose only set byte is the fifth
(2^32) is above MINSIGSTKSZ and installs (`size_t ss_size = ss->ss_size`,
kernel/signal.c:4414, Linux v6.18.46; the bound at :4440 is a lower one),
where a reader of four size bytes would see 0 and answer -ENOMEM.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_size_2_32_installs (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_size_2_32 mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...so the narrower reader's -ENOMEM is refused.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_size_2_32_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_size_2_32 mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- There is no upper bound: `(size_t)-1` installs.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0xffffffffffffffff 0 -/
theorem sigaltstack_huge_size_installs (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_huge mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...so a huge size is not refused.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-ENOMEM -- ss ok buf 0x0 0xffffffffffffffff 0 -/
theorem sigaltstack_huge_size_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_huge mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute

/-! ## The install: the one arm that raises `sas_ss_size`

`t->sas_ss_sp = ss_sp; t->sas_ss_size = ss_size; t->sas_ss_flags = ss_flags;`
(kernel/signal.c:4445-4448, Linux v6.18.46), reached with a non-zero
`ss_size`: the bit is set, the return is 0, and no user memory is written
or recorded — the 24 bytes went into a kernel local (:4457). -/

/-- The install: 0, the bit set, and the blocked mask untouched — the
replacement for 132's line in `sig_mask_windows`, made about what the arm
DOES: `do_sigaltstack` names `blocked` nowhere and `SYSCALL_DEFINE2(sigaltstack)`
calls no `set_user_sigmask`.
rocq-twin: sigaltstack_leaves_the_mask_alone
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_leaves_the_mask_alone (o : outcome SyscallEffect) :
    (sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [])
    ∧ m_sigmask installed_model = sig_entry_mask := by
  refine ⟨?_, rfl⟩
  sys_norm
/-- Writing nothing is an obligation: a store smuggled through the install
is refused.
rocq-twin: sigaltstack_success_admits_no_write
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:smuggle-write:a0:8 -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_success_admits_no_write :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect 0 [(4096, [0])] []) installed_model []) := by
  sys_refute
/-- ...and so is recording no copy-in: the ledger stays empty, as the
spec's is.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:smuggle-copyin:a0:24 -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_records_no_copyin :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (with_copyins [(4096, 24)] (mkEffect 0 [] [])) installed_model []) := by
  sys_refute
/-- The install without the bit is not an answer: the model that comes back
is the one with `sas_ss_size` raised.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sigaltstack_install_without_the_bit_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect 0 [] []) sig_model_blocked []) := by
  sys_refute
/-- 16 KiB is not too small.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-ENOMEM -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_install_enomem_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret ENOMEM) [] []) sig_model_blocked []) := by
  sys_refute
/-- Nothing is on an alternate stack that was never installed: no -EPERM.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EPERM -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_install_eperm_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EPERM) [] []) sig_model_blocked []) := by
  sys_refute
/-- Mode 0 is a valid mode: no -EINVAL.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EINVAL -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_install_einval_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked []) := by
  sys_refute
/-- A fully readable `uss` is not a fault: no -EFAULT.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EFAULT -- ss ok buf 0x0 0x4000 0 -/
theorem sigaltstack_install_efault_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_sigaltstack_ok mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked []) := by
  sys_refute
/-- `ss_sp` is stored, never validated: an unmapped one installs fine.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok far 0x0 0x4000 0 -/
theorem sigaltstack_far_sp_installs (o : outcome SyscallEffect) :
    sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_far mem_none) sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...and is not a fault.
probe: testing/syscall-check/tests/sigaltstack_spec.c#reject --mutate sigaltstack:ret=-EFAULT -- ss ok far 0x0 0x4000 0 -/
theorem sigaltstack_far_sp_efault_rejected :
    ¬ sigaltstack_spec 4096 0 (sigaltstack_in mem_ss_far mem_none) sig_model_blocked
        (Ok (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked []) := by
  sys_refute

/-! ### sigaltstack through the table

Syscall 132 reaches `sigaltstack_spec` with a0 and a1 as they are: both are
pointers and neither is narrowed. -/

/-- The install through the dispatcher.
probe: testing/syscall-check/tests/sigaltstack_spec.c#conform -- ss ok buf 0x0 0x4000 0 -/
theorem sysno_132_installs_through_the_table (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- ...and declines through it once the bit is set.
probe: testing/syscall-check/tests/sigaltstack_spec.c#fail-closed -- twice -/
theorem sysno_132_after_an_install_declined (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 132 [4096, 0, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        installed_model o
      ↔ o = Unmodeled := by
  sys_norm
/-- a0 is not narrowed: with the struct mapped ONLY at `(1 << 32) + 4096`,
the install goes through — a table that dropped the high half would read
4096, find nothing, and answer -EFAULT.
kernel: kernel/signal.c:sigaltstack@v6.18.46 -/
theorem sysno_132_uss_not_narrowed (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 132 [4294971392, 0, 0, 0, 0, 0] mem_ss_ok_high mem_none)
        sig_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) installed_model [] := by
  sys_norm
/-- a1 is not narrowed either: `1 << 32` is a non-NULL `uoss`, declined.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem sysno_132_uoss_bit32_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 132 [4096, 4294967296, 0, 0, 0, 0] mem_sigaltstack_ok mem_none)
        sig_model_blocked o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## tkill and tgkill: the declaration, ahead of the kernel

`State.in_abort_terminal` is the task's stance, and with it clear both
arms answer `Unmodeled` for EVERY argument shape — before the -EINVAL
`SYSCALL_DEFINE2(tkill)` (kernel/signal.c:4195-4196, Linux v6.18.46) would
answer first — because a coverage gate is not a kernel test.  The
spec-level statement of that is `tkill_spec_off_unmodeled` beside the
spec; these are its worked cases.  `abort_model_undeclared` has the tid
pinned and the declaration off. -/

/-- With the declaration off, the very call that kills below is DECLINED,
byte for byte the behaviour 130 had when it was not in the table at all.
rocq-twin: tkill_off_declined
probe: testing/syscall-check/tests/abort_terminal.c#fail-closed --expect-unmodeled tkill --guest-signal 6 -- now -/
theorem tkill_off_declined (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- ...and so is tgkill's.
rocq-twin: tgkill_off_declined
probe: testing/syscall-check/tests/abort_terminal.c#fail-closed --expect-unmodeled tgkill --guest-signal 6 -- tgkill -/
theorem tgkill_off_declined (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- The decline sits AHEAD of the kernel's first test: a non-positive pid
with the declaration off is declined, not -EINVAL, for both arms.
kernel: kernel/signal.c:tkill,tgkill@v6.18.46 -/
theorem tkill_off_beats_einval (o : outcome SyscallEffect) :
    tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- ...and tgkill's, for a non-positive pid, tgid, or both.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem tgkill_off_beats_einval (o : outcome SyscallEffect) :
    (tgkill_spec 0 0 6 (tgkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled)
    ∧ (tgkill_spec 4242 0 6 (tgkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled)
    ∧ (tgkill_spec 0 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- ...and ahead of the signal test: an invalid signal is declined too
with the declaration off, not -EINVAL.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem tkill_off_beats_bad_signal (o : outcome SyscallEffect) :
    tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- ...and ahead of the tgid test: a wrong tgid is declined, not -ESRCH.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_off_beats_esrch (o : outcome SyscallEffect) :
    tgkill_spec 7 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- The shared helper repeats the gate, so it is closed on its own: a
caller that forgot the test would still decline here.
kernel: kernel/signal.c:do_tkill@v6.18.46 -/
theorem tkill_self_off_declined (o : outcome SyscallEffect) :
    tkill_self 4242 6 (tkill_in mem_none mem_none) abort_model_undeclared o ↔ o = Unmodeled := by
  sys_norm
/-- No kernel answer rescues the decline: not the death, not the pending
bit, not the -EINVAL.
probe: testing/syscall-check/tests/abort_terminal.c#fail-closed --expect-unmodeled tkill --guest-signal 6 -/
theorem tkill_off_lies_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_undeclared) [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_undeclared) [])
    ∧ ¬ tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_undeclared []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- ...and tgkill's gate is its own first test (not `tkill_self`'s), so its
lies are refused on their own: the death, the untouched model, the -ESRCH
a wrong tgid would earn with the declaration on.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem tgkill_off_lies_rejected :
    ¬ tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_undeclared) [])
    ∧ ¬ tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect 0 [] []) abort_model_undeclared [])
    ∧ ¬ tgkill_spec 7 4242 6 (tgkill_in mem_none mem_none) abort_model_undeclared
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_undeclared []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

/-! ## The two `SYSCALL_DEFINE`s: `pid <= 0`

`SYSCALL_DEFINE2(tkill)` refuses `pid <= 0` with -EINVAL
(kernel/signal.c:4195-4196, Linux v6.18.46) and `SYSCALL_DEFINE3(tgkill)`
refuses `pid <= 0 || tgid <= 0` (:4179-4180), on the `pid_t` — an `int`,
so every negative value is at or above 2^31 after the table's `pid32` —
before any task is looked up.  `abort_model_unblocked`
has the declaration on, the tid 4242 pinned and nothing blocked. -/

/-- `pid` 0 is -EINVAL before any task is looked up.
rocq-twin: tkill_nonpositive_pid_einval
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_nonpositive_pid_einval (o : outcome SyscallEffect) :
    tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [] := by
  sys_norm
/-- So is every negative `pid_t`: INT_MIN (2^31 after truncation) and -1
(0xffffffff).
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_negative_pid_einval (o : outcome SyscallEffect) :
    (tkill_spec 2147483648 6 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (tkill_spec 4294967295 6 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- The -EINVAL kills nothing and pends nothing.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_nonpositive_pid_lies_rejected :
    ¬ tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ ¬ tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- The pid gate runs before any signal test: `pid` 0 is -EINVAL whether
the signal is one the model delivers (6), one it declines (10) or the
probe 0 — `pid <= 0` at kernel/signal.c:4195-4196 (Linux v6.18.46) fires
before `do_tkill` looks at `sig`.  A spec that declined an undeliverable
signal ahead of the gate would pass every pid-0 pin with signal 6 or 65.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_nonpositive_pid_beats_the_signal (o : outcome SyscallEffect) :
    (tkill_spec 0 10 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (tkill_spec 0 0 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- `pid` 1 and INT_MAX are positive: neither is -EINVAL.  Neither is the
caller's tid either, so both decline one test later — which is what tells
`1 <= pid` from `1 < pid` (pid 1 passes); the upper bound, `pid < 2^31`
against `pid <= 2^31`, is `tkill_negative_pid_einval` above (2^31 fails)
together with INT_MAX passing here.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_positive_pids_pass_the_gate (o : outcome SyscallEffect) :
    (tkill_spec 1 6 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled)
    ∧ (tkill_spec 2147483647 6 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- tgkill refuses EITHER argument at or below 0: `pid` 0, `tgid` 0, both,
and a negative `tgid`.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem tgkill_nonpositive_einval (o : outcome SyscallEffect) :
    (tgkill_spec 4242 0 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (tgkill_spec 0 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (tgkill_spec 0 0 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (tgkill_spec 2147483648 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm
/-- A `tgid` of 0 is -EINVAL and not the -ESRCH a wrong tgid earns: the
`<= 0` test runs in the syscall (:4179), the tgid comparison in
`do_send_specific` (:4135).
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem tgkill_nonpositive_beats_esrch :
    ¬ tgkill_spec 0 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [])
    ∧ ¬ tgkill_spec 4242 0 6 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## `find_task_by_vpid`: a task this model does not know

`p = find_task_by_vpid(pid); if (p && …)` (kernel/signal.c:4134-4135,
Linux v6.18.46) searches the whole pid namespace; the model knows one
task, its own, and only once something has pinned its tid.  Every other
positive pid declines — -ESRCH would be a claim about every other process
on the machine — and so does a call before the tid is pinned. -/

/-- A pid that is not the caller's own is declined.
rocq-twin: tkill_other_pid_declined
kernel: kernel/pid.c:find_task_by_vpid@v6.18.46 -/
theorem tkill_other_pid_declined (o : outcome SyscallEffect) :
    tkill_spec 4243 6 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- ...and the decline precedes the signal test: with the task not found,
`check_kill_permission` never runs (:4135-4136), so an invalid signal to
another pid is not -EINVAL.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_other_pid_beats_bad_signal (o : outcome SyscallEffect) :
    tkill_spec 4243 65 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- Neither the -ESRCH the kernel would answer for a pid nobody holds nor
the 0 it would answer for one somebody does is given.
kernel: kernel/pid.c:find_task_by_vpid@v6.18.46 -/
theorem tkill_other_pid_lies_rejected :
    ¬ tkill_spec 4243 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [])
    ∧ ¬ tkill_spec 4243 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- Before anything has pinned the tid there is nothing to compare `pid`
against: declined, whatever the pid.
kernel: kernel/pid.c:find_task_by_vpid@v6.18.46 -/
theorem tkill_unpinned_tid_declined (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unpinned o ↔ o = Unmodeled := by
  sys_norm
/-- ...for tgkill as well.
kernel: kernel/pid.c:find_task_by_vpid@v6.18.46 -/
theorem tgkill_unpinned_tid_declined (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_unpinned o ↔ o = Unmodeled := by
  sys_norm
/-- ...but the pid gate still answers on that model: it runs before the
lookup.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem tkill_unpinned_tid_still_refuses_pid_zero (o : outcome SyscallEffect) :
    tkill_spec 0 6 (tkill_in mem_none mem_none) abort_model_unpinned o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned [] := by
  sys_norm
/-- ...and the signal test does not: with the tid unpinned an invalid signal
is declined, not -EINVAL, because the lookup (`find_task_by_vpid`,
kernel/signal.c:4134, Linux v6.18.46) comes before `check_kill_permission`
(:4136) and the model cannot perform it.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_unpinned_tid_beats_bad_signal (o : outcome SyscallEffect) :
    tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_unpinned o ↔ o = Unmodeled := by
  sys_norm
/-- No answer rescues the unpinned decline: not the death, not the untouched
0, not the -EINVAL for the invalid signal.
kernel: kernel/pid.c:find_task_by_vpid@v6.18.46 -/
theorem tkill_unpinned_tid_lies_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unpinned
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unpinned) [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unpinned
        (Ok (mkEffect 0 [] []) abort_model_unpinned [])
    ∧ ¬ tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_unpinned
        (Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unpinned []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute
/-- tgkill to another pid declines whatever the tgid — the caller's own or
a third one — because the task is not found before the tgid is compared.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_other_pid_declined (o : outcome SyscallEffect) :
    (tgkill_spec 4243 4243 6 (tgkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled)
    ∧ (tgkill_spec 4242 4243 6 (tgkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled)
    ∧ (tgkill_spec 7 4243 6 (tgkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- ...so a wrong tgid on an unknown pid is not -ESRCH here.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_other_pid_esrch_rejected :
    ¬ tgkill_spec 7 4243 6 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked []) := by
  sys_refute

/-! ## `do_send_specific`'s tgid test: -ESRCH for the caller under another group

`int error = -ESRCH; … if (p && (tgid <= 0 || task_tgid_vnr(p) == tgid))`
(kernel/signal.c:4131, :4135, Linux v6.18.46): the task is found and its
thread-group id does not match, so the seeded -ESRCH stands and
`check_kill_permission` never runs.  One thread, one group: the caller's
tgid is its tid. -/

/-- The caller's own tid under someone else's tgid is -ESRCH.
rocq-twin: tgkill_wrong_tgid_esrch
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_wrong_tgid_esrch (o : outcome SyscallEffect) :
    tgkill_spec 7 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [] := by
  sys_norm
/-- So is INT_MAX as the tgid: positive, so past the syscall's gate, and
wrong.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_int_max_tgid_esrch (o : outcome SyscallEffect) :
    tgkill_spec 2147483647 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [] := by
  sys_norm
/-- The tgid test beats the signal test: a wrong tgid with an invalid
signal is -ESRCH, not -EINVAL, and with signal 0 or SIGUSR1 it is -ESRCH
rather than a decline — `check_kill_permission` sits behind the `&&`.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_wrong_tgid_beats_the_signal (o : outcome SyscallEffect) :
    (tgkill_spec 7 4242 65 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [])
    ∧ (tgkill_spec 7 4242 0 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [])
    ∧ (tgkill_spec 7 4242 10 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- The -ESRCH kills nothing, and the invalid signal's -EINVAL is not
given under it.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_wrong_tgid_lies_rejected :
    ¬ tgkill_spec 7 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ ¬ tgkill_spec 7 4242 65 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- The caller is not "no such task": with its own tgid the -ESRCH is refused.
probe: testing/syscall-check/tests/abort_terminal.c#reject --mutate tgkill:ret=-ESRCH --abort-terminal --guest-signal 6 -- tgkill -/
theorem tgkill_own_tgid_esrch_rejected :
    ¬ tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked []) := by
  sys_refute

/-! ## `check_kill_permission`: `valid_signal`

`check_kill_permission`'s first test (kernel/signal.c:805-806, Linux
v6.18.46) is reached because the task lookup succeeded, and it is
`valid_signal` (include/linux/signal.h:272-275, Linux v6.18.46): `sig <=
_NSIG` on the widened `unsigned long`, 64 included.  A negative `int`
widens to something enormous and fails. -/

/-- Signal 65 to the caller's own tid is -EINVAL.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem tkill_sig65_einval (o : outcome SyscallEffect) :
    tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [] := by
  sys_norm
/-- So is -1, which after the `int` truncation is 0xffffffff.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem tkill_negative_sig_einval (o : outcome SyscallEffect) :
    tkill_spec 4242 4294967295 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [] := by
  sys_norm
/-- Through tgkill too, with both ids the caller's.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem tgkill_sig65_einval (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 65 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [] := by
  sys_norm
/-- The bound is inclusive: 64 is a valid signal, so it is not -EINVAL —
it is declined one test later, as every signal but SIGABRT is.
kernel: include/linux/signal.h:valid_signal@v6.18.46 -/
theorem tkill_sig64_declined (o : outcome SyscallEffect) :
    tkill_spec 4242 64 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- The -EINVAL sends nothing: neither the death nor the pending bit.
kernel: kernel/signal.c:check_kill_permission@v6.18.46 -/
theorem tkill_sig65_lies_rejected :
    ¬ tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ ¬ tkill_spec 4242 65 (tkill_in mem_none mem_none) abort_model_blocked
        (Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## The null signal, and every signal but SIGABRT

`if (!error && sig)` (kernel/signal.c:4141, Linux v6.18.46): signal 0 is a
permission-and-existence probe whose answer is `security_task_kill`'s
(:832), an LSM question; every other signal in 1..64 would be delivered,
and the model has a disposition for SIGABRT and for no other. -/

/-- Signal 0 is declined rather than answered 0.
rocq-twin: tkill_signal_zero_declined
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_signal_zero_declined (o : outcome SyscallEffect) :
    tkill_spec 4242 0 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- ...through tgkill as well.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tgkill_signal_zero_declined (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 0 (tgkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- ...its 0 is not given.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_signal_zero_success_rejected :
    ¬ tkill_spec 4242 0 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) abort_model_unblocked []) := by
  sys_refute
/-- A signal that is not SIGABRT is declined even under the declaration:
SIGUSR1, and SIGKILL, and SIGINT — a signal whose handler install
`rt_sigaction` accepts is still not one this model can deliver.
rocq-twin: tkill_other_signal_declined
kernel: kernel/signal.c:do_send_sig_info@v6.18.46 -/
theorem tkill_other_signal_declined (o : outcome SyscallEffect) :
    (tkill_spec 4242 10 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled)
    ∧ (tkill_spec 4242 9 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled)
    ∧ (tkill_spec 4242 2 (tkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- ...through tgkill as well.
kernel: kernel/signal.c:do_send_sig_info@v6.18.46 -/
theorem tgkill_other_signal_declined (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 10 (tgkill_in mem_none mem_none) abort_model_unblocked o ↔ o = Unmodeled := by
  sys_norm
/-- ...and neither a 0 nor a death is given for them.
kernel: kernel/signal.c:do_send_sig_info@v6.18.46 -/
theorem tkill_other_signal_lies_rejected :
    ¬ tkill_spec 4242 10 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) abort_model_unblocked [])
    ∧ ¬ tkill_spec 4242 9 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_killed 9 abort_model_unblocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-! ## SIGABRT to oneself: pending under the mask, fatal without it

`__send_signal_locked` adds the signal to the pending set
(`sigaddset(&pending->signal, sig)`, kernel/signal.c:1137, Linux v6.18.46),
and `complete_signal` does not flag a task whose mask covers it —
`wants_signal` returns false on `sigismember(&p->blocked, sig)` (:946-949)
— so it stays pending until a mask change lets `recalc_sigpending_tsk`
(:159-175) find it; an unblocked one is taken on the way back to user
space, where `get_signal` finds SIG_DFL (:2942) for a coredumping signal
and reaches the fatal branch (:3016-3043).  `abort_model_blocked` has SIGABRT
(bit 5, so 32) blocked, the state musl's `raise` sends from; the two
`abort_model_*_others` fixtures below set other bits beside it, because the
kernel tests the one bit — `sigismember(&p->blocked, sig)` in `wants_signal`
— and a predicate reading "any bit" or "exactly 32" must not pass. -/

/-- With SIGABRT unblocked, `tkill(tid, SIGABRT)` ends the process: the
post-model is `with_killed 6`, which `Run.sstep_killed` reads to emit a
`KillEv` instead of an `ExitEv`.
rocq-twin: tkill_sigabrt_unblocked_kills
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -- now -/
theorem tkill_sigabrt_unblocked_kills (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [] := by
  sys_norm
/-- With SIGABRT blocked the same call does NOT kill: 0, the signal pending,
which is exactly where musl's `raise` leaves it.
rocq-twin: tkill_sigabrt_blocked_pends
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -/
theorem tkill_sigabrt_blocked_pends (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) [] := by
  sys_norm
/-- tgkill with the caller's own tgid and tid reaches the same place, which
is what makes 131 an alias of 130 here rather than a second model.
rocq-twin: tgkill_self_sigabrt_kills
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -- tgkill -/
theorem tgkill_self_sigabrt_kills (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [] := by
  sys_norm
/-- ...and pends under the mask, like tkill.
kernel: kernel/signal.c:__send_signal_locked,wants_signal,recalc_sigpending_tsk@v6.18.46 -/
theorem tgkill_self_sigabrt_blocked_pends (o : outcome SyscallEffect) :
    tgkill_spec 4242 4242 6 (tgkill_in mem_none mem_none) abort_model_blocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) [] := by
  sys_norm
/-- A second SIGABRT while one is pending leaves the model where it was: a
standard signal already pending is not queued twice (`legacy_queue`,
kernel/signal.c:1037-1040, Linux v6.18.46, tested at :1063), and the
pending bit is one bit.
kernel: kernel/signal.c:__send_signal_locked,legacy_queue@v6.18.46 -/
theorem tkill_pending_twice_stays_pending (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) (with_sigabrt_pending abort_model_blocked) o
      ↔ o = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked) [] := by
  sys_norm
/-- Other signals blocked and SIGABRT not: the send KILLS.  `wants_signal`
tests `sigismember(&p->blocked, sig)` for the one signal
(kernel/signal.c:946-949, Linux v6.18.46), so bits 1, 2 and 16 in the mask
change nothing; a `sigabrt_blocked` that read "any bit set" would pend
here.
kernel: kernel/signal.c:wants_signal,__send_signal_locked@v6.18.46 -/
theorem tkill_sigabrt_unblocked_among_others_kills (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_others_blocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_others_blocked) [] := by
  sys_norm
/-- ...and the pending bit is refused there.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem tkill_sigabrt_unblocked_among_others_pending_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_others_blocked
        (Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_others_blocked) []) := by
  sys_refute
/-- SIGABRT blocked AMONG other signals: the send PENDS, exactly as with 32
alone — the mask is not compared to 32, bit 5 is read out of it.
kernel: kernel/signal.c:wants_signal,__send_signal_locked@v6.18.46 -/
theorem tkill_sigabrt_blocked_among_others_pends (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked_among_others o
      ↔ o = Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_blocked_among_others) [] := by
  sys_norm
/-- ...and the death is refused there.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem tkill_sigabrt_blocked_among_others_death_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked_among_others
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_blocked_among_others) []) := by
  sys_refute
/-- Every other blockable signal blocked and SIGABRT not: the send KILLS.
`wants_signal` asks about the one signal being sent (kernel/signal.c:946-949,
Linux v6.18.46); sixty-one other set bits are not it.  A `sigabrt_blocked`
reading any bit but 5, alone or together with 5, pends here.
kernel: kernel/signal.c:wants_signal,__send_signal_locked@v6.18.46 -/
theorem tkill_sigabrt_alone_unblocked_kills (o : outcome SyscallEffect) :
    tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_all_but_sigabrt_blocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_all_but_sigabrt_blocked) [] := by
  sys_norm
/-- ...and the pending bit is refused there.
kernel: kernel/signal.c:wants_signal@v6.18.46 -/
theorem tkill_sigabrt_alone_unblocked_pending_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_all_but_sigabrt_blocked
        (Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_all_but_sigabrt_blocked) []) := by
  sys_refute
/-- A second SIGABRT while one is pending is not a death either: the lie
`legacy_queue` rules out (kernel/signal.c:1037-1040, Linux v6.18.46).
kernel: kernel/signal.c:legacy_queue@v6.18.46 -/
theorem tkill_pending_twice_death_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) (with_sigabrt_pending abort_model_blocked)
        (Ok (mkEffect 0 [] []) (with_killed 6 (with_sigabrt_pending abort_model_blocked)) []) := by
  sys_refute
/-- The lies about the blocked send: a death the mask forbids, and a send
that left nothing pending.
kernel: kernel/signal.c:__send_signal_locked,wants_signal,recalc_sigpending_tsk@v6.18.46 -/
theorem tkill_blocked_lies_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_blocked) [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked
        (Ok (mkEffect 0 [] []) abort_model_blocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- The lies about the unblocked send: a pending bit where the process
died, and a process that lived.
kernel: kernel/signal.c:get_signal; kernel/exit.c:do_group_exit@v6.18.46 -/
theorem tkill_unblocked_lies_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) (with_sigabrt_pending abort_model_unblocked) [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- A lying kernel that claims the abort SUCCEEDED WITH A WRITE is refused:
neither call writes user memory on any branch.
rocq-twin: tkill_forged_write_rejected
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem tkill_forged_write_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 0 [(4096, [0])] []) (with_killed 6 abort_model_unblocked) [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked
        (Ok (mkEffect 0 [(4096, [0])] []) (with_sigabrt_pending abort_model_blocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- A kernel that answered the kill with anything but 0 is refused: an
LSM's -EPERM is not admitted (bugs/tkill-lsm-denial-not-admitted.md).
rocq-twin: tkill_forged_return_rejected
probe: testing/syscall-check/tests/abort_terminal.c#reject --mutate tkill:ret=-EPERM --abort-terminal --guest-signal 6 -/
theorem tkill_forged_return_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked [])
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret EPERM) [] []) (with_killed 6 abort_model_unblocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute
/-- Nor is "no such task" for the caller itself.
probe: testing/syscall-check/tests/abort_terminal.c#reject --mutate tkill:ret=-ESRCH --abort-terminal --guest-signal 6 -/
theorem tkill_forged_esrch_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked []) := by
  sys_refute
/-- Nor any success but 0 (the value is unobservable — `Run.sstep_killed`
discards the effect — but the relation is total on the shape).
probe: testing/syscall-check/tests/abort_terminal.c#reject --mutate tkill:ret=1 --abort-terminal --guest-signal 6 -/
theorem tkill_forged_one_rejected :
    ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_unblocked
        (Ok (mkEffect 1 [] []) (with_killed 6 abort_model_unblocked) []) := by
  sys_refute
/-- THE MASK CLAIM THE SPEC HEADER'S ENUMERATION OWES, positive and negative
in one: `tkill` READS the blocked mask — the two fixtures differ in
nothing else, and one dies where the other pends — and WRITES none, so the
value `rt_sigprocmask` hands back through `oset` is still the one it
installed — `do_send_specific` and `__send_signal_locked` never assign
`->blocked` (kernel/signal.c:4127-4155 and :1042-1157, Linux v6.18.46;
:1137 touches `pending`).
rocq-twin: tkill_reads_the_mask_and_writes_none
kernel: kernel/signal.c:do_send_specific,__send_signal_locked@v6.18.46 -/
theorem tkill_reads_the_mask_and_writes_none :
    m_sigmask (with_killed 6 abort_model_unblocked) = m_sigmask abort_model_unblocked
    ∧ m_sigmask (with_sigabrt_pending abort_model_blocked) = m_sigmask abort_model_blocked
    ∧ m_killed (with_killed 6 abort_model_unblocked) = some 6
    ∧ m_killed (with_sigabrt_pending abort_model_blocked) = none
    ∧ ¬ tkill_spec 4242 6 (tkill_in mem_none mem_none) abort_model_blocked
        (Ok (mkEffect 0 [] []) (with_killed 6 abort_model_blocked) []) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  sys_refute

/-! ### tkill and tgkill through the table

Syscall 130 reaches `tkill_spec` with a0 through `pid32` and a1 through
`sig32`; 131 reaches `tgkill_spec` with a0 and a1 through `pid32` and a2
through `sig32`: every argument is an `int` and only its low half counts. -/

/-- The kill through the dispatcher.
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -- now -/
theorem sysno_130_kills_through_the_table (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [] := by
  sys_norm
/-- ...and the decline through it with the declaration off.
probe: testing/syscall-check/tests/abort_terminal.c#fail-closed --expect-unmodeled tkill --guest-signal 6 -- now -/
theorem sysno_130_off_declined (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 130 [4242, 6, 0, 0, 0, 0] mem_none mem_none) abort_model_undeclared o
      ↔ o = Unmodeled := by
  sys_norm
/-- `(1 << 32) | 4242` is pid 4242, and `(1 << 32) | 6` is SIGABRT: the
high halves of a0 and a1 are dropped.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem sysno_130_high_halves_dropped (o : outcome SyscallEffect) :
    (syscall_spec (SyscallInput.mkInput 130 [4294971538, 6, 0, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ (syscall_spec (SyscallInput.mkInput 130 [4242, 4294967302, 0, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- ...and the 32-bit `-1` (0xffffffff, what `pid32` leaves of any register
whose low half is all ones) in a0 is a negative `pid_t`, -EINVAL; the same
in a1 is a negative `int`, -EINVAL from `valid_signal`.
kernel: kernel/signal.c:tkill,check_kill_permission@v6.18.46 -/
theorem sysno_130_negative_ints (o : outcome SyscallEffect) :
    (syscall_spec (SyscallInput.mkInput 130 [4294967295, 6, 0, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked [])
    ∧ (syscall_spec (SyscallInput.mkInput 130 [4242, 4294967295, 0, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm
/-- 131: the kill through the dispatcher, and the decline with the
declaration off.
probe: testing/syscall-check/tests/abort_terminal.c#conform --abort-terminal --guest-signal 6 -- tgkill -/
theorem sysno_131_kills_through_the_table (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 131 [4242, 4242, 6, 0, 0, 0] mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [] := by
  sys_norm
/-- ...the decline through it with the declaration off.
probe: testing/syscall-check/tests/abort_terminal.c#fail-closed --expect-unmodeled tgkill --guest-signal 6 -- tgkill -/
theorem sysno_131_off_declined (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 131 [4242, 4242, 6, 0, 0, 0] mem_none mem_none) abort_model_undeclared o
      ↔ o = Unmodeled := by
  sys_norm
/-- The high halves of a0, a1 and a2 are dropped: three `int`s.
kernel: kernel/signal.c:tgkill@v6.18.46 -/
theorem sysno_131_high_halves_dropped (o : outcome SyscallEffect) :
    (syscall_spec (SyscallInput.mkInput 131 [4294971538, 4242, 6, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ (syscall_spec (SyscallInput.mkInput 131 [4242, 4294971538, 6, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) [])
    ∧ (syscall_spec (SyscallInput.mkInput 131 [4242, 4242, 4294967302, 0, 0, 0] mem_none mem_none)
        abort_model_unblocked o
      ↔ o = Ok (mkEffect 0 [] []) (with_killed 6 abort_model_unblocked) []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm
/-- A wrong tgid through the table is -ESRCH.
kernel: kernel/signal.c:do_send_specific@v6.18.46 -/
theorem sysno_131_wrong_tgid_esrch (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 131 [7, 4242, 6, 0, 0, 0] mem_none mem_none) abort_model_unblocked o
      ↔ o = Ok (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Signal
