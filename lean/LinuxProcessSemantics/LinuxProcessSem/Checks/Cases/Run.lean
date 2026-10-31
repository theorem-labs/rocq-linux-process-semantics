import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.OmniRun
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File

/-! # Checks.Cases.Run — pins for the terminal rules, the budget mark and the configured run

Pins for the ticket A12 additions to `LinuxProcessSem/Run.lean` — the
`sstep_killed` rule and the kill-freedom premise of `sstep_exit` — and
for the two predicates that read them, `MustExit.must_exit_at` and
`OmniRun.exits_with`, which have no `Checks/Cases` mirror of their own:
what they pin is the terminal-rule surface this file's subject added.
Rocq keeps the corresponding examples with the `tkill` arm
(`Checks/Cases/Kernel/Signal.v`) and in `Checks/Examples.v`
(`checker_ok_is_run_step`, `exit_dispatch_not_killed`).  The killed
configuration here is built by hand with `State.with_killed`, the setter
that arm calls, and not through the arm, so these pins hold whatever the
arm's own firing conditions are; the arm's pins are in
`Checks/Cases/Kernel/Signal.lean`.  The section headed A13 pins the budget
mark the same file gained with that ticket.  Five sections pin the
spurious-failure configuration of ticket K10-prereq-run where
`Checks/SpuriousCfg.lean`, the twin of Rocq's file, does not reach: the
filter on `brk`; one place where it removes `dup`'s forced -EMFILE; the
table's columns and the switches that read them; the two injecting arms
the table has no entry for; and the premise `Run.refusal_decided`, which
Lean discharges classically.  The last section pins the declared AT_HWCAP
pair and the abort-enabled input stance, `Run.valid_input_abort`.

Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Each decision about the kernel gets an
accepting and a rejecting instance, stated about what the kernel does; the
pins that state a fact about the definitions alone say so in their
evidence lines. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem (reg_get csr_slice)
open LinuxProcessSemantics.Riscv.DecodeC (decode_any)
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap (mmap_fd_none mmap_errnos with_brk_next)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude (CheckOk)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap (check_brk check_brk_sound_ok)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect (mprotect_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap (mremap_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap (brk_arm)
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
  (spent_budget_model over_budget_model noaccess_page_model noaccess_three_pages_model
   brk_in brk_reserved m_tight_brk m_grown brk_grow_within_budget_grants
   brk_grow_beyond_budget_returns_break)
open LinuxProcessSemantics.LinuxProcessSem.StackLayout (hwcap_rv64gc hwcap_rv64gcv)
open LinuxProcessSemantics.LinuxProcessSem.Fs (valid_fs)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath (getcwd_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File (dup_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei (unlinkat_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open (faccessat_errnos openat_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe (pipe2_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys (setid_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork (clone_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
  (socket_errnos socketpair_reserve_errnos socketpair_create_errnos bind_errnos
   listen_errnos accept_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random (getrandom_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.File (dup_arm)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File
  (dup_model_nofile4 dup_above_the_soft_limit_still_admits_the_slot)

/-! ## A killed configuration takes no step

A process the kernel has terminated by a fatal signal does not return to
user space: `get_signal` reaches `do_group_exit(signr)` and does not come
back (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).  In the
model that is `with_killed` writing `procst_halted`, the field every
`sstep` rule requires to be `none`, so nothing — no instruction, no
syscall, no second terminal rule — steps out of a killed configuration. -/

/-- THE PIN: a killed configuration takes no syscall step, and no step of
any other kind, whatever the machine state and whatever it has pending.
kernel: kernel/signal.c:get_signal; kernel/exit.c:do_group_exit@v6.18.46 -/
theorem killed_config_takes_no_step (segs : List Segment) (ms : machine_state) (m : Model)
    (sig : word) (evs : List event) (st : step_to) :
    ¬ sstep segs (config.mkCfg ms (with_killed sig m)) evs st :=
  fun h => nomatch (sstep_not_halted segs _ _ _ h : (some sig : Option word) = none)

/-- The refutation of "no step" being vacuous: the SAME machine state,
stopped at an `exit` ecall, does step when the model is still running —
so it is the kill, not the machine state, that stops the run: `exit_group`
reaches `do_group_exit` with an exit code, and the process is over by an
exit rather than a signal.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem running_config_at_exit_steps (segs : List Segment) (ms : machine_state) (m : Model)
    (x8 : word) :
    m_halted m = none →
    ms.ms_svc_pending = some x8 →
    exit_sysno x8 →
    ∃ evs st, sstep segs (config.mkCfg ms m) evs st := by
  intro hh hsvc hno
  refine ⟨[] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0) (Z_to_bv 64 255))
                   (m_fs (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                              (Z_to_bv 64 255)) m))],
          SNext (config.mkCfg ms (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                                (Z_to_bv 64 255)) m)), ?_⟩
  exact sstep.sstep_exit ms m x8 _ _ [] _ hh hsvc (exit_dispatch_admits _ m hno) rfl rfl

/-- And the halt a kill leaves is the one every rule reads: the killed
configuration is halted, by the signal number `do_group_exit` is handed.
kernel: kernel/signal.c:get_signal; kernel/exit.c:do_group_exit@v6.18.46 -/
theorem killed_config_is_halted (ms : machine_state) (m : Model) (sig : word) :
    m_halted (config.mkCfg ms (with_killed sig m)).cfg_model = some sig := rfl

/-! ## The two terminal rules are disjoint

`sstep_exit` carries `m_killed model' = none` and `sstep_killed` carries
`m_killed model' = some sig`, so one post-model selects at most one of
them.  At an `exit` ecall the post-model is `with_halted`'s, whose flag is
clear, so only the exit rule can fire there. -/

/-- The exit arm's post-model cannot feed the kill rule: `exit_group(6)`
reaches `do_group_exit` with `(6 & 0xff) << 8`, not with a signal
(`SYSCALL_DEFINE1(exit_group)`, kernel/exit.c, Linux v6.18.46, commit
1f99e9ab748f), and the model's flag says so.
kernel: kernel/exit.c:exit_group,wait_task_zombie@v6.18.46 -/
theorem exit_post_model_is_not_killed (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    exit_sysno i.in_sysno →
    LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec i m
      (LinuxProcessSemantics.LinuxProcessSem.Monad.outcome.Ok eff m' evs) →
    m_killed m' = none ∧ m_killed m' ≠ some (Z_to_bv 64 6) := by
  intro hno hspec
  have hk := exit_dispatch_not_killed _ _ _ _ _ hno hspec
  exact ⟨hk, fun h => nomatch (hk ▸ h : (none : Option word) = some (Z_to_bv 64 6))⟩

/-- A step INTO a halted configuration is one of exactly two things, and
the kill flag tells them apart — as `wait_task_zombie`'s `status & 0x7f`
tells a parent: `sstep_next_halts_by_exit`'s middle branch is refuted for
a killed successor…
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem halting_step_into_a_kill_is_not_an_exit (segs : List Segment) (c : config)
    (evs : List event) (ms : machine_state) (m : Model) (sig : word) :
    sstep segs c evs (SNext (config.mkCfg ms (with_killed sig m))) →
    ∃ evs0, evs = evs0 ++ [KillEv sig (m_fs (with_killed sig m))] := by
  intro hss
  rcases sstep_next_halts_by_exit _ _ _ _ hss with
    hnone | ⟨_, _, _, _, hk⟩ | ⟨evs0, sig', hevs, hk⟩
  · exact nomatch (hnone : (some sig : Option word) = none)
  · exact nomatch (hk : (some sig : Option word) = none)
  · have hsig : sig = sig' := Option.some.inj (hk : (some sig : Option word) = some sig')
    subst hsig
    exact ⟨evs0, hevs⟩

/-- …and the last branch is refuted for an exited one.
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem halting_step_into_an_exit_is_not_a_kill (segs : List Segment) (c : config)
    (evs : List event) (ms : machine_state) (m : Model) (code : word) :
    sstep segs c evs (SNext (config.mkCfg ms (with_halted code m))) →
    ∃ evs0, evs = evs0 ++ [ExitEv code (m_fs (with_halted code m))] := by
  intro hss
  rcases sstep_next_halts_by_exit _ _ _ _ hss with
    hnone | ⟨evs0, code', hevs, hh, _⟩ | ⟨_, _, _, hk⟩
  · exact nomatch (hnone : (some code : Option word) = none)
  · have hc : code = code' := Option.some.inj (hh : (some code : Option word) = some code')
    subst hc
    exact ⟨evs0, hevs⟩
  · exact nomatch (hk : (none : Option word) = some _)

/-! ## A death by signal is not an exit, for the verdict predicates

A parent reads `status & 0x7f` (`wait_task_zombie`, kernel/exit.c, Linux
v6.18.46, commit 1f99e9ab748f): 0 after `exit(6)`, 6 after a death by
SIGABRT.  `must_exit_at` and `exits_with` must not confuse the two, and
the kill conjunct on each is what stops them. -/

/-- `must_exit_at` accepts an exited configuration at its code…
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem must_exit_at_accepts_an_exit (segs : List Segment) (ms : machine_state) (m : Model)
    (code : word) :
    must_exit_at segs code (config.mkCfg ms (with_halted code m)) :=
  must_exit_at.must_exit_at_halted _ rfl rfl

/-- …and REFUSES a killed one at every code, the signal number included:
without the kill conjunct a death by SIGABRT would read as `exit(6)`.
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem must_exit_at_refuses_a_kill (segs : List Segment) (ms : machine_state) (m : Model)
    (sig code : word) :
    ¬ must_exit_at segs code (config.mkCfg ms (with_killed sig m)) := by
  intro h
  cases h with
  | must_exit_at_halted _ _ hk => exact nomatch (hk : (some sig : Option word) = none)
  | must_exit_at_running _ hn _ _ _ => exact nomatch (hn : (some sig : Option word) = none)

/-- The same pair for `exits_with`, the omni form's postcondition: an exit
is accepted at its code…
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem exits_with_accepts_an_exit (ms : machine_state) (m : Model) (code : word) :
    exits_with code [] (OHalt (config.mkCfg ms (with_halted code m))) := ⟨rfl, rfl⟩

/-- …and a kill is refused at the signal number, which is the code a
parent would NOT read back.
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem exits_with_refuses_a_kill (ms : machine_state) (m : Model) (sig : word) :
    ¬ exits_with sig [] (OHalt (config.mkCfg ms (with_killed sig m))) :=
  fun h => nomatch (h.2 : (some sig : Option word) = none)

/-- The declaration-off frame is an INVARIANT, not a one-sided frame: its
hypotheses are inhabited at the model every run in this tree starts from,
so the consequences drawn from it (`star_off_no_kill`) are not vacuous.
model: the frame's two hypotheses at the demo run's initial model; the declaration is the task's, not the kernel's. -/
theorem decl_off_frame_hypotheses_inhabited :
    m_abort_terminal (init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit demo_proc_input)
      = false
    ∧ m_sigabrt_pending (init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit demo_proc_input)
      = false := ⟨rfl, rfl⟩


/-! ## A13: the budget mark

Pins for `Run.alloc_budget_refused_b`, `Run.budget_refused_at` and the
dispatcher's list, the Lean half of what `Checks/BudgetPremise.v` pins
arm by arm (its PART 1 and PART 3; ticket K10 is that file's twin, and
its soundness lemmas, its first-touch clauses and its run-level images
wait there).  Rocq keeps no file mirroring this one; the pins below keep
`Checks/BudgetPremise.v`'s names where they restate its Examples, and each
is still labelled by what justifies it — the kernel line that makes the
budget's answer the kernel's, or the fact about the model's own tables —
rather than `rocq-twin:`, because the argument for a budget pin is the
kernel's accounting, not the Rocq statement.
The mark is a statement about what the BUDGET leaves the kernel — a model
constant and model-internal state — so no probe reaches it; the forged
GRANT beyond budget is `Checks/Cases/Mm/Mmap.lean`'s
`rw_grant_over_budget_is_enomem` and is not repeated here.

The fixtures keep the Rocq names (`mmap_in` from `Checks/Cases/Mm/Mmap.v`;
`mmap_fixed_rw_in`, `fixed_rw_model`, `mprotect_in` from
`Checks/BudgetPremise.v`; `tight_model` and `noaccess_base` from the
Prelude; `spent_budget_model`, `over_budget_model` and the two ledgers
`fixed_rw_model` and `three_pages_span_model` are spelled as, from
`Checks/Cases/Mm/Mmap.lean`), so a
reader can lay the two files side by side. -/

/-! ### The dispatcher and its list

Each tree's list is the allocation arms of its own `injected_table`, and
the Lean `injected_table` is Rocq's entry for entry:
`Run.alloc_family_dispatched` proves, in each tree, that every `FamAlloc`
arm of that table is on the list.  What is pinned here is the tie to the
syscall table in both directions: every listed number is a modeled arm of
the Lean syscall table (`alloc_mark_sysnos_are_modeled`), and each number
Rocq lists and this does not is one the table declines, in the register
shapes `tools/check_decline_registers.py` reads — a set empty since the
mremap dispatch, all four of Rocq's arms being ported.  Should Rocq's list
gain a fifth arm, its port and the dispatch of its mark arrive in two
changes, the port PR and the `lean: base:` companion
`Run.alloc_mark_sysnos` describes (`Run.lean` is frozen to a port PR), and
the pins here flip with the companion, as `mremap_is_dispatched` below
did.  The four `_is_dispatched` pins are `Run.alloc_family_dispatched`
applied at each `FamAlloc` entry of the table, as `Checks/BudgetPremise.v`'s
are, so they are that lemma's consumer: deleting it, or an entry leaving
the table or its family, fails this file.  That every listed number has
an arm in the dispatcher is `each_listed_number_reaches_a_refusing_mark`'s,
after the `mprotect` pins below. -/

/-- Every number the dispatcher lists is an arm of the Lean table: the
mark of a declined number would answer for an arm that does not exist.
model: `alloc_mark_sysnos` against `modeled_sysnos`, both read off the Lean tables. -/
theorem alloc_mark_sysnos_are_modeled : ∀ no ∈ alloc_mark_sysnos, no ∈ modeled_sysnos := by
  decide

/-- mmap (222) is dispatched to its mark…
kernel: include/uapi/asm-generic/unistd.h:__NR3264_mmap@v6.18.46 -/
theorem mmap_is_dispatched : (222 : Int) ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 222 (InjectedArm.mkInjectedArm 222 FamAlloc mmap_errnos) rfl rfl

/-- …and so is mprotect (226).
kernel: include/uapi/asm-generic/unistd.h:__NR_mprotect@v6.18.46 -/
theorem mprotect_is_dispatched : (226 : Int) ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 226 (InjectedArm.mkInjectedArm 226 FamAlloc mprotect_errnos) rfl rfl

/-- brk (214) is an arm of the Lean table…
kernel: include/uapi/asm-generic/unistd.h:__NR_brk@v6.18.46 -/
example : (214 : Int) ∈ modeled_sysnos := by decide

/-- …and is dispatched to its mark.
kernel: include/uapi/asm-generic/unistd.h:__NR_brk@v6.18.46 -/
theorem brk_is_dispatched : (214 : Int) ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 214 (InjectedArm.mkInjectedArm 214 FamAlloc []) rfl rfl

/-- mremap (216) has an arm in the Lean table since #810 (`Sys/Registry/Mm/Mremap.lean`)…
kernel: include/uapi/asm-generic/unistd.h:__NR_mremap@v6.18.46 -/
example : (216 : Int) ∈ modeled_sysnos := by decide

/-- …and on the dispatcher's list since the `lean: base:` follow-up #810
owed landed with the 2026-09-12 integration: `Run.lean` is a frozen base
file (`tools/check_lean_port_scope.py`), so the port could not add
`Mremap.mremap_budget_refused_b`'s arm to `alloc_budget_refused_b` in the
same change, and `tools/check_budget_marks.py`'s DISPATCH rule named the
gap (a budget-refused mremap request answered `false`, the false negative
the Rocq `Run.alloc_budget_refused_b` docstring warns of) until the arm,
the number and this pin's flip from `mremap_is_not_yet_dispatched` landed
together.
kernel: include/uapi/asm-generic/unistd.h:__NR_mremap@v6.18.46 -/
theorem mremap_is_dispatched : (216 : Int) ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 216 (InjectedArm.mkInjectedArm 216 FamAlloc mremap_errnos) rfl rfl

/-- The brk request Rocq's mark fires on (`Checks/BudgetPremise.v`'s
`brk_two_pages_is_budget_refused`: two pages past a break at 65536 on a
one-page budget) is budget-refused through the dispatcher.  The fixtures
are `Checks/Cases/Mm/Mmap.lean`'s (`brk_in`, `m_tight_brk`, `m_grown`);
the mark itself is pinned there, beside the arm's budget pins.
model: the model's budget device (`State.vm_limit`, issue #131) read through the dispatcher; the kernel refusal it stands for is `do_brk_flags`'s -ENOMEM, pinned as `brk_grow_beyond_budget_returns_break` in `Checks/Cases/Mm/Mmap.lean`. -/
theorem brk_two_pages_is_budget_refused :
    alloc_budget_refused_b (brk_in 73728) m_tight_brk = true := by decide

/-- …while the one-page grow that fits is not.
model: the model's budget device read through the dispatcher; the grant it leaves is `brk_grow_within_budget_grants` in `Checks/Cases/Mm/Mmap.lean`. -/
theorem brk_one_page_is_not_budget_refused :
    alloc_budget_refused_b (brk_in 69632) m_tight_brk = false := by decide

/-- A query is never budget-refused, whatever the budget…
model: the mark reads the request against the break before the budget; a query moves nothing. -/
theorem brk_query_is_never_budget_refused :
    alloc_budget_refused_b (brk_in 0) m_tight_brk = false := by decide

/-- …nor is a shrink.
model: the mark fires on a grow only; a shrink gives backing back. -/
theorem brk_shrink_is_never_budget_refused :
    alloc_budget_refused_b (brk_in 65536) m_grown = false := by decide

/-- A modeled arm off the list is never budget-refused either, whatever
it asks and whatever the state: `exit_group` (94) asked with mmap's
register image.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit_group@v6.18.46 -/
theorem exit_group_is_never_budget_refused (m : Model) :
    alloc_budget_refused_b
      (SyscallInput.mkInput 94 [0, 8192, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)) m
      = false :=
  alloc_budget_refused_b_outside _ m (by decide)

/-! ### The grant clause on mmap's fixtures

`tight_model`: budget 8192, one live page — one page of budget left.
`spent_budget_model`: the same page under a budget of 4096 — nothing
left.  `mmap_in len` is the hint-placed rw anonymous request.  The kernel
line that makes -ENOMEM the budget's answer is `__mmap_prepare`'s
`security_vm_enough_memory_mm` on an accountable mapping (mm/vma.c, Linux
v6.18.46, commit 1f99e9ab748f), and what makes a request NOT accountable
is `accountable_mapping` there: `VM_NORESERVE`, or no `VM_WRITE`. -/

/-- The hint-placed rw anonymous request of `len` bytes. -/
def mmap_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- Two pages on a one-page remainder: budget-refused.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_two_pages_is_budget_refused :
    alloc_budget_refused_b (mmap_in 8192) tight_model = true := by decide

/-- Within budget the mark is `false` — although -ENOMEM is still
admissible there (`mmap_spec` keeps its `alt` onto `mmap_errnos`): that is
the "forged budget refusal", and the mark does not carry it.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_one_page_is_not_budget_refused :
    alloc_budget_refused_b (mmap_in 4096) tight_model = false := by decide

/-- On the spent budget — the fixture whose `iff` in
`Checks/Cases/Mm/Mmap.lean` admits nothing but -ENOMEM — one page is
budget-refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mmap_in 4096) spent_budget_model = true := by decide

/-- …and so is one byte, since the charge is the page-rounded length.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_one_byte_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mmap_in 1) spent_budget_model = true := by decide

/-- The same request with `MAP_NORESERVE`. -/
def mmap_noreserve_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 3, 16418, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- A `MAP_NORESERVE` request beyond the budget is free at grant time and
so not a budget refusal: `accountable_mapping` is false under
`VM_NORESERVE`, which `do_mmap` sets from `MAP_NORESERVE` whenever
`sysctl_overcommit_memory` is not `OVERCOMMIT_NEVER` — the overcommit
modes 0 and 1 the model states (the `MAP_NORESERVE` docstring of
`Sys/Mm/Mmap.lean`); under mode 2 the grant is accounted and this pin's
answer is not the kernel's.  Its
pages are charged on first touch — the instruction clause of
`Run.budget_refused_at`, whose fixtures are K10's PART 2.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping; include/uapi/asm-generic/mman.h:MAP_NORESERVE@v6.18.46 -/
theorem mmap_noreserve_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreserve_in 8192) tight_model = false := by decide

/-- The PROT_NONE reservation of `len` bytes. -/
def mmap_noaccess_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 0, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- A PROT_NONE reservation consumes no backing: without `VM_WRITE` the
mapping is not accountable, whatever the budget.
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mmap_prot_none_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noaccess_in 8192) tight_model = false := by decide

/-! ### What an argument gate answers is never a budget refusal

Each of these is refused by Linux before any accounting runs, and the mark
reads the gates in the spec's order, so it is silent on them even on a
spent budget — with one exception, pinned at the end of this section: the
hint-placed rw shape has no placement gate in the mark, so a request no
placement satisfies — a length whose page rounding wraps, or any length
past `alloc_top` — is refused by the constraint the spec's `choose`
carries and the mark does not see, and on a spent budget the mark fires
on it. -/

/-- A misaligned offset: -EINVAL before generic mm runs.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem mmap_misaligned_offset_is_not_budget_refused :
    alloc_budget_refused_b
      (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 1] (fun _ => none) (fun _ => none))
      spent_budget_model = false := by decide

/-- A zero length: `do_mmap`'s first test.  On `over_budget_model`, a
ledger past its budget, because a budget merely spent cannot tell the
length gate from a zero charge behind it (`Checks/Cases/Mm/Mmap.lean`'s
`mark_zero_length_is_silent` says why).
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_zero_len_is_not_budget_refused :
    alloc_budget_refused_b
      (SyscallInput.mkInput 222 [0, 0, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none))
      over_budget_model = false := by decide

/-- `Checks/SpuriousCfg.v`'s `mmap_overflow_i`: a MAP_FIXED PROT_NONE
request whose length is within a page of `2^64`. -/
def mmap_overflow_i : SyscallInput :=
  SyscallInput.mkInput 222 [4097, Z_to_bv 64 (-1), 0, 50, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

/-- The -ENOMEM an ARGUMENT GATE determines is not a budget refusal
either, although -ENOMEM is the one member of `mmap_errnos`: `len` within
a page of `2^64` rounds to zero in machine arithmetic and `do_mmap`
answers -ENOMEM before any shape is matched.  What this request exercises
in the MARK, though, is only its `mmap_fixed_noaccess_b` branch — PROT_NONE
under MAP_FIXED, `false` whatever the length — so the overflow gate itself
is the rw spelling's business, next…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_overflowing_len_is_not_budget_refused :
    alloc_budget_refused_b mmap_overflow_i noaccess_base = false := by decide

/-- …and the rw spelling of the same overflow, inside the charging shape,
is silent too: the gate answers ahead of the charge.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_rw_overflowing_len_is_not_budget_refused :
    alloc_budget_refused_b
      (SyscallInput.mkInput 222 [0x1001, Z_to_bv 64 (-1), 3, 50, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      spent_budget_model = false := by decide

/-- The hint-placed rw spelling is the exception the section heading
names, here in its wrapping instance.  `mmap_spec`'s `mmap_modeled_b`
branch has no overflow gate: the wrapping length is refused by the
`choose`'s `a + nZ ≤ alloc_top h`, unsatisfiable at `nZ = 2^64`, so the
errno branch is the only resolution whatever the budget.  The mark reads
the request and the pre-state and not the placement constraint, and
answers its budget gate — so on a spent budget it FIRES, for a request
the address space refuses: `do_mmap` answers -ENOMEM to the wrapped
length (`PAGE_ALIGN(len)` is 0, mm/mmap.c:368-370 at v6.18.46) before
any accounting.  Conservative (a run excluded from the budget family,
not a trace admitted), inherited from Rocq's mark, and pinned so that a
port adding the gate to both trees knows which pin flips.
model: the `true` is the mark's blindness to the `choose`'s placement constraint, `4096 + 2^64 ≤ 4096` failing on `spent_budget_model`; the `do_mmap` line above is what makes it conservative rather than wrong -/
theorem mmap_rw_overflowing_len_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mmap_in (Z_to_bv 64 (-1))) spent_budget_model = true := by decide

/-- An empty ledger under a budget of `2^70` bytes, for the request no
budget below `2^64` can hold. -/
def vast_budget_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 1180591620717411303424 0 demo_sp)

/-- …and under a budget the wrapping length fits, the same request is
silent: what the mark tracks there is the budget, not the placement.
model: `0 + 2^64 ≤ 2^70` on `vast_budget_model`, and the mark reads nothing else of the request -/
theorem mmap_rw_overflowing_len_within_vast_budget_is_not_budget_refused :
    alloc_budget_refused_b (mmap_in (Z_to_bv 64 (-1))) vast_budget_model = false := by decide

/-- The wrap is one instance, not the exception itself.  A length of
`2^48` wraps nothing, and no placement satisfies the `choose` for it
either; Linux refuses it by the address space, not the budget.  Under the
Sv48 address space the model declares (`State.in_va_size`, the size the
sealed statements pin) `TASK_SIZE` is `2^47` -- `TASK_SIZE_64`,
arch/riscv/include/asm/pgtable.h:1081 at v6.18.46 -- and the first
bound mm/mmap.c:823-825 at v6.18.46 checks, `__get_unmapped_area`'s
`len > TASK_SIZE`, answers -ENOMEM before any placement helper runs; a
length below `TASK_SIZE` but above `mmap_end - mmap_min_addr` is refused
one call deeper instead, by `generic_get_unmapped_area_topdown`
(mm/mmap.c:747-748 at v6.18.46; the legacy layout's
`generic_get_unmapped_area`, :697-698), still before any gap is searched.  Under Sv57 neither test
fires and the kernel searches for a gap; that declaration is one the
sealed statements refuse.  On a spent budget the mark fires on it just
the same.
model: the `true` is the mark's blindness to the `choose`'s placement constraint, `4096 + 2^48 ≤ 4096` failing on `spent_budget_model`; the `__get_unmapped_area` line above is what makes it conservative rather than wrong -/
theorem mmap_rw_unplaceable_len_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mmap_in (Z_to_bv 64 281474976710656)) spent_budget_model = true := by
  decide

/-- …and under the `2^70` budget the same length is silent, as the
wrapping one is.
model: `0 + 2^48 ≤ 2^70` on `vast_budget_model`, and the mark reads nothing else of the request -/
theorem mmap_rw_unplaceable_len_within_vast_budget_is_not_budget_refused :
    alloc_budget_refused_b (mmap_in (Z_to_bv 64 281474976710656)) vast_budget_model = false := by
  decide

/-! ### The MAP_FIXED shapes: the replacement is charged as a delta -/

/-- One page at 65536, owned and inaccessible, under budget `lim`
(`Checks/BudgetPremise.v`'s `fixed_rw_model`): `Checks/Cases/Mm/Mmap.lean`'s
`noaccess_page_model`, under the Rocq name. -/
def fixed_rw_model (lim : Int) : Model := noaccess_page_model lim

/-- The contained MAP_FIXED rw commit exposing that page. -/
def mmap_fixed_rw_in : SyscallInput :=
  SyscallInput.mkInput 222 [65536, 4096, 3, 50, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- The contained commit, exposing a PROT_NONE page: on a spent budget it
is refused — `__mmap_prepare` charges `pglen - nr_accounted`, the pages the
request exposes that were not accounted before…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_commit_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 0) = true := by decide

/-- …and with a page left it is not.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_commit_within_budget_is_not_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 4096) = false := by decide

/-- A free-range MAP_FIXED rw grant charges like any grant: two pages on a
one-page remainder are refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_fresh_two_pages_is_budget_refused :
    alloc_budget_refused_b
      (SyscallInput.mkInput 222 [131072, 8192, 3, 50, mmap_fd_none, 0] (fun _ => none) (fun _ => none))
      tight_model = true := by decide

/-- …and one page is not.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_fresh_one_page_is_not_budget_refused :
    alloc_budget_refused_b
      (SyscallInput.mkInput 222 [131072, 4096, 3, 50, mmap_fd_none, 0] (fun _ => none) (fun _ => none))
      tight_model = false := by decide

/-- Three pages at 65536, owned and inaccessible, under budget `lim`: the
ledger a SPANNING commit meets when it names the last of them and the
free page beyond.  Not Rocq's `span_model`, which is a different ledger;
`Checks/Cases/Mm/Mmap.lean`'s `noaccess_three_pages_model`, under this
file's name. -/
def three_pages_span_model (lim : Int) : Model := noaccess_three_pages_model lim

/-- The spanning commit: pages 73728 and 77824, the first inaccessible and
owned, the second free. -/
def mmap_fixed_rw_span_in : SyscallInput :=
  SyscallInput.mkInput 222 [73728, 8192, 3, 50, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- The spanning commit charges both the exposed page and the newly owned
one: two pages on a one-page budget are refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_span_on_one_page_budget_is_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_span_in (three_pages_span_model 4096) = true := by decide

/-- …and fit a two-page budget exactly.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_fixed_span_within_budget_is_not_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_span_in (three_pages_span_model 8192) = false := by decide

/-- The MAP_FIXED_NOREPLACE rw grant over a free range. -/
def mmap_noreplace_in (prot len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [131072, len, prot, 1048610, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- The grant charges like any fresh rw grant: two pages on
`tight_model`'s one-page remainder are refused…  Rocq:
`Checks/BudgetPremise.v`'s `mmap_noreplace_two_pages_is_budget_refused`.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_noreplace_two_pages_is_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 3 8192) tight_model = true := by decide

/-- …and one page fits it exactly.  Rocq:
`mmap_noreplace_one_page_is_not_budget_refused`.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_noreplace_one_page_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 3 4096) tight_model = false := by decide

/-- The PROT_NONE spelling consumes nothing.  Rocq:
`mmap_noreplace_prot_none_is_not_budget_refused`.
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mmap_noreplace_prot_none_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 0 8192) tight_model = false := by decide

/-- PROT_SEM beside rw is a prot the Lean spec declines
(`Checks/Cases/Mm/Mmap.lean`'s `noreplace_prot_sem_is_unmodeled`), so the
request admits no grant and the mark is silent where prot 3 fires
(`mmap_noreplace_two_pages_is_budget_refused`).  Linux reads the three
prot bits alone and charges this request like rw: the `false` is the
decline's, not an exemption Linux grants.
model: a declared decline of the Lean twin; the mark reads the request and the pre-state, and a declined request has nothing for the budget to refuse. -/
theorem mmap_noreplace_declined_prot_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 11 8192) tight_model = false := by decide

/-! ### The grant clause on mprotect's fixtures -/

/-- The `mprotect` request, with a3..a5 zero. -/
def mprotect_in (addr len prot : word) : SyscallInput :=
  SyscallInput.mkInput 226 [addr, len, prot, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The reserve-then-commit idiom: a PROT_NONE page inside a live mapping,
exposed rw.  On a spent budget the exposure is refused — `mprotect_fixup`
charges the pages that turn writable and answers -ENOMEM when
`security_vm_enough_memory_mm` refuses…
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_expose_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 0) = true := by decide

/-- …with a page left it is not…
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_expose_within_budget_is_not_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 4096) = false := by decide

/-- …and exposing an already-rw page charges nothing, even on a spent
budget: `mprotect_fixup` charges only when the old flags lacked
`VM_WRITE`.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_already_rw_is_not_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) spent_budget_model = false := by decide

/-! ### Every listed number has an arm that fires

`Run.alloc_mark_sysnos_dispatched` states the four arms as written, so a
number the list gains with no arm beside it falls to the dispatcher's
`false` default, and `Run.lean` still builds.  The pin below asks, for
each number on the list, for a request the dispatcher refuses, which the
default does not supply.  `mremap`'s request is the one
this file had no fixture for. -/

/-- The `mremap` request, with a4 and a5 zero. -/
def mremap_in (addr old_len new_len flags : word) : SyscallInput :=
  SyscallInput.mkInput 216 [addr, old_len, new_len, flags, 0, 0] (fun _ => none) (fun _ => none)

/-- Growing `tight_model`'s one live page to three, MREMAP_MAYMOVE set, is
budget-refused through the dispatcher: the two-page budget does not
hold the result, in place or moved…
model: the model's budget device read through the dispatcher's `mremap` arm; the mark is pinned against the kernel as `budget_mark_fires_over_budget` in `Checks/Cases/Mm/Mremap.lean`. -/
theorem mremap_three_pages_is_budget_refused :
    alloc_budget_refused_b (mremap_in 65536 4096 12288 1) tight_model = true := by decide

/-- …while growing it to two pages, which the budget holds, is not.
model: the model's budget device read through the dispatcher; the same request is `budget_mark_silent_within_budget`'s first conjunct in `Checks/Cases/Mm/Mremap.lean`. -/
theorem mremap_two_pages_is_not_budget_refused :
    alloc_budget_refused_b (mremap_in 65536 4096 8192 1) tight_model = false := by decide

/-- Each number on `Run.alloc_mark_sysnos` has a request the dispatcher
refuses, so each has an arm in it: a number on the list with no arm
falls to the dispatcher's `false` default, and this pin stops building
until the number's arm lands and a refused request for it is added
here.  The requests are the fixtures above, one per arm.
model: `Run.alloc_mark_sysnos` read against `Run.alloc_budget_refused_b`, one refused request per listed number. -/
theorem each_listed_number_reaches_a_refusing_mark :
    ∀ no ∈ alloc_mark_sysnos,
      ∃ i m, bv_unsigned i.in_sysno = no ∧ alloc_budget_refused_b i m = true := by
  intro no hno
  simp only [alloc_mark_sysnos, List.mem_cons, List.not_mem_nil, or_false] at hno
  rcases hno with rfl | rfl | rfl | rfl
  · exact ⟨brk_in 73728, m_tight_brk, by decide, brk_two_pages_is_budget_refused⟩
  · exact ⟨mremap_in 65536 4096 12288 1, tight_model, by decide,
      mremap_three_pages_is_budget_refused⟩
  · exact ⟨mmap_in 8192, tight_model, by decide, mmap_two_pages_is_budget_refused⟩
  · exact ⟨mprotect_in 65536 4096 3, fixed_rw_model 0, by decide,
      mprotect_expose_on_spent_budget_is_budget_refused⟩

/-! ### The mark at a configuration

A machine stopped at an `ecall` with the six arguments in a0..a5, as
`RiscvSemantics.step` leaves it, and `sys_input` reading them back into
the `SyscallInput` the dispatcher sees.  Where the fixture holds no
`MAP_NORESERVE` page the two first-touch clauses are false
(`Run.budget_refused_at_no_lazy_syscall`), so what the mark says at the
ecall is the grant clause: `true` on the spent budget, `false` within
it. -/

/-- A machine stopped at an `ecall`: syscall `x8` pending, `a0..a5` set,
every other register zero, no memory. -/
def svc_ms (x8 a0 a1 a2 a3 a4 a5 : word) : machine_state :=
  { ms_regs := bvmap_set 10 a0 (bvmap_set 11 a1 (bvmap_set 12 a2 (bvmap_set 13 a3
                 (bvmap_set 14 a4 (bvmap_set 15 a5 bvmap_empty))))),
    ms_fregs := bvmap_empty, ms_pc_val := Z_to_bv 64 0x100, ms_svc_pending := some x8,
    ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := fun _ => none, ms_rom := fun _ => none }

/-- `sys_input` hands the dispatcher the six a-registers, in order.
model: the register reading of `Run.sys_input` at `svc_ms`, a rewrite for the pins below. -/
theorem sys_input_svc_ms (segs : List Segment) (x8 a0 a1 a2 a3 a4 a5 : word) :
    sys_input segs (svc_ms x8 a0 a1 a2 a3 a4 a5) x8
      = SyscallInput.mkInput x8 [a0, a1, a2, a3, a4, a5]
          (ms_read_byte (svc_ms x8 a0 a1 a2 a3 a4 a5))
          (ms_writable_byte segs (svc_ms x8 a0 a1 a2 a3 a4 a5)) := by
  simp +decide only [sys_input, syscall_args, ms_gpr, svc_ms, reg_get, bvmap_get_set, ↓reduceIte]

/-- THE PIN: at the `mmap(0, 4096, rw, anon)` ecall on the spent budget,
the configuration is budget-refused — by the grant clause, in zero steps.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_ecall_on_spent_budget_is_budget_refused :
    budget_refused_at [] (config.mkCfg (svc_ms 222 0 4096 3 34 mmap_fd_none 0) spent_budget_model) :=
  ⟨rfl, Or.inr ⟨222, rfl, Or.inl (by
    show alloc_budget_refused_b (sys_input [] (svc_ms 222 0 4096 3 34 mmap_fd_none 0) 222)
           spent_budget_model = true
    rw [sys_input_svc_ms]
    decide)⟩⟩

/-- …so the run from that configuration reaches a budget-refused one.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_ecall_on_spent_budget_reaches_budget_refused :
    reaches_budget_refused []
      (config.mkCfg (svc_ms 222 0 4096 3 34 mmap_fd_none 0) spent_budget_model) :=
  reaches_budget_refused_intro [] _ mmap_ecall_on_spent_budget_is_budget_refused

/-- Within budget the same ecall is NOT budget-refused: no outcome of the
call leaves a lazy page (the request is not `MAP_NORESERVE`), so the mark
is the grant clause alone, and that is silent with a page left.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_ecall_within_budget_is_not_budget_refused :
    ¬ budget_refused_at [] (config.mkCfg (svc_ms 222 0 4096 3 34 mmap_fd_none 0) tight_model) := by
  rw [budget_refused_at_no_lazy_syscall [] (svc_ms 222 0 4096 3 34 mmap_fd_none 0) tight_model 222
        rfl rfl ?lazy]
  · rw [sys_input_svc_ms]
    decide
  case lazy =>
    intro eff model' evs hspec
    rw [sys_input_svc_ms] at hspec
    sys_norm at hspec
    -- the errno outcome names `tight_model` outright; the grant arrives as
    -- two cases, because the normal form distributes the disjointness
    -- disjunction (`Cases.Mm.Mmap.region_free_one`) over the existential,
    -- and both name the ledger `sys_norm` read off `with_mmap_backing` (no
    -- `MAP_NORESERVE` in 34, so no lazy entry) over `tight_model`; either
    -- way the lazy ledger is the empty one `fixture` gives
    rcases hspec with ⟨-, rfl, -⟩ | ⟨a, -, rfl, -⟩ | ⟨a, -, rfl, -⟩
    all_goals rfl

/-- At an INSTRUCTION the spent budget is not a refusal while no
`MAP_NORESERVE` page is there to charge: the first-touch clause needs a
lazy page, and the same machine with nothing pending is not refused.
model: `Run.budget_refused_at_no_lazy_instr` at the spent-budget fixture, which holds no lazy page. -/
theorem instr_on_spent_budget_without_lazy_is_not_budget_refused :
    ¬ budget_refused_at []
        (config.mkCfg { svc_ms 222 0 4096 3 34 mmap_fd_none 0 with ms_svc_pending := none }
           spent_budget_model) :=
  budget_refused_at_no_lazy_instr [] _ _ rfl rfl

/-- No run is budget-refused at its entry: `execve` hands the process no
`MAP_NORESERVE` page and no pending syscall, so a refusal takes at least
one step.  Stated for every image, entry, budget and input.
model: `Run.budget_refused_at_no_lazy_instr` at `Run.init_config`, whose model `State.init_model` builds with an empty lazy ledger. -/
theorem entry_is_not_budget_refused (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ budget_refused_at img.img_segments
        (init_config img.img_segments img.img_init_pc img.img_phdrs
           en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) :=
  budget_refused_at_no_lazy_instr _ _ _ rfl rfl


/-! ## The forced-only filter on `brk`

`brk` is the one arm that refuses by VALUE: its injected failure is the
old break, not an errno, so `Run.refusal_b` reads it through
`Run.brk_refusal_b` rather than through a list, and
`Checks/SpuriousCfg.lean`, which pins the filter on `getcwd`, `setsid` and
`mmap` as Rocq's `Checks/SpuriousCfg.v` does, has no `brk` case.  The pins
here fire the filter on the budget fixtures above (`m_tight_brk`: a break
at 65536 under a one-page budget), pin three requests the state answers
with the old break and `Run.brk_refusal_b` does not count as refusals, and
pin one place where the filter removes an answer Linux v6.18.46 is forced
to give (`brk_shrink_over_nothing_mapped_is_filtered`).  The exactness
paragraph of `Run.lean`'s spurious-failure section names the others it
knows of. -/

/-- Within budget the old break is a SPURIOUS refusal: the one-page grow
`brk_grow_within_budget_grants` admits beside it is not a refusal, so
under `forced_only_cfg` the filter removes the old break and leaves the
grow.  Linux answers the old break there only when a `goto out` of
`SYSCALL_DEFINE1(brk)` (mm/mmap.c, Linux v6.18.46) fires for a reason this
state does not decide, such as an rlimit or the overcommit check in
`do_brk_flags` (mm/vma.c): the environment failure the forced-only reading
assumes away.
model: the filter's three conjuncts at `m_tight_brk`; what Linux answers there is `brk_grow_within_budget_grants`'s claim, which its probe carries -/
theorem brk_old_break_is_spurious_within_budget :
    spurious_refusal_cfg forced_only_cfg (brk_in 69632) m_tight_brk (mkEffect 65536 [] []) :=
  ⟨by decide, by decide, _, _, _,
   (dispatch_arm spec_table (brk_in 69632) m_tight_brk _ brk_arm rfl).2
     ((brk_grow_within_budget_grants _ _).2 (Or.inl rfl)),
   by decide⟩

/-- …and beyond it the old break is FORCED and kept: the two-page grow has
no grant (`brk_grow_beyond_budget_returns_break`), so no answer that is
not a refusal stands beside the old break and the filter removes nothing.
model: the filter's third conjunct fails at `m_tight_brk` for 73728; the answer itself is `brk_grow_beyond_budget_returns_break`'s claim -/
theorem brk_old_break_kept_beyond_budget :
    ¬ spurious_refusal_cfg forced_only_cfg (brk_in 73728) m_tight_brk (mkEffect 65536 [] []) := by
  rintro ⟨-, -, eff', m', evs', hspec, hnr⟩
  have h := (brk_grow_beyond_budget_returns_break _ _).1
    ((dispatch_arm spec_table (brk_in 73728) m_tight_brk _ brk_arm rfl).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-- Three requests the STATE answers with the old break are not refusals,
so the filter leaves that answer in place
(`Run.spurious_refusal_not_refusal`): the query `brk(0)`…
model: `brk_refusal_b`'s first exclusion, and its second too, since 0 is below `min_brk` here; `brk_r_ok` admits the old break alone on a query -/
theorem brk_query_is_not_a_refusal : refusal_b (brk_in 0) m_tight_brk 65536 = false := by
  decide

/-- …a request below `min_brk`, which `SYSCALL_DEFINE1(brk)` answers with
the old break (`if (brk < min_brk) goto out;`, mm/mmap.c, Linux
v6.18.46)…
model: `brk_refusal_b`'s second exclusion; `brk_r_ok` admits the old break alone below `min_brk` -/
theorem brk_below_min_brk_is_not_a_refusal : refusal_b (brk_in 65535) m_tight_brk 65536 = false := by
  decide

/-- …and a request for the break the process already has.
model: `brk_refusal_b`'s third exclusion; the old break is the request itself there -/
theorem brk_at_the_break_is_not_a_refusal : refusal_b (brk_in 65536) m_tight_brk 65536 = false := by
  decide

/-- A SHRINK over the heap the break granted is filtered correctly: Linux
finds the heap's VMA in `[newbrk, oldbrk)`, unmaps it and answers the
request (`SYSCALL_DEFINE1(brk)`, mm/mmap.c, Linux v6.18.46).  It answers
the old break there only on a failure the model does not track, such as
`check_data_rlimit` refusing or `do_vmi_align_munmap` failing, each a
`goto out` of the same function, so under `forced_only_cfg` the old break
is spurious and removed.
model: the filter's three conjuncts at `m_grown`, the break at 131072 over the heap `[65536, 131072)` -/
theorem brk_shrink_over_the_heap_old_break_is_spurious :
    spurious_refusal_cfg forced_only_cfg (brk_in 65536) m_grown (mkEffect 131072 [] []) :=
  ⟨by decide, by decide, _, _, _,
   (dispatch_arm spec_table (brk_in 65536) m_grown _ brk_arm rfl).2
     (check_brk_sound_ok 65536 (brk_in 65536) _ _ _ _
       (rfl : check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(65536, 65536)] [] [])
                m_grown = CheckOk (with_brk_next m_grown 65536 65536) [])),
   by decide⟩

/-- A break at 69632 over NOTHING mapped: the heap grant `[65536, 69632)`
is gone and the break is where it was, as a `munmap` of the heap leaves
it. -/
def m_heap_unmapped : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 69632 demo_limit 0 demo_sp)

/-- THE KNOWN DEFECT, inherited from `Run.v`: here the filter removes the
answer Linux v6.18.46 is forced to give.  To shrink to 65536 over nothing
mapped, `SYSCALL_DEFINE1(brk)` (mm/mmap.c, Linux v6.18.46) finds no VMA in
`[newbrk, oldbrk)` and takes `if (!brkvma || brkvma->vm_start >= oldbrk)
goto out;`, so it answers the OLD break, 69632.  Linux v4.17, v5.15 and
v6.0 answer the request there, and so does QEMU 11.1.1's user-mode
`do_brk` (the exactness paragraph of `Run.lean`'s spurious-failure section
cites both), so `Mmap.brk_r_ok`'s shrink branch rightly admits the
request too.  But `Run.brk_refusal_b` counts the old break as a refusal
beside it, so under `forced_only_cfg` the old break is filtered out and
only the request is left.  `may_fail_cfg` keeps both answers and stays
sound.  This pin stops building when `brk_refusal_b` stops counting the
old break here, which is the repair, and then flips to its `¬` form, as
`brk_old_break_kept_beyond_budget` is stated; it also stops building if
`brk_r_ok` stops admitting the request, which would take the other
implementations' answer out of `run`.
model: the filter's three conjuncts at `m_heap_unmapped`, computed; the kernel line above is what makes them the wrong answer -/
theorem brk_shrink_over_nothing_mapped_is_filtered :
    spurious_refusal_cfg forced_only_cfg (brk_in 65536) m_heap_unmapped (mkEffect 69632 [] []) :=
  ⟨by decide, by decide, _, _, _,
   (dispatch_arm spec_table (brk_in 65536) m_heap_unmapped _ brk_arm rfl).2
     (check_brk_sound_ok 65536 (brk_in 65536) _ _ _ _
       (rfl : check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
                m_heap_unmapped = CheckOk (with_brk_next m_heap_unmapped 65536 65536) [])),
   by decide⟩

/-! ## The filter on `dup`, at the soft RLIMIT_NOFILE

The exactness paragraph of `Run.lean`'s spurious-failure section names the
descriptor allocators as one kind of place where the filter removes an
answer Linux is forced to give.  `Checks/Cases/Fs/File.lean` pins the
state, `dup_model_nofile4` (descriptors 0 to 4 held under a soft
RLIMIT_NOFILE of 4), and what `dup(2)` is admitted there: Linux's -EMFILE,
an -ENOMEM, and descriptor 5 beside them.  The pins here fire the filter
on that state. -/

/-- The `dup` request, with a1 to a5 zero. -/
def dup_in (oldfd : word) : SyscallInput :=
  SyscallInput.mkInput 23 [oldfd, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- A SECOND KNOWN DEFECT, inherited from `Run.v`, of the kind
`brk_shrink_over_nothing_mapped_is_filtered` is: here the filter removes
the answer Linux v6.18.46 is forced to give.  `SYSCALL_DEFINE1(dup)`
(fs/file.c:1457-1470, Linux v6.18.46) takes a slot through
`get_unused_fd_flags` (:620-623), which passes the soft RLIMIT_NOFILE to
`__get_unused_fd_flags` (:615-618) as the `end` of `alloc_fd`
(:570-613).  With descriptors 0 to 4 held and a limit of 4, the lowest
free slot is 5, and `alloc_fd` answers -EMFILE at its `fd >= end` test
(:591-593), before anything else can fail.  `Fs.File.lowest_fd` reads no
limit, so `dup_spec` admits descriptor 5 beside the -EMFILE
(`dup_above_the_soft_limit_still_admits_the_slot`), and under
`forced_only_cfg`, whose fd switch is off, the -EMFILE is filtered out.
`may_fail_cfg` keeps it (`dup_emfile_at_the_soft_limit_kept_under_may_fail`
below).  This pin stops building when `lowest_fd` reads the limit, the fix
bugs/fd-allocation-ignores-rlimit-nofile.md names, and then flips to its
`¬` form, as `brk_old_break_kept_beyond_budget` is stated.
model: the filter's three conjuncts at `dup_model_nofile4`, computed; the kernel lines above are what make them the wrong answer -/
theorem dup_emfile_at_the_soft_limit_is_filtered :
    spurious_refusal_cfg forced_only_cfg (dup_in 2) dup_model_nofile4
      (mkEffect (errno_ret EMFILE) [] []) :=
  ⟨by decide, by decide, _, _, _,
   (dispatch_arm spec_table (dup_in 2) dup_model_nofile4 _ dup_arm rfl).2
     ((dup_above_the_soft_limit_still_admits_the_slot (dup_in 2) _).2 (Or.inr rfl)),
   by decide⟩

/-- …and `may_fail_cfg` keeps the -EMFILE, as it keeps every answer
(`Run.spurious_refusal_may_fail`), so `run_scfg` at `may_fail_cfg`, which
agrees with `run` (`Run.run_scfg_may_fail`), stays sound here.
model: the filter's first conjunct at `may_fail_cfg`, which turns no family off -/
theorem dup_emfile_at_the_soft_limit_kept_under_may_fail :
    ¬ spurious_refusal_cfg may_fail_cfg (dup_in 2) dup_model_nofile4
      (mkEffect (errno_ret EMFILE) [] []) := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-! ## The table's columns, and the switches that read them

`Run.injected_table`'s columns decide which switch filters which arm and
which answers count as refusals, and a configuration is read through
`Run.family_may_fail`.  `Checks/SpuriousCfg.lean` fires the filter on
three arms, `getcwd`, `setsid` and `mmap`, under `forced_only_cfg`,
`may_fail_cfg` and `alloc_only_cfg false`.  Its pins therefore stand when
another entry moves among the fs, fd, net, cred and intr families or
carries another list, when two of those five switches are read crosswise,
and when `Run.alloc_only_cfg false` turns its fd, net, cred or intr switch
off.  The pins here state the columns, `family_may_fail` and
`alloc_only_cfg` whole. -/

/-- The table, column by column: number, family and errno list, in
`Run.v`'s order.  A list is stated by the name of the arm's own list, so
it is compared by value and moves with its arm.
model: `Run.injected_table` read back whole -/
theorem injected_table_columns :
    injected_table.map (fun a => (a.ia_no, a.ia_family, a.ia_errnos)) =
      [ (17, FamFs, getcwd_errnos), (23, FamFd, dup_errnos),
        (35, FamFs, unlinkat_errnos), (48, FamFs, faccessat_errnos),
        (56, FamFs, openat_errnos), (59, FamFd, pipe2_errnos),
        (101, FamIntr, [EINTR]),
        (144, FamCred, setid_errnos true), (146, FamCred, setid_errnos true),
        (147, FamCred, setid_errnos true), (149, FamCred, setid_errnos true),
        (157, FamCred, [EPERM]),
        (198, FamFd, socket_errnos),
        (199, FamFd, socketpair_reserve_errnos ++ socketpair_create_errnos),
        (200, FamNet, bind_errnos), (201, FamNet, listen_errnos),
        (202, FamFd, accept_errnos),
        (214, FamAlloc, []), (216, FamAlloc, mremap_errnos),
        (220, FamFd, clone_errnos),
        (222, FamAlloc, mmap_errnos), (226, FamAlloc, mprotect_errnos),
        (242, FamFd, accept_errnos), (278, FamIntr, getrandom_errnos),
        (435, FamFd, clone_errnos) ] := rfl

/-- Each family reads its own switch, at every configuration.
model: `Run.family_may_fail` read back at each family -/
theorem family_may_fail_reads_its_own_switch (cfg : SpuriousCfg) :
    family_may_fail cfg FamAlloc = cfg.sc_alloc
    ∧ family_may_fail cfg FamFs = cfg.sc_fs
    ∧ family_may_fail cfg FamFd = cfg.sc_fd
    ∧ family_may_fail cfg FamNet = cfg.sc_net
    ∧ family_may_fail cfg FamCred = cfg.sc_cred
    ∧ family_may_fail cfg FamIntr = cfg.sc_intr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `alloc_only_cfg b` sets the alloc field to `b` and the other five to
`true`, the may-fail reading.
model: `Run.alloc_only_cfg` read back whole -/
theorem alloc_only_cfg_sets_the_alloc_switch_alone (b : Bool) :
    alloc_only_cfg b = SpuriousCfg.mkSpuriousCfg b true true true true true := rfl

/-! ## Two injecting arms with no table entry

`getdents64` (61) and `faccessat2` (439) draw an errno with
`Syscall.errno_from` beside the answer the state determines, as the arms
whose `Run.injected_table` entries name a spec's errno list do, but
neither tree's table has an entry for them. -/

/-- Neither number has an entry, so `Run.refusal_b` counts none of their
answers as a refusal and a forced-only statement still admits their
injected errnos.  That is sound, since an answer that is not a refusal is
removed nowhere (`Run.spurious_refusal_not_refusal`), but it is filtering
the family's switch promises.  When an
entry lands, in `Run.v` and here, this pin fails on that number.
model: the Lean `injected_table` read through `Run.injected_arm` -/
theorem injected_table_omits_getdents64_and_faccessat2 :
    injected_arm 61 = none ∧ injected_arm 439 = none := ⟨rfl, rfl⟩

/-! ## `refusal_decided` holds everywhere, classically

`Run.sstep_cfg_progress` takes `Run.refusal_decided` as a premise because
the Rocq tree can prove it only case by case: it uses no classical axiom,
and nothing in either tree DECIDES it in general (for `mmap` it is the
placement question; `Checks/SpuriousCfg.v`'s `getcwd_decided` is one case,
proved by exhibiting the answer).  Lean's logic has excluded middle
(`Classical.em`, whose axiom the policy audit allows), so here the premise
holds at every argument (`refusal_decided_classical`) and progress needs
none (`sstep_cfg_progress_classical`).  What stays open is deciding it by
computation, which the conformance harness would need before it could
certify a forced-only reading. -/

/-- The premise holds at every configuration, input and model.
model: excluded middle over the premise's own disjunction; no kernel claim -/
theorem refusal_decided_classical (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) :
    refusal_decided cfg i m := by
  intro _
  rcases Classical.em (∃ eff' m' evs',
      syscall_spec i m (Ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false) with h | h
  · exact Or.inl h
  · refine Or.inr (fun eff' m' evs' hs => ?_)
    cases hr : refusal_b i m eff'.eff_ret
    · exact absurd ⟨eff', m', evs', hs, hr⟩ h
    · rfl

/-- …so the filtered run takes a step wherever the unfiltered one does,
with no premise.
model: `Run.sstep_cfg_progress` with its premise discharged by `refusal_decided_classical` -/
theorem sstep_cfg_progress_classical (segs : List Segment) (cfg : SpuriousCfg)
    (ms : machine_state) (model : Model) (evs : List event) (st : step_to) :
    sstep segs (config.mkCfg ms model) evs st →
    ∃ evs' st', sstep_cfg segs cfg (config.mkCfg ms model) evs' st' :=
  sstep_cfg_progress segs cfg ms model evs st (fun _ _ => refusal_decided_classical _ _ _)


/-! ## The declared AT_HWCAP pair, and the abort-enabled input stance

Pins for the default stance's two declarations `Run.valid_input_hwcap_rv64gc`
and `_rv64gcv`, for `Run.valid_input_abort` and `Run.valid_input_either`,
and for the abort stance's two declarations
`Run.valid_input_abort_hwcap_rv64gc` and `_rv64gcv`.  The pins that restate
the Examples of parts (i), (ii), (iv) and (v) of
`theories/LinuxProcessSem/Checks/Cases/Hwcap.v` keep their names.  Parts
(iii) and (vi) are restated under their Rocq names in
`Checks/Cases/EquivalenceDefinition/Equivalence.lean`: part (iii) uses
`auxv_hwcap_is_exactly_the_launch_word` to pin the declared auxv words,
and part (vi) pins the budget cells' split lemmas.  All six parts are
restated across these two files, but `Hwcap.v` has no Lean mirror at its
mirror path, so `tools/lean_port_graph.py`'s DECLINED still declines `Hwcap.v`
as a file and points to those restatements.  The pins here stand beside
the pins on `Run.lean`'s own
predicates, and are labelled `model:` rather than `rocq-twin:`, which reads
a mirror at this file's path.  What they pin is the input DOMAIN a
statement quantifies over: both declarations are the task's and not the
kernel's, and the fixtures are the Rocq ones, the demo launch with the word
and the declaration varied, so every refusal below bites on the one field
it names.  Part (iv) is the exception: it pins the ISA model (decoder,
`csr_slice`, semantics) on the probe and the words beside it. -/

/-- One clause the stances share, at the demo launch: unfold the clause's
own predicate and evaluate it.  The `Int` comparisons against literals up to
2^32 unfold one `Meta.whnf` frame per step (the "Evaluation depth" section
of `Checks/Cases/Checks/Sys/Mm/Mremap.lean` says why), so the depth is
raised for the evaluation alone. -/
local macro "demo_launch_clause" : tactic =>
  `(tactic| (simp only [valid_argv, valid_envp, valid_fs, valid_creds, valid_id,
      valid_nofile, valid_sigmask, valid_hwcap]
             set_option maxRecDepth 32768 in decide))

/-- A declared predicate at the demo launch, split along its conjunction
spine however many clauses it has, then each clause closed by its shape: the
shared clauses by `demo_launch_clause`, the declared fields by `rfl`, the
random device's by `default_urandom_infinite`.  No anonymous constructor of
today's arity, for the rule above `Run.valid_input_va_size`.  The spine is
split under reducible transparency, so no clause's own predicate is opened
into more conjuncts, and before any clause is closed, so `rfl` never meets a
conjunction: it reads `A ∧ B` as a relation between the conjuncts and
compares them by defeq, which on the suffix from `valid_creds` runs
`valid_id`'s bound against `valid_nofile`'s into the recursion limit, an
error `first` does not catch.  A clause of a shape none of the three closes
fails by name until a shape is added for it: the trailing `fail` keeps every
real shape out of the last position, whose error `first` reports as its own,
so a refused clause does not read as `default_urandom_infinite`'s type
mismatch.  So a wrong declared word is refused at its own clause:
`demo_launch_clause`'s `simp only` cannot move a bare field equation, and
`rfl` evaluates it. -/
local macro "declared_launch" : tactic =>
  `(tactic| (repeat' with_reducible apply And.intro
             all_goals first
               | demo_launch_clause
               | rfl
               | exact default_urandom_infinite
               | fail "declared_launch: a clause matched none of the shapes"))

/-- `Checks/Cases/Hwcap.v`'s `hwcap_input`: the demo launch with its AT_HWCAP
word as a parameter, under the default stance. -/
def hwcap_input (h : word) : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) h false .Sv48

/-- The word the fixtures of this tree launch with — `Cases/Prelude`'s
`demo_hwcap`, not `hwcap_input`'s parameter — is the mask WITHOUT V.
Documentary: it holds by definition.
model: `Checks.Cases.Prelude.demo_hwcap`'s definition, the tree's fixture word. -/
theorem the_trees_launch_word_is_the_v_less_mask : demo_hwcap = hwcap_rv64gc := rfl

/-- Part (i): each default-stance declaration holds of its own word, by the
shared clauses and the one capability clause, which closes by `rfl` rather
than by picking a side of a disjunction — the whole difference between a
declaration and the default.
model: the default-stance declared predicate at the demo launch; the declaration is the task's, not the kernel's. -/
theorem hwcap_input_gc_declared :
    valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc) := by
  unfold valid_input_hwcap_rv64gc; declared_launch

/-- model: the default-stance declared predicate at the demo launch; the declaration is the task's, not the kernel's. -/
theorem hwcap_input_gcv_declared :
    valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv) := by
  unfold valid_input_hwcap_rv64gcv; declared_launch

/-- Both words are admitted by the DEFAULT, which is what makes a statement
issued without a declaration a statement about both harts.  Derived from
the declared predicates, so the narrowing lemmas run on a concrete input;
it is also the control for every refusal below, which would otherwise pass
on a fixture nothing accepts.
model: `Run.valid_input_of_valid_input_hwcap_rv64gc` and its twin at the two fixtures. -/
theorem both_words_are_valid_under_the_default :
    valid_input (hwcap_input hwcap_rv64gc) ∧ valid_input (hwcap_input hwcap_rv64gcv) :=
  ⟨valid_input_of_valid_input_hwcap_rv64gc _ hwcap_input_gc_declared,
   valid_input_of_valid_input_hwcap_rv64gcv _ hwcap_input_gcv_declared⟩

/-- …and the split lemma sends each fixture to its OWN declaration: the
exhaustiveness claim fired rather than stated.  A conjunction, not a
disjunction per fixture: a disjunction would say only that SOME declaration
catches each fixture, and a split lemma that always answered the left arm
would satisfy it.  The conclusion here names the arm, and the proof runs
through `Run.valid_input_hwcap_splits` rather than around it; the wrong arm
is closed by the word, on the spot.
model: `Run.valid_input_hwcap_splits` at the two fixtures. -/
theorem the_default_splits_each_fixture_to_its_own :
    valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc)
    ∧ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv) := by
  refine ⟨?_, ?_⟩
  · rcases valid_input_hwcap_splits _
      (valid_input_of_valid_input_hwcap_rv64gc _ hwcap_input_gc_declared) with h | h
    · exact h
    · exact absurd (valid_input_hwcap_rv64gcv_word _ h) (by decide)
  · rcases valid_input_hwcap_splits _
      (valid_input_of_valid_input_hwcap_rv64gcv _ hwcap_input_gcv_declared) with h | h
    · exact absurd (valid_input_hwcap_rv64gc_word _ h) (by decide)
    · exact h

/-- Part (ii): a wrong declaration is refused, at the word.  The control is
`both_words_are_valid_under_the_default`: the same fixture satisfies the
default under both words, so what these refuse is the declaration.
model: the declared word read back by `Run.valid_input_hwcap_rv64gc_word` and its twin. -/
theorem each_declaration_refuses_the_other_word :
    ¬ valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gcv)
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gc) :=
  ⟨fun h => absurd (valid_input_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gcv_word _ h) (by decide)⟩

/-- …and both refuse the words outside the pair, which keeps a declaration
a declaration rather than a free parameter: the zero an absent AT_HWCAP
entry delivers, the A-less mask 0x112C, and 0x40112D, which sets a letter
`riscv_fill_hwcap` (arch/riscv/kernel/cpufeature.c, Linux v6.18.46) never
assigns.  The default refuses the same three words
(`the_default_refuses_a_word_outside_the_pair` below, as `Cases/Prelude.v`
pins them in Rocq), so on these words the declarations refuse where the
default does.
model: the declared word read back by `Run.valid_input_hwcap_rv64gc_word` and its twin. -/
theorem both_declarations_refuse_a_word_outside_the_pair :
    ¬ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0x40112D))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0x40112D)) :=
  ⟨fun h => absurd (valid_input_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gcv_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gcv_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_hwcap_rv64gcv_word _ h) (by decide)⟩

/-- THE DEFAULT refuses them too, on the same fixture: the control that the
refusals above are not an artifact of the declarations being narrow.
model: the capability clause read back by `Run.valid_input_hwcap`. -/
theorem the_default_refuses_a_word_outside_the_pair :
    ¬ valid_input (hwcap_input (Z_to_bv 64 0))
    ∧ ¬ valid_input (hwcap_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input (hwcap_input (Z_to_bv 64 0x40112D)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rcases valid_input_hwcap _ h with hw | hw <;>
    exact absurd hw (by decide)

/-! Part (iv), the reason the declaration exists: the probe is unmodeled.

A runtime that wants to know whether it has a vector unit reads `vlenb`, a
V-extension CSR: `csrr t0, vlenb`, CSRRS with rd = t0, rs1 = x0 and csr =
0xC22, the word 0xC22022F3.  It is not the decoder that declines it: the
word is an ordinary Zicsr access and `decode_any` decodes it, which is worth
pinning because the obvious guess — that a V-extension probe is undecodable
the way a vector instruction is — sends a reader to the wrong place.  The
decline is one level further in: `Sem.csr_slice` resolves only the fcsr
aliases, so `Sem.exec_csr` answers `EIllegal`, which
`RiscvSemantics.interp_eff_accesses` reports as `MachineUnmodeled`, the ISA
semantics declining to say rather than the architecture trapping.

That is why the declaration is the task's rather than the model's.  Under
the permissive default a statement about a binary carrying this probe ranges
over `hwcap_rv64gcv` as well, the probe is taken, and the statement is false
as issued even though the binary never vectorises anything; under
`Run.valid_input_hwcap_rv64gc` the published word has no V bit and the probe
is never reached.  Nothing here claims the hart lacks a vector unit, only
that the kernel published a word without the bit. -/

/-- The probe decodes, as CSRRS reading csr 0xC22 (3106) into t0.
model: the ported decoder's answer on the probe word, a fact about the model's ISA surface. -/
theorem the_vlenb_probe_decodes_as_an_ordinary_csr_read :
    decode_any (Z_to_bv 32 0xC22022F3) = some (.Csr .CSR_RS 5 0 3106, 4) := by
  decide

/-- …but the model resolves no `vlenb`.
model: `Sem.csr_slice`, which resolves only the fcsr aliases. -/
theorem the_model_resolves_no_vlenb_csr : csr_slice (Z_to_bv 12 0xC22) = none := by
  decide

/-- …so the probe leaves the modeled surface, whatever the segments and the
state.
model: the ISA semantics' answer on the probe word. -/
theorem the_vlenb_probe_leaves_the_modeled_surface : ∀ segs st,
    decode_exec_accesses segs st (Z_to_bv 32 0xC22022F3) = MachineUnmodeled := by
  intro segs st; rfl

/-- The vector work the probe would guard leaves by the other route: a
`vsetvli`, 0x0C0072D7, is a word the decoder does not decode at all.
Together the two routes are what the declaration rests on, that neither the
probe nor the work it guards is modeled, rather than one encoding or one
mechanism.
model: the ported decoder's answer on a `vsetvli` word. -/
theorem a_vector_word_is_not_decoded_at_all :
    decode_any (Z_to_bv 32 0x0C0072D7) = none := by
  decide

/-- model: the ISA semantics' answer on the `vsetvli` word. -/
theorem the_guarded_vector_word_leaves_the_modeled_surface : ∀ segs st,
    decode_exec_accesses segs st (Z_to_bv 32 0x0C0072D7) = MachineUnmodeled := by
  intro segs st; rfl

/-- The control: the model does not answer `MachineUnmodeled` to everything.
A scalar word beside them, `addi t0, zero, 0` (0x00000293), is modeled, so
the declines above are about the instruction and not the pin.
model: the ISA semantics' answer on an `addi` word. -/
theorem a_scalar_word_beside_them_is_modeled : ∀ segs st,
    decode_exec_accesses segs st (Z_to_bv 32 0x00000293) ≠ MachineUnmodeled := by
  intro segs st h; cases h

/-- Part (v): `Checks/Cases/Hwcap.v`'s `hwcap_abort_input`, the same launch
with the abort path declared, the only field that differs. -/
def hwcap_abort_input (h : word) : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) h true .Sv48

/-- Each abort-stance declaration holds of its own word at the fixture.
model: the abort-stance declared predicate at the demo launch; the declaration is the task's, not the kernel's. -/
theorem hwcap_abort_input_gc_declared :
    valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc) := by
  unfold valid_input_abort_hwcap_rv64gc; declared_launch

/-- model: the abort-stance declared predicate at the demo launch; the declaration is the task's, not the kernel's. -/
theorem hwcap_abort_input_gcv_declared :
    valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv) := by
  unfold valid_input_abort_hwcap_rv64gcv; declared_launch

/-- The abort-stance split lemma, fired: the abort default admits the two
words and no third, and each fixture lands in its own arm, so a task that
declares the stance and not the word is held to both readings of the hart.
model: `Run.valid_input_abort_hwcap_splits` at the two fixtures. -/
theorem the_abort_default_splits_each_fixture_to_its_own :
    valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
    ∧ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv) := by
  refine ⟨?_, ?_⟩
  · rcases valid_input_abort_hwcap_splits _
      (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ hwcap_abort_input_gc_declared)
      with h | h
    · exact h
    · exact absurd (valid_input_abort_hwcap_rv64gcv_word _ h) (by decide)
  · rcases valid_input_abort_hwcap_splits _
      (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _ hwcap_abort_input_gcv_declared)
      with h | h
    · exact absurd (valid_input_abort_hwcap_rv64gc_word _ h) (by decide)
    · exact h

/-- A wrong declaration is refused, at the word.
model: the declared word read back by `Run.valid_input_abort_hwcap_rv64gc_word` and its twin. -/
theorem each_abort_declaration_refuses_the_other_word :
    ¬ valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gcv)
    ∧ ¬ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gc) :=
  ⟨fun h => absurd (valid_input_abort_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gcv_word _ h) (by decide)⟩

/-- …and both refuse the three words outside the pair that
`both_declarations_refuse_a_word_outside_the_pair` refuses under the
default stance.
model: the declared word read back by `Run.valid_input_abort_hwcap_rv64gc_word` and its twin. -/
theorem both_abort_declarations_refuse_a_word_outside_the_pair :
    ¬ valid_input_abort_hwcap_rv64gc (hwcap_abort_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_abort_hwcap_rv64gc (hwcap_abort_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input_abort_hwcap_rv64gc (hwcap_abort_input (Z_to_bv 64 0x40112D))
    ∧ ¬ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input (Z_to_bv 64 0x40112D)) :=
  ⟨fun h => absurd (valid_input_abort_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gcv_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gcv_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gc_word _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gcv_word _ h) (by decide)⟩

/-- THE ABORT DEFAULT refuses them too, through its split lemma: the
control that the refusals above are not an artifact of the declarations
being narrow.
model: `Run.valid_input_abort_hwcap_splits` into the two declared words. -/
theorem the_abort_default_refuses_a_word_outside_the_pair :
    ¬ valid_input_abort (hwcap_abort_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_abort (hwcap_abort_input (Z_to_bv 64 0x112C))
    ∧ ¬ valid_input_abort (hwcap_abort_input (Z_to_bv 64 0x40112D)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rcases valid_input_abort_hwcap_splits _ h with h' | h'
  · exact absurd (valid_input_abort_hwcap_rv64gc_word _ h') (by decide)
  · exact absurd (valid_input_abort_hwcap_rv64gcv_word _ h') (by decide)
  · exact absurd (valid_input_abort_hwcap_rv64gc_word _ h') (by decide)
  · exact absurd (valid_input_abort_hwcap_rv64gcv_word _ h') (by decide)
  · exact absurd (valid_input_abort_hwcap_rv64gc_word _ h') (by decide)
  · exact absurd (valid_input_abort_hwcap_rv64gcv_word _ h') (by decide)

/-- THE AXES ARE INDEPENDENT: the declaration of the word does not carry the
declaration of the stance, in either direction.  Without it the declared
predicates could collapse onto each other and no pin would notice.
model: the stance read back by the two `_abort_terminal` lemmas of `Run.lean`. -/
theorem the_word_declaration_does_not_carry_the_stance :
    ¬ valid_input_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
    ∧ ¬ valid_input_abort_hwcap_rv64gc (hwcap_input hwcap_rv64gc) :=
  ⟨fun h => absurd (valid_input_hwcap_rv64gc_abort_terminal _ h) (by decide),
   fun h => absurd (valid_input_abort_hwcap_rv64gc_abort_terminal _ h) (by decide)⟩

/-- The two stances are disjoint on the field: the default stance refuses
the abort fixture, and the abort stance refuses the default one; the
controls are `both_words_are_valid_under_the_default` and
`hwcap_abort_input_gc_declared`.
model: the stance read back by `Run.valid_input_abort_terminal` and `Run.valid_input_abort_abort_terminal`. -/
theorem each_stance_refuses_the_other_fixture :
    ¬ valid_input (hwcap_abort_input hwcap_rv64gc)
    ∧ ¬ valid_input_abort (hwcap_input hwcap_rv64gc) :=
  ⟨fun h => absurd (valid_input_abort_terminal _ h) (by decide),
   fun h => absurd (valid_input_abort_abort_terminal _ h) (by decide)⟩

/-- The stance that pins neither admits both fixtures, which is what makes a
statement over it the conjunction of the two.
model: `Run.valid_input_either` reached from each stance at its own fixture. -/
theorem either_admits_both_fixtures :
    valid_input_either (hwcap_input hwcap_rv64gc)
    ∧ valid_input_either (hwcap_abort_input hwcap_rv64gc) :=
  ⟨valid_input_either_of_valid_input _ both_words_are_valid_under_the_default.1,
   valid_input_either_of_valid_input_abort _
     (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ hwcap_abort_input_gc_declared)⟩

/-- …and still refuses a word outside the pair under either declaration of
the stance: dropping the stance drops nothing else.
model: `Run.valid_input_either_splits` into the two stances' own hwcap splits. -/
theorem either_refuses_a_word_outside_the_pair :
    ¬ valid_input_either (hwcap_input (Z_to_bv 64 0))
    ∧ ¬ valid_input_either (hwcap_abort_input (Z_to_bv 64 0)) := by
  have refuse : ∀ inp : ProcInput, inp.in_hwcap = Z_to_bv 64 0 → ¬ valid_input_either inp := by
    intro inp hw h
    rcases valid_input_either_splits _ h with hd | ha
    · rcases valid_input_hwcap_splits _ hd with h' | h'
      · exact absurd ((valid_input_hwcap_rv64gc_word _ h').symm.trans hw) (by decide)
      · exact absurd ((valid_input_hwcap_rv64gcv_word _ h').symm.trans hw) (by decide)
    · rcases valid_input_abort_hwcap_splits _ ha with h' | h'
      · exact absurd ((valid_input_abort_hwcap_rv64gc_word _ h').symm.trans hw) (by decide)
      · exact absurd ((valid_input_abort_hwcap_rv64gcv_word _ h').symm.trans hw) (by decide)
  exact ⟨refuse _ rfl, refuse _ rfl⟩

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
