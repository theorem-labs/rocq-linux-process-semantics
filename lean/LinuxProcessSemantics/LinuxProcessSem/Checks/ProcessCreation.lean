import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.ProcessCreation — process creation, pinned

Mirrors `theories/LinuxProcessSem/Checks/ProcessCreation.v` at the header's
baseline, name for name where a statement can be made over the Lean table
as it stands, and says below where each remaining statement lives or what
it waits on.  Not part of the trusted specification: this file is QA on
the definitions, in the sense of the header of
`theories/LinuxProcessSem/Checks/Examples.v`.  The quantified statements
earn their place under the FIRST of the four reasons that header lists —
they range over models, arguments and memories, which no finite set of
traces can establish.  A conformance probe can show that ONE flag word
was declined, or that ONE forged zero was refused; only a `∀` can say
that every one is.  The concrete companions in the second half fix a
`pc_model` no probe can seed, which is that header's THIRD reason.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f).

## What this pins, and why it is not decoration

Three arguments in the Lean tree are load-bearing and are the reason this
file exists.  The first rests on two syscall NUMBERS being outside the
modeled surface, which is what the tripwires below pin; the second rests
on a fact about the ENVIRONMENT, and is listed so that nobody pins it here
by mistake; the third rests on a FLAG WORD and a signal number, and is
pinned beside its arm:

- `Sys/Uaccess.lean`'s header transcribes `__access_ok` and notes that
  riscv64's `access_ok` (arch/riscv/include/asm/uaccess.h, Linux v6.18.46)
  wraps its address in `untagged_addr`, which is the identity whenever
  the process's pointer-masking length is zero (and unconditionally on a
  hart without Supm, or a build without `CONFIG_RISCV_ISA_SUPM`, since
  `set_tagged_addr_ctrl` refuses there and the length stays zero).  That
  length is
  `mm->context.pmlen`, read by `__untagged_addr_remote` in the same
  header; every `execve` installs a fresh mm through `exec_mmap`
  (fs/exec.c, v6.18.46), and riscv64's `activate_mm`
  (arch/riscv/include/asm/mmu_context.h) writes the length to zero under
  `CONFIG_RISCV_ISA_SUPM` as it does so.  Afterwards it is written only by
  `set_tagged_addr_ctrl` (arch/riscv/kernel/process.c), which has TWO
  callers: `prctl` (kernel/sys.c, v6.18.46, the
  `PR_SET_TAGGED_ADDR_CTRL` case) and `PTRACE_SETREGSET` on the
  `NT_RISCV_TAGGED_ADDR_CTRL` regset through `tagged_addr_ctrl_set`
  (arch/riscv/kernel/ptrace.c, v6.18.46).  "Two" is a grep for the name
  over arch/riscv and kernel/ at that version, and a third caller
  falsifies this bullet rather than the pins.  Declining 117 rules out
  the ptrace route FROM INSIDE the model, and the prctl route is closed
  at the OPTION on both sides: Rocq's 167 has an arm answering
  `PR_CAPBSET_READ`, so its tripwire is `prctl_option_unmodeled`, and
  `prctl_tagged_addr_ctrl_declines` below is the concrete option-55
  companion, at an input the register reader does not read.  The NUMBER
  167 is deliberately NOT registered in this file: while it has no Lean
  arm the generated `Checks/Cases/SyscallTable.lean` holds it, and a
  number-level entry here collides with the prctl arm the moment that
  port lands — measured on a merge with it, both register readers fire
  and a `rfl` on `lookup_arm spec_table 167 = none` stops closing.
  Either way the traced process cannot enable masking on itself.
- `Sys/Kernel/Fork.lean`'s `set_tid_address_spec` accepts and ignores its
  `tidptr`, and NOT for any reason on this list.  The caller's pointer is
  written by `mm_release` (kernel/fork.c, v6.18.46) when the CALLER exits
  or execs, gated on `mm_users > 1`, so what rules it out is that this
  model has no second holder of an mm — a closed-world statement about the
  environment, not a flag test.  See that spec's header; do not re-derive
  it from `CLONE_CHILD_CLEARTID` below, which is a different writer into a
  same-named field.
- The Rocq block above `Kernel.Fork.SIGCHLD` in
  `theories/LinuxProcessSem/Sys/Kernel/Fork.v`, which the header of
  `Sys/Kernel/Fork.lean` points at rather than repeating, argues that the
  SIGCHLD the one accepted flag word requests comes to nothing.  Neither half of that
  argument is a statement about a declined number: 134 and 135 both have
  arms.  What carries it is `Sys/Kernel/Signal.lean`'s `sigaction_accepted`,
  which excludes SIGCHLD so an install for it fails closed at the SIGNAL,
  pinned in `Checks/Cases/Kernel/Signal.lean` as
  `rt_sigaction_sigchld_unmodeled`.  A changeable mask does not reopen it:
  unblocking a queued SIGCHLD hands it to `get_signal` (kernel/signal.c,
  v6.18.46), which re-reads the disposition and discards a `SIG_DFL`
  SIGCHLD through `sig_kernel_ignore` (include/linux/signal.h), so the
  blocked case funnels into the unblocked one.

Not everything in the neighbourhood is.  The `access_ok` argument ALSO
relies on there being no second process to be the tracer, which nothing
about 220 gives it: a tracer is an independently started process, and
that half is a closed-world assumption about the ENVIRONMENT, recorded in
bugs/access-okb-closed-world.md.  And it holds only on a build with
`CONFIG_MMU` and without `CONFIG_ALTERNATE_USER_ADDRESS_SPACE`, which no
syscall number can rule out; bugs/access-okb-early-return-unmodeled.md
records that.  What this file pins is the IN-MODEL half.

## How the tripwires are proved

Each number's decline is proved DIRECTLY against `syscall_spec`, through
`Sys.Dispatch.dispatch_unmodeled` and a `rfl` over the table, rather than
through `Specs.modeled_sysnos`: a change that gave the number an arm
without touching the list would leave a statement about the list
provable, and this one stops closing.  `tools/check_decline_registers.py`
reads the quantified statements as register L2 and the concrete
`pc_input` companions as register L3, and compares both against the Lean
table; a collision it reports is a soundness question, answered by moving
the check to the fact that still closes the window, never by deleting the
entry.  The concrete companions are the twins of Rocq's
`<syscall>_checker_unmodeled` examples, stated over `syscall_spec` because
the executable checker is not ported yet (ticket K3); when it lands they
are restated over it and these stay as the spec half.

## What is twinned elsewhere, and what waits

The clone statements of the Rocq file that need the resolution's internals
were ported with the arm, in `Checks/Cases/Kernel/Fork.lean`:
`clone_never_returns_zero`, `clone3_never_returns_zero` and
`clone_errno_ret_nonzero` under their own names, `clone_open_file_unmodeled`
as `clone_gate_closed_declines`, and `clone_resolve_declines_or_sets_children`
as the pair `clone_errno_leaves_the_model` / `clone_pid_records_the_child`
— those two at the accepted word, 17, and under a gate-open hypothesis,
where Rocq states one lemma over `clone_resolve` for any model.  This file
keeps the statements that sit ABOVE the arm: the sharing bits, that 220
and 435 reach `clone_spec` and `clone3_spec` and not some other spec that
refuses the same inputs, and `clone_success_sets_children`, their
composition through the dispatcher over both numbers at once.

`wait4` (260) is MODELED and, at a childless caller, never declined on
its one shape — with a child recorded it declines
(`Checks/Cases/Kernel/Exit.lean`'s
`wait4_with_child_is_unmodeled_for_every_model`).  Rocq states
that in the negative through the executable checker; `wait4_not_unmodeled`
and `wait4_answers_only_echild` below are the same statements proved
through the arm, and `Checks/Cases/Kernel/Exit.lean`'s
`wait4_childless_is_echild_for_every_model` is the model half the concrete
companions compose with.  `setsid` (157) is modeled on both sides — the
Lean arm is `Sys/Kernel/Sys.lean`'s `setsid_spec` — and its two lemmas are
twinned below under Rocq's names, the negative one over
`Checks/Cases/Kernel/Sys.lean`'s `setsid_never_declines` and the
characterization over `dispatch_arm` alone.  Its six `setsid_checker_*`
examples are NOT waited on: their content is already in
`Checks/Cases/Kernel/Sys.lean`, quantified over the model where Rocq fixes
one — `setsid_first_call_may_be_eperm`, `setsid_first_call_may_answer_one`
and `setsid_first_call_success_records` for the first call,
`setsid_zero_rejected`, `setsid_envelope_end_rejected` and
`setsid_eacces_rejected` for the forged answers,
`setsid_after_a_success_is_eperm`, `setsid_repeat_success_rejected` and
`setsid_bit_alone_rejects_success` for the second call — and they compose
with `setsid_is_setsid_spec` below.  What does wait on the checker (K3) is
`check_clone_success_sets_children` and `prctl_checker_capbset_read`.
`prctl`'s option-level statements are the prctl arm's to twin over
`prctl_spec` beside that arm; this file keeps only the concrete option-55
companion, `prctl_tagged_addr_ctrl_declines`, which needs no arm to state.

## `rt_sigprocmask` (135): the decision this ticket records

Register L1, `sig_mask_windows` in `Checks/Cases/Kernel/Signal.lean`, is
Rocq's list, ported with the arm.  It is live because the Lean
`rt_sigprocmask_spec` ANSWERS `oset` — `write_oset` copies out the mask the
model keeps — exactly as the Rocq spec does; the alternative the ticket
allowed, declining `oset` so that no argument rests on the mask being
Linux's, was not taken.  What that answer rests on: `rt_sigprocmask`
(kernel/signal.c, v6.18.46) snapshots `old_set = current->blocked` before
`sigprocmask` installs anything, so `oset` receives the mask Linux
carried into the call, and the model's copy equals it only while nothing
Linux would run between two calls writes `->blocked` behind the model's
back.  The syscall writers are L1; the writers that are NO syscall are
the premise of bugs/rt-sigprocmask-mask-answer-rests-on-no-signals.md,
which this file does not discharge.  That entry records delivery —
`signal_delivered` (kernel/signal.c, v6.18.46) — and the riscv
`rt_sigreturn` restoring the saved set; a third writer of the same kind,
`force_sig_info_to_task` in kernel/signal.c, which clears the blocked bit
of a signal the kernel forces on the task, is not written there yet and
belongs on the same list.  135 itself is not on any register here, for the same
reason it left the Rocq file: it has an arm, so a lemma saying it falls
through the dispatcher would be false.

## What holds this file, and what does not

`lake build` and the policy replay read it through the lakefile's glob;
`tools/check_decline_registers.py` sweeps every `.lean` under `lean/`, so
the L2 and L3 entries below are registered and collide when an arm lands;
`tools/check_kernel_citations.py`'s strict tier resolves the bracketed
names the prose pairs with a path; `tools/check_lean_pin_placement.py`'s
SHADOW rule reads every `.lean` under `LinuxProcessSem/`, this one
included, which is why `CLONE_VM` is read from the register below rather
than defined here.  The guards that hold `Checks/Cases/` do not read this
directory: pins, evidence lines, vacuity, placement's twin-and-home half,
cases-parity against `ProcessCreation.v`, mutation scoring and the
monotonic guard.  So a `kernel:` trailer here is checked by a reviewer
and not a tool, an `iff` here has no vacuity check, and the account of
what is and is not ported from the Rocq file is prose.  The statements
sit here rather than under `Checks/Cases/` because they range over the
TABLE, which the Cases convention states per spec.  This paragraph stops
being true as each of those guards widens to `Checks/`;
`tools/check_lean_cases_parity.py`'s `CASES_EXTRA` is where its own
comment says the parity half is to be enrolled.

## What it does NOT claim

Nothing here says these syscalls SHOULD stay unmodeled, and nothing here
is a model of them.  Declining is what the dispatcher already does; this
file states it, in the one place a future change has to look at. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys

/-! ## `clone` (220) and `clone3` (435): the bits the flag gate keeps out

MODELED, parent-side, and stated here in the negative because 220 and 435
are where the Rocq file used to carry a decline.  What replaced it is a
spec that answers exactly one flag word, `SIGCHLD`; the flag bits below
are the ones that decline has to leave behind.  The values are
`include/uapi/linux/sched.h`'s (Linux v6.18.46).  The clone gates read no
`CLONE_*` constant at all — `clone_fork_flags_b` and `clone3_fork_args_b`
are equalities on whole words, not mask tests — so the trusted tree
carries only the one clone bit a spec does read: `Sys/Uapi/Sched.lean`'s
`CLONE_VM`, for the futex pins' empty-waiter-set argument.  The mask below
reads that register constant by its qualified name rather than defining a
second `CLONE_VM`: Lean resolves a name against the enclosing namespace
before an opened one, so a same-named `def` here would be the `CLONE_VM`
every later line of this file reads while the register kept its own, and
`tools/check_lean_pin_placement.py`'s SHADOW rule refuses the
redeclaration for that reason.  Rocq's `ProcessCreation.v` defines all
thirteen beside its own `clone_sharing_bits`, its `CLONE_VM` a second
copy of the 256 that Rocq's `Uapi.v` defines as well (Rocq has no such
rule, and its two copies agree); the other twelve are defined here under
Rocq's names, `clone_bit_values` holds each of them, and
`clone_sharing_bits_value` holds the mask they make; both are read
against include/uapi/linux/sched.h (Linux v6.18.46). -/

def CLONE_FS             : Int := 0x00000200
def CLONE_FILES          : Int := 0x00000400
def CLONE_SIGHAND        : Int := 0x00000800
def CLONE_PIDFD          : Int := 0x00001000
def CLONE_VFORK          : Int := 0x00004000
def CLONE_THREAD         : Int := 0x00010000
def CLONE_SYSVSEM        : Int := 0x00040000
def CLONE_SETTLS         : Int := 0x00080000
def CLONE_PARENT_SETTID  : Int := 0x00100000
def CLONE_CHILD_CLEARTID : Int := 0x00200000
def CLONE_CHILD_SETTID   : Int := 0x01000000
def CLONE_IO             : Int := 0x80000000

/-- The bits the flag gate has to keep out.  Not the complete set a child
could share — `CLONE_PARENT` and the ptrace pair are absent — and it does
not need to be: the gate is an allowlist of one word, and the lemma below
is a sufficient condition over it, not the thing doing the refusing.
Five kinds, each with a reason the Rocq definition spells out in full: the
child reaches back into the parent (`CLONE_VM`, `CLONE_VFORK`,
`CLONE_FILES`, `CLONE_FS`, `CLONE_SYSVSEM`, `CLONE_IO`); the call itself
touches the parent (`CLONE_PIDFD`, `CLONE_PARENT_SETTID`); a thread group
with more than one member (`CLONE_THREAD`, `CLONE_SIGHAND`), which
`set_tid_address_spec` needs never to exist; a slot in a DIFFERENT task
that `mm_release` (kernel/fork.c, Linux v6.18.46) writes through when that
task exits or execs (`CLONE_CHILD_CLEARTID`); and an argument the spec does not fetch
(`CLONE_CHILD_SETTID`, `CLONE_SETTLS`).  Widening the gate to any of them
stops `clone_sharing_flags_unmodeled` closing rather than silently
falsifying the comment that cites it.  What the mask is SILENT on — a
word with no sharing bit and a different exit-signal byte, no signal at
all, `CLONE_PARENT`, the ptrace pair, every `CLONE_NEW*` — is refused by
the gate all the same, and `Checks/Cases/Kernel/Fork.lean` pins four of
those words by name (`clone_no_signal_declines`,
`clone_sigstkflt_declines`, `clone_sigcont_declines`,
`clone_high_bits_declines`) under the quantified
`clone_other_word_declines` every proof here goes through.  The disjunction is taken over `Nat`
and read back as an `Int`, the spelling `Sys/Uapi/Fs.lean` uses for a
mask: Lean's core has no `Int.lor`, and every summand is non-negative, so
the value is Rocq's `fold_left Z.lor`. -/
def clone_sharing_bits : Int :=
  ((([Sys.Uapi.CLONE_VM, CLONE_FS, CLONE_FILES, CLONE_SIGHAND, CLONE_PIDFD,
      CLONE_VFORK, CLONE_THREAD, CLONE_SYSVSEM, CLONE_SETTLS,
      CLONE_PARENT_SETTID, CLONE_CHILD_CLEARTID, CLONE_CHILD_SETTID,
      CLONE_IO].map Int.toNat).foldl (· ||| ·) 0 : Nat) : Int)

/-- The mask, as one number: 0x813d5f00.  Rocq's `clone_sharing_bits`
(`Checks/ProcessCreation.v`) is a bare `fold_left Z.lor` over the same
thirteen names and states no literal, so this is the value of that fold
read off `include/uapi/linux/sched.h`, not a number Rocq proves.  A bit
added to or dropped from the list above moves this and nothing else, so
it is the tripwire on the LIST, as `clone_sharing_flags_unmodeled` is the
tripwire on the GATE.  It is a tripwire on the OR only: two of the twelve
swapping values, or one growing to cover another, leaves the mask where
it is, which is what `clone_bit_values` is for.
kernel: include/uapi/linux/sched.h:CLONE_VM,CLONE_IO@v6.18.46 -/
theorem clone_sharing_bits_value : clone_sharing_bits = 0x813d5f00 := by decide

/-- Each of the twelve bits defined in this file, held one by one to
`include/uapi/linux/sched.h` (Linux v6.18.46), in the order they are
defined above.  The register's `CLONE_VM` is held by
`Checks/Cases/Sys/Uapi/Sched.lean`'s `CLONE_VM_is_bit_8` and is not
repeated here.
kernel: include/uapi/linux/sched.h:CLONE_FS,CLONE_IO@v6.18.46 -/
theorem clone_bit_values :
    [CLONE_FS, CLONE_FILES, CLONE_SIGHAND, CLONE_PIDFD, CLONE_VFORK,
     CLONE_THREAD, CLONE_SYSVSEM, CLONE_SETTLS, CLONE_PARENT_SETTID,
     CLONE_CHILD_CLEARTID, CLONE_CHILD_SETTID, CLONE_IO] =
    [0x00000200, 0x00000400, 0x00000800, 0x00001000, 0x00004000,
     0x00010000, 0x00040000, 0x00080000, 0x00100000, 0x00200000,
     0x01000000, 0x80000000] := by decide

/-- The low byte of a clone flag word is the exit signal (`CSIGNAL`,
include/uapi/linux/sched.h, Linux v6.18.46), and no sharing bit lives
there: the mask and `CSIGNAL` are disjoint.  This is why "17 has none of
these bits", which `clone_sharing_flags_unmodeled` rests on, is a fact
about the mask and not a coincidence of the one accepted word — no
exit-signal byte on its own can ever trip the sharing test, and a word
that does carries a real sharing request.
kernel: include/uapi/linux/sched.h:CSIGNAL@v6.18.46 -/
theorem clone_sharing_bits_clear_of_csignal :
    (clone_sharing_bits.toNat &&& 0xff : Nat) = 0 := by decide

/-- A flag word with any sharing bit set is declined, whatever else it
carries.  Proved through `Checks/Cases/Kernel/Fork.lean`'s quantified gate
pin: the one accepted word is 17, and 17 has none of these bits.  Rocq:
`Z.land (bv_unsigned flags) clone_sharing_bits ≠ 0`; both operands are
non-negative, so the `Nat` conjunction of their `toNat`s is the same value.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_sharing_flags_unmodeled (flags : word) (i : SyscallInput) (m : Model) :
    ((bv_unsigned flags).toNat &&& clone_sharing_bits.toNat : Nat) ≠ 0 →
    clone_spec flags i m Unmodeled :=
  fun hbit =>
    (clone_other_word_declines flags (fun h17 => hbit (by rw [h17]; decide)) i m Unmodeled).mpr rfl

/-- The same statement for `clone3`, where the flag word is field 0 of a
struct in user memory rather than a register: a readable struct whose
`flags` carries a sharing bit is declined.  `clone3_fork_args_b` requires
that field to be ZERO, so a word with any bit set fails it.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_sharing_flags_unmodeled (uargs size : word) (i : SyscallInput) (m : Model)
    (bs : List byte) :
    read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) = some bs →
    ((bv_unsigned (clone_args_field bs 0)).toNat &&& clone_sharing_bits.toNat : Nat) ≠ 0 →
    clone3_spec uargs size i m Unmodeled := by
  intro hread hbit
  unfold clone3_spec
  by_cases hs : (!bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) = true
  · simp only [hs, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff, hread]
    have ha : clone3_fork_args_b bs = false := by
      refine Bool.eq_false_iff.mpr (fun ha => hbit ?_)
      have h0 : w_is0 (clone_args_field bs 0) = true := by
        simp only [clone3_fork_args_b, Bool.and_eq_true] at ha
        simp only [ha]
      rw [(bv_eqb_eq _ _).mp h0]
      decide
    simp only [ha, Bool.false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- THE ARM IS THE ONE IT CLAIMS TO BE.  A refusal lemma characterises its
number completely only because `Unmodeled` is the whole answer; the
positive direction needs saying too: 220 reaches `clone_spec` on a0, and
not some other total spec that refuses the same inputs.
`Sys.Dispatch.dispatch_arm` states the biconditional for any table and
arm, so this costs a lookup and a `rfl`.
rocq-twin: clone_is_clone_spec -/
theorem clone_is_clone_spec (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 220 → (syscall_spec i m o ↔ clone_spec (in_arg i 0) i m o) :=
  fun h => by
    unfold syscall_spec
    exact dispatch_arm spec_table i m o clone_arm (by rw [h]; rfl)

/-- …and 435 reaches `clone3_spec` on a0 and a1.
rocq-twin: clone3_is_clone3_spec -/
theorem clone3_is_clone3_spec (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 435 →
    (syscall_spec i m o ↔ clone3_spec (in_arg i 0) (in_arg i 1) i m o) :=
  fun h => by
    unfold syscall_spec
    exact dispatch_arm spec_table i m o clone3_arm (by rw [h]; rfl)

/-- The same claim at the dispatcher, over both entry points at once.
`clone3` adds a copy-in ledger and nothing else — `clone3_resolve_inv`
strips it and hands back the very `clone_resolve` outcome, with the same
post-model — so one theorem covers 220 and 435 and the two cannot drift
apart.  Rocq closes both numbers with one lemma over `clone_resolve`
(`clone_resolve_declines_or_sets_children`); the Lean arm's pins state
that pair at the accepted word under a gate-open hypothesis, so this
proof reads `clone_resolve_reading` directly and takes the gate-closed
case from `clone_resolve_gate_closed`, where no `Ok` outcome exists.
kernel: kernel/fork.c:clone,clone3,kernel_clone,copy_process@v6.18.46 -/
theorem clone_success_sets_children (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    bv_unsigned i.in_sysno = 220 ∨ bv_unsigned i.in_sysno = 435 →
    syscall_spec i m (Ok eff m' evs) →
    (errno_ret_in clone_errnos eff.eff_ret = true → m' = m)
    ∧ (errno_ret_in clone_errnos eff.eff_ret = false → m_has_children m' = true) := by
  intro hno h
  have hres : ∃ e0 : SyscallEffect,
      clone_resolve i m (Ok e0 m' evs) ∧ eff.eff_ret = e0.eff_ret := by
    rcases hno with hno | hno
    · rw [clone_is_clone_spec i m _ hno] at h
      by_cases hf : clone_fork_flags_b (in_arg i 0) = true
      · simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
        exact ⟨eff, h, rfl⟩
      · simp only [clone_spec.eq_1, hf, Bool.false_eq_true, ↓reduceIte, unmodeled_iff] at h
        exact nomatch h
    · rw [clone3_is_clone3_spec i m _ hno] at h
      by_cases hs : (!bv_eqb (in_arg i 1) (Z_to_bv 64 CLONE_ARGS_SIZE)) = true
      · simp only [clone3_spec.eq_1, hs, ↓reduceIte, unmodeled_iff] at h
        exact nomatch h
      · simp only [clone3_spec.eq_1, hs, Bool.false_eq_true, ↓reduceIte, bind_input_iff] at h
        cases hr : read_bytes_map i.in_mem (in_arg i 0) (Z_to_bv 64 CLONE_ARGS_SIZE) with
        | none =>
          simp only [hr, unmodeled_iff] at h
          exact nomatch h
        | some bs =>
          simp only [hr] at h
          by_cases ha : clone3_fork_args_b bs = true
          · simp only [ha, ↓reduceIte] at h
            exact clone3_resolve_inv (in_arg i 0) i m eff m' evs h
          · simp only [ha, Bool.false_eq_true, ↓reduceIte, unmodeled_iff] at h
            exact nomatch h
  obtain ⟨e0, hres, hret⟩ := hres
  rw [hret]
  by_cases hg : clone_no_shared_file_b (m_fds m) = true
  · rcases (clone_resolve_reading i m _ hg).mp hres with ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
    · obtain ⟨he0, hm, -⟩ := outcome.Ok.inj ho
      have hr : e0.eff_ret = errno_ret e := by subst he0; rfl
      rw [hr, hm]
      exact ⟨fun _ => rfl,
        fun hf => absurd (errno_ret_in_intro clone_errnos e he)
          (by rw [hf]; exact Bool.false_ne_true)⟩
    · obtain ⟨he0, hm, -⟩ := outcome.Ok.inj ho
      have hr : e0.eff_ret = pid := by subst he0; rfl
      rw [hr, hm]
      exact ⟨fun ht =>
          absurd ((errno_ret_in_true clone_errnos pid).mp ht)
            (fun ⟨e, he, hpe⟩ => clone_pid_not_errno m pid hok e he hpe),
        fun _ => rfl⟩
  · have hg' : clone_no_shared_file_b (m_fds m) = false := Bool.eq_false_iff.mpr hg
    exact nomatch (clone_resolve_gate_closed i m _ hg').mp hres

/-! ## The tripwires — one per number, proved against the dispatcher itself -/

/-- `execve` (221).  A successful exec replaces the address space, which
this development cannot express at all: the loaded segments are a SECTION
PARAMETER of `Run`'s `WithMemImage`, fixed for the whole run, so no step
can replace them.  `begin_new_exec` (fs/exec.c, Linux v6.18.46) also
installs the fresh mm through `exec_mmap` — on riscv64 `activate_mm`
(arch/riscv/include/asm/mmu_context.h) zeroes the pointer-masking length
as it does so — resets signal dispositions, and closes the close-on-exec
descriptors through `do_close_on_exec` (fs/file.c).  The failure returns are not separable either: `do_open_execat` (fs/exec.c)
opens with `MAY_EXEC`, and `Fs.Fs` records no file modes, so a spec that
answered -EFAULT for a bad argv would be REJECTING the -EACCES a real
kernel returns for the same call on a non-executable file.
kernel: fs/exec.c:execve,begin_new_exec,exec_mmap,do_open_execat; fs/file.c:do_close_on_exec; arch/riscv/include/asm/mmu_context.h:activate_mm@v6.18.46 -/
theorem execve_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 221 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; rfl)

/-- `execveat` (281).  `execve` plus a dirfd and the three flags
`do_open_execat` accepts — `AT_SYMLINK_NOFOLLOW`, `AT_EMPTY_PATH` and
`AT_EXECVE_CHECK`; `execveat(AT_FDCWD, p, a, e, 0)` is `execve(p, a, e)`:
both entry points end in `do_execveat_common` (fs/exec.c, Linux v6.18.46),
`execve` through `do_execve` with `AT_FDCWD` and no flags, `execveat`
through `do_execveat` with its own.  Everything said of 221 applies, over
a resolution base the model would additionally have to carry.
kernel: fs/exec.c:execveat,do_open_execat,do_execve,do_execveat,do_execveat_common@v6.18.46 -/
theorem execveat_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 281 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; rfl)

/-- `getrlimit` (163) READS, and passes NULL for `new_rlim` to `do_prlimit`
(kernel/sys.c, Linux v6.18.46), so it changes nothing.  Its decline is
load-bearing on the other side: no modeled syscall reads the limit back,
so the tracer's RLIMIT_NOFILE report at the exec stop is the only
measurement of the number `State.in_nofile` is seeded from.  It enters
`do_prlimit` directly, skipping the `check_prlimit_permission` that
`prlimit64` runs — which returns early for the caller's own task and, for
any other, tests the caller's credentials (-EPERM) before it reaches the
`security_task_prlimit` hook (security/security.c) — so it is a different
call from 261 and would need its own argument.
kernel: kernel/sys.c:getrlimit,do_prlimit,check_prlimit_permission,prlimit64; security/security.c:security_task_prlimit@v6.18.46 -/
theorem getrlimit_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 163 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; rfl)

/-- `setrlimit` (164) WRITES.  `State.limst_nofile` holds ONE soft
RLIMIT_NOFILE for a whole run and `Sys/Fs/File.lean`'s `dup3_spec`
compares `newfd` against it, which are both claims that nothing modeled
can change the limit.  Three system calls reach `do_prlimit` (kernel/sys.c,
Linux v6.18.46) with a `new_rlim`: 164, its compat twin on the same
number, and `prlimit64` (261).  261 is neither
registered nor argued here: in Rocq it has an arm that declines every
resource but RLIMIT_CORE, and a port of that arm has to keep the
RLIMIT_NOFILE decline for this entry's claim to survive it —
`Checks/Cases/Fs/File.lean` carries the gate-side statements about both
numbers, and its `sysno_164_is_unmodeled` is this entry's fact read from
the gate's side.  Only three writers can reach the RLIMIT_NOFILE slot of
a live process's `signal->rlim` at all (a sweep for every assignment to
`rlim[`, `rlim_cur` and `rlim_max` at v6.18.46; a new writer naming the
slot, or one iterating every slot of a live task, falsifies the count and
this entry has to be re-argued): `do_prlimit`,
and two LSM hooks that run inside the exec 221 declines — AppArmor's
`__aa_transition_rlimits` (security/apparmor/resource.c), which clamps a
profile's resources, and SELinux's `selinux_bprm_committing_creds`
(security/selinux/hooks.c), which on a domain transition the policy
denies `rlimitinh` to resets every soft limit to the lower of the hard
limit and `init_task`'s soft limit.
The other writers name another slot or another task — `finalize_exec`
(fs/exec.c) the stack limit, `umh_coredump_setup` (fs/coredump.c) the core
limit of the helper a piped `core_pattern` spawns, the accounting and
CPU-timer paths the size and time limits, and `copy_signal` (kernel/fork.c)
a CHILD's fresh copy.
kernel: kernel/sys.c:setrlimit,do_prlimit,prlimit64; security/apparmor/resource.c:__aa_transition_rlimits; security/selinux/hooks.c:selinux_bprm_committing_creds; fs/exec.c:finalize_exec; fs/coredump.c:umh_coredump_setup; kernel/fork.c:copy_signal@v6.18.46 -/
theorem setrlimit_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 164 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; rfl)

/-! ### `prctl` (167) is registered at the OPTION, not the number

Rocq's 167 has an arm answering `PR_CAPBSET_READ`, so its tripwire is the
OPTION: `prctl_option_unmodeled` and `prctl_tagged_addr_ctrl_unmodeled`
there say that option 55, `PR_SET_TAGGED_ADDR_CTRL`
(include/uapi/linux/prctl.h, Linux v6.18.46), falls through — the case
the `access_ok` argument needs, since that option is the caller's own
route to `set_tagged_addr_ctrl` (arch/riscv/kernel/process.c).

A number-level `bv_unsigned i.in_sysno = 167 → syscall_spec i m
Unmodeled` was written here first and removed in review.  It is true only
while the Lean table has no arm at 167, `tools/check_decline_registers.py`
registers it as L2 (and its `pc_input 167` companion as L3), and the
prctl port then lands into a collision on both readers and a `rfl` that
no longer closes — measured on a merge with that port.  A decline the
next arm has to delete is not a tripwire but a landing-order hazard, and
while 167 has no arm the generated `Checks/Cases/SyscallTable.lean` pin
already holds the number.  Two shapes NOT to use for the option-level
twin, because the register reader reads them wrongly: an option
hypothesis BEFORE the number hypothesis still matches its L2 reader and
registers the NUMBER; an option hypothesis AFTER it is a statement that
reader cannot classify and fails the run.  State the option-level fact
over `prctl_spec` itself, beside the arm, or over a concrete input the
reader does not know — which is what `prctl_tagged_addr_ctrl_declines`
below does.  This paragraph stops being needed when that reader learns
an option-level shape. -/

/-- `ptrace` (117).  The OTHER caller of `set_tagged_addr_ctrl`
(arch/riscv/kernel/process.c, Linux v6.18.46): `ptrace_request` dispatches
`PTRACE_SETREGSET` to `ptrace_regset` (kernel/ptrace.c), which for
`NT_RISCV_TAGGED_ADDR_CTRL` (include/uapi/linux/elf.h) runs
`tagged_addr_ctrl_set` (arch/riscv/kernel/ptrace.c).  Both routes sit
under the same `CONFIG_RISCV_ISA_SUPM` — the regset and its setter in
ptrace.c, `set_tagged_addr_ctrl` in process.c; both arrived in v6.13 in
one series, so no supported kernel offers the prctl route without the
ptrace one (a version putting either behind a second symbol falsifies
this), which is why this number is pinned beside the prctl option rather
than left to the argument about there being no second task.
kernel: kernel/ptrace.c:ptrace,ptrace_request,ptrace_regset; arch/riscv/kernel/ptrace.c:tagged_addr_ctrl_set; include/uapi/linux/elf.h:NT_RISCV_TAGGED_ADDR_CTRL@v6.18.46 -/
theorem ptrace_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 117 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; rfl)

/-! ## What a declined syscall does to a RUN -/

section Runs

variable (segs : List Segment)

/-- The syscall counterpart of `Run.reaches_unmodeled_intro`, which covers
only the INSTRUCTION arm.  Stated at the configuration level so the
numbers above compose with it.
rocq-twin: unmodeled_at_syscall -/
theorem unmodeled_at_syscall (ms : machine_state) (model : Model) (x8 : word) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model Unmodeled →
    unmodeled_at segs (config.mkCfg ms model) :=
  fun hh hsvc hspec => ⟨hh, Or.inr ⟨x8, hsvc, hspec⟩⟩

/-- …and what that costs a source binary: reaching such a configuration on
ANY execution refutes `modeled`, so no equivalence theorem can be proved
about it.  This is the coverage cost of declining, stated once and
precisely.  It is NOT a soundness risk and NOT a vacuous pass: `modeled` is
a conjunct the equivalence proof must DISCHARGE, so a forking source makes
the theorem unprovable rather than free.
rocq-twin: reaches_unmodeled_syscall -/
theorem reaches_unmodeled_syscall (c0 : config) (tr : List event) (ms : machine_state)
    (model : Model) (x8 : word) :
    star segs c0 tr (config.mkCfg ms model) →
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model Unmodeled →
    reaches_unmodeled segs c0 :=
  fun hstar hh hsvc hspec =>
    ⟨tr, config.mkCfg ms model, hstar, unmodeled_at_syscall segs ms model x8 hh hsvc hspec⟩

/-- The two composed, at a number that is still declined: a run that
reaches a pending `execve` is a run this model does not cover.  Rocq used
to state it at `clone` (220); 220 is modeled parent-side and 221 is the
number the child reaches immediately afterwards, so the statement moved
rather than went away.
rocq-twin: execve_refutes_coverage -/
theorem execve_refutes_coverage (c0 : config) (tr : List event) (ms : machine_state)
    (model : Model) (x8 : word) :
    star segs c0 tr (config.mkCfg ms model) →
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    bv_unsigned x8 = 221 →
    reaches_unmodeled segs c0 :=
  fun hstar hh hsvc hno =>
    reaches_unmodeled_syscall segs c0 tr ms model x8 hstar hh hsvc
      (execve_unmodeled (sys_input segs ms x8) model hno)

/-- THE OTHER DIRECTION, so the two above are not satisfied by a
`syscall_spec` that declines everything: a pending syscall at a number
whose arm never declines is NOT a configuration the model gives up on.
Stated at `exit_group` (94), the arm `modeled_number_is_not_unmodeled`
below uses as its witness, over every machine state and model: the
`sstep_syscall_unmodeled` transition out of such a configuration needs
`syscall_spec … Unmodeled`, and `Checks/Cases/Kernel/Exit.lean`'s
`exit_never_unmodeled` refuses it for every argument.  The instruction
disjunct of `unmodeled_at` is closed by the pending syscall itself.
kernel: kernel/exit.c:exit_group@v6.18.46 -/
theorem exit_group_pending_is_not_unmodeled_at (ms : machine_state) (model : Model)
    (x8 : word) :
    ms.ms_svc_pending = some x8 →
    bv_unsigned x8 = 94 →
    ¬ unmodeled_at segs (config.mkCfg ms model) := by
  intro hsvc h94 hun
  rcases hun with ⟨_, (⟨hnone, _⟩ | ⟨x8', hsome, hspec⟩)⟩
  · exact nomatch hsvc.symm.trans hnone
  · have hx : x8' = x8 := Option.some.inj (hsome.symm.trans hsvc)
    rw [hx] at hspec
    unfold syscall_spec at hspec
    rw [dispatch_arm spec_table (sys_input segs ms x8) model Unmodeled exit_group_arm
      (by show lookup_arm spec_table (bv_unsigned x8) = some exit_group_arm
          rw [h94]; rfl)] at hspec
    exact exit_never_unmodeled _ _ _ hspec

end Runs

/-! ## The concrete companions — the other half of every statement above

The Rocq file closes each number's loop through the executable checker,
`check_syscall (pc_input N) (mkEffect 0 [] []) pc_model = CheckUnmodeled`,
so the Rocq half and the harness half are pinned to the same verdict.
The checker is ticket K3; until it lands these are stated over
`syscall_spec` at the same concrete input, quantified over the model where
the Rocq example fixes `pc_model` — no field of the process input reaches
a decline, since every declined number falls through before any model
state is read — and the clone and wait4 companions, which DO read the
model, run on `pc_model` as Rocq's do. -/

/-- The process the Rocq examples run on.  None of its fields is a claim:
every declined number falls through before any model state is read, and
the clone and wait4 companions below say which fields they read.  It is
`Checks/Cases/Prelude.lean`'s `demo_model` in every field but the
supplementary groups — `[]` here, `demo_groups` there — spelled as
Rocq's `pc_model` is, so that the Rocq name has a twin; nothing in this
file reads the groups. -/
def pc_model : Model :=
  init_model [] 0 0 (Z_to_bv 64 sp_window_lo) 0x40000000
    (ProcInput.mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
      net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false VaSize.Sv48)

/-- Syscall `n` with every argument register zero and no readable or
writable memory: what `tools/check_decline_registers.py` reads as a
register-L3 input. -/
def pc_input (n : Int) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 n) [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! ### `clone` and `clone3`, which are modeled, run the other way round

The dispatcher must DECLINE the flag words the spec does not accept, and
answer the one it does.  `pc_input` passes zero in every argument
register, which is a flag word of 0 — not `SIGCHLD` — and a `clone3` whose
`size` is 0.  These names do not end in `_unmodeled` on purpose: that
suffix is how the register reader tells a claim about the NUMBER from a
claim about a shape, and 220 and 435 have arms. -/

/-- `clone(0, …)` is declined: 0 is not the accepted word.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_flags_zero_declines : syscall_spec (pc_input 220) pc_model Unmodeled :=
  (clone_is_clone_spec (pc_input 220) pc_model Unmodeled rfl).mpr
    ((clone_other_word_declines (in_arg (pc_input 220) 0) (by decide) (pc_input 220) pc_model
      Unmodeled).mpr rfl)

/-- `clone3(…, 0)` is declined at the size, before the struct is read.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_size_zero_declines : syscall_spec (pc_input 435) pc_model Unmodeled :=
  (clone3_is_clone3_spec (pc_input 435) pc_model Unmodeled rfl).mpr
    (by
      have hs : (!bv_eqb (in_arg (pc_input 435) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)) = true := by decide
      simp only [clone3_spec.eq_1, hs, ↓reduceIte]
      exact unmodeled_intro _ _)

/-- `clone(SIGCHLD, 0, 0, 0, 0)` against `pc_model`, which has no open
regular file: the shape the accepting companions run on. -/
def pc_clone_input : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 220) [Z_to_bv 64 SIGCHLD, 0, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- `pc_model`'s descriptor table lets the fork gate through: its three
descriptors are the `FdChannel` seeds `State.init_model` installs, which
is what makes the accepting companions non-vacuous.
model: a fact about `pc_model`'s descriptor table, seeded by `State.init_model` -/
theorem pc_model_gate_open : clone_no_shared_file_b (m_fds pc_model) = true := by
  decide

/-- The success arm records the child: `clone_resolve` applies
`State.with_children` on this branch, so the post-model is not `pc_model`.
That is what `wait4_spec`'s -ECHILD gate reads, and pinning it here is
what makes the two compose.
kernel: kernel/fork.c:kernel_clone,copy_process; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_admits_a_pid :
    syscall_spec pc_clone_input pc_model
      (Ok (mkEffect (Z_to_bv 64 4242) [] []) (with_children pc_model) []) := by
  rw [clone_is_clone_spec pc_clone_input pc_model _ rfl]
  have hf : clone_fork_flags_b (in_arg pc_clone_input 0) = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte]
  exact (clone_resolve_reading pc_clone_input pc_model _ pc_model_gate_open).mpr
    (Or.inr ⟨Z_to_bv 64 4242, rfl, by decide⟩)

/-- -EAGAIN is answered with the model left alone: the errno arm records
nothing.
kernel: kernel/fork.c:kernel_clone,copy_process@v6.18.46 -/
theorem clone_admits_eagain :
    syscall_spec pc_clone_input pc_model (Ok (mkEffect (errno_ret EAGAIN) [] []) pc_model []) := by
  rw [clone_is_clone_spec pc_clone_input pc_model _ rfl]
  have hf : clone_fork_flags_b (in_arg pc_clone_input 0) = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte]
  exact (clone_resolve_reading pc_clone_input pc_model _ pc_model_gate_open).mpr
    (Or.inl ⟨EAGAIN, by decide, rfl⟩)

/-- 0 — the CHILD's answer — is refused whatever model and events a kernel
claims beside it.
kernel: kernel/fork.c:kernel_clone; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_refuses_zero (m' : Model) (evs : List event) :
    ¬ syscall_spec pc_clone_input pc_model (Ok (mkEffect 0 [] []) m' evs) :=
  fun h =>
    clone_never_returns_zero (in_arg pc_clone_input 0) pc_clone_input pc_model _ m' evs
      ((clone_is_clone_spec pc_clone_input pc_model _ rfl).mp h) rfl

/-- The envelope bound itself, `PID_MAX_ENVELOPE`, is refused: every
accepted pid is strictly below it, and no accepted errno encodes it.
kernel: kernel/pid.c:alloc_pid; include/linux/threads.h:PID_MAX_LIMIT@v6.18.46 -/
theorem clone_refuses_the_envelope_bound (m' : Model) (evs : List event) :
    ¬ syscall_spec pc_clone_input pc_model
        (Ok (mkEffect (Z_to_bv 64 PID_MAX_ENVELOPE) [] []) m' evs) := by
  intro h
  rw [clone_is_clone_spec pc_clone_input pc_model _ rfl] at h
  have hf : clone_fork_flags_b (in_arg pc_clone_input 0) = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
  rcases (clone_resolve_reading pc_clone_input pc_model _ pc_model_gate_open).mp h with
    ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
  · have hr : Z_to_bv 64 PID_MAX_ENVELOPE = errno_ret e :=
      congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  · have hp : pid = Z_to_bv 64 PID_MAX_ENVELOPE :=
      (congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1).symm
    rw [hp] at hok
    exact absurd hok (by decide)

/-- `ENFILE` is 23 and `EMFILE`, which IS accepted, is 24 — so this refuses
the nearest neighbour of an accepted errno rather than a distant one.
kernel: kernel/fork.c:kernel_clone,copy_process@v6.18.46 -/
theorem clone_refuses_another_errno (m' : Model) (evs : List event) :
    ¬ syscall_spec pc_clone_input pc_model (Ok (mkEffect (errno_ret ENFILE) [] []) m' evs) := by
  intro h
  rw [clone_is_clone_spec pc_clone_input pc_model _ rfl] at h
  have hf : clone_fork_flags_b (in_arg pc_clone_input 0) = true := by decide
  simp only [clone_spec.eq_1, hf, ↓reduceIte] at h
  rcases (clone_resolve_reading pc_clone_input pc_model _ pc_model_gate_open).mp h with
    ⟨e, he, ho⟩ | ⟨pid, ho, hok⟩
  · have hr : errno_ret ENFILE = errno_ret e :=
      congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
    simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  · have hp : pid = errno_ret ENFILE :=
      (congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1).symm
    rw [hp] at hok
    exact absurd hok (by decide)

/-- THE SHARED FILE OFFSET.  The quantified statement is
`Checks/Cases/Kernel/Fork.lean`'s `clone_gate_closed_declines`; this is its
concrete companion, over one model and one descriptor shape: `pc_model`
with a regular file open at 3.  `copy_files` (kernel/fork.c, Linux v6.18.46)
duplicates the table while both tables point at the same `struct file`,
and `State.FdEntry` inlines the offset into the descriptor, so the sharing
is not expressible and the spec declines rather than pretending otherwise. -/
def pc_model_open_file : Model :=
  with_fds ((Z_to_bv 64 3, FdEntry.FdFile [] (Z_to_bv 64 0)) :: m_fds pc_model) pc_model

/-- …and the decline it produces, at the accepted flag word.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_declines_with_a_file_open :
    syscall_spec pc_clone_input pc_model_open_file Unmodeled :=
  (clone_is_clone_spec pc_clone_input pc_model_open_file Unmodeled rfl).mpr
    (clone_gate_closed_declines _ _ _ (by decide))

/-! ### The declined numbers, at the register-L3 input -/

/-- Twin of Rocq's `execve_checker_unmodeled`, over the spec.
kernel: fs/exec.c:execve@v6.18.46 -/
theorem execve_concrete_unmodeled (m : Model) : syscall_spec (pc_input 221) m Unmodeled := rfl

/-- Twin of Rocq's `execveat_checker_unmodeled`, over the spec.
kernel: fs/exec.c:execveat@v6.18.46 -/
theorem execveat_concrete_unmodeled (m : Model) : syscall_spec (pc_input 281) m Unmodeled := rfl

/-- Twin of Rocq's `getrlimit_checker_unmodeled`, over the spec.
kernel: kernel/sys.c:getrlimit@v6.18.46 -/
theorem getrlimit_concrete_unmodeled (m : Model) : syscall_spec (pc_input 163) m Unmodeled := rfl

/-- Twin of Rocq's `setrlimit_checker_unmodeled`, over the spec.
kernel: kernel/sys.c:setrlimit@v6.18.46 -/
theorem setrlimit_concrete_unmodeled (m : Model) : syscall_spec (pc_input 164) m Unmodeled := rfl

/-- Twin of Rocq's `ptrace_checker_unmodeled`, over the spec.
kernel: kernel/ptrace.c:ptrace@v6.18.46 -/
theorem ptrace_concrete_unmodeled (m : Model) : syscall_spec (pc_input 117) m Unmodeled := rfl

/-- `prctl(opt, 0, 0, 0, 0)`; `pc_prctl_input 55` is `PR_SET_TAGGED_ADDR_CTRL`
(include/uapi/linux/prctl.h, Linux v6.18.46), the option the tagging
argument names. -/
def pc_prctl_input (opt : Int) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 167) [Z_to_bv 64 opt, 0, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- NAMED FOR THE OPTION, NOT THE NUMBER: the concrete half of the
statement the `access_ok` argument needs, and the only 167 entry this
file keeps.  Its `rfl` closes in both worlds — with no arm at 167 it is
the dispatcher's fall-through, and with the prctl arm it is the arm's
first test, whose option list does not hold 55 (checked on a merge with
that port) — so the port neither breaks it nor has to restate it; and
`tools/check_decline_registers.py` does not know `pc_prctl_input`, so it
neither registers 167 nor stumbles on it.  What it does NOT say is that
EVERY argument shape of option 55 is declined, which is Rocq's
`prctl_tagged_addr_ctrl_unmodeled` (∀ i m over the `int` truncation of
a0): that is stated over `prctl_spec` where the arm is, as is
`prctl_option_unmodeled`.  An arm answering option 55 for some a1 while
declining a1 = 0 would keep this `rfl` closing; only the quantified twin
beside the arm refuses that.
kernel: kernel/sys.c:prctl; include/uapi/linux/prctl.h:PR_SET_TAGGED_ADDR_CTRL; arch/riscv/kernel/process.c:set_tagged_addr_ctrl@v6.18.46 -/
theorem prctl_tagged_addr_ctrl_declines (m : Model) :
    syscall_spec (pc_prctl_input 55) m Unmodeled := rfl

/-! ### `wait4`, which is modeled, pins what is ACCEPTED and what is REJECTED

`pc_input` carries all-zero arguments, which is `upid = 0` — a declining
shape — so these use `wait4_input_any`, the shape both dropbear call sites
issue: `waitpid(-1, NULL, WNOHANG)`. -/

/-- `wait4` (260) is MODELED and not declined on its shape: a childless
caller's `waitpid(-1, NULL, WNOHANG)` is answered.  -ECHILD is what
`kernel_wait4` returns when `__do_wait` finds neither a child nor a
tracee, and `State.ProcInput`'s lists are the two the model consults.

THE OTHER HALF IS NOT DISCHARGED IN THE MODEL.  The lists must also have
STARTED empty, and that is a property of the LAUNCHER: Linux's `execve`
empties neither, so a process that forked a grandchild or attached a
tracee before exec'ing this image hands it something to wait for.  Under
testing/syscall-check that is checked rather than assumed — the tracer
counts the tasks the probe could wait for at the exec stop — and outside
that harness it binds nothing.

SINCE THE CHILD GATE this statement is carried by two facts at once: at a
childless caller -ECHILD really is the only answer, and at a caller with a
child there is no `Ok` outcome at all because `wait4_spec` declines
(`Checks/Cases/Kernel/Exit.lean`'s
`wait4_with_child_is_unmodeled_for_every_model`).  Both halves are needed;
dropping the gate would leave the first covering a case it is false for.
What the arm rests on is not that no child can exist but that the model
RECORDS whether one does — `clone_success_sets_children` above.

The three guards that still decline are `wait4_spec`'s: any `upid` but -1,
any `options` but `WNOHANG` (a blocking wait is a wait-queue sleep, and can
answer -ERESTARTSYS, which reaches the caller as -EINTR when the handler
lacks `SA_RESTART` and is restarted otherwise, arch/riscv/kernel/signal.c,
Linux v6.18.46),
and a non-NULL `rusage`.  `stat_addr` is not among them and
is not read at all — `kernel_wait4` guards its copy-out on `ret > 0`, so no
-ECHILD touches the pointer — which is why no hypothesis names it.

Rocq proves this through the executable checker; Lean has no checker yet
(K3), so it is proved through the arm.  The number hypothesis is LAST, the
reverse of Rocq's order, on purpose: `tools/check_decline_registers.py`
reads a `bv_unsigned i.in_sysno = N` hypothesis followed directly by the
conclusion, and registers it as a decline unless the conclusion is
negated.  Written first, `= 260 → … → ¬ …` puts four hypotheses between
the number and the `¬`, which is the shape the tool cannot read and fails
the run on.  Written last, the tool reads the negation and skips it.
kernel: kernel/exit.c:wait4,kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_not_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned (pid32 (in_arg i 0)) = WAIT_ANY32 →
    bv_unsigned (waitopts32 (in_arg i 2)) = Sys.Uapi.WNOHANG →
    w_is0 (in_arg i 3) = true →
    m_has_children m = false →
    bv_unsigned i.in_sysno = 260 →
    ¬ syscall_spec i m Unmodeled := by
  intro h1 h2 h3 h4 hno h
  unfold syscall_spec at h
  rw [dispatch_arm spec_table i m _ wait4_arm (by rw [hno]; rfl)] at h
  simp only [wait4_arm, wait4_spec.eq_1, ne_eq, h1, h2, not_true_eq_false, h3, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind_get_model_iff, h4, err_ret.eq_1, ret_only.eq_1,
    pure_iff] at h
  exact nomatch h

/-- …and what it is not declined TO, which is the half a `¬ Unmodeled`
statement cannot carry.  This is the soundness claim for 260 in one line:
EVERY admissible resolution of the number, at every argument shape and in
every model, is -ECHILD with no memory moved.  No argument hypothesis is
needed — outside the modeled shape there is no `Ok` outcome to constrain.

A conformance probe reaches the accepting half of this and one forged
rejection at a time; only a `∀` says that a reaped pid, WNOHANG's bare 0
and an -EFAULT are ALL absent, and that no arm anywhere writes through
`stat_addr`.  That is `theories/LinuxProcessSem/Checks/Examples.v`'s first
reason, and it is the statement priority 2 turns on: a childless process
cannot reap, so a model accepting a reap would accept a trace Linux cannot
produce.
kernel: kernel/exit.c:wait4,kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_answers_only_echild (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    bv_unsigned i.in_sysno = 260 →
    syscall_spec i m (Ok eff m' evs) →
    eff = mkEffect (errno_ret ECHILD) [] [] ∧ m' = m ∧ evs = [] := by
  intro hno h
  unfold syscall_spec at h
  rw [dispatch_arm spec_table i m _ wait4_arm (by rw [hno]; rfl)] at h
  simp only [wait4_arm] at h
  by_cases h1 : bv_unsigned (pid32 (in_arg i 0)) = WAIT_ANY32
  · by_cases h2 : bv_unsigned (waitopts32 (in_arg i 2)) = Sys.Uapi.WNOHANG
    · by_cases h3 : w_is0 (in_arg i 3) = true
      · by_cases h4 : m_has_children m = true
        · simp only [wait4_spec.eq_1, ne_eq, h1, h2, not_true_eq_false, h3, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, bind_get_model_iff, h4, unmodeled_iff] at h
          exact nomatch h
        · have h4' : m_has_children m = false := Bool.eq_false_iff.mpr h4
          simp only [wait4_spec.eq_1, ne_eq, h1, h2, not_true_eq_false, h3, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, bind_get_model_iff, h4', err_ret.eq_1, ret_only.eq_1,
            pure_iff] at h
          exact outcome.Ok.inj h
      · have h3' : w_is0 (in_arg i 3) = false := Bool.eq_false_iff.mpr h3
        simp only [wait4_spec.eq_1, ne_eq, h1, h2, not_true_eq_false, h3', Bool.not_false,
          ↓reduceIte, unmodeled_iff] at h
        exact nomatch h
    · simp only [wait4_spec.eq_1, ne_eq, h1, not_true_eq_false, h2, not_false_eq_true, ↓reduceIte,
        unmodeled_iff] at h
      exact nomatch h
  · simp only [wait4_spec.eq_1, ne_eq, h1, not_false_eq_true, ↓reduceIte, unmodeled_iff] at h
    exact nomatch h

/-! ### `setsid` (157), which is modeled, stated in the negative

157 is where the Rocq file used to carry a decline, and the register
reader is why the statement is here at all: a file of tripwires is only
worth reading if it stops being one when the fact changes.  The first
theorem fails to compile the moment 157 loses its arm, exactly as its
neighbours fail the moment one of theirs gains one.  Rocq proves it
through the executable checker (`check_setsid_no_unmodeled`); here the
model half is `Checks/Cases/Kernel/Sys.lean`'s `setsid_never_declines`,
and this file adds only the dispatcher step.  The number hypothesis is
FIRST here, unlike `wait4_not_unmodeled`'s, because nothing sits between
it and the negated conclusion for the register reader to trip on. -/

/-- `setsid` never declines: `ksys_setsid` (kernel/sys.c) has two tests,
and the model answers both — -EPERM for the leader bit it records, and
either -EPERM or a session id for the process-group test it cannot see.
kernel: kernel/sys.c:setsid,ksys_setsid@v6.18.46 -/
theorem setsid_not_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 157 → ¬ syscall_spec i m Unmodeled :=
  fun hno h => by
    unfold syscall_spec at h
    rw [dispatch_arm spec_table i m Unmodeled setsid_arm (by rw [hno]; rfl)] at h
    exact setsid_never_declines i m h

/-- AND THE FULL CHARACTERIZATION, which is what makes 157's entry as
strong as its neighbours rather than merely non-vacuous.  A decline
theorem says EVERYTHING about its number, because `Unmodeled` is the whole
answer; `setsid_not_unmodeled` rules out one answer and would still hold if
157 dispatched to some other total spec that never declines.  This closes
that gap: at 157 the dispatcher is `setsid_spec` and nothing else, for
every input, model and outcome.  Replace the arm and this breaks; remove
it and `setsid_not_unmodeled` breaks.  Free, because
`Sys.Dispatch.dispatch_arm` states the biconditional for any table and
arm.  `Checks/Cases/Kernel/Sys.lean`'s `dispatch_157_is_setsid` is the
same lookup composed with the first-call answer set, under the hypotheses
that answer set needs; this one has none.
rocq-twin: setsid_is_setsid_spec -/
theorem setsid_is_setsid_spec (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 157 → (syscall_spec i m o ↔ setsid_spec i m o) :=
  fun hno => by
    unfold syscall_spec
    exact dispatch_arm spec_table i m o setsid_arm (by rw [hno]; rfl)

/-- `waitpid(-1, NULL, WNOHANG)` as a `SyscallInput`, the shape both
dropbear call sites issue. -/
def wait4_input_any : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 260)
    [Z_to_bv 64 (-1), 0, Z_to_bv 64 1, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The arguments `wait4_input_any` hands the arm, after the `int`
truncations the dispatcher applies: `waitpid(-1, NULL, WNOHANG)`.
model: the `int` truncations of one fixed input; no kernel answer is involved -/
theorem wait4_input_any_args :
    pid32 (in_arg wait4_input_any 0) = 4294967295
    ∧ in_arg wait4_input_any 1 = 0
    ∧ waitopts32 (in_arg wait4_input_any 2) = 1
    ∧ in_arg wait4_input_any 3 = 0 := by
  decide

/-- A childless `pc_model` is answered -ECHILD with the model untouched:
`wait4_not_unmodeled`'s concrete half at the shape its hypotheses name.
kernel: kernel/exit.c:wait4,kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_echild :
    syscall_spec wait4_input_any pc_model (Ok (mkEffect (errno_ret ECHILD) [] []) pc_model []) := by
  unfold syscall_spec
  rw [dispatch_arm spec_table wait4_input_any pc_model _ wait4_arm rfl]
  simp only [wait4_arm]
  obtain ⟨h0, h1, h2, h3⟩ := wait4_input_any_args
  rw [h0, h1, h2, h3]
  exact (wait4_childless_is_echild_for_every_model 0 wait4_input_any pc_model (by decide) _).mpr rfl

/-- The concrete witness for `wait4_answers_only_echild`: a kernel claiming
to have reaped pid 4321 is REJECTED, whatever model and events it claims
beside it — the case that would have caught a `wait4` that accepted a
reap.  Without it the accept above is satisfied by a spec that says yes
to everything.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_rejects_a_reap (m' : Model) (evs : List event) :
    ¬ syscall_spec wait4_input_any pc_model (Ok (mkEffect (Z_to_bv 64 4321) [] []) m' evs) := by
  intro h
  unfold syscall_spec at h
  rw [dispatch_arm spec_table wait4_input_any pc_model _ wait4_arm rfl] at h
  simp only [wait4_arm] at h
  obtain ⟨h0, h1, h2, h3⟩ := wait4_input_any_args
  rw [h0, h1, h2, h3] at h
  have ho := (wait4_childless_is_echild_for_every_model 0 wait4_input_any pc_model (by decide) _).mp h
  have hr : Z_to_bv 64 4321 = errno_ret ECHILD :=
    congrArg SyscallEffect.eff_ret (outcome.Ok.inj ho).1
  exact absurd hr (by decide)

/-! ### Non-vacuity -/

/-- NON-VACUITY.  Most of what is above rules something OUT, and a
dispatcher declining EVERY number would satisfy all of it, so it is worth
pinning that the shape can also come out the other way — with a number
this file does not otherwise mention, as a pure witness rather than a
constraint.  Rocq's witness is `read` (63), which has no arm in this table
yet; `exit_group` (94) is on the surface and never declines
(`Checks/Cases/Kernel/Exit.lean`'s `exit_never_unmodeled`).  The witness
moves back to 63 when `read` is ported.
kernel: kernel/exit.c:exit_group@v6.18.46 -/
theorem modeled_number_is_not_unmodeled (m : Model) :
    ¬ syscall_spec (pc_input 94) m Unmodeled := by
  intro h
  unfold syscall_spec at h
  rw [dispatch_arm spec_table (pc_input 94) m Unmodeled exit_group_arm rfl] at h
  exact exit_never_unmodeled _ _ _ h

end LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation
