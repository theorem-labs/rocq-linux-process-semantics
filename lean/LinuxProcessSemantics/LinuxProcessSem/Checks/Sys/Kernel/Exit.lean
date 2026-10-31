import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Exit — the exit (93), exit_group (94) and wait4 (260) checkers, witnesses, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Exit.v` — the
executable checkers `check_exit` and `check_wait4`, each with its four
proofs — and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Kernel/Exit.v` — the progress
witnesses `exit_witness` and `wait4_witness` with their `*_ok` lemmas.
All answer to the relational specs in `Sys/Kernel/Exit.lean`, which
answer to Linux `kernel/exit.c`.  Not part of the trusted specification:
the checkers' proofs relate them to the specs, and the proofs are what
carry the trust.  The `wait4` half follows the sentinel line below the
`exit` sections (BRIEF.md section 4).
The frame lemmas `check_exit_frame` and `check_wait4_frame`, which Rocq
states in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, are here
too, beside the checkers whose accepted models they describe: `Checks/VmMapsDisjoint.lean`
holds the invariant and the arm-generic lemmas and names no syscall
checker, so a checker's frame lemma lives in the checker's own file and
no port ticket edits the invariant's file.  `check_wait4_fd_state_frame`
is here by the same rule, on the `m_fd` projection the registry in
`Checks/Invariants.lean` reads — that file's header says a checker's
frame lemma belongs beside the checker and holds `check_exit_fd_state_frame`
in the wrong file knowingly.  The witnesses `exit_witness` and
`wait4_witness` twin `Checks/Witness/Kernel/Exit.v`, a file the
`rocq-baseline:` register above is not keyed to, so a witness is never an
`unported:` entry here: a ticket's promised witness is met by its
definition (`lean_port_brief.py --lint` reads the definitions) or it is
missing, and `Checks/Sys/Mm/Mmap.lean`'s header leans on this sentence
for its own witnesses.  What CANNOT be here is the arm-level fact
`arm_exit_preserves_vm`, or the one the wait4 arm's registration owes: the arm it names lives in
`Checks/Sys/Table.lean`, which imports every checker, so a checker's file
cannot see its own arm, and the fact lives beside the alternation it
feeds (`Checks/VmMapsDisjoint/Arms.lean`).

THIS IS THE WORKED EXAMPLE in two halves, and it is the smallest one
there is: a checker with no argument guard, no descriptor lookup and no
memory access, so what is left is exactly the shape every arm has.  A C
ticket copies the checker, its four proofs, the witness with its
receptiveness proof and the frame lemma, all in its own file, with a
Cases twin; the arm's registering ticket — a V ticket's first step since
#904, K6a here — copies the arm block with its `arm_unfold` lemmas in
`Checks/Sys/Table.lean` and the arm-level fact with its alternative in
`Checks/VmMapsDisjoint/Arms.lean`.  (`CHECK_ACCEPT` in
`tools/lean_port_graph.py` still lists the frame lemma on the V side;
the four landed checker twins and `Checks/VmMapsDisjoint.lean`'s import
discipline put it here, and this file follows them.)  This K ticket does
both halves at once because it is the example.  Two arms of the table,
`exit` and `exit_group`, are built over this one checker, exactly as
`Sys/SyscallTable.lean` builds both rows over the one spec.

Every kernel claim below is read at Linux v6.18.46 (commit
1f99e9ab748f).  The definition-level argument — why the recorded code is
the low byte, and why `exit_group` shares the spec — is on
`Sys/Kernel/Exit.lean` and is not repeated.  What this file adds is the
ACCEPTOR reading: which `(effect, model, events)` triple the checker
admits for a call that, in Linux, never returns.

The proofs do not mirror Rocq's scripts tactic for tactic.  Rocq opens
the spec with `sys_unfold` and closes with `inv_ok`; here the two
primitives the spec is built from are opened by name, `bind_modify_iff`
for the halt and `pure_iff` for the return, so that each step names the
lemma it stands on and a change to either primitive fails here by name. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- The exit checker, shared by the `exit` (93) and `exit_group` (94)
arms.  Rocq: `Exit.check_exit`.

ONE ACCEPTED TRIPLE: a zero return with every ledger empty, the model with
`code & 0xff` recorded as the halt, and no event.  The mask is the
kernel's: `SYSCALL_DEFINE1(exit, int, error_code)` hands `do_exit` the
value `(error_code & 0xff) << 8`, and `exit_group` hands `do_group_exit`
the same expression (kernel/exit.c:1085-1088 and :1129-1134, Linux
v6.18.46, commit 1f99e9ab748f).  The low byte is what a waiting parent
recovers from the status word, which is why the model keeps the byte and
not the shifted word; the spec's docstring walks that path.

THE ZERO RETURN IS A CONVENTION THE TESTER AND THE SPEC SHARE, not a
value Linux produces: `do_exit` (kernel/exit.c:903, Linux v6.18.46) and
`do_group_exit` (kernel/exit.c:1094-1095, Linux v6.18.46) are both
declared noreturn, so no instruction of the program runs after the
`ecall` and there is no register to read a return from.  The tester
synthesizes the effect this checker is shown — return 0, every ledger
empty — because the run ends at the trap; the terminal arm for numbers
93 and 94 in `testing/syscall-check/main.ml` is where that effect is
built, and the spec's `ret_only` of 0 is the same convention on the spec
side.  What `CheckReject` refuses is therefore a `--mutate` lie about
that effect, never a real kernel, and every ledger operator of that
harness reaches this arm: the terminal effect passes through the same
`mutate` as any other.  `check_ret_only` matches all six fields of the
effect, not the three `mkEffect` spells out — a checker that matched
only the first three would pass every pin stated over `mkEffect` and
accept a smuggled copy-in, which is why the Cases twin states its
ledger refusals over `mkEffectU`.

THE EMPTY WRITE LEDGER IS A KERNEL CLAIM ALL THE SAME, and one the
harness cannot test: the effect it shows this checker is synthesized, so
no trace can carry a write the kernel made on the way out, and the claim
is carried by the reading below alone.  Every store the exit path can
make into the dying address space sits behind something no admitted run
has.  Two go through a pointer the task registered by syscall, and
`exit_mm` (kernel/exit.c:556-560, Linux v6.18.46) reaches both through
`exit_mm_release` (kernel/fork.c:1457-1461, Linux v6.18.46), in order.

First `futex_exit_release` (kernel/futex/core.c:1540-1545, Linux
v6.18.46): its `futex_cleanup` (kernel/futex/core.c:1439-1455, Linux
v6.18.46) walks the task's robust list through `exit_robust_list`
(kernel/futex/core.c:1185, Linux v6.18.46) when `tsk->robust_list` is set
(kernel/futex/core.c:1441), and for each entry `handle_futex_death`
(kernel/futex/core.c:1015, Linux v6.18.46) reads the word and, only when
the dying task itself holds it — `(uval & FUTEX_TID_MASK) ==
task_pid_vnr(curr)` (kernel/futex/core.c:1098-1105) — compare-and-exchanges
`FUTEX_OWNER_DIED` (include/uapi/linux/futex.h:167, Linux v6.18.46) into
it (kernel/futex/core.c:1118, :1129); a word another task holds is left
as it is.  That list is installed by `set_robust_list` (99) alone, and 99
has no arm: the dispatcher declines the number before any pointer is
stored, so no run the model admits reaches the exit with a list to walk.
This is the premise `testing/syscall-check/tests/unmodeled_set_robust_list.c`
carries on the Rocq side, `set_robust_list_has_no_arm` in the Cases twin
states it in the shape `tools/check_decline_registers.py` reads, and the
day 99 gains an arm this paragraph is the first thing to revisit.

Second `mm_release` (kernel/fork.c:1424, Linux v6.18.46): its
`put_user(0, tsk->clear_child_tid)` and the futex wake beside it
(kernel/fork.c:1442-1444) run only when the pointer is set AND
`mm_users > 1` (kernel/fork.c:1436-1437, Linux v6.18.46).  Under musl
the pointer is always set — `__init_tp` calls `set_tid_address` (96,
which has an arm) at start-up, as
`testing/syscall-check/tests/musl_abort.c` records — so the count is the
only gate, and it is closed by a model fact and an environment premise
together: no admitted run creates a second `CLONE_VM` holder of the mm
(a thread, a vfork child, an io-wq worker), and `Sys/Kernel/Fork.lean`'s
`set_tid_address_spec` docstring states, as a closed-world premise about
the ENVIRONMENT, that no remote holder taken through `get_task_mm`
(kernel/fork.c:1330, Linux v6.18.46) — a `/proc/<pid>/mem` or
`process_vm_readv` read in flight — is present at the moment
`mm_release` runs.  It argues "no second holder of an mm", not "no
second thread", on purpose.

Three more stores go into memory a syscall with no arm would have mapped.
`do_exit` calls `io_uring_files_cancel` (include/linux/io_uring.h:16-20,
Linux v6.18.46; the call is kernel/exit.c:923), which posts completion
entries into a ring only `io_uring_setup` (425; io_uring/io_uring.c:4019,
Linux v6.18.46) creates; it calls `perf_event_exit_task`
(kernel/events/core.c:14261, Linux v6.18.46; the call is
kernel/exit.c:963), which writes a `PERF_RECORD_EXIT` record into a ring
only `perf_event_open` (241; kernel/events/core.c:13460, Linux v6.18.46)
opens; and dropping the mm runs `exit_aio` from `__mmput`
(kernel/fork.c:1136, Linux v6.18.46), which completes events into a ring
only `io_setup` (0; fs/aio.c:1382, Linux v6.18.46) creates.  The Cases
twin declines all three numbers in the register shape beside 99.  A
sixth, kcov's coverage words, stops at `kcov_task_exit` (kernel/kcov.c:444,
Linux v6.18.46), which `do_exit` calls first (kernel/exit.c:916, Linux
v6.18.46); it needs a debugfs fd the declared image does not offer and
an `ioctl` the arm declines on an fd kind it does not know — an image
premise, not a missing arm.  The day any of those numbers gains an arm,
or the image gains debugfs, this paragraph is the first thing to
revisit.  QEMU's user-mode exit path is not read here; the checker
mirrors Rocq's `check_exit`, and that half of the claim is the spec's to
carry. -/
def check_exit (code : word) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only eff (Z_to_bv 64 0) (with_halted (bv_and code (Z_to_bv 64 255)) m) []

/-! ## The four proofs

Each is one of the five obligations `CheckedArm` demands, stated over the
checker's own arguments so that `Checks/Sys/Table.lean` can supply it by
instantiating `code` with `in_arg i 0`.  The fifth, receptiveness, is the
witness's `exit_witness_ok` below. -/

/-- Soundness on `CheckOk`: what the checker accepts, the spec admits.
Rocq: `Exit.check_exit_sound_ok`.  `check_ret_only_ok_iff` fixes the
effect, the model and the events; the spec is then one `modify` followed
by one `pure`, which `bind_ok0` joins with an empty first event list. -/
theorem check_exit_sound_ok (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_exit code eff m = CheckOk m' evs) : exit_spec code i m (Ok eff m' evs) := by
  unfold check_exit at h
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  unfold exit_spec set_halted ret_only
  exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)

/-- Soundness on `CheckUnmodeled`: the checker never declines, so the
hypothesis is refuted rather than used.  Rocq:
`Exit.check_exit_sound_unmodeled`.  This is the shape a checker with no
gate has; a gated checker discharges the same obligation by showing the
spec declines at the same gate. -/
theorem check_exit_sound_unmodeled (code : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput)
    (h : check_exit code eff m = CheckUnmodeled) : exit_spec code i m Unmodeled :=
  absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Completeness on `Ok`: what the spec admits, the checker accepts.
Rocq: `Exit.check_exit_complete_ok`.  The spec's `modify` is opened by
`bind_modify_iff`, its `pure` by `pure_iff`, and the one `Ok = Ok` that
remains fixes the effect, the model and the events. -/
theorem check_exit_complete_ok (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : exit_spec code i m (Ok eff m' evs)) : check_exit code eff m = CheckOk m' evs := by
  unfold exit_spec set_halted ret_only at h
  have hk := (bind_modify_iff _ _ i m _).mp h
  have hok := (pure_iff _ i _ _).mp hk
  injection hok with heff hm hevs
  subst heff hm hevs
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Completeness on `Unmodeled`: the spec never declines, so the
hypothesis is refuted.  Rocq: `Exit.check_exit_complete_unmodeled`.  The
`modify` is opened as above, and what remains says `Unmodeled` is an
`Ok`. -/
theorem check_exit_complete_unmodeled (code : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect)
    (h : exit_spec code i m Unmodeled) : check_exit code eff m = CheckUnmodeled := by
  exfalso
  unfold exit_spec set_halted ret_only at h
  have hk := (bind_modify_iff _ _ i m _).mp h
  exact absurd ((pure_iff _ i _ _).mp hk) (fun hno => nomatch hno)

/-! ## The witness -/

/-- The progress witness: the one outcome the spec admits, as a value.
Rocq: `Exit.exit_witness`.  It is the accepted triple of `check_exit`
written out, and `exit_witness_ok` below says the spec admits it at every
input and every model — the fifth field of `CheckedArm`, the one that
stops a checker from being vacuously complete over a spec that admits
nothing. -/
def exit_witness (code : word) (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) (with_halted (bv_and code (Z_to_bv 64 255)) m)

/-- Rocq: `Exit.exit_witness_ok`.  One `bind_step` over the `modify` and
the `pure`. -/
theorem exit_witness_ok (code : word) (i : SyscallInput) (m : Model) :
    exit_spec code i m (exit_witness code m) := by
  unfold exit_spec set_halted ret_only exit_witness ret_outcome
  exact bind_step _ _ i m () _ _ (modify_ok _ i m) (pure_ok _ i _)

/-! ## The frame lemma -/

/-- An accepted exit leaves the VM ledger as it found it: the model handed
back is `with_halted` of the model handed in, and `with_halted` rebuilds
the process state alone.  Rocq: `VmMapsDisjoint.check_exit_frame`, stated
here for the reason the file header gives; the arm-level fact
`Checks/VmMapsDisjoint/Arms.lean` derives from it is what the ledger
alternation names. -/
theorem check_exit_frame (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : check_exit code eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_exit at h
  obtain ⟨_, rfl, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  rfl

-- lean-port sentinel: ticket C-Kernel-Exit appends below this line

/-! ## wait4

C-Kernel-Exit's half.  A gated checker, where `exit` above has no gate,
so what the two halves show side by side is what a gate adds to the same
five obligations: `sound_unmodeled` is discharged by declining at the
spec's own gate rather than by refuting the hypothesis, and
`complete_unmodeled` walks the same four `by_cases` the spec's `if`s are
stated in.  Everything under this heading is stated over the checker's
own arguments, as the exit half is, so that the arm the V ticket
registers can supply each by instantiating `upid`, `stat_addr`,
`options` and `rusage` with the row's `pid32 (in_arg i 0)`, `in_arg i 1`,
`waitopts32 (in_arg i 2)` and `in_arg i 3`. -/

set_option linter.unusedVariables false in
/-- wait4: three argument guards and one answer.  `Sys.Kernel.Exit.wait4_spec`
is a caller with no children, so -ECHILD is the whole of what a modeled
call accepts, and every other kernel answer — a reaped pid, WNOHANG's
bare 0, an -EFAULT through `stat_addr` — is REJECTED rather than
accepted.  The argument for each gate is on the spec; what the checker
adds is the acceptor's side of it, read at Linux v6.18.46 (commit
1f99e9ab748f):

- the three argument gates and the children gate decline before any
  effect is looked at, in the spec's order, so a call the spec declines
  is `CheckUnmodeled` whatever the kernel reported for it — the
  `--mutate wait4:ret=4321 -- blocking` case of
  `testing/syscall-check/tests/wait4_spec.c` is that order, observed on
  the Rocq acceptor;
- past the gates the effect must be return-only with the return
  `errno_ret ECHILD`: `__do_wait` (kernel/exit.c:1665-1710, Linux
  v6.18.46) seeds `wo->notask_error = -ECHILD` and, with the
  `PIDTYPE_MAX` walk finding no child, returns that seed at `notask:`,
  so no pid and no 0 can come back; every ledger is empty because
  `kernel_wait4` (kernel/exit.c:1848-1889, Linux v6.18.46) reaches its
  `put_user` only under `ret > 0` and reads nothing from user memory,
  and `SYSCALL_DEFINE4(wait4, ...)` (kernel/exit.c:1907-1918, Linux
  v6.18.46) copies the rusage out under `err > 0` as well.

`stat_addr` is not read here for the same reason it is not read in the
spec: `kernel_wait4`'s copy-out is guarded on `ret > 0`
(kernel/exit.c:1885-1886, Linux v6.18.46), so no -ECHILD touches it.
The `i` argument is Rocq's signature, kept so that the dispatcher row
hands the checker the same arguments as every other arm; nothing here
reads it.  Rocq: `Exit.check_wait4` — which inlines the return-only
match that `check_exit` takes from `check_ret_only`, and the twin
mirrors it as written rather than calling the helper. -/
def check_wait4 (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if bv_unsigned upid ≠ WAIT_ANY32 then CheckUnmodeled
  else if bv_unsigned options ≠ WNOHANG then CheckUnmodeled
  else if !(w_is0 rusage) then CheckUnmodeled
  else if m_has_children m then CheckUnmodeled
  else
    match eff with
    | SyscallEffect.mkEffectU r [] [] [] [] [] =>
      if bv_eqb r (errno_ret ECHILD) then CheckOk m [] else CheckReject
    | _ => CheckReject

/-- Rocq: `Exit.check_wait4_sound_ok`.  Rocq's
`destruct` on each `negb (Z.eqb …)` gate is `split at h` on the
checker's `if`, and the spec's matching `if` is then rewritten with the
case's hypothesis; Rocq's `wait4_empty_ledgers` and the `bv_eqb`
destruct are `split at h` on the effect `match` and on the return test. -/
theorem check_wait4_sound_ok (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs) :
    wait4_spec upid stat_addr options rusage i m (Ok eff m' evs) := by
  unfold check_wait4 at h
  unfold wait4_spec
  split at h
  · simp only [reduceCtorEq] at h
  rename_i h1
  rw [ite_eq_right h1]
  split at h
  · simp only [reduceCtorEq] at h
  rename_i h2
  rw [ite_eq_right h2]
  split at h
  · simp only [reduceCtorEq] at h
  rename_i h3
  rw [ite_eq_right h3]
  split at h
  · simp only [reduceCtorEq] at h
  rename_i h4
  rw [bind_get_model_iff]
  rw [ite_eq_right h4]
  unfold err_ret ret_only
  split at h
  · rename_i r
    split at h
    · rename_i hr
      injection h with hm hevs
      subst hm
      subst hevs
      rw [bv_eqb_eq] at hr
      subst hr
      exact pure_ok _ i _
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-- Rocq: `Exit.check_wait4_sound_unmodeled`. -/
theorem check_wait4_sound_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled) :
    wait4_spec upid stat_addr options rusage i m Unmodeled := by
  unfold check_wait4 at h
  unfold wait4_spec
  split at h
  · rename_i h1
    rw [ite_eq_left h1]
    exact unmodeled_intro i m
  rename_i h1
  rw [ite_eq_right h1]
  split at h
  · rename_i h2
    rw [ite_eq_left h2]
    exact unmodeled_intro i m
  rename_i h2
  rw [ite_eq_right h2]
  split at h
  · rename_i h3
    rw [ite_eq_left h3]
    exact unmodeled_intro i m
  rename_i h3
  rw [ite_eq_right h3]
  rw [bind_get_model_iff]
  split at h
  · rename_i h4
    rw [ite_eq_left h4]
    exact unmodeled_intro i m
  -- no children: the checker answers `CheckOk` or `CheckReject`, never
  -- `CheckUnmodeled`, whatever the effect
  exfalso
  split at h
  · split at h <;> simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-- Rocq: `Exit.check_wait4_complete_ok`.  Rocq's
`destruct` on each gate is `by_cases` here, with the spec's applied `if`
rewritten in the hypothesis and the checker's in the goal. -/
theorem check_wait4_complete_ok (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : wait4_spec upid stat_addr options rusage i m (Ok eff m' evs)) :
    check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs := by
  unfold wait4_spec at h
  unfold check_wait4
  by_cases h1 : bv_unsigned upid ≠ WAIT_ANY32
  · rw [ite_eq_left h1, unmodeled_iff] at h
    simp only [reduceCtorEq] at h
  rw [ite_eq_right h1] at h
  rw [ite_eq_right h1]
  by_cases h2 : bv_unsigned options ≠ WNOHANG
  · rw [ite_eq_left h2, unmodeled_iff] at h
    simp only [reduceCtorEq] at h
  rw [ite_eq_right h2] at h
  rw [ite_eq_right h2]
  by_cases h3 : (!w_is0 rusage) = true
  · rw [ite_eq_left h3, unmodeled_iff] at h
    simp only [reduceCtorEq] at h
  rw [ite_eq_right h3] at h
  rw [ite_eq_right h3]
  rw [bind_get_model_iff] at h
  by_cases h4 : m_has_children m = true
  · -- a caller with a child: the spec's continuation is `unmodeled`,
    -- which accepts no `Ok` at all
    rw [ite_eq_left h4, unmodeled_iff] at h
    simp only [reduceCtorEq] at h
  rw [ite_eq_right h4] at h
  rw [ite_eq_right h4]
  unfold err_ret ret_only at h
  rw [pure_iff] at h
  injection h with heff hm' hevs
  subst heff
  subst hevs
  rw [hm']
  show (if bv_eqb (errno_ret ECHILD) (errno_ret ECHILD) = true then CheckOk m [] else CheckReject)
      = CheckOk m []
  rw [ite_eq_left (bv_eqb_refl _)]

/-- Rocq: `Exit.check_wait4_complete_unmodeled`. -/
theorem check_wait4_complete_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (m : Model) (eff : SyscallEffect)
    (h : wait4_spec upid stat_addr options rusage i m Unmodeled) :
    check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled := by
  unfold wait4_spec at h
  unfold check_wait4
  by_cases h1 : bv_unsigned upid ≠ WAIT_ANY32
  · rw [ite_eq_left h1]
  rw [ite_eq_right h1] at h
  rw [ite_eq_right h1]
  by_cases h2 : bv_unsigned options ≠ WNOHANG
  · rw [ite_eq_left h2]
  rw [ite_eq_right h2] at h
  rw [ite_eq_right h2]
  by_cases h3 : (!w_is0 rusage) = true
  · rw [ite_eq_left h3]
  rw [ite_eq_right h3] at h
  rw [ite_eq_right h3]
  rw [bind_get_model_iff] at h
  by_cases h4 : m_has_children m = true
  · rw [ite_eq_left h4]
  rw [ite_eq_right h4] at h
  -- no children: the continuation is `err_ret ECHILD`, which answers, so
  -- the spec cannot be `Unmodeled` here
  exfalso
  unfold err_ret ret_only at h
  rw [pure_iff] at h
  simp only [reduceCtorEq] at h

/-- The only `CheckOk` the checker gives keeps the model: no branch of
`check_wait4` builds a new one.  Rocq:
`VmMapsDisjoint.check_wait4_frame`, the lemma
`checked_table_preserves_vm`'s alternation names for this arm, which
`check_syscall_preserves_vm_wf` then consumes.  Stated
here for the reason the file header gives; the arm-level fact
`Checks/VmMapsDisjoint/Arms.lean` derives from it — the wait4 arm's
registration's to add, beside `arm_exit_preserves_vm` — is what the
Lean alternation names. -/
theorem check_wait4_frame (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_wait4 at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · split at h
    · injection h with hm _
      rw [hm]
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-- ...and keeps the descriptor subsystem with it: the one `CheckOk` hands
back the model it was handed, so every invariant `Checks/Invariants.lean`
registers over `m_fd` — descriptor-table uniqueness and the pipe
capacity bound today — is discharged by this projection alone, the way
`check_exit_fd_state_frame` discharges them for `exit`.  Same proof as
`check_wait4_frame` with a different projection at the end.  No Rocq
twin: Rocq's invariant is `vm_wf` alone.  The arm-level facts the wait4
arm's registration owes `Checks/Invariants.lean`'s alternation derive
from it. -/
theorem check_wait4_fd_state_frame (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_wait4 at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · simp only [reduceCtorEq] at h
  split at h
  · split at h
    · injection h with hm _
      rw [hm]
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-! ## The wait4 witness

Rocq keeps the witnesses in `Checks/Witness/Kernel/Exit.v`; this file
takes that one, as its header explains.  A witness is the outcome the
progress argument (`Checks/Progress.lean`) shows the spec admits for
every input and model: it is what makes the model never stuck.  For
`wait4` it is the checker's own branch structure read as an outcome —
every gate that makes `check_wait4` answer `CheckUnmodeled` makes the
witness `Unmodeled`, and the one modeled call has exactly one answer. -/

set_option linter.unusedVariables false in
/-- wait4 (260) — witness: `-ECHILD`, the one answer a modeled call admits.
Rocq: `Exit.wait4_witness` (Checks/Witness/Kernel/Exit.v).  The gates are the
spec's, in the spec's order, each declining as `Unmodeled`; past them the
call has no child to report (`m_has_children m = false`), and the spec's
only outcome is `err_ret ECHILD`, which `Checks/Witness/Prelude.lean`'s
`ret_outcome` spells as the effect returning `errno_ret ECHILD` with no
writes and no events.  The status pointer and the input are unused, as
they are in the spec: a call the model answers reports no child, so
nothing is written through `stat_addr`, and no gate reads the input. -/
def wait4_witness (upid stat_addr options rusage : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if bv_unsigned upid ≠ WAIT_ANY32 then Unmodeled
  else if bv_unsigned options ≠ WNOHANG then Unmodeled
  else if !(w_is0 rusage) then Unmodeled
  else if m_has_children m then Unmodeled
  else ret_outcome (errno_ret ECHILD) m

/-- The spec admits the witness.  Rocq: `Exit.wait4_witness_ok`
(Checks/Witness/Kernel/Exit.v).  Rocq's `destruct` on
each gate is `by_cases` with the matching `if` rewritten on both sides
(`ite_eq_left`/`ite_eq_right`, as the checker's proofs above do);
Rocq's `bind_step`/`bind_unmodeled2` over `get_model_ok` is the one
rewrite `bind_get_model_iff` gives, since `get_model` is deterministic;
the last step unfolds `err_ret` down to `pure`, where `ret_outcome` is
the outcome `pure_iff` names. -/
theorem wait4_witness_ok (upid stat_addr options rusage : word) (i : SyscallInput) (m : Model) :
    wait4_spec upid stat_addr options rusage i m
      (wait4_witness upid stat_addr options rusage i m) := by
  unfold wait4_spec wait4_witness
  by_cases h1 : bv_unsigned upid ≠ WAIT_ANY32
  · rw [ite_eq_left h1, ite_eq_left h1]
    exact unmodeled_intro i m
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : bv_unsigned options ≠ WNOHANG
  · rw [ite_eq_left h2, ite_eq_left h2]
    exact unmodeled_intro i m
  rw [ite_eq_right h2, ite_eq_right h2]
  by_cases h3 : (!w_is0 rusage) = true
  · rw [ite_eq_left h3, ite_eq_left h3]
    exact unmodeled_intro i m
  rw [ite_eq_right h3, ite_eq_right h3]
  rw [bind_get_model_iff]
  by_cases h4 : m_has_children m = true
  · rw [ite_eq_left h4, ite_eq_left h4]
    exact unmodeled_intro i m
  rw [ite_eq_right h4, ite_eq_right h4]
  unfold err_ret ret_only ret_outcome
  rw [pure_iff]

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Exit
