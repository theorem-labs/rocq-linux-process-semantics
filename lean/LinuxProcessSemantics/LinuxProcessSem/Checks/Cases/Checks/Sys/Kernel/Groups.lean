-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Groups.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Groups — what the `getgroups` and `setgroups` CHECKERS accept and their WITNESSES name, read off against Linux

Pins over `Checks.Sys.Kernel.Groups`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Groups.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Groups.v`: the two
checkers first, then the two witnesses, and last the `V_Kernel_Groups`
section, which pins both through `checked_table`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ.
Each `kernel:` pin in it rests on a claim about what the kernel does —
the answer a checker accepts or refuses, the outcome a witness names, or
the kernel fact a decline stands on — with the kernel source beside it;
each `model:` pin is a claim about this tree's own definitions — a table
lookup, the register an input carries, or closed values shown to satisfy
a hypothesis — and cites no kernel source.  Every kernel line below was
read at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT A CHECKER PIN IS.  `Checks/Cases/Kernel/Groups.lean` states, for each
decision of the spec, an `iff` over every outcome and refutes the lie a
kernel could not tell.  The checker is that spec made executable — the
four `_sound_`/`_complete_` lemmas beside it say the two agree on every
input — so a checker pin here does not restate those `iff`s.  It hands
the checker what a trace reaches it with — the effect, and of the input
what that checker is passed: `getgroups`'s size word, nothing for
`setgroups`, and the whole input record where a pin goes through
`check_syscall` — closed, or quantified over a size, a pointer, a model
or the effect itself, and states the verdict: `CheckOk` on the kernel's
answer, `CheckReject` on the lie or, where a pin says so, on an answer
qemu-user gives that the arm refuses, and `CheckUnmodeled` where the
spec declines.  That is the question a trace asks, and the one the four
lemmas cannot:
soundness and completeness are biconditionals between two definitions of
this tree, and hold as well of a wrong spec beside a matching wrong
checker.  Only a statement about a value named from outside tells the two
apart.  Each `kernel:` pin on a checker below is a verdict on one.  Each
`kernel:` pin on a witness — the `TheWitnesses` section, and the three
`_witnessed_` pins that end `V_Kernel_Groups` — states no verdict: it
names the outcome the witness gives, at a closed fixture or over the
sizes and models its hypotheses allow, and `getgroups_witness_ok` and
`setgroups_witness_ok`, and through the table `receptive_checked`
(`Checks/Progress.lean`), hold the spec to admitting that outcome there.
Where the spec answers, the outcome named is the kernel's answer, and
the pin catches a spec that lost it; where the spec declines, it is
`Unmodeled`, and the pin catches a spec that stopped declining.  Neither
kind refutes a lie.

WHAT THIS RESTATES.  Rocq keeps the worked examples for these checkers
in `Checks/Cases/Kernel/Groups.v`, beside the spec's, as `Example`s over
`check_syscall`.  Each is restated here on `check_getgroups
gidsetsize eff m` or `check_setgroups eff m` directly — the body of the
arm the checked table holds for 158 and 159 — and is one line over
`check_syscall`, which the `V_Kernel_Groups` section at the end of this
file states for nine of the ten:
`getgroups_size_zero_reports_the_count` is
`check_getgroups_size_zero_accepts_the_count`;
`getgroups_wrong_count_rejected` is
`check_getgroups_size_zero_rejects_a_wrong_count`;
`getgroups_negative_size_is_einval` is
`check_getgroups_negative_size_accepts_einval_on_every_model` with
`check_getgroups_size_sign_is_the_low_words`;
`getgroups_size_truncates_to_int` is
`check_getgroups_size_truncates_to_int`;
`getgroups_size_too_small_is_einval_not_efault` is the `TooSmall` section;
`getgroups_empty_list_returns_zero_without_touching_the_array` is the
`EmptyList` section; `getgroups_writing_path_fails_closed` is the
`WritingPath` section — its two declining sizes, 3 and 64, are two of
that pin's conjuncts — with its two accepting conjuncts in `Count` and
`TooSmall`; `setgroups_refuses_before_it_reads_an_argument` is
`check_setgroups_unprivileged_accepts_eperm` with
`check_setgroups_unprivileged_rejects_the_lies`; and
`privileged_setgroups_fails_closed` is `check_setgroups_privileged_declines`.
The tenth, `setgid_keeps_the_supplementary_group_list`, chains `setgid`
(144) through `check_syscall` into a `getgroups` count read: a dispatcher
fact over two arms, restatable only once both are registered, and the
table has no row for 144 yet, so it waits on that registration.
What a restatement loses is the register file — which of a0 and a1 an arm
reads, and where the table sends each number — and the `V_Kernel_Groups`
section pins those.
That list is prose: nothing reads it, and it goes stale on a rename with
nothing going red.  Its mechanical home is the coverage header
`check_lean_cases_parity.py` reads, on `Checks/Cases/Kernel/Groups.lean`,
the Lean mirror of the Rocq file that holds the ten.  This file mirrors
no Rocq Cases file — Rocq keeps no worked cases over these checkers apart
from the ten — so it carries no such header, and that checker would
refuse one here; carrying the ten in the mirror's header is a follow-up
on that file.

NO DEFAULT PROBE VERDICT IS ABOUT THIS FILE.  Under the default `--model
rocq` the harness runs the EXTRACTED ROCQ model (`run-tests.sh` extracts
it through `harness-env.sh`'s `checker_build`), so a probe's verdict is
about the Rocq checker.  The Lean checker meets a trace in three places:
the replay of `lean/LpsRunner/Replay.lean`, which folds
`check_syscall_for_run` over `checked_table` and so reaches
`check_getgroups` and `check_setgroups` since the registration;
`run-tests.sh --model lean`, which holds a live run to the Lean checker's
answers as well (`testing/syscall-check/main.ml`, the `--model` section);
and `Checks/Cases/Oracle.lean`'s `oracle_fold`, which folds only the
records before a row through `check_syscall_for_run` (a row's own call
goes to `syscall_spec` through `spec_at`) and today folds mmap records
only, so it reaches neither 158 nor 159 until a row whose prefix holds
one of them lands.  The probe cases that state the same facts of the
Rocq side are `testing/syscall-check/tests/getgroups.c` — `count` with
its `ret+1`, `ret=-EINVAL` and `getgroups#2:smuggle-write` rejects, and
`negative` with its two `ret=0` rejects; its `garbage64` (`ret=-EFAULT`)
and `big70000` (`ret=-EINVAL`) rejects carry unnumbered selectors, so
they land on occurrence 1, `getgroups(0, 0)`, and test the size-0 count
rather than the empty list or the missing upper bound
(`linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md`) — and
`creds_spec.c`'s five `setgroups-*` cases with their `ret=0`,
`ret=-EINVAL` and `ret=-EFAULT` rejects, three of which — the
`ret=-EINVAL` on `setgroups-neg` and on `setgroups-big`, and the
`ret=-EFAULT` on `setgroups-fault` — refuse qemu-user's own answers at
those shapes (`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`).  Each
`kernel:` pin below cites kernel source and not the probe, because what
it rests on is a claim about Linux, and a probe verdict, under `--model
lean` as under the default, is one run of the pinned kernel, which
settles nothing about the supported set; the `model:` pins state this
tree's own table, registers and fixtures, and cite no kernel source.

WHAT IS PINNED BEYOND THE SPEC'S FIXTURES.  The ORDER at the checker over
a symbolic size: a negative size is -EINVAL on EVERY model, the one the
spec would otherwise decline included, so the checker's `NGROUPS_MAX`
decline sits behind the sign test.  (The kernel's `getgroups` has no such
bound at all; the decline sits where the kernel first reads the list,
after its own sign test.)

HOW THE PINS ARE PROVED.  Each symbolic one opens with `generalize sint32
gidsetsize = n`, for the reason `Checks/Sys/Kernel/Groups.lean` gives: a
case split on the `sint32` decision of a symbolic word does not
terminate, and one on an opaque `n` does.  The closed `getgroups` pins
are not `rfl` for the same reason one step removed: the checker is a
function and on a fixture it computes, but the unifier behind `rfl`
walks into that decision even at a literal size and does not come back.
They run `check_norm` instead — one `simp +decide only` pass that opens the checker
and the acceptor and DECIDES the closed gates, which is the evaluation
`sys_norm` performs on the spec pins for the same sizes, then `sys_norm`
for whatever fixture read is left; the closed witness pins run
`witness_norm`, the same pass over the witnesses.  The `setgroups` pins
have no `sint32` in them and stay `rfl`.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What a
`kernel:` pin proves is that this checker, or this witness, agrees with a
named line of Linux; what a `model:` pin proves is a fact about this
tree's own definitions. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Groups

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-- Evaluate a closed call of one of the two checkers: open the checker
and the acceptor, decide every closed gate, read the fixture model with
the `sys_simp` set, and finish with `sys_norm` if a read is left.  The
header says why this and not `rfl`. -/
macro "check_norm" : tactic =>
  `(tactic| (simp +decide only [check_getgroups, check_setgroups, check_ret_only, sys_simp,
      ↓reduceIte]; first | done | sys_norm))

section NegativeSize

/-! ## `getgroups` (158): a negative size is -EINVAL, and it is decided FIRST

`if (gidsetsize < 0) return -EINVAL;` (kernel/groups.c:166-167, Linux
v6.18.46) runs before `cred->group_info` is read at :170 and before the
`if (gidsetsize)` block at :171.  The register value 0xffffffff is
`gidsetsize = -1` after the `int` cast, and 0x80000000 is `INT_MIN`. -/

/-- A negative size is accepted with -EINVAL on EVERY model, the one with
more than `NGROUPS_MAX` stored groups included, because the kernel's sign
test runs before the group list is read.  The model is untouched and no
event is emitted.  Stated over an arbitrary model so that it is the ORDER
of the checker's two guards that is pinned, not one fixture's answer: a
checker that tested the list length first would decline here.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_negative_size_accepts_einval_on_every_model (m : Model) :
    check_getgroups 4294967295 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  have hneg : sint32 4294967295 < 0 := by decide
  unfold check_getgroups
  dsimp only
  simp only [hneg, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- `INT_MIN` is negative too: the cast is signed.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_int_min_accepts_einval :
    check_getgroups 2147483648 (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by check_norm

/-- The lie a faulting kernel would tell: -EFAULT at a negative size is
refused, because the store `groups_to_user` would fault on (:47-48) is
never reached from :166.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_negative_size_rejects_efault :
    check_getgroups 4294967295 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by check_norm

/-- …and a success at a negative size is refused, whether it reports the
count or nothing.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_negative_size_rejects_success :
    check_getgroups 4294967295 (mkEffect 3 [] []) demo_model = CheckReject
      ∧ check_getgroups 4294967295 (mkEffect 0 [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and the right errno with a store beside it is refused: -EINVAL at
:166-167 writes nothing, so an effect carrying a four-byte store at the
`grouplist` pointer is not the kernel's.  The pointer is symbolic: the
verdict does not read it.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_negative_size_rejects_a_write (grouplist : word) :
    check_getgroups 4294967295 (mkEffect (errno_ret EINVAL) [(grouplist, [0, 0, 0, 0])] [])
        demo_model = CheckReject := by check_norm

/-- The errno is the WHOLE register's.  `__do_sys_getgroups` returns
`long` and `__se_sys_getgroups` hands that `long` back unchanged
(arch/riscv/include/asm/syscall_wrapper.h:82-93, Linux v6.18.46), and
`syscall_handler` stores it whole — `regs->a0 = fn(regs)`
(arch/riscv/include/asm/syscall.h:112) — so -EINVAL in a0 is
0xffffffffffffffea and never its low word, 0x00000000ffffffea.  Every
other lie in this file differs from the kernel's answer in the low word
as well; this is the one a checker comparing only the low 32 bits of a0
would take for -EINVAL, and it is refused.
kernel: kernel/groups.c:getgroups; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getgroups_negative_size_rejects_a_truncated_errno :
    check_getgroups 4294967295 (mkEffect 4294967274 [] []) demo_model = CheckReject := by
  check_norm

end NegativeSize

section Count

/-! ## The count: `gidsetsize = 0`

`if (gidsetsize)` (kernel/groups.c:171, Linux v6.18.46) skips the whole
block, so the call returns `i = cred->group_info->ngroups` (:170,
:181-182) and the `grouplist` pointer is not touched.  `demo_groups` holds
three gids, so the count is 3. -/

/-- Size 0 on `demo_model`: the count, 3, with nothing written, no event
and the model unchanged, is accepted.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_zero_accepts_the_count :
    check_getgroups 0 (mkEffect 3 [] []) demo_model = CheckOk demo_model [] := by check_norm

/-- THE COUNT IS A LENGTH: one more, one fewer, and a member of the list
in place of its length (1002 is `demo_groups`' second gid) are all
refused.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_zero_rejects_a_wrong_count :
    check_getgroups 0 (mkEffect 4 [] []) demo_model = CheckReject
      ∧ check_getgroups 0 (mkEffect 2 [] []) demo_model = CheckReject
      ∧ check_getgroups 0 (mkEffect 1002 [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Size 0 never fails — :171 skips the only block that can — so -EINVAL
at size 0 is refused.  (A POSITIVE size can: -EINVAL at :172-175 when it
is too small, -EFAULT at :177 on the writing path.)
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_zero_rejects_einval :
    check_getgroups 0 (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject := by
  check_norm

/-- Size 0 WRITES NOTHING: the count beside a four-byte store at the
pointer is refused, since :171 never enters the block `groups_to_user` is
called from.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_zero_rejects_a_write (grouplist : word) :
    check_getgroups 0 (mkEffect 3 [(grouplist, [0, 0, 0, 0])] []) demo_model
      = CheckReject := by check_norm

/-- …and the count is the whole register's too: `return i` widens the
`int` to the `long` `__do_sys_getgroups` returns, and `syscall_handler`
stores it whole (arch/riscv/include/asm/syscall.h:112, Linux v6.18.46),
so 3 in a0 is 0x0000000000000003; 0xffffffff00000003 — the count with
every high bit set, which a checker comparing the low word alone would
accept — is refused.
kernel: kernel/groups.c:getgroups; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getgroups_size_zero_rejects_a_count_with_the_high_word_set :
    check_getgroups 0 (mkEffect 18446744069414584323 [] []) demo_model = CheckReject := by
  check_norm

/-- a0 = 2^32 is `gidsetsize = 0` after the `int` cast — `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) narrows the register to the
declared `int` before the body runs — so it is the count that is
accepted, and not the declining writing path a checker comparing the
whole register would take.
kernel: kernel/groups.c:getgroups; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem check_getgroups_size_truncates_to_int :
    check_getgroups 4294967296 (mkEffect 3 [] []) demo_model = CheckOk demo_model [] := by
  check_norm

/-- On a process with no supplementary groups the count is 0.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_zero_accepts_zero_on_an_empty_list :
    check_getgroups 0 (mkEffect 0 [] []) no_groups_model = CheckOk no_groups_model [] := by
  check_norm

/-- Size 0 beside anything but a bare return is refused: -EFAULT (the
`put_user` at :47 is never reached once :171 skips the block), a copy-in
ledger entry (the kernel reads no user memory on this path), a zero-fill,
an unmap and a pre-effect copy — every ledger of `SyscallEffect` but the
stores, each offered alone.  Only `eff_writes` is refused above; a
checker comparing the return and the stores alone passes those pins and
fails these.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_size_zero_rejects_efault_and_other_ledgers (p : word) :
    check_getgroups 0 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
      ∧ check_getgroups 0 (SyscallEffect.mkEffectU 3 [] [] [] [] [(p, 4)]) demo_model = CheckReject
      ∧ check_getgroups 0 (SyscallEffect.mkEffectU 3 [] [(p, 4)] [] [] []) demo_model = CheckReject
      ∧ check_getgroups 0 (SyscallEffect.mkEffectU 3 [] [] [(p, 4096)] [] []) demo_model
          = CheckReject
      ∧ check_getgroups 0 (SyscallEffect.mkEffectU 3 [] [] [] [MemCopy.mkCopy p p 4] [])
          demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The sign is the LOW word's.  `__SC_CAST` (include/linux/syscalls.h:132,
Linux v6.18.46) narrows the register to the declared `int` before the body
runs, so a0 = 2^64 − 1 (Rocq's fixture, every bit set) and a0 = 2^33 − 1
(bit 32 alone above the word) are both −1 (-EINVAL), a0 = 0xffffffff00000000
is 0 (the count) and a0 = 0xffffffff00000005 is 5 (0 on the empty list).  A
checker reading the sign of the whole register, or the low word unsigned,
answers them differently.
kernel: kernel/groups.c:getgroups; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem check_getgroups_size_sign_is_the_low_words :
    check_getgroups 18446744073709551615 (mkEffect (errno_ret EINVAL) [] []) demo_model
        = CheckOk demo_model []
      ∧ check_getgroups 8589934591 (mkEffect (errno_ret EINVAL) [] []) demo_model
        = CheckOk demo_model []
      ∧ check_getgroups 18446744069414584320 (mkEffect 3 [] []) demo_model = CheckOk demo_model []
      ∧ check_getgroups 18446744069414584325 (mkEffect 0 [] []) no_groups_model
          = CheckOk no_groups_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end Count

section TooSmall

/-! ## A size too small: -EINVAL BEFORE any store

`if (i > gidsetsize) { i = -EINVAL; goto out; }` (kernel/groups.c:172-175,
Linux v6.18.46) fires before `groups_to_user` is called at :176. -/

/-- `getgroups(2, …)` and `getgroups(1, …)` on three groups: -EINVAL,
model untouched, accepted.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_too_small_accepts_einval :
    check_getgroups 2 (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
      ∧ check_getgroups 1 (mkEffect (errno_ret EINVAL) [] []) demo_model
          = CheckOk demo_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- -EFAULT is refused at a size too small: the store the pointer would
fault on is never attempted, because :172-175 returns first.  So is the
count: `i` reaches :182 holding the count at size 0 and after a
successful copy on the writing path, never on this one, where :172-175
has already set `i = -EINVAL` before the `goto out`.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_size_too_small_rejects_efault_and_the_count :
    check_getgroups 2 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
      ∧ check_getgroups 2 (mkEffect 3 [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Too small beside the other lies: a success — 0, and the 2 a kernel
that truncated the list to fit would return, with or without the two gids
it would have stored (:172-175 fails the call before any store) — and
-EINVAL with a store beside it (nothing is written before the `goto out`).
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem check_getgroups_size_too_small_rejects_success_and_a_write (grouplist : word) :
    check_getgroups 2 (mkEffect 0 [] []) demo_model = CheckReject
      ∧ check_getgroups 2 (mkEffect 2 [] []) demo_model = CheckReject
      ∧ check_getgroups 2 (mkEffect 2 [(grouplist, [0, 0, 0, 0, 0, 0, 0, 0])] []) demo_model
          = CheckReject
      ∧ check_getgroups 2 (mkEffect (errno_ret EINVAL) [(grouplist, [0, 0, 0, 0])] []) demo_model
          = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end TooSmall

section EmptyList

/-! ## The zero-length list: a positive size at zero groups answers 0

With `gidsetsize > 0` and no supplementary groups, control enters the
block at kernel/groups.c:171 and `groups_to_user` (kernel/groups.c:37-51,
Linux v6.18.46) runs its loop zero times, returning 0 at :50 without a
single `put_user`.  `Checks/Cases/Kernel/Groups.lean`, under "The
zero-length list: the subtle arm", says what qemu-user answers instead and
names the `bugs/` entry;
the checker admits Linux's answer alone, and the two refutations below are
the checker's side of that. -/

/-- ANY nonnegative size at zero groups: 0, nothing written, accepted.
Stated over the size, since the claim is about the loop's trip count and
not about one size.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_empty_list_accepts_zero (gidsetsize : word)
    (h : 0 ≤ sint32 gidsetsize) :
    check_getgroups gidsetsize (mkEffect 0 [] []) no_groups_model
      = CheckOk no_groups_model [] := by
  unfold check_getgroups
  dsimp only
  generalize sint32 gidsetsize = n at h ⊢
  have hneg : ¬ n < 0 := by omega
  have hlen : ((m_creds no_groups_model).cr_groups.length : Int) = 0 := rfl
  have hmax : ¬ NGROUPS_MAX < (0 : Int) := by decide
  simp only [hneg, hlen, hmax, ↓reduceIte]
  by_cases hzero : n = 0
  · simp only [hzero, ↓reduceIte]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hzero, ↓reduceIte]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- `getgroups(64, <garbage>)` and `getgroups(70000, buf)` at zero groups:
0.  The second says Linux has no upper bound on `gidsetsize` —
`SYSCALL_DEFINE2(getgroups, ...)` never compares the size against
`NGROUPS_MAX`; of the syscalls riscv64 builds only `setgroups` does
(kernel/groups.c:205-206 — the 16-bit `setgroups16` tests it too, at
kernel/uid16.c:184, but riscv selects no `HAVE_UID16` and that file is
not built).
kernel: kernel/groups.c:getgroups,setgroups@v6.18.46 -/
example :
    check_getgroups 64 (mkEffect 0 [] []) no_groups_model = CheckOk no_groups_model []
      ∧ check_getgroups 70000 (mkEffect 0 [] []) no_groups_model
          = CheckOk no_groups_model [] :=
  ⟨check_getgroups_empty_list_accepts_zero _ (by decide),
   check_getgroups_empty_list_accepts_zero _ (by decide)⟩

/-- -EFAULT at zero groups is refused (a kernel validating the
destination before a copy of nothing is not Linux: `groups_to_user`'s
validation is the per-element `put_user` at :47, and the loop runs no
iteration), and so is -EINVAL at 70000 (range-checking a size Linux's
`getgroups` does not range-check).  Both are qemu-user's answers
(`linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md`).
The arm admits Linux alone.  The fix that entry describes declines any
size above `NGROUPS_MAX` at every destination, so the second conjunct
flips to `CheckUnmodeled` the day it moves.  The first names no
destination, since the checker reads none today; that entry says what
the fix does with one.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_empty_list_rejects_efault_and_einval :
    check_getgroups 64 (mkEffect (errno_ret EFAULT) [] []) no_groups_model = CheckReject
      ∧ check_getgroups 70000 (mkEffect (errno_ret EINVAL) [] []) no_groups_model
          = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A wrong nonzero return at zero groups is refused: the size handed in,
and a count of one.  `i` is the count read at :170, 0 here; the loop at
:44-49 runs no iteration, so `groups_to_user` returns 0 at :50, the
-EFAULT assignment at :177 is skipped, and :182 returns `i` — not the
size, and not a count the list does not have.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_empty_list_rejects_a_wrong_count :
    check_getgroups 64 (mkEffect 64 [] []) no_groups_model = CheckReject
      ∧ check_getgroups 64 (mkEffect 1 [] []) no_groups_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The empty list beside a store is refused, in the shape a wrong port
would produce (four bytes at the pointer) and the degenerate one (an empty
store at the pointer): the loop at :44-49 runs `ngroups = 0` times, nothing
reaches `put_user`, and the kernel's effect carries no write at all.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_empty_list_rejects_a_write (grouplist : word) :
    check_getgroups 64 (mkEffect 0 [(grouplist, [0, 0, 0, 0])] []) no_groups_model = CheckReject
      ∧ check_getgroups 64 (mkEffect 0 [(grouplist, [])] []) no_groups_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- One supplementary group: `demo_model`'s credentials with the list cut
to `[demo_gid]`.  The fixtures this file imports hold zero groups or
three, and neither tells `ngroups == 0` — the loop at kernel/groups.c:44
(Linux v6.18.46) running no iteration — from `ngroups <= 1` or `<= 2`: a checker whose
empty-list arm fired up to one group answers as this one does on every
pin above.  This fixture sits on that boundary. -/
def one_group_model : Model :=
  with_creds { demo_creds with cr_groups := [demo_gid] } demo_model

/-- One group at size 1 is the WRITING path — `1 > 1` at :172 is false and
`groups_to_user` stores the one gid at :47 — so the checker declines for
every effect, where a checker whose empty-list arm fired at `ngroups <= 1`
would accept a return of 0 with nothing stored: a wrong accept on a state
Linux builds.  So is size 64 on the same model; size 0 is the count, 1.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_one_group_is_not_the_empty_list (eff : SyscallEffect) :
    check_getgroups 1 eff one_group_model = CheckUnmodeled
      ∧ check_getgroups 64 eff one_group_model = CheckUnmodeled
      ∧ check_getgroups 0 (mkEffect 1 [] []) one_group_model = CheckOk one_group_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

end EmptyList

section OverNgroupsMax

/-! ## More than `NGROUPS_MAX` stored groups: declined, but BEHIND the sign test

`setgroups` refuses a list longer than `NGROUPS_MAX` (kernel/groups.c:205-206,
Linux v6.18.46), so a process holding one is a state Linux never builds; the
spec declines to answer `getgroups` on such a model rather than invent the
count, and the checker declines with it.  `NGROUPS_MAX` is 65536
(include/uapi/linux/limits.h:7, Linux v6.18.46). -/

/-- Any nonnegative size, on any model whose stored list is longer than
`NGROUPS_MAX`, is `CheckUnmodeled` for EVERY offered effect: the checker
neither accepts nor rejects, it declines.  (A negative size on the same
model is -EINVAL, accepted: `check_getgroups_negative_size_accepts_einval_on_every_model`.)
kernel: kernel/groups.c:setgroups; include/uapi/linux/limits.h:NGROUPS_MAX@v6.18.46 -/
theorem check_getgroups_over_ngroups_max_declines (gidsetsize : word)
    (h : 0 ≤ sint32 gidsetsize) (m : Model)
    (hm : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)) (eff : SyscallEffect) :
    check_getgroups gidsetsize eff m = CheckUnmodeled := by
  unfold check_getgroups
  dsimp only
  generalize sint32 gidsetsize = n at h ⊢
  have hneg : ¬ n < 0 := by omega
  simp only [hneg, hm, ↓reduceIte]

/-- THE GUARD IS STRICT, as `setgroups`' is: a list of exactly `NGROUPS_MAX`
entries is one the kernel installs, so `getgroups(0, …)` on it is
answered with that count, and accepted.
kernel: kernel/groups.c:setgroups,getgroups@v6.18.46 -/
theorem check_getgroups_at_ngroups_max_accepts_the_count (m : Model)
    (hm : (((m_creds m).cr_groups).length : Int) = NGROUPS_MAX) :
    check_getgroups 0 (mkEffect (Z_to_bv 64 NGROUPS_MAX) [] []) m = CheckOk m [] := by
  have h0 : sint32 0 = 0 := by decide
  unfold check_getgroups
  dsimp only
  rw [h0, hm]
  simp only [Int.lt_irrefl, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The two hypotheses above are SATISFIABLE by values of this tree: a
`Creds` holding exactly `NGROUPS_MAX` zeros, and one holding one more,
carried into a `Model` by `with_creds`.  Without this the two pins would
close as well over an unsatisfiable hypothesis; `cr_groups : List word`
is unbounded today, and this is what goes red the day it is bounded.
model: existence witnesses for the two hypotheses above, closed values of the model's own `Creds`. -/
example (eff : SyscallEffect) :
    check_getgroups 0 eff
        (with_creds { demo_creds with cr_groups := List.replicate 65537 0 } demo_model)
      = CheckUnmodeled
    ∧ check_getgroups 0 (mkEffect (Z_to_bv 64 NGROUPS_MAX) [] [])
        (with_creds { demo_creds with cr_groups := List.replicate 65536 0 } demo_model)
      = CheckOk (with_creds { demo_creds with cr_groups := List.replicate 65536 0 } demo_model)
          [] :=
  ⟨check_getgroups_over_ngroups_max_declines _ (by decide) _
      (by show NGROUPS_MAX < ((List.replicate 65537 (0 : word)).length : Int)
          simp only [List.length_replicate]; decide) eff,
   check_getgroups_at_ngroups_max_accepts_the_count _
      (by show ((List.replicate 65536 (0 : word)).length : Int) = NGROUPS_MAX
          simp only [List.length_replicate]; rfl)⟩

end OverNgroupsMax

section WritingPath

/-! ## The writing path is DECLINED

`gidsetsize >= ngroups > 0` reaches the call at kernel/groups.c:176 (Linux
v6.18.46) of `groups_to_user` (kernel/groups.c:37-51, Linux v6.18.46),
which stores `ngroups` 4-byte gids through the pointer;
the spec declines that path (`Checks/Cases/Kernel/Groups.lean`, under
"The writing path is DECLINED", says why), and the checker declines with
it, whatever effect a trace offers. -/

/-- The exact size, the next one, Rocq's roomy 64 and `INT_MAX` on three
groups: declined for every effect.  Nothing is accepted and nothing is
rejected on this path — a trace reaching it stops the check rather than
passing or failing it.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem check_getgroups_writing_path_declines (eff : SyscallEffect) :
    check_getgroups 3 eff demo_model = CheckUnmodeled
      ∧ check_getgroups 4 eff demo_model = CheckUnmodeled
      ∧ check_getgroups 64 eff demo_model = CheckUnmodeled
      ∧ check_getgroups 2147483647 eff demo_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end WritingPath

section Setgroups

/-! ## `setgroups` (159): -EPERM first, and the privileged path declined

`if (!may_setgroups()) return -EPERM;` (kernel/groups.c:203-204, Linux
v6.18.46) is the first statement of `SYSCALL_DEFINE2(setgroups, ...)`,
ahead of the `NGROUPS_MAX` test at :205-206 and of every read through the
pointer.  `may_setgroups` (:185-191) asks `ns_capable_setid`
(kernel/capability.c:398-401, Linux v6.18.46) for `CAP_SETGID` in the
caller's EFFECTIVE CAPABILITY SET — no uid is read — and
`userns_may_setgroups` (kernel/user_namespace.c:1293-1307, Linux
v6.18.46) about the namespace; the model reads
the pair as the effective uid being 0 (`State.creds_privileged`), which
is exact only under the standing assumptions that predicate's docstring
names: in security/commoncap.c (Linux v6.18.46) `handle_privileged_root`
(:848-849) marks an exec whose effective uid is 0 `effective` and
`cap_bprm_creds_from_file` (:970-971) copies the permitted set into the
effective set on that mark; `cap_emulate_setxuid` (security/commoncap.c,
Linux v6.18.46) clears the effective set when the effective uid leaves 0
(:1132-1133) and restores it from the permitted set when the effective
uid returns to 0 (:1134-1135), so under those assumptions the bit tracks
`euid = 0` across every set*uid the model admits, `setuid` and
`setresuid` included. -/

/-- Unprivileged: -EPERM, model untouched, accepted.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem check_setgroups_unprivileged_accepts_eperm :
    check_setgroups (mkEffect (errno_ret EPERM) [] []) demo_model = CheckOk demo_model [] := rfl

/-- The lies: -EINVAL (the size test at :205 is never reached), -EFAULT
(no read through the pointer happens before :203 returns) and a success
are all refused on an unprivileged caller.  -EINVAL and -EFAULT are
qemu-user's answers at three argument shapes — a negative size, a size
above `NGROUPS_MAX`, a positive size whose list is unreadable
(`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`).  The arm admits
Linux alone at those three shapes.  The fix that entry describes
declines all three — the third at the low end of the entry-stack band
only if it does not leave that band open, which the entry allows — and,
on its second route, every list that meets a writable LOAD segment too,
`setgroups-one`'s readable one among them; so once the arm moves and
the checker reads its arguments, these verdicts become `CheckUnmodeled`
at every call the fixed arm declines and stay `CheckReject` wherever it
answers, which in a band left open still refuses qemu-user's -EFAULT.
kernel: kernel/groups.c:setgroups,groups_from_user@v6.18.46 -/
theorem check_setgroups_unprivileged_rejects_the_lies :
    check_setgroups (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject
      ∧ check_setgroups (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
      ∧ check_setgroups (mkEffect 0 [] []) demo_model = CheckReject := ⟨rfl, rfl, rfl⟩

/-- -EPERM beside a store is refused: `setgroups` never writes to user
memory on any path, and least of all on the one that returns at :204.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem check_setgroups_unprivileged_rejects_a_write (grouplist : word) :
    check_setgroups (mkEffect (errno_ret EPERM) [(grouplist, [0, 0, 0, 0])] []) demo_model
      = CheckReject := rfl

/-- Privileged — root, and a set-user-ID-root process whose REAL uid is not
0 — is declined for every effect: the installing path is unmodeled, and
the checker neither accepts nor rejects on it.  The two fixtures together
say the checker keys on the effective uid — the model's stand-in for the
`CAP_SETGID` bit `may_setgroups` tests, which a set-user-ID-root exec
raises (`handle_privileged_root`, security/commoncap.c:848-849, marks the
exec `effective`; `cap_bprm_creds_from_file`, :970-971, then copies the
permitted set into the effective set) — and not on the real one.
kernel: kernel/groups.c:setgroups,may_setgroups; security/commoncap.c:handle_privileged_root,cap_bprm_creds_from_file@v6.18.46 -/
theorem check_setgroups_privileged_declines (eff : SyscallEffect) :
    check_setgroups eff root_model = CheckUnmodeled
      ∧ check_setgroups eff setuid_root_model = CheckUnmodeled := ⟨rfl, rfl⟩

/-- Root that has dropped its effective uid is unprivileged again —
`cap_emulate_setxuid` (security/commoncap.c) clears the effective
capability set on the euid 0 → non-0 transition — so -EPERM, accepted.
The real uid is 0 here, so a checker keyed on it would decline.
kernel: kernel/groups.c:setgroups,may_setgroups; security/commoncap.c:cap_emulate_setxuid@v6.18.46 -/
theorem check_setgroups_dropped_euid_accepts_eperm :
    check_setgroups (mkEffect (errno_ret EPERM) [] []) dropped_euid_model
      = CheckOk dropped_euid_model [] := rfl

/-- The lies on that model are refused too: a success and -EINVAL.
`may_setgroups` (:185-191) asks `ns_capable_setid` (kernel/capability.c:398-401)
for `CAP_SETGID` in the effective CAPABILITY SET, which the model reads
as the effective uid (`State.creds_privileged`); a real uid of 0 buys
nothing at :203, so the installing path is not reached and the size test
at :205 is not either.  Without this pin a checker that admitted every
effect on this model would pass every pin above; one that declined here
already fails the pin before this.  The -EINVAL verdict is right for
Linux alone: qemu-user answers -EINVAL to a size negative as an `int` or
above `NGROUPS_MAX` whatever the credentials, before the host call in
which `may_setgroups` runs
(linux-user/syscall.c:12620-12621, QEMU v11.1.1;
`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`).
kernel: kernel/groups.c:setgroups,may_setgroups; kernel/capability.c:ns_capable_setid@v6.18.46 -/
theorem check_setgroups_dropped_euid_rejects_the_lies :
    check_setgroups (mkEffect 0 [] []) dropped_euid_model = CheckReject
      ∧ check_setgroups (mkEffect (errno_ret EINVAL) [] []) dropped_euid_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Effective uid 0 with real AND saved uid `demo_uid`: a set-user-ID-root
process after `setresuid(-1, -1, demo_uid)`.  The two privileged fixtures
above both carry a saved uid of 0, so between them and `dropped_euid_model`
a checker keyed on `euid == 0 && suid == 0` is not told from one keyed on
the effective uid alone; this fixture has the effective uid alone. -/
def euid_only_root_model : Model :=
  with_creds { demo_creds with cr_euid := 0 } demo_model

/-- …and it is privileged: `cap_emulate_setxuid` (security/commoncap.c)
clears the effective set when the EFFECTIVE uid leaves 0 (:1132-1133) and
no rule of it touches the set while the effective uid stays 0, so a
`setresuid` that moves the saved uid alone leaves it raised,
`may_setgroups()` holds and the installing path is reached — declined for
every effect, where a checker keyed on the saved uid as well would accept
-EPERM, a return Linux does not give here.
kernel: kernel/groups.c:setgroups,may_setgroups; security/commoncap.c:cap_emulate_setxuid@v6.18.46 -/
theorem check_setgroups_euid_only_root_declines (eff : SyscallEffect) :
    check_setgroups eff euid_only_root_model = CheckUnmodeled := rfl

/-- -EPERM beside a copy-in is refused: `may_setgroups` is tested at
:203-204 before `groups_from_user` (:211) reads anything, so Linux's
refused call has an empty copy-in ledger.  -ENOMEM is refused too:
`groups_alloc` (:208-210) is not reached by an unprivileged caller.
Both verdicts are right for Linux alone: at a size from 1 to
`NGROUPS_MAX` qemu-user can answer -ENOMEM, and -EPERM beside the
copy-in of the whole list, which at a size of 1 is the four bytes the
first conjunct names (`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`).
kernel: kernel/groups.c:setgroups,may_setgroups,groups_from_user,groups_alloc@v6.18.46 -/
theorem check_setgroups_unprivileged_rejects_a_copyin_and_enomem (grouplist : word) :
    check_setgroups (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [] [(grouplist, 4)])
        demo_model = CheckReject
      ∧ check_setgroups (mkEffect (errno_ret ENOMEM) [] []) demo_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- -EPERM beside the remaining ledgers — a zero-fill, an unmap, a
pre-effect copy — is refused as the write and the copy-in are: nothing
about the machine changes when :204 returns.  And -EPERM's low word alone,
0x00000000ffffffff, is refused too: `__se_sys_setgroups` returns the whole
`long` (arch/riscv/include/asm/syscall_wrapper.h:82-93) and
`syscall_handler` stores it whole (arch/riscv/include/asm/syscall.h:112).
kernel: kernel/groups.c:setgroups,may_setgroups; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_setgroups_unprivileged_rejects_other_ledgers_and_a_truncated_errno (p : word) :
    check_setgroups (SyscallEffect.mkEffectU (errno_ret EPERM) [] [(p, 4)] [] [] []) demo_model
        = CheckReject
      ∧ check_setgroups (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [(p, 4096)] [] [])
          demo_model = CheckReject
      ∧ check_setgroups (SyscallEffect.mkEffectU (errno_ret EPERM) [] [] [] [MemCopy.mkCopy p p 4] [])
          demo_model = CheckReject
      ∧ check_setgroups (mkEffect 4294967295 [] []) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

end Setgroups

section TheWitnesses

/-! ## The witnesses: which outcome each names

A witness is one outcome the spec admits, computed from the arguments and
the model with no effect to check; `getgroups_witness_ok` and
`setgroups_witness_ok` say each one is admitted, which is the
receptiveness field of the arm the registration step builds.  What that
lemma cannot say is WHICH outcome the witness names, so each pin below
names it, at a closed fixture or over the sizes and models its
hypotheses allow: the kernel's return on the path the model answers,
`Unmodeled` on the path it declines.  A witness that named a different
admitted outcome — there is none, the spec is deterministic where it
answers, but a lemma does not know that — would pass `_ok` and fail
here. -/

/-- Evaluate a closed witness: open it, decide every closed gate, read the
fixture model with the `sys_simp` set, and finish with `sys_norm` if a
read is left.  The header says why this and not `rfl`. -/
macro "witness_norm" : tactic =>
  `(tactic| (simp +decide only [getgroups_witness, setgroups_witness, sys_simp,
      ↓reduceIte]; first | done | sys_norm))

/-- A negative size: the witness is -EINVAL with the model untouched
(`if (gidsetsize < 0) return -EINVAL;`, kernel/groups.c:166-167), on
`demo_model` and on a process with no groups alike.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_witness_negative_size_is_einval :
    getgroups_witness 4294967295 demo_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []
      ∧ getgroups_witness 4294967295 no_groups_model
          = Ok (mkEffect (errno_ret EINVAL) [] []) no_groups_model [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- …and on EVERY model, the over-long list included, since the sign test
at :166 runs before the list is read at :170.  The checker's
`NegativeSize` section pins this order over an arbitrary model; this is
the witness's half, and the only witness pin a sign test dropped
altogether would fail — on the two fixtures above a size of -1 falls
through to the too-small arm and names the same -EINVAL.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_witness_negative_size_is_einval_on_every_model (m : Model) :
    getgroups_witness 4294967295 m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  have hneg : sint32 4294967295 < 0 := by decide
  unfold getgroups_witness
  dsimp only
  simp only [hneg, ↓reduceIte]

/-- Size 0 is the count — `i = cred->group_info->ngroups` (kernel/groups.c:170,
Linux v6.18.46), returned at :181-182 because :171 skips the block: 3 on
the demo fixture and 0 at zero groups; a0 = 2^32 is size 0 after the `int`
cast (`__SC_CAST`, include/linux/syscalls.h:132).
kernel: kernel/groups.c:getgroups; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem getgroups_witness_size_zero_is_the_count :
    getgroups_witness 0 demo_model = Ok (mkEffect 3 [] []) demo_model []
      ∧ getgroups_witness 4294967296 demo_model = Ok (mkEffect 3 [] []) demo_model []
      ∧ getgroups_witness 0 no_groups_model = Ok (mkEffect 0 [] []) no_groups_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> witness_norm

/-- A size too small for three groups: -EINVAL (`if (i > gidsetsize)`,
kernel/groups.c:172-175), before any store.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_witness_size_too_small_is_einval :
    getgroups_witness 2 demo_model = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []
      ∧ getgroups_witness 1 demo_model
          = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- A positive size at zero groups: 0, with nothing written, since
`groups_to_user`'s loop (kernel/groups.c:44-49) runs zero times.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_witness_empty_list_is_zero :
    getgroups_witness 5 no_groups_model = Ok (mkEffect 0 [] []) no_groups_model []
      ∧ getgroups_witness 70000 no_groups_model
          = Ok (mkEffect 0 [] []) no_groups_model [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- One group at size 1 is the writing path, so the witness is `Unmodeled`
— where a witness whose empty-list arm fired at `ngroups <= 1` would name
0 — and size 0 on the same model names the count, 1.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_witness_one_group_is_not_the_empty_list :
    getgroups_witness 1 one_group_model = Unmodeled
      ∧ getgroups_witness 0 one_group_model = Ok (mkEffect 1 [] []) one_group_model [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- The writing path — a size that fits three groups — is declined, so the
witness is `Unmodeled`: a witness of a decline is a witness.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_witness_writing_path_is_unmodeled :
    getgroups_witness 3 demo_model = Unmodeled
      ∧ getgroups_witness 2147483647 demo_model = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- On any model with more than `NGROUPS_MAX` stored groups — a state
`setgroups` never installs (kernel/groups.c:205-206) — and any nonnegative
size, the witness is `Unmodeled`.  Opened with `generalize`, for the
reason `Checks/Sys/Kernel/Groups.lean` gives.
kernel: kernel/groups.c:setgroups; include/uapi/linux/limits.h:NGROUPS_MAX@v6.18.46 -/
theorem getgroups_witness_over_ngroups_max_is_unmodeled (gidsetsize : word)
    (h : 0 ≤ sint32 gidsetsize) (m : Model)
    (hm : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)) :
    getgroups_witness gidsetsize m = Unmodeled := by
  unfold getgroups_witness
  dsimp only
  generalize sint32 gidsetsize = n at h ⊢
  have hneg : ¬ n < 0 := by omega
  simp only [hneg, hm, ↓reduceIte]

/-- INT_MIN — a0 = 2^31 — is negative after the `int` cast, so the witness
names -EINVAL, as the `NegativeSize` section pins for the checker.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_witness_int_min_is_einval :
    getgroups_witness 2147483648 demo_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  witness_norm

/-- A list of exactly `NGROUPS_MAX` entries is answered with its count at
size 0 — the guard is strict, as `setgroups`' is — and the witness names
that count where the `OverNgroupsMax` section accepts it for the checker.
kernel: kernel/groups.c:getgroups,setgroups; include/uapi/linux/limits.h:NGROUPS_MAX@v6.18.46 -/
theorem getgroups_witness_at_ngroups_max_is_the_count (m : Model)
    (hm : (((m_creds m).cr_groups).length : Int) = NGROUPS_MAX) :
    getgroups_witness 0 m = Ok (mkEffect (Z_to_bv 64 NGROUPS_MAX) [] []) m [] := by
  have h0 : sint32 0 = 0 := by decide
  unfold getgroups_witness
  dsimp only
  rw [h0, hm]
  simp only [Int.lt_irrefl, ↓reduceIte]

/-- The two witness hypotheses are satisfiable by the same closed values
the `OverNgroupsMax` section instantiates the checker's with.
model: existence witnesses for the two hypotheses above, closed values of the model's own `Creds`. -/
example :
    getgroups_witness 0
        (with_creds { demo_creds with cr_groups := List.replicate 65537 0 } demo_model)
      = Unmodeled
    ∧ getgroups_witness 0
        (with_creds { demo_creds with cr_groups := List.replicate 65536 0 } demo_model)
      = Ok (mkEffect (Z_to_bv 64 NGROUPS_MAX) [] [])
          (with_creds { demo_creds with cr_groups := List.replicate 65536 0 } demo_model) [] :=
  ⟨getgroups_witness_over_ngroups_max_is_unmodeled _ (by decide) _
      (by show NGROUPS_MAX < ((List.replicate 65537 (0 : word)).length : Int)
          simp only [List.length_replicate]; decide),
   getgroups_witness_at_ngroups_max_is_the_count _
      (by show ((List.replicate 65536 (0 : word)).length : Int) = NGROUPS_MAX
          simp only [List.length_replicate]; rfl)⟩

/-- Unprivileged: the witness is -EPERM with the model untouched (`if
(!may_setgroups()) return -EPERM;`, kernel/groups.c:203-204), on
`demo_model` and on root that has dropped its effective uid.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_witness_unprivileged_is_eperm :
    setgroups_witness demo_model = Ok (mkEffect (errno_ret EPERM) [] []) demo_model []
      ∧ setgroups_witness dropped_euid_model
          = Ok (mkEffect (errno_ret EPERM) [] []) dropped_euid_model [] := ⟨rfl, rfl⟩

/-- Privileged — root, set-user-ID root, and an effective uid of 0 with
the real and saved uid both `demo_uid` — is the declined installing
path, so the witness is `Unmodeled`; the third fixture is the one that
tells a witness keyed on the effective uid from one keyed on the
effective and the saved uid together.
kernel: kernel/groups.c:setgroups,may_setgroups; security/commoncap.c:cap_emulate_setxuid@v6.18.46 -/
theorem setgroups_witness_privileged_is_unmodeled :
    setgroups_witness root_model = Unmodeled
      ∧ setgroups_witness setuid_root_model = Unmodeled
      ∧ setgroups_witness euid_only_root_model = Unmodeled := ⟨rfl, rfl, rfl⟩

end TheWitnesses

-- lean-port sentinel: ticket V-Kernel-Groups appends below this line

section V_Kernel_Groups

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Groups — `getgroups` and `setgroups` over the real table

WHAT IS TWINNED HERE.  The sections above state each Rocq example on the
checkers themselves, because `checked_table` carried no row for 158 or 159
when they were written.  This section is the restatement through
`check_syscall`, which the registration makes possible.  Nine of
the ten examples `theories/LinuxProcessSem/Checks/Cases/Kernel/Groups.v`
states through `check_syscall` are restated here through the Lean
`check_syscall`, over `checked_table` itself, at the Rocq inputs
(`getgroups_in size list`, and `setgroups_in size list` for Rocq's
`mkInput 159 [...]`), under the Rocq name with `_over_the_real_table`
after it, K6b's convention.  The tenth,
`setgid_keeps_the_supplementary_group_list`, chains a `setgid` (144)
through `check_syscall` first, and the Lean table carries no row for 144,
so its `check_syscall` declines and the example is not statable yet: it
goes with the registration of 144, whose ticket owns the arm that makes
it true.

WHAT A PIN HERE ADDS to the checker-level pins above is the ARM's claim,
in two halves that different pins carry.  The first is that the lookup
at 158 and 159 finds a row rather than the dispatcher's own decline, and
every pin here that states an answer carries it, since a number with no
row declines: `check_syscall_in` answers `CheckUnmodeled`
(`Checks/ExecutableSpecs.lean`) and `table_witness` `Unmodeled`
(`Checks/Progress.lean`).  So
`privileged_setgroups_fails_closed_over_the_real_table` and
`setgroups_privileged_witnessed_unmodeled_over_the_real_table` hold with
or without the row at 159 and carry no part of the claim, and which row
the lookup finds is `lookup_getgroups_in`'s and `lookup_setgroups_in`'s.
The second half is which register each arm hands its checker, and a pin
carries it against another register only where its verdict would change
under an arm that read that register instead, whatever verdict it
states.  An answer at `getgroups_in 0 0` or `setgroups_in 0 0` carries
the first half alone, since every argument register holds 0 there; and
a decline can carry the second, since an arm reading `a2` would answer
the count where the writing-path pin declines.  The nine twins restate
checker-level pins through the table;
`getgroups_refuses_qemu_users_enomem_over_the_real_table` states for
`getgroups` a verdict that no checker-level pin above states; and
`setgroups_size_zero_is_eperm_under_every_implementation_over_the_real_table`
states `setgroups`'s verdicts at a size of 0, where every supported
implementation gives an unprivileged caller the same outcome.
`getgroups` reads `a0`, and the count example's second conjunct carries
that against `a1`: it puts 0xdeadbeef there, which as an `int` is
negative, so an arm reading `a1` would answer -EINVAL and refuse the
count.  `setgroups` reads no register at all, and its example's first
conjunct carries that against a size test: it puts `2^64 - 1` in `a0`,
which an arm that tested the size before `may_setgroups` would refuse
the -EPERM at.  That is Linux's answer, and
qemu-user's is -EINVAL there (`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`),
so the arm admits Linux alone at that shape.

WHY THE `getgroups` PINS ARE NOT `rfl`: the unifier walks into the
`sint32` decision the header names and does not come back, so each is
rewritten down to a closed `check_getgroups` call first.

POLARITY is the header's: `kernel:` on a pin that rests on a claim about
the kernel, and `model:` on one about this tree's own definitions,
whatever verdict or outcome its statement spells.  Here the `model:`
pins are the two lookups, which state the table's contents, and the
register pin; above, they are the two `example`s whose closed values
satisfy a hypothesis, one over the checker and one over the witness. -/

/-- The lookup the dispatcher performs on a `getgroups_in`: `in_sysno` is
`158` whatever the two words hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_getgroups_in (gidsetsize grouplist : word) :
    lookup_ca checked_table (bv_unsigned (getgroups_in gidsetsize grouplist).in_sysno)
      = some arm_getgroups :=
  lookup_ca_checked_table_getgroups

/-- …and on a `setgroups_in`, at `159`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_setgroups_in (gidsetsize grouplist : word) :
    lookup_ca checked_table (bv_unsigned (setgroups_in gidsetsize grouplist).in_sysno)
      = some arm_setgroups :=
  lookup_ca_checked_table_setgroups

/-- Register `a0` of a `getgroups_in` is its size, the register the arm reads.
model: `in_arg` at a closed input shape; a projection, not a kernel claim. -/
theorem in_arg_0_of_getgroups_in (gidsetsize grouplist : word) :
    in_arg (getgroups_in gidsetsize grouplist) 0 = gidsetsize :=
  rfl

/-! ### The nine Rocq examples, through `check_syscall` -/

/-- `getgroups_size_zero_reports_the_count` over the real table: size 0
asks for the count, `cred->group_info->ngroups`, and the `if (gidsetsize)`
block that reads `grouplist` is skipped (kernel/groups.c, Linux v6.18.46),
so `demo_model`'s three groups answer 3 whether `a1` is 0 or 0xdeadbeef,
the model untouched and no event.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_size_zero_reports_the_count_over_the_real_table :
    check_syscall (getgroups_in 0 0) (mkEffect 3 [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (getgroups_in 0 3735928559) (mkEffect 3 [] []) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `getgroups_wrong_count_rejected` over the real table: the count is the
LENGTH of the list, so 4, 2 and 1002 — the second of the ids in it — are
each a lie at size 0.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_wrong_count_rejected_over_the_real_table :
    check_syscall (getgroups_in 0 0) (mkEffect 4 [] []) demo_model = CheckReject
    ∧ check_syscall (getgroups_in 0 0) (mkEffect 2 [] []) demo_model = CheckReject
    ∧ check_syscall (getgroups_in 0 0) (mkEffect 1002 [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `getgroups_negative_size_is_einval` over the real table: a0 =
0xffffffff is `gidsetsize = -1` after riscv's wrapper casts the register
to `int` (`__SC_CAST`, include/linux/syscalls.h, applied at
arch/riscv/include/asm/syscall_wrapper.h, Linux v6.18.46), and
`if (gidsetsize < 0) return -EINVAL;` answers before the list is read, on
`demo_model` and on the model with no groups alike; `2^64 - 1` narrows to
the same -1.
kernel: kernel/groups.c:getgroups; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem getgroups_negative_size_is_einval_over_the_real_table :
    check_syscall (getgroups_in 4294967295 3735928559) (mkEffect (errno_ret EINVAL) [] [])
        demo_model = CheckOk demo_model []
    ∧ check_syscall (getgroups_in 4294967295 3735928559) (mkEffect (errno_ret EINVAL) [] [])
        no_groups_model = CheckOk no_groups_model []
    ∧ check_syscall (getgroups_in 18446744073709551615 0) (mkEffect (errno_ret EINVAL) [] [])
        demo_model = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `getgroups_size_truncates_to_int` over the real table: a0 = 2^32 is
`gidsetsize = 0` after the `int` cast, so it asks for the count.
kernel: kernel/groups.c:getgroups; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem getgroups_size_truncates_to_int_over_the_real_table :
    check_syscall (getgroups_in 4294967296 0) (mkEffect 3 [] []) demo_model
      = CheckOk demo_model [] := by
  rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
    in_arg_0_of_getgroups_in]
  check_norm

/-- `getgroups_size_too_small_is_einval_not_efault` over the real table: a
size of 2 against three groups is refused with -EINVAL by `if (i >
gidsetsize)` before `groups_to_user` touches `grouplist`, so an -EFAULT
at an unmapped 0xdeadbeef is a lie.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_size_too_small_is_einval_not_efault_over_the_real_table :
    check_syscall (getgroups_in 2 3735928559) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (getgroups_in 2 3735928559) (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `getgroups_empty_list_returns_zero_without_touching_the_array` over the
real table: with no groups, `groups_to_user` copies nothing, so a size of
64 at an unmapped 0xdeadbeef answers 0 and an -EFAULT is refused.
qemu-user answers that -EFAULT there (`lock_user` on the destination
before the copy, `linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md`),
or -ENOMEM when the `g_try_new` ahead of it fails
(linux-user/syscall.c:12592-12596, QEMU v11.1.1): the arm admits Linux
alone here, and both conjuncts flip to `CheckUnmodeled` when the fix
that entry describes lands.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_empty_list_returns_zero_without_touching_the_array_over_the_real_table :
    check_syscall (getgroups_in 64 3735928559) (mkEffect 0 [] []) no_groups_model
      = CheckOk no_groups_model []
    ∧ check_syscall (getgroups_in 64 3735928559) (mkEffect (errno_ret EFAULT) [] [])
        no_groups_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `getgroups_writing_path_fails_closed` over the real table: a size at
least the three groups reaches `groups_to_user`'s stores, which the spec
declines, at 3 and at 64; the two sizes on the other side of that path at
the same pointer, 0 and 2, are answered, so the declines are a boundary.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_writing_path_fails_closed_over_the_real_table :
    check_syscall (getgroups_in 3 4096) (mkEffect 3 [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (getgroups_in 64 4096) (mkEffect 3 [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (getgroups_in 0 4096) (mkEffect 3 [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (getgroups_in 2 4096) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-- `setgroups_refuses_before_it_reads_an_argument` over the real table:
`if (!may_setgroups()) return -EPERM;` is the first statement of
`SYSCALL_DEFINE2(setgroups)` (kernel/groups.c, Linux v6.18.46), ahead of
the `NGROUPS_MAX` test and of `groups_from_user`, so an unprivileged
caller's size of `2^64 - 1` is -EPERM, and an -EINVAL at a size of 1 and
a list at 4096 is a lie under every implementation.  The -EFAULT there is
`groups_from_user`'s, which only a caller past `may_setgroups` reaches
under Linux.  The first and third verdicts are right for Linux alone:
qemu-user answers -EINVAL at a size of `2^64 - 1`, and -EFAULT or -ENOMEM
at a size of 1 and a list at 4096
(`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`).
All three conjuncts flip to `CheckUnmodeled` when the fix that entry
describes lands: the first because that fix declines a size negative as
an `int`, and the second and third because they share an input (a size
of 1 and a list at 4096 in `setgroups_in`, whose memory views hold no
byte, so the list is unreadable on any model) and that fix declines an
unreadable list whatever errno the effect offers.  The second is a lie
under every implementation all the same, and is refused today.
kernel: kernel/groups.c:setgroups,may_setgroups,groups_from_user@v6.18.46 -/
theorem setgroups_refuses_before_it_reads_an_argument_over_the_real_table :
    check_syscall (setgroups_in 18446744073709551615 4096) (mkEffect (errno_ret EPERM) [] [])
        demo_model = CheckOk demo_model []
    ∧ check_syscall (setgroups_in 1 4096) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject
    ∧ check_syscall (setgroups_in 1 4096) (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- `privileged_setgroups_fails_closed` over the real table: a privileged
caller passes `may_setgroups` and installs a new list, which the model
does not carry out, so it declines rather than accept a call whose effect
it would drop.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem privileged_setgroups_fails_closed_over_the_real_table :
    check_syscall (setgroups_in 0 0) (mkEffect 0 [] []) root_model = CheckUnmodeled := rfl

/-! ### qemu-user's -ENOMEM, refused on two `getgroups` arms

At a size from 1 to `NGROUPS_MAX` qemu-user allocates its own copy of the
list before its host call, and answers -ENOMEM where that allocation
fails (`g_try_new`, linux-user/syscall.c:12592-12596, QEMU v11.1.1).
Linux allocates nothing on the way to the too-small arm's -EINVAL or to
the empty list's 0, so the arm answers both with Linux's answer alone
and refuses that -ENOMEM on both
(`linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md`).  The pin below
states that refusal as it stands, a verdict right for Linux alone; each
of its conjuncts flips when the fix that entry describes lands. -/

/-- Sizes of 2 and 1 against `demo_model`'s three groups, and of 64
against none, at the unmapped 0xdeadbeef the twins above use: -ENOMEM
is refused at all three.  `if (i > gidsetsize)` (:172-175) returns before
`groups_to_user` is called, that function's loop runs zero times on an
empty list, and every -ENOMEM kernel/groups.c spells is on the path that
installs a list — `setgroups` when `groups_alloc` fails (:208-210), and
`set_current_groups` when it cannot allocate the new credentials
(:140-142) — which `getgroups` never enters.  Each verdict is right
for Linux alone, as the note above says.
kernel: kernel/groups.c:getgroups,groups_to_user,setgroups,set_current_groups@v6.18.46 -/
theorem getgroups_refuses_qemu_users_enomem_over_the_real_table :
    check_syscall (getgroups_in 2 3735928559) (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckReject
    ∧ check_syscall (getgroups_in 1 3735928559) (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckReject
    ∧ check_syscall (getgroups_in 64 3735928559) (mkEffect (errno_ret ENOMEM) [] [])
        no_groups_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [check_syscall_of_found _ _ _ _ (lookup_getgroups_in _ _), ca_check_arm_getgroups,
        in_arg_0_of_getgroups_in]; check_norm)

/-! ### `setgroups` at a size of 0, which every implementation answers alike

At a size of 0 qemu-user's size test passes, its `gidsetsize > 0` guard
skips `g_try_new`, `lock_user` and the loop, and its host call answers
the -EPERM with nothing read (linux-user/syscall.c:12620-12639, QEMU v11.1.1);
Linux answers -EPERM at kernel/groups.c:203-204 (Linux v6.18.46) having
read nothing either.  So at that size an unprivileged caller's outcome is
the same under every supported implementation
(`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`), and no fix that entry
describes flips the pin below. -/

/-- `setgroups(0, NULL)` from an unprivileged caller: -EPERM accepted, and
-EINVAL, -EFAULT and -ENOMEM refused.  Linux returns at :203-204, before
the size test (:205-206), the allocation (:208-210) and the read of the
list (:211), so none of the three is reachable; and qemu-user answers
none of them at this size, as the note above says.
kernel: kernel/groups.c:setgroups,may_setgroups,groups_from_user@v6.18.46 -/
theorem setgroups_size_zero_is_eperm_under_every_implementation_over_the_real_table :
    check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EPERM) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject
    ∧ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject
    ∧ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The witnesses the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so each arm's
`ca_witness` is what it answers at 158 and 159; the witness pins above
state each witness on its own arguments, a bare size word for
`getgroups_witness` and none for `setgroups_witness`.  Of the three pins
below, the first two carry both halves of the section note's claim for
the witness, the register half against two of the three mistakes that
note names for the checker: a witness handed `a1`, and one that tests
the size in `a0` first.  The third, a decline, would hold with no row at
159, as the section note says. -/

/-- The count at size 0, with 0xdeadbeef in `a1`: the witness exhibits the
kernel's 3, the model untouched, no event — which a witness handed `a1`
would not, since that word is a negative `int`.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_count_witnessed_over_the_real_table :
    syscall_spec_witness (getgroups_in 0 3735928559) demo_model
      = Ok (mkEffect 3 [] []) demo_model [] := by
  simp only [syscall_spec_witness, table_witness, lookup_getgroups_in, ca_witness_arm_getgroups,
    in_arg_0_of_getgroups_in]
  witness_norm

/-- Unprivileged `setgroups` at `2^64 - 1` and an unmapped list: the witness
exhibits Linux's -EPERM, which qemu-user does not
(`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md`), so this pin flips
when the arm is fixed.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_eperm_witnessed_over_the_real_table :
    syscall_spec_witness (setgroups_in 18446744073709551615 4096) demo_model
      = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [] := rfl

/-- …and privileged, the witness exhibits the decline.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_privileged_witnessed_unmodeled_over_the_real_table :
    syscall_spec_witness (setgroups_in 0 0) root_model = Unmodeled := rfl

end V_Kernel_Groups

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Groups
