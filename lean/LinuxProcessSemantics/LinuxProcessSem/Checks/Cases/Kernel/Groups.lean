-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Groups.v

import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic


/-! # Checks.Cases.Kernel.Groups — what `getgroups` and `setgroups` answer, read off against Linux

Worked examples over `Sys.Kernel.Groups.getgroups_spec` and
`Sys.Kernel.Groups.setgroups_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Groups.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  Each decision of a spec gets an `iff` over EVERY
outcome `o` — the positive half (what is admitted) and the negative half
(nothing else is) in one statement — and beside it the concrete mistake a
lying kernel could report, refuted on its own.  Both are closed by the
tactics of `Checks/Cases/Tactic.lean`: `sys_norm` reads the call off its
monad primitives and decides the closed gates, `sys_refute` is `sys_norm`
that must close the goal.  A gate over a SYMBOLIC argument or model
survives `sys_norm`'s first pass as `(if g then c1 else c2) i m o`; those
checks `split` on it and discharge the excluded branch from the
hypothesis, which is how the ORDER of two gates is stated rather than
sampled.

WHY SO MUCH OF THIS IS SYMBOLIC.  A probe cannot choose how many
supplementary groups the process it runs as has: `setgroups` needs
privilege the run does not have, and the model declines it anyway
(`setgroups_spec`), so the branches that turn on that number are only
conditionally reachable from a run.  Rocq's file answers that with
fixtures; this one keeps the fixtures AND states the two gates whose
order matters over an arbitrary model, because a fixture samples an order
and a hypothesis states it.

WHAT ROCQ'S FILE KEEPS THAT THIS ONE DOES NOT.  One example,
`setgid_keeps_the_supplementary_group_list`, checks that `setgid` (144)
carries `cr_groups` over, by running the two calls in sequence through
the checker.  Its Lean twin is in `Checks/Cases/Kernel/Sys.lean`, the
file of the ticket that ports `Sys/Kernel/Sys.v`, under the same name:
that file imports this one, so arm 144 and the `getgroups` unfolding are
both in reach there and neither is here.  Every other example of that
file has a pin below.  `root_model` is Rocq's fixture from
`Checks/Cases/Kernel/Sys.v`; it is defined HERE, with Rocq's value, and
re-exported by that twin — the reverse of Rocq's import direction,
because this twin landed first.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! The specs' unfoldings.  `Checks/Cases/Tactic.lean`'s register is where
a spec's `.eq_1` line is owed; this ticket leaves that file untouched, so
the two lines sit here until the register's next edit takes them, as
`Checks/Cases/Kernel/Exit.lean` does for `wait4_spec`. -/
attribute [sys_simp low] getgroups_spec.eq_1 setgroups_spec.eq_1

/-! ## The numbers these checks spell out

Kept as numerals in the statements so a reader sees the register value a
program passes; these pins say what each one is. -/

/-- `EINVAL` is 22.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
example : EINVAL = 22 := by decide
/-- `EPERM` is 1.
kernel: include/uapi/asm-generic/errno-base.h:EPERM@v6.18.46 -/
example : EPERM = 1 := by decide
/-- `EFAULT` is 14 — the errno `groups_to_user`'s `put_user` produces
(kernel/groups.c:47-48) and the one every check below refuses on a path
that never reaches it.
kernel: include/uapi/asm-generic/errno-base.h:EFAULT; kernel/groups.c:groups_to_user@v6.18.46 -/
example : EFAULT = 14 := by decide
/-- `NGROUPS_MAX` is 65536: the ceiling `SYSCALL_DEFINE2(setgroups, ...)`
enforces on the list it installs (kernel/groups.c:205-206), so no
`struct group_info` a process holds is longer.
kernel: include/uapi/linux/limits.h:NGROUPS_MAX; kernel/groups.c:setgroups@v6.18.46 -/
example : NGROUPS_MAX = 65536 := by decide

/-! ### `int gidsetsize`, as the kernel reads it

`SYSCALL_DEFINE2(getgroups, int, gidsetsize, ...)` (kernel/groups.c:161,
Linux v6.18.46) declares the size an `int`, and `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46, applied by
`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux
v6.18.46) casts a0 to it before `gidsetsize < 0` (:166) ever runs.  So the high half
of the register is gone and the low half is read as two's complement.
`Syscall.sint32` is that reading. -/

/-- 0xffffffff is the `int` -1, not 2^32 - 1.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example : sint32 4294967295 = -1 := by decide
/-- …and so is -1 sign-extended to the whole 64-bit register.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example : sint32 (Z_to_bv 64 (-1)) = -1 := by decide
/-- THE TRUNCATION IS THE BEHAVIOR in the other direction: a0 = 2^32 has a
zero low half, so it is `gidsetsize = 0` and asks for the count.  A model
that compared the full 64-bit register would call this a huge positive
size and take the writing path.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example : sint32 4294967296 = 0 := by decide
/-- 0x80000000 is `INT_MIN`, not +2^31.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example : sint32 2147483648 = -2147483648 := by decide

/-! ## The fixtures

`demo_model` (`Checks/Cases/Prelude.lean`) is the unprivileged launch every
check starts from; its `demo_groups` is three ascending gids, none of them
3, so a count of 3 is a count and not a member.  Two fixtures are added
here: a process with NO supplementary groups, which is the one that
reaches the zero-length arm, and a ROOT process, which is the one
`setgroups` declines. -/

/-- A process with no supplementary groups: `demo_model`'s credentials
with an empty list.  Spelled as a record update of `Prelude.demo_creds`
rather than positionally, so that "only the list differs" is what the
definition SAYS and stays true if `Creds` gains a field; a check that
answers differently here therefore answers to the list. -/
def no_groups_creds : Creds := { demo_creds with cr_groups := [] }

def no_groups_model : Model := with_creds no_groups_creds demo_model

/-- A ROOT process: all six ids 0, which is what `State.init_model` builds
for a launch by root and what makes `State.creds_privileged` true — the
model's reading of `ns_capable_setid(old->user_ns, CAP_SETUID)`
(kernel/capability.c:398-401, Linux v6.18.46), exact under the conditions
`State.creds_privileged`'s docstring names.  Rocq's fixture of the same
name and value lives in `theories/LinuxProcessSem/Checks/Cases/Kernel/Sys.v`;
`Checks/Cases/Kernel/Sys.lean` re-exports this one. -/
def root_model : Model :=
  with_creds (Creds.mkCreds 0 0 0 0 0 0 demo_groups) demo_model

/-- A set-user-ID-root process: real uid `demo_uid`, effective and saved
uid 0, everything else `demo_model`'s.  Rocq's Cases files have no fixture
of this shape; it is here because the `setgroups` pins need a model on
which the REAL and the EFFECTIVE uid disagree, so that a spec keyed on the
wrong one is told apart.  `Checks/Cases/State.lean` pins
`creds_privileged` itself on these two shapes; the pins here run the
SYSCALL on them. -/
def setuid_root_model : Model :=
  with_creds { demo_creds with cr_euid := 0, cr_suid := 0 } demo_model

/-- Root that has dropped its effective uid: real and saved uid 0,
effective uid `demo_uid`, everything else `demo_model`'s. -/
def dropped_euid_model : Model :=
  with_creds { demo_creds with cr_uid := 0, cr_suid := 0 } demo_model

/-- The call shape the dispatcher pins use: syscall 158 with a size and a
list pointer. -/
def getgroups_in (gidsetsize grouplist : word) : SyscallInput :=
  SyscallInput.mkInput 158 [gidsetsize, grouplist, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The call shape the `setgroups` dispatcher pins use: syscall 159 with a
size and a list pointer. -/
def setgroups_in (gidsetsize grouplist : word) : SyscallInput :=
  SyscallInput.mkInput 159 [gidsetsize, grouplist, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The three fixtures' group lists, read off.
model: a fixture projection at a closed value, the fact every `getgroups` pin below turns on. -/
theorem groups_of_the_fixtures :
    (m_creds demo_model).cr_groups = demo_groups
      ∧ (m_creds no_groups_model).cr_groups = []
      ∧ (m_creds root_model).cr_groups = demo_groups := ⟨rfl, rfl, rfl⟩

/-- `demo_model` is unprivileged and `root_model` is privileged.  This is
what `may_setgroups()` (kernel/groups.c:185-191) is being asked, through
the effective uid `State.creds_privileged` answers it with.
kernel: kernel/groups.c:may_setgroups@v6.18.46 -/
theorem privilege_of_the_fixtures :
    creds_privileged (m_creds demo_model) = false
      ∧ creds_privileged (m_creds root_model) = true := ⟨rfl, rfl⟩

/-! ## `getgroups` (158): the negative size, and that it is decided FIRST

`if (gidsetsize < 0) return -EINVAL;` (kernel/groups.c:166-167, Linux
v6.18.46) runs before `cred->group_info` is read at :170 and before the `if (gidsetsize)` block
at :171.  Two consequences a check can state: a negative size with a
garbage `grouplist` is -EINVAL and never -EFAULT, and the answer does not
depend on the group list at all — which is why the check is stated over an
ARBITRARY model rather than on a fixture. -/

/-- A negative `gidsetsize` is -EINVAL on EVERY model, including one whose
group list is longer than `NGROUPS_MAX` and which the spec would otherwise
decline: the kernel's negative-size test comes first, so the model's
`NGROUPS_MAX` guard must not reorder ahead of it.  Nothing is written and
the model is untouched.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_negative_size_is_einval_before_any_other_test
    (gidsetsize : word) (h : sint32 gidsetsize < 0)
    (m : Model) (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec gidsetsize i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_simp_pass +decide
  split
  · sys_norm
  · exfalso; omega

/-- a0 = 0xffffffff, the `int` -1, on the fixture with three groups.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 4294967295 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] :=
  getgroups_negative_size_is_einval_before_any_other_test _ (by decide) _ i o

/-- …the same answer on the fixture with none, so it does not depend on
the list.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 4294967295 i no_groups_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) no_groups_model [] :=
  getgroups_negative_size_is_einval_before_any_other_test _ (by decide) _ i o

/-- …and a0 = 2^64 - 1, whose low half is the same `int`.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 18446744073709551615 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] :=
  getgroups_negative_size_is_einval_before_any_other_test _ (by decide) _ i o

/-- A kernel answering -EFAULT to a negative size is lying: the pointer is
not touched, because :166-167 returns before the `if (gidsetsize)` block
at :171 that `groups_to_user` is called from.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_negative_size_efault_rejected (i : SyscallInput) :
    ¬ getgroups_spec 4294967295 i demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- …and one answering a success is lying too, whether the 0 the recorded
run forges at this call or the count: a negative size never succeeds.
Stated at a0 = 2^64 - 1, the register the probe's `getgroups(-1, …)`
really passes (`(i64)-1`), so the pin and the recorded case agree on the
register and not only on the `int` it truncates to; the 32-bit spelling
of the same `int` is the two pins above.
probe: testing/syscall-check/tests/getgroups.c#reject --mutate getgroups:ret=0 -- negative -/
theorem getgroups_negative_size_success_rejected (i : SyscallInput) :
    ¬ getgroups_spec 18446744073709551615 i demo_model
        (Ok (mkEffect 0 [] []) demo_model [])
      ∧ ¬ getgroups_spec 18446744073709551615 i demo_model
          (Ok (mkEffect 3 [] []) demo_model []) := by
  constructor <;> sys_refute

/-- `INT_MIN` is a negative size like any other: a0 = 0x80000000 is
-EINVAL, not the +2^31 a model reading the register unsigned would see.
probe: testing/syscall-check/tests/getgroups.c#conform -- negative -/
theorem getgroups_int_min_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 2147483648 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] :=
  getgroups_negative_size_is_einval_before_any_other_test _ (by decide) _ i o

/-- …so a kernel that read a0 = 0x80000000 as +2^31 and answered the
count (0 on the probe's process, which is what the mutation forges) is
refused: the sign bit of the low half is the sign of the `int`.
probe: testing/syscall-check/tests/getgroups.c#reject --mutate getgroups#2:ret=0 -- negative -/
theorem getgroups_int_min_count_rejected (i : SyscallInput) :
    ¬ getgroups_spec 2147483648 i no_groups_model
        (Ok (mkEffect 0 [] []) no_groups_model []) := by
  sys_refute

/-! ## The `NGROUPS_MAX` guard: a state Linux cannot build

`groups_alloc` (kernel/groups.c:15-25, Linux v6.18.46) bounds nothing — it takes its
caller's size at :23 — so what makes a longer list unreachable is the
CALLER: on riscv64 the calling task's list is installed only by
`setgroups` (159), whose `(unsigned)gidsetsize > NGROUPS_MAX`
(kernel/groups.c:205-206, Linux v6.18.46) refuses a longer one, through
the tree's one assignment to a task credential's `group_info`
(`set_groups`, kernel/groups.c:122, Linux v6.18.46).  So a
longer `State.cr_groups` describes no process and `getgroups_spec` declines
rather than answering for it — `ngroups` is an `int`
(include/linux/cred.h:30, Linux v6.18.46) and the count such a state would report need not
even fit the `int` this syscall returns.  The guard sits AFTER the
negative-size test, which is what the check above states; this one states
that it fires for every nonnegative size. -/

/-- Any nonnegative size, on any model whose stored list is longer than
`NGROUPS_MAX`, declines.  The decline admits nothing, which the `iff`
says: no count and no errno is offered for such a state.
kernel: kernel/groups.c:setgroups; include/uapi/linux/limits.h:NGROUPS_MAX@v6.18.46 -/
theorem getgroups_over_ngroups_max_is_unmodeled
    (gidsetsize : word) (h : 0 ≤ sint32 gidsetsize)
    (m : Model) (hm : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int))
    (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec gidsetsize i m o ↔ o = Unmodeled := by
  -- `hm` is normalized with the goal, so that both spell the list the
  -- same way (`m_creds` unfolded) and `omega` reads one atom, not two.
  sys_simp_pass +decide at hm ⊢
  split
  · exfalso; omega
  · sys_simp_pass +decide
    split
    · sys_norm
    · -- `omega` rather than `absurd`, so that a guard moved by one
      -- (`NGROUPS_MAX + 1 < ng`) leaves a list of `NGROUPS_MAX + 1`
      -- entries answered and this proof open: the pin fixes the bound,
      -- not only the arm.
      exfalso; omega

/-- THE GUARD IS STRICT: a list of exactly `NGROUPS_MAX` entries is one
`SYSCALL_DEFINE2(setgroups, ...)` installs — `(unsigned)gidsetsize >
NGROUPS_MAX` (kernel/groups.c:205) is a STRICT `>`, so 65536 itself passes
it.  (The cast that test names is doing work of its own: it makes every
negative size compare above `NGROUPS_MAX` too, which is why `setgroups`
needs no separate negative test where `getgroups` has one at :166-167.
What matters here is only that 65536 is not refused.)  So a
process can hold it, and `getgroups(0, …)` answers its length.  Stated on
the length rather than on a 65536-element fixture, since nothing here
needs to evaluate such a list; with the count pins above it is what tells
`NGROUPS_MAX < ng` from `NGROUPS_MAX ≤ ng`.
kernel: kernel/groups.c:setgroups,getgroups@v6.18.46 -/
theorem getgroups_at_ngroups_max_is_answered (m : Model)
    (hm : ((m_creds m).cr_groups.length : Int) = NGROUPS_MAX)
    (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 0 i m o ↔
      o = Ok (mkEffect (Z_to_bv 64 NGROUPS_MAX) [] []) m [] := by
  sys_simp_pass +decide at hm ⊢
  split
  · exfalso; omega
  · rw [hm]; sys_norm

/-- The two symbolic pins above range over models that EXIST: a `Creds`
with exactly `NGROUPS_MAX` entries, and one with more, are both values the
model can spell (`with_creds` carries either into a `Model`), so neither
hypothesis is vacuous.  Linux can build the first and not the second — the
guard is for the second.
model: existence witnesses for the two hypotheses above, closed values of the model's own `Creds`. -/
example :
    (∃ c : Creds, (c.cr_groups.length : Int) = NGROUPS_MAX)
      ∧ (∃ c : Creds, NGROUPS_MAX < (c.cr_groups.length : Int)) :=
  ⟨⟨{ demo_creds with cr_groups := List.replicate 65536 0 }, by
      simp only [List.length_replicate]; rfl⟩,
   ⟨{ demo_creds with cr_groups := List.replicate 65537 0 }, by
      simp only [List.length_replicate]; decide⟩⟩

/-! ## The count: `gidsetsize = 0`

`if (gidsetsize)` (kernel/groups.c:171, Linux v6.18.46) skips the whole
block, so the call returns `i = cred->group_info->ngroups` (:170, :181-182) and the
`grouplist` pointer is not touched at any width.  The count is the LENGTH
of the stored list: `demo_groups` holds 27, 1002 and 4000, and the answer
is 3. -/

/-- Size 0 answers the count, reads nothing from the input record, moves
no memory, emits no event and leaves the model alone.  The `iff` is over
every outcome, so no other answer is admitted.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_size_zero_reports_the_count (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 0 i demo_model o ↔ o = Ok (mkEffect 3 [] []) demo_model [] := by
  sys_norm

/-- The whole call through the dispatcher, at a GARBAGE `grouplist`, and
at NULL: syscall 158 answers 3 either way, which is what the `if
(gidsetsize)` guard at :171 buys.  The pointer cannot change the answer
because no modeled path reads it — at the spec level by construction,
since `grouplist` is not an argument of `getgroups_spec`.  What this pin
fixes is therefore the DISPATCHER: a table arm that read a1 as the size
would see 0xdeadbeef as a negative `int` and answer -EINVAL, not 3.  It is
the one pin in this file that tells a0 from a1.
probe: testing/syscall-check/tests/getgroups.c#conform -- count -/
theorem sysno_158_size_zero_ignores_the_pointer (o : outcome SyscallEffect) :
    (syscall_spec (getgroups_in 0 3735928559) demo_model o ↔
       o = Ok (mkEffect 3 [] []) demo_model [])
    ∧ (syscall_spec (getgroups_in 0 0) demo_model o ↔
       o = Ok (mkEffect 3 [] []) demo_model []) := by
  constructor <;> sys_norm

/-- a0 = 2^32 is `gidsetsize = 0` after the `int` cast, so it asks for the
count.  A model comparing the full register would call it a huge positive
size and take the writing path, which declines — so this pin tells the
truncation apart from its absence by the ANSWER, not only by the arm.
probe: testing/syscall-check/tests/getgroups.c#conform -- count -/
theorem getgroups_size_truncates_to_int (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 4294967296 i demo_model o ↔
      o = Ok (mkEffect 3 [] []) demo_model [] := by
  sys_norm

/-- THE COUNT IS A LENGTH, not an approximation to it: one more is
refused.
probe: testing/syscall-check/tests/getgroups.c#reject --mutate getgroups:ret+1 -- count -/
theorem getgroups_count_plus_one_rejected (i : SyscallInput) :
    ¬ getgroups_spec 0 i demo_model (Ok (mkEffect 4 [] []) demo_model []) := by
  sys_refute

/-- …one fewer is refused.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_count_minus_one_rejected (i : SyscallInput) :
    ¬ getgroups_spec 0 i demo_model (Ok (mkEffect 2 [] []) demo_model []) := by
  sys_refute

/-- …and a MEMBER of the list instead of its length is refused: 1002 is
`demo_groups`' second element.  A model that handed back a gid where the
kernel returns `ngroups` would pass a check stated only on a fixture whose
length happened to be a member.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_member_instead_of_count_rejected (i : SyscallInput) :
    ¬ getgroups_spec 0 i demo_model (Ok (mkEffect 1002 [] []) demo_model []) := by
  sys_refute

/-- A nonnegative size never fails: -EINVAL at size 0 is refused.
probe: testing/syscall-check/tests/getgroups.c#reject --mutate getgroups:ret=-EINVAL -- count -/
theorem getgroups_size_zero_einval_rejected (i : SyscallInput) :
    ¬ getgroups_spec 0 i demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- Size 0 WRITES NOTHING AT ALL: a four-byte store at the `grouplist`
pointer is refused, since :171 never enters the block `groups_to_user` is
called from.  (No modeled arm of this spec emits a write — the one that
would is declined — so this pin fixes the SHAPE of the size-0 answer and
cannot tell two arms apart; its probe twin is what shows a real kernel's
size-0 call carrying no store.)
probe: testing/syscall-check/tests/getgroups.c#reject --mutate getgroups#2:smuggle-write:a1:4 -- count -/
theorem getgroups_size_zero_writes_nothing (grouplist : word) (i : SyscallInput) :
    ¬ getgroups_spec 0 i demo_model
        (Ok (mkEffect 3 [(grouplist, [0, 0, 0, 0])] []) demo_model []) := by
  sys_refute

/-! ## A size too small: -EINVAL BEFORE any store

`if (i > gidsetsize) { i = -EINVAL; goto out; }` (kernel/groups.c:172-175,
Linux v6.18.46) fires before `groups_to_user` is called at :176, so a size the kernel
cannot fill is refused with nothing written and -EFAULT is not admissible
however bad the pointer is. -/

/-- `getgroups(2, <garbage>)` on a process with three groups is -EINVAL,
and the model is untouched.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_size_too_small_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 2 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  sys_norm

/-- …and -EFAULT is refused: the store the pointer would fault on is never
attempted, because :172-175 returns first.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_size_too_small_efault_rejected (i : SyscallInput) :
    ¬ getgroups_spec 2 i demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- Size 1 is too small in the same way: the test is `ngroups >
gidsetsize`, not `gidsetsize = 0`.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_size_one_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 1 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  sys_norm

/-! ## The zero-length list: the subtle arm

With `gidsetsize > 0` and no supplementary groups, control DOES enter the
block at :171 and `groups_to_user` IS called at :176 — and its loop
(kernel/groups.c:44-49, Linux v6.18.46) runs `ngroups` times, which is
zero, so it returns 0 at :50 without a single `put_user`.  There is no up-front `access_ok`
over the array; validation is per element, at :47.  So under Linux the
call returns 0 and cannot fault, whatever the pointer is.

UNDER QEMU-USER IT CAN, and the arm admits Linux's answer alone.
`TARGET_NR_getgroups` (QEMU v11.1.1, linux-user/syscall.c:12582-12612)
refuses a size above `NGROUPS_MAX` with -EINVAL first (:12589-12591) and,
for any positive size, locks the whole array for writing before it copies
anything (:12599-12604; `lock_user` is NULL where `access_ok_untagged`
fails, linux-user/uaccess.c:8-15, QEMU v11.1.1), so an unmapped
destination is -EFAULT there even at zero groups.  The two refutations at the end of this section
refuse exactly those two answers; they fix what Rocq's arm decides, and
`linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md` records the defect
and what closes it. -/

/-- ANY nonnegative size, on a process with no supplementary groups,
answers 0 and touches nothing: Linux's answer, and the only one the arm
admits (the section note says what qemu-user answers instead).  Stated
over the size rather than sampled
at one, because the claim is about the loop trip count and not about the
size: `gidsetsize` of 0 answers the count, which is also 0, and every
larger size reaches `groups_to_user` and writes nothing.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_empty_list_returns_zero (gidsetsize : word)
    (h : 0 ≤ sint32 gidsetsize) (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec gidsetsize i no_groups_model o ↔
      o = Ok (mkEffect 0 [] []) no_groups_model [] := by
  sys_simp_pass +decide
  split
  · exfalso; omega
  · -- `sys_norm`'s second pass evaluates the fixture's closed list length
    -- to 0 inside the gates that still mention the symbolic size, so the
    -- spec's third gate, `n < ng`, reads `n < 0`: the negation of the
    -- first gate's hypothesis, which `split` discharges from context while
    -- it cases on the second gate, `n = 0`.  Both branches answer 0.
    sys_norm
    split <;> sys_norm

/-- `getgroups(64, <garbage>)` at zero groups: 0.
probe: testing/syscall-check/tests/getgroups.c#conform -- garbage64 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 64 i no_groups_model o ↔
      o = Ok (mkEffect 0 [] []) no_groups_model [] :=
  getgroups_empty_list_returns_zero _ (by decide) i o

/-- LINUX HAS NO UPPER BOUND ON `gidsetsize`: `getgroups(70000, buf)` is
answered, not refused.  `SYSCALL_DEFINE2(getgroups, ...)` never compares
the size against `NGROUPS_MAX` — only `setgroups` does
(kernel/groups.c:205-206).  qemu-user does compare it
(linux-user/syscall.c:12589-12591, QEMU v11.1.1) and answers -EINVAL; the
arm admits Linux's answer alone.
probe: testing/syscall-check/tests/getgroups.c#conform -- big70000 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    getgroups_spec 70000 i no_groups_model o ↔
      o = Ok (mkEffect 0 [] []) no_groups_model [] :=
  getgroups_empty_list_returns_zero _ (by decide) i o

/-- A kernel faulting on the garbage pointer at zero groups validates the
destination before the copy, which Linux does not do: `groups_to_user`'s
validation is the per-element `put_user` at :47, and the loop at :44 runs
no iteration.  qemu-user does exactly that (`lock_user` at
linux-user/syscall.c:12600-12604, QEMU v11.1.1), so the answer this pin
refuses is a real one of a supported implementation: the pin fixes Rocq's
Linux-only arm, and `linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md`
is the defect.  (The probe's `garbage64` reject case is not cited: its
unindexed `--mutate getgroups:` selects the run's FIRST call,
`getgroups(0, 0)`, so it records the size-0 arm, not this shape.)
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_empty_list_efault_rejected (i : SyscallInput) :
    ¬ getgroups_spec 64 i no_groups_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) no_groups_model []) := by
  sys_refute

/-- …and one refusing the big size with -EINVAL is range-checking against
`NGROUPS_MAX`, which Linux's `getgroups` does not do and qemu-user's does
(linux-user/syscall.c:12589-12591, QEMU v11.1.1): the same defect, refused
the same way.  (The probe's `big70000` reject case selects its first call,
`getgroups(0, 0)`, for the reason given above, and is not cited.)
kernel: kernel/groups.c:getgroups,setgroups@v6.18.46 -/
theorem getgroups_big_size_einval_rejected (i : SyscallInput) :
    ¬ getgroups_spec 70000 i no_groups_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) no_groups_model []) := by
  sys_refute

/-! ## The writing path is DECLINED

`gidsetsize >= ngroups > 0` reaches the call at kernel/groups.c:176 (Linux
v6.18.46) of `groups_to_user` (kernel/groups.c:37-51, Linux v6.18.46),
which stores `ngroups` 4-byte
`gid_t`s ascending from `grouplist`, each through its own `put_user`
(:47), and a fault at element k leaves elements 0..k-1 written — the
kernel does not roll back.
`Sys/Kernel/Groups.lean`'s `getgroups_spec` says why that is left
`unmodeled` rather than guessed at.  Declining is the whole answer, so no
observation of it is accepted either. -/

/-- The exact size for three groups declines.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_exact_size_fails_closed (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 3 i demo_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does a size with room to spare.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_roomy_size_fails_closed (i : SyscallInput)
    (o : outcome SyscallEffect) :
    getgroups_spec 64 i demo_model o ↔ o = Unmodeled := by
  sys_norm

/-- The decline admits NOTHING, not even the answer Linux gives: a
successful 3, and the -EFAULT a bad pointer would produce, are both
refused.  This is what fail-closed costs and what it buys — the model
offers no answer here rather than a plausible one.
kernel: kernel/groups.c:getgroups,groups_to_user@v6.18.46 -/
theorem getgroups_writing_path_admits_no_answer (i : SyscallInput) :
    ¬ getgroups_spec 3 i demo_model (Ok (mkEffect 3 [] []) demo_model [])
      ∧ ¬ getgroups_spec 3 i demo_model
            (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  constructor <;> sys_refute

/-- THE DECLINE IS A BOUNDARY, not a description of one: the two sizes on
either side of the writing path are still ANSWERED on the same fixture.
Size 0 asks for the count and never reaches `groups_to_user`; size 2 is
too small for three groups and is refused at :172-175 before it does.
This is the check that notices `getgroups` starting to decline MORE.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem getgroups_declines_only_the_writing_path (i : SyscallInput) :
    getgroups_spec 0 i demo_model (Ok (mkEffect 3 [] []) demo_model [])
      ∧ getgroups_spec 2 i demo_model
          (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  constructor <;> sys_norm

/-! ## `setgroups` (159)

`if (!may_setgroups()) return -EPERM;` (kernel/groups.c:203-204, Linux
v6.18.46) is the FIRST thing the syscall does — before the `(unsigned)gidsetsize >
NGROUPS_MAX` bound at :205-206 and before `groups_from_user` touches the
pointer at :211.  So an unprivileged caller gets -EPERM whatever it
passes, and the spec needs neither argument.  A privileged call would
write `State.cr_groups`, the list `getgroups` reports the length of
(`set_current_groups`, kernel/groups.c:134-157, Linux v6.18.46), so the
model declines it rather than accepting the call and discarding what it
wrote.

UNDER QEMU-USER THE ANSWER IS NOT -EPERM at the three shapes below, and
the arm admits Linux's alone.  `TARGET_NR_setgroups` (QEMU v11.1.1,
linux-user/syscall.c:12613-12639) tests both arguments BEFORE the host
call: -EINVAL for a size negative or above `NGROUPS_MAX` at :12620-12621,
-EFAULT for an unreadable list at :12628-12631 (`lock_user` is NULL where
`access_ok_untagged` fails, linux-user/uaccess.c:8-15, QEMU v11.1.1), and
`sys_setgroups` — where `may_setgroups` finally runs — only at :12639.
So the -EINVAL and -EFAULT the two refutations below refuse are real
answers of a supported implementation, exactly as on the `getgroups`
zero-length arm; they fix what Rocq's arm decides, and
`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md` records the defect and
what closes it. -/

/-- An unprivileged caller gets -EPERM, whatever the arguments were: the
spec does not take them, and the input record is symbolic here to say so.
Nothing is written and the credentials are unchanged.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_unprivileged_is_eperm (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setgroups_spec i demo_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [] := by
  sys_norm

/-- The same through the dispatcher, at the three argument shapes a kernel
that checked arguments first would answer differently on: a negative size,
a size past `NGROUPS_MAX`, and an unreadable list.  All three are -EPERM,
because :203-204 runs before :205-206 and before :211.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem sysno_159_is_eperm_before_any_argument_test (o : outcome SyscallEffect) :
    (syscall_spec (setgroups_in 18446744073709551615 4096) demo_model o ↔
       o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [])
    ∧ (syscall_spec (setgroups_in 70000 4096) demo_model o ↔
       o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [])
    ∧ (syscall_spec (setgroups_in 1 3735928559) demo_model o ↔
       o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- A kernel answering -EINVAL to an unprivileged caller with a size past
`NGROUPS_MAX` is checking the bound at :205-206 before the permission at
:203-204, which is the wrong order.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem setgroups_unprivileged_einval_rejected (i : SyscallInput) :
    ¬ setgroups_spec i demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- …and one answering -EFAULT has read the list at :211 before refusing
the caller at :203-204.
kernel: kernel/groups.c:setgroups,groups_from_user@v6.18.46 -/
theorem setgroups_unprivileged_efault_rejected (i : SyscallInput) :
    ¬ setgroups_spec i demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- …and an unprivileged `setgroups` never succeeds.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_unprivileged_success_rejected (i : SyscallInput) :
    ¬ setgroups_spec i demo_model (Ok (mkEffect 0 [] []) demo_model []) := by
  sys_refute

/-- …and it does not change the group list it was refused permission to
set: an -EPERM landing in a model whose `cr_groups` is empty is refused on
the model.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem setgroups_eperm_leaves_the_list_alone (i : SyscallInput) :
    ¬ setgroups_spec i demo_model
        (Ok (mkEffect (errno_ret EPERM) [] []) no_groups_model []) := by
  sys_refute

/-- A PRIVILEGED `setgroups` declines, on every privileged model: the call
would write the supplementary group list, and `getgroups` above reports
that list's length, so accepting it while discarding what it wrote would
make the next `getgroups` answer for a list nobody set.  What is left to
model is `groups_from_user`'s per-element import with its index-ordered
-EFAULT-before-EINVAL precedence (kernel/groups.c:54-74) and
`groups_sort`'s ascending reorder (:84-88, called at :217), which is
observable because `getgroups` hands back the STORED order.
kernel: kernel/groups.c:setgroups,groups_from_user,groups_sort,set_current_groups@v6.18.46 -/
theorem setgroups_privileged_fails_closed (m : Model)
    (hm : creds_privileged (m_creds m) = true)
    (i : SyscallInput) (o : outcome SyscallEffect) :
    setgroups_spec i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc; exact absurd hm hc

/-- The root fixture, through the dispatcher: the `setgroups` arm declines
on a PRIVILEGED caller.  A shape decline, not a number decline — 159 has
an arm, and `sysno_159_is_setgroups` below answers it on `demo_model` —
so no decline register lists this number.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem sysno_159_privileged_fails_closed (o : outcome SyscallEffect) :
    syscall_spec (setgroups_in 0 0) root_model o ↔ o = Unmodeled := by
  sys_norm

/-- The decline admits nothing: the success Linux really gives a root
caller with a readable list is not offered.
kernel: kernel/groups.c:setgroups,set_current_groups@v6.18.46 -/
theorem setgroups_privileged_success_rejected (i : SyscallInput) :
    ¬ setgroups_spec i root_model (Ok (mkEffect 0 [] []) root_model []) := by
  sys_refute

/-- …nor is -EPERM, which is the answer for the OTHER caller: a model that
answered -EPERM here would be reporting the unprivileged arm for a
privileged process.
kernel: kernel/groups.c:setgroups,may_setgroups@v6.18.46 -/
theorem setgroups_privileged_eperm_rejected (i : SyscallInput) :
    ¬ setgroups_spec i root_model
        (Ok (mkEffect (errno_ret EPERM) [] []) root_model []) := by
  sys_refute

/-! ### The discriminant is the EFFECTIVE uid

`demo_model` and `root_model` differ in all six ids at once, so every pin
above would still close for a spec that read the real uid, or the saved
one, instead of the effective one.  The two fixtures below split them.
The kernel fact: `may_setgroups` (kernel/groups.c:185-191, Linux v6.18.46)
asks `ns_capable_setid(user_ns, CAP_SETGID)` at :189, one bit of
`cred->cap_effective`, and under `State.creds_privileged`'s standing
assumptions that bit follows the EFFECTIVE uid — in
security/commoncap.c (Linux v6.18.46), `handle_privileged_root` sets it
when the euid is root and `cap_emulate_setxuid` clears it on every euid
0 → non-0 transition.
`Checks/Cases/State.lean`'s `creds_privileged_setuid_root` and
`creds_privileged_rejects_real_uid_zero` pin that argument on the
predicate; these two run `setgroups` on it. -/

/-- A set-user-ID-root process (real uid 1000, effective uid 0) is
privileged, so the arm DECLINES here exactly as on `root_model`; a spec
keyed on the real uid would answer -EPERM.
kernel: kernel/groups.c:may_setgroups; security/commoncap.c:handle_privileged_root@v6.18.46 -/
theorem setgroups_setuid_root_fails_closed (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setgroups_spec i setuid_root_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and root that has dropped its effective uid (real and saved uid 0,
effective uid 1000) is NOT: the call is -EPERM with the credentials
untouched.  A spec keyed on the real uid, or on the saved one, would
decline here instead.
kernel: kernel/groups.c:setgroups,may_setgroups; security/commoncap.c:cap_emulate_setxuid@v6.18.46 -/
theorem setgroups_dropped_euid_is_eperm (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setgroups_spec i dropped_euid_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) dropped_euid_model [] := by
  sys_norm

/-! ## The dispatcher carries both numbers to the right arm -/

/-- Syscall 158 is `getgroups`: a0 is the size, and a1 reaches nothing.
kernel: kernel/groups.c:getgroups@v6.18.46 -/
theorem sysno_158_is_getgroups (o : outcome SyscallEffect) :
    syscall_spec (getgroups_in 4294967295 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  sys_norm

/-- Syscall 159 is `setgroups`, which on an unprivileged caller is -EPERM.
kernel: kernel/groups.c:setgroups@v6.18.46 -/
theorem sysno_159_is_setgroups (o : outcome SyscallEffect) :
    syscall_spec (setgroups_in 0 0) demo_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups
