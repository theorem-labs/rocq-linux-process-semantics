-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Sys.v

import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups


/-! rocq-cases: a71fd38a08571d519b9cfc5f66308db5c26da570
covers: getpid_first_choice_is_within_modeled_envelope -- getpid_first_call_draws_a_live_tid
covers: gettid_first_choice_is_within_modeled_envelope -- gettid_first_call_draws_a_live_tid
covers: uname_first_copy_pins -- uname_first_copy_pins
covers: uname_wrong_sysname_rejected -- uname_wrong_sysname_rejected
covers: uname_unterminated_release_rejected -- uname_unterminated_release_rejected
covers: uname_pinned_copy_repeats -- uname_pinned_copy_repeats
covers: uname_pinned_copy_defector_rejected -- uname_pinned_copy_defector_rejected
covers: uname_defector_is_itself_admissible_first -- uname_defector_is_itself_admissible_first
covers: uname_access_ok_fault -- uname_access_ok_fault
covers: uname_one_byte_short_is_unmodeled -- uname_one_byte_short_is_unmodeled
covers: uname_wrap_would_pass_the_bare_walk -- uname_wrap_would_pass_the_bare_walk
covers: uname_wrap_name_is_not_access_ok -- uname_wrap_name_is_not_access_ok
covers: uname_wrapping_destination_faults -- uname_wrapping_destination_faults
covers: uname_wrapping_destination_rejects_the_copy -- uname_wrapping_destination_rejects_the_copy
covers: prlimit64_first_read_pins -- prlimit64_first_read_pins
covers: prlimit64_read_soft_over_hard_rejected -- prlimit64_read_soft_over_hard_rejected
covers: prlimit64_pinned_read_repeats -- prlimit64_pinned_read_repeats
covers: prlimit64_pinned_read_defector_rejected -- prlimit64_pinned_read_defector_rejected
covers: prlimit64_set_new_soft_replaces_the_record -- prlimit64_set_new_soft_replaces_the_record
covers: prlimit64_set_access_ok_fault_has_no_copyins -- prlimit64_set_access_ok_fault_has_no_copyins
covers: prlimit64_set_access_ok_fault_rejects_copyins -- prlimit64_set_access_ok_fault_rejects_copyins
covers: prlimit64_read_after_set_reports_the_set_pair -- prlimit64_read_after_set_reports_the_set_pair
covers: prlimit64_read_after_set_rejects_the_old_pair -- prlimit64_read_after_set_rejects_the_old_pair
covers: each_reader_reads_its_own_field -- each_reader_reads_its_own_field
covers: privileged_setuid_moves_all_three_ids -- privileged_setuid_moves_all_three_ids
covers: eagain_only_when_a_privileged_setuid_moves_the_real_uid -- eagain_only_when_a_privileged_setuid_moves_the_real_uid
covers: unprivileged_setuid_moves_only_the_effective_id -- unprivileged_setuid_to_the_real_uid_moves_the_effective_id
covers: setresgid_parks_a_group_in_the_saved_id -- setresgid_parks_a_group_in_the_saved_id
covers: setresuid_reaches_its_allocating_branch -- setresuid_reaches_its_allocating_branch
covers: unprivileged_setresuid_may_rearrange_held_ids -- unprivileged_setresuid_may_rearrange_held_ids -/

/-! # Checks.Cases.Kernel.Sys — what getpid, gettid, setsid, uname, prctl, prlimit64 and the eight id calls answer, read off against Linux

Worked examples over the specs of `Sys/Kernel/Sys.lean`: `getpid_spec`,
`gettid_spec`, `setsid_spec`, `getid_spec`, `setid_spec`, `setresid_spec`,
`uname_spec`, `prlimit64_spec` and `prctl_spec`.  Mirrors
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sys.v`: every worked case
of that file is twinned below, each on a `rocq-twin:` line and in the
`rocq-cases:` register above, which `tools/check_lean_cases_parity.py`
reads back against both files.  Two groups Rocq states elsewhere are
held here too: the `setsid` pins, which Rocq states over the executable
checker in `Checks/ProcessCreation.v` (`setsid_checker_*`), and the
`prctl` pins, which Rocq states there as well — `prctl_modeled_options_are`
by reflexivity on the list, `prctl_option_unmodeled` and
`prctl_tagged_addr_ctrl_unmodeled` over the DISPATCHER (`syscall_spec`,
for every input and model), and only `prctl_checker_*` over the
executable checker.  Neither group is in the mirror file, so each pin
here cites the kernel rather than a twin; the prctl section says how the
two dispatcher-level lemmas are twinned.  The `uname` fixtures Rocq's Prelude
builds on the Sys file (`uts_name_of`, `uts_demo`, `uts_demo_b`,
`uts_bad_sysname`, `uts_unterminated_release`, `uts_pinned`) are defined
here, name for name, beside the pins whose Rocq twins use them, and the
Lean Prelude's header registers them unported with that reason; Rocq's
`rlim_model` and `uts_model` are `demo_model`, and the pins say so.
Not part of the trusted specification: this file is QA on the
definitions, written to be READ, and every claim in it is a claim about
what the kernel does, with the citation beside it.  Every kernel line
below was read at Linux v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  Each decision of a spec gets an `iff` over EVERY
outcome `o` — the positive half (what is admitted) and the negative half
(nothing else is) in one statement — and beside it the concrete mistake a
lying kernel could report, refuted on its own.  Both are closed by the
tactics of `Checks/Cases/Tactic.lean`: `sys_norm` reads the call off its
monad primitives and decides the closed gates, `sys_refute` is `sys_norm`
that must close the goal.  Where an arm is an `alt` between the
environment's errnos and a success, the `iff`'s right-hand side keeps the
`alt`'s own grouping — the errno disjunction first, then the success — so
that it is the normal form `sys_norm` produces and nothing has to be
re-associated.  The credential fixtures are CLOSED models, so they need no
line in the register (`Checks/Cases/Prelude.lean`'s header says why: the
second pass evaluates every closed term to its constructor tree); the
`setsid` and `getpid` checks run on a SYMBOLIC model with the two gates
the spec reads stated as hypotheses, and hand the spec's unfolding and the
reading of `get_model` to `simp only` first, for the reason
`Checks/Cases/Kernel/Fork.lean`'s header gives about a match on a getter.
The three `*_never_declines` pins quantify over a spec's OWN arguments —
`get`, `put`, `user`, the ids — so no closed evaluation reaches their
gates; each is closed by `sys_simp_pass +decide`, then `repeat' split` to
open every `if` the symbolic arguments leave standing, then `sys_refute`
on each leaf.

Rocq's mirror file defines its own `demo_model`; here the Prelude's
`demo_model` is that model (the two are `init_model` of the same input),
and `split_ids_model` is built on it name for name.  `root_model` is the
one `Checks/Cases/Kernel/Groups.lean` defines, re-exported here: Rocq's
`Groups.v` imports it from `Sys.v`, and the Lean direction is reversed
because that twin landed first.  NO PROBE RUNS FROM `root_model`,
`split_ids_model`, `root_split_model` or `suid_root_model`: the harness
launches unprivileged with each triple collapsed to one id, so every pin
on those fixtures is judged against the kernel source alone, with the
citation beside it, and none carries a `probe:` line.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding, its errno list's, and its post-state builders', at low
priority.  The lines live here rather than in `Tactic.lean`'s register on
purpose: a port PR creates its own files and edits no shared one, so that
ports merge in any order.  `set_tid_address_spec.eq_1`, which `getpid_spec`
and `gettid_spec` unfold to, is registered by `Checks/Cases/Kernel/Fork.lean`
and imported. -/

attribute [sys_simp low]
  getpid_spec.eq_1 gettid_spec.eq_1 setsid_spec.eq_1 getid_spec.eq_1
  setid_spec.eq_1 setresid_spec.eq_1 setid_errnos.eq_1
  cred_uids.eq_1 cred_gids.eq_1 set_cred_uids.eq_1 set_cred_gids.eq_1
  uname_spec.eq_1 prlimit64_spec.eq_1 prctl_spec.eq_1
  rlim64_wf.eq_1 utsname_wf.eq_1

-- `record_copyins` is not in `Tactic.lean`'s register (`Checks/Cases/Fs/Namei.lean`
-- registers it locally for the same reason): `prlimit64_spec`'s set arm is
-- the only caller here.
attribute [local sys_simp low] record_copyins.eq_1

/-- `in_arg` is not in `sys_simp`, so a dispatcher pin whose spec matches on
memory at `in_arg i k` would stay stuck until the ground pass; these four
let the first pass read the register off a concrete `mkInput` (the shape
`Checks/Cases/Fs/Stat.lean` registers).  `a0` is the first register.
model: `in_arg` on a literal six-register `mkInput`, by `rfl`. -/
theorem in_arg_mkInput_0 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- `a1`, the second register.
model: `in_arg` on a literal six-register `mkInput`, by `rfl`. -/
theorem in_arg_mkInput_1 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- `a2`, the third register.
model: `in_arg` on a literal six-register `mkInput`, by `rfl`. -/
theorem in_arg_mkInput_2 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 2 = a2 := rfl
/-- `a3`, the fourth register.
model: `in_arg` on a literal six-register `mkInput`, by `rfl`. -/
theorem in_arg_mkInput_3 (n : word) (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 3 = a3 := rfl
attribute [local sys_simp] in_arg_mkInput_0 in_arg_mkInput_1 in_arg_mkInput_2 in_arg_mkInput_3

/-- A word equals itself: what `setresid_spec`'s no-op gate reduces to on a
SYMBOLIC credential record once every `(uid_t)-1` argument has been read
as "keep the current id".  Kept local: no other file states a check whose
gate compares a field with itself.
model: `bv_eqb x x` decided on a symbolic `x`, a rewrite for `sys_norm` -/
@[local sys_simp] theorem bv_eqb_self (x : word) : bv_eqb x x = true := (bv_eqb_eq x x).mpr rfl

/-- An equation on the bound variable in the LAST of four positions: what
`setsid_spec`'s `choose` guard leaves once a recorded tid makes its match
`t = t0`, behind the outcome equation and the two envelope bounds.  Core's
`exists_eq_right_right` stops at three.
model: the existential shape one guard leaves, a rewrite for `sys_norm` -/
@[local sys_simp] theorem exists_eq_right_right_right {α : Sort _} {p q r : α → Prop} {v : α} :
    (∃ a, p a ∧ q a ∧ r a ∧ a = v) ↔ p v ∧ q v ∧ r v := by
  constructor
  · rintro ⟨a, hp, hq, hr, rfl⟩
    exact ⟨hp, hq, hr⟩
  · rintro ⟨hp, hq, hr⟩
    exact ⟨v, hp, hq, hr, rfl⟩

/-! ## The numbers these checks spell out

Kept as numerals in the statements so a reader sees the register value a
kernel would answer; these pins say what each one is. -/

/-- `EPERM` is 1.
kernel: include/uapi/asm-generic/errno-base.h:EPERM@v6.18.46 -/
example : EPERM = 1 := by decide
/-- `EINVAL` is 22.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
example : EINVAL = 22 := by decide
/-- `ENOMEM` is 12.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
example : ENOMEM = 12 := by decide
/-- `EAGAIN` is 11.
kernel: include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
example : EAGAIN = 11 := by decide

/-- The model's spelling of `(uid_t)-1` after the `uid32` narrowing, at a
numeral.
model: the model's own constant at a numeral; the kernel reading is on `Sys/Uapi/Sched.lean`'s `ID_MINUS_ONE` and the `sysno_146_minus_one_is_einval` pin below -/
example : ID_MINUS_ONE = 4294967295 := by decide

/-- The envelope end `setsid`'s session id is drawn below, at a numeral.
model: the model's own constant at a numeral; the kernel reading behind it is on `Sys/Kernel/Fork.lean`'s `PID_MAX_ENVELOPE` -/
example : PID_MAX_ENVELOPE = 4194304 := by decide

/-- A user-id setter that moves the real uid can fail two ways: `-ENOMEM`
from `prepare_creds`'s allocation (`__sys_setuid`, kernel/sys.c:663-665,
Linux v6.18.46) and `-EAGAIN` from `set_user` (kernel/sys.c:527-529),
whose `alloc_uid` (kernel/user.c:204-244) returned NULL.
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
example : setid_errnos true = [ENOMEM, EAGAIN] := by decide
/-- ...and one that does not, or a group setter, only the first:
`__sys_setgid` (kernel/sys.c:479-513, Linux v6.18.46) answers
`prepare_creds`'s NULL with `-ENOMEM` (:491-493) and calls no `set_user`.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
example : setid_errnos false = [ENOMEM] := by decide

/-! ## Fixtures this file adds to the Prelude's

Rocq's mirror file defines `root_model` and `split_ids_model` over its own
`demo_model`; here they are the same setter applied to the Prelude's. -/

/-! A ROOT process — all six ids 0 — is `Checks/Cases/Kernel/Groups.lean`'s
`root_model`, whose docstring carries the privilege reading.  It is ONE
definition, shared, so that a pin here and a pin there run on the same
state; the header says why the import runs this way round. -/
export LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Groups (root_model)

/-- A process whose six ids are SIX DIFFERENT NUMBERS.  Nothing at launch
looks like this — `State.init_model` collapses each triple to one value —
so only a privilege change produces it and no probe run starts here.  Six
distinct values are what make the checks below discriminate: on a state
where the uid triple and the gid triple coincide, a dispatcher that wired
`getegid` to `cr_euid` would pass. -/
def split_ids_model : Model :=
  with_creds (Creds.mkCreds 1000 1001 1002 2000 2001 2002 demo_groups) demo_model

/-- A PRIVILEGED process whose saved uid is not its real one: real 0,
effective 0, saved 5 — what root becomes after `setresuid(-1, -1, 5)`, a
call the permission test lets a capable caller make (kernel/sys.c:745-747,
Linux v6.18.46) and that installs only the saved id (:763-764).
`State.init_model` never builds it, and it is the one state on which the
ORDER of `setuid`'s capability test and its real-or-saved rule is
observable. -/
def root_split_model : Model :=
  with_creds (Creds.mkCreds 0 0 5 0 0 0 demo_groups) demo_model

/-- A PRIVILEGED process whose REAL uid is not its effective one: real 5,
effective 0, saved 0 — what a mode-04755 root-owned binary runs as after
`execve` by uid 5, since `bprm_fill_uid` (fs/exec.c:1534, Linux v6.18.46)
sets only the effective uid to the file owner's under `S_ISUID` (:1575-1578)
and `cap_bprm_creds_from_file` (security/commoncap.c:909, Linux v6.18.46)
then copies it into the saved one (`new->suid = new->fsuid = new->euid`,
:953).  The group triple is root's for the fixture's sake; no pin below
reads it.  It is the one shape on which
"the real uid moves" and "the effective uid moves" come apart for a
privileged caller. -/
def suid_root_model : Model :=
  with_creds (Creds.mkCreds 5 0 0 0 0 0 demo_groups) demo_model

/-- The credential builders carry the supplementary list over: a user
triple installed by `set_cred_uids` leaves the three group ids and the
list exactly as they were, as `prepare_creds`'s `memcpy` of the old
`struct cred` and `get_group_info(new->group_info)` (kernel/cred.c:219 and
:223, Linux v6.18.46) leave them for every id setter.
kernel: kernel/cred.c:prepare_creds@v6.18.46 -/
example : set_cred_uids (IdTriple.mkIdTriple 1 2 3) demo_creds
    = Creds.mkCreds 1 2 3 demo_gid demo_gid demo_gid demo_groups := rfl
/-- ...and the group builder leaves the user ids and the list alone.
kernel: kernel/cred.c:prepare_creds@v6.18.46 -/
example : set_cred_gids (IdTriple.mkIdTriple 1 2 3) demo_creds
    = Creds.mkCreds demo_uid demo_uid demo_uid 1 2 3 demo_groups := rfl

/-! ## `getpid` (172) and `gettid` (178): one relation, three numbers

`SYSCALL_DEFINE0(getpid)` is `return task_tgid_vnr(current);` and
`SYSCALL_DEFINE0(gettid)` is `return task_pid_vnr(current);`
(kernel/sys.c:999-1002 and :1005-1008, Linux v6.18.46).  The second
expression is also what `SYSCALL_DEFINE1(set_tid_address)`
(kernel/fork.c:1747-1752) returns.  The specs ARE
`set_tid_address_spec`, so each pin below is the `set_tid_address` pin
under the name a reader asks for, closed by that pin — which is the point
of stating them: a reader asking "what may `getpid` answer?" should not
have to know that three numbers share one relation before the answer is
reachable.  The two `_first_call_draws_a_live_tid` pins are the twins of
the Rocq mirror file's two envelope lemmas. -/

/-- The whole first `getpid`: some tid strictly inside the envelope,
returned, recorded in `m_tid`, no write, no event.  The envelope's two ends
are `alloc_pid`'s `pid_min = 1` (kernel/pid.c:226, Linux v6.18.46) and
`idr_alloc_cyclic`'s exclusive `end`, the namespace's `pid_max`
(kernel/pid.c:193, :238-239; lib/idr.c:102), which the `pid_max` sysctl
holds at or below `PID_MAX_LIMIT` (kernel/pid.c:65, :743-749, :805); the tgid a
thread-group leader reports is the pid of the one `struct pid` in both
its slots (kernel/fork.c:2379-2381).
rocq-twin: getpid_first_choice_is_within_modeled_envelope
kernel: kernel/sys.c:getpid; include/linux/pid.h:task_tgid_vnr; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem getpid_first_call_draws_a_live_tid (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (o : outcome SyscallEffect) :
    getpid_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 :=
  set_tid_address_first_call_draws_a_live_tid i m h o

/-- The whole first `gettid`, the same envelope: `task_pid_vnr(current)` is
one expression evaluated by this call (kernel/sys.c:1007, Linux v6.18.46)
and by `set_tid_address` (kernel/fork.c:1751), so nothing has to be
joined.
rocq-twin: gettid_first_choice_is_within_modeled_envelope
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem gettid_first_call_draws_a_live_tid (i : SyscallInput) (m : Model)
    (h : m_tid m = none) (o : outcome SyscallEffect) :
    gettid_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 :=
  set_tid_address_first_call_draws_a_live_tid i m h o

/-- Once a tid is recorded — by any of the three calls — `getpid` answers
it and moves nothing: `task_tgid_vnr` reads a `struct pid` the task holds
for its whole life (include/linux/pid.h:296-299, Linux v6.18.46).
kernel: kernel/sys.c:getpid; include/linux/pid.h:task_tgid_vnr@v6.18.46 -/
theorem getpid_repeats_the_recorded_tid (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (o : outcome SyscallEffect) :
    getpid_spec i m o ↔ o = Ok (mkEffect tid [] []) m [] :=
  set_tid_address_repeats_the_recorded_tid i m tid h o

/-- ...and so does `gettid`: whichever of the three calls ran first pinned
the identity, and the others return it (the `gettid-first` and
`getpid-first` cases of `testing/syscall-check/tests/gettid_spec.c`).
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem gettid_repeats_the_recorded_tid (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (o : outcome SyscallEffect) :
    gettid_spec i m o ↔ o = Ok (mkEffect tid [] []) m [] :=
  set_tid_address_repeats_the_recorded_tid i m tid h o

/-- A kernel answering pid 0 is lying: `alloc_pid` allocates from
`pid_min`, initialised to 1 and only ever raised (kernel/pid.c:226-232,
Linux v6.18.46).
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem getpid_zero_pid_rejected (i : SyscallInput) (m : Model) (h : m_tid m = none) :
    ¬ getpid_spec i m (Ok (mkEffect 0 [] []) (with_tid 0 m) []) :=
  set_tid_address_zero_tid_rejected i m h

/-- ...and so is one answering `2^22` itself, the exclusive envelope end
(`idr_alloc_cyclic`, lib/idr.c:102, Linux v6.18.46).
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem getpid_envelope_end_rejected (i : SyscallInput) (m : Model) (h : m_tid m = none) :
    ¬ getpid_spec i m (Ok (mkEffect 4194304 [] []) (with_tid 4194304 m) []) :=
  set_tid_address_envelope_end_rejected i m h

/-- `gettid` answering 0 is the same lie, for the same reason.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem gettid_zero_tid_rejected (i : SyscallInput) (m : Model) (h : m_tid m = none) :
    ¬ gettid_spec i m (Ok (mkEffect 0 [] []) (with_tid 0 m) []) :=
  set_tid_address_zero_tid_rejected i m h

/-- ...and `2^22` too.
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem gettid_envelope_end_rejected (i : SyscallInput) (m : Model) (h : m_tid m = none) :
    ¬ gettid_spec i m (Ok (mkEffect 4194304 [] []) (with_tid 4194304 m) []) :=
  set_tid_address_envelope_end_rejected i m h

/-- A later `getpid` answering a DIFFERENT number is lying: nothing in the
call allocates or changes a pid.
kernel: kernel/sys.c:getpid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem getpid_cannot_change_the_recorded_tid (i : SyscallInput) (m : Model) (tid tid' : word)
    (h : m_tid m = some tid) (hne : tid' ≠ tid) :
    ¬ getpid_spec i m (Ok (mkEffect tid' [] []) m []) :=
  set_tid_address_second_call_cannot_change_the_tid i m tid tid' h hne

/-- ...and a `gettid` defecting from the pid `getpid` pinned is the lie the
`reject --mutate gettid:ret+1 -- getpid-first` case of
`testing/syscall-check/tests/gettid_spec.c` tells.
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem gettid_cannot_defect_from_the_recorded_tid (i : SyscallInput) (m : Model)
    (tid tid' : word) (h : m_tid m = some tid) (hne : tid' ≠ tid) :
    ¬ gettid_spec i m (Ok (mkEffect tid' [] []) m []) :=
  set_tid_address_second_call_cannot_change_the_tid i m tid tid' h hne

/-- Neither call writes user memory: both bodies are a single `return`
(kernel/sys.c:1001 and :1007, Linux v6.18.46), and riscv's
`SYSCALL_DEFINE0` reads no argument register for them
(arch/riscv/include/asm/syscall_wrapper.h:99-103).
kernel: kernel/sys.c:getpid,gettid@v6.18.46 -/
theorem getpid_writes_no_user_memory (i : SyscallInput) (m : Model) (h : m_tid m = none)
    (tid a : word) (b : byte) :
    ¬ getpid_spec i m (Ok (mkEffect tid [(a, [b])] []) (with_tid tid m) []) :=
  set_tid_address_writes_no_user_memory i m h tid a b

/-- Neither call declines or answers an errno: `SYSCALL_DEFINE0(getpid)`
and `SYSCALL_DEFINE0(gettid)` have no error path (kernel/sys.c:999-1008,
Linux v6.18.46); the one residual, `ALLOW_ERROR_INJECTION`, is stated on
the spec and not modeled.
kernel: kernel/sys.c:getpid,gettid@v6.18.46 -/
theorem getpid_never_declines (i : SyscallInput) (m : Model) : ¬ getpid_spec i m Unmodeled :=
  set_tid_address_never_declines i m

/-- ...`gettid` neither.
kernel: kernel/sys.c:getpid,gettid@v6.18.46 -/
theorem gettid_never_declines (i : SyscallInput) (m : Model) : ¬ gettid_spec i m Unmodeled :=
  set_tid_address_never_declines i m

/-- A kernel reporting `-EINVAL` from `getpid` is lying: there is no error
path (kernel/sys.c:999-1002, Linux v6.18.46), and `errno_ret EINVAL` is
`2^64 - 22`, which no tid inside the envelope can be.
kernel: kernel/sys.c:getpid@v6.18.46 -/
theorem getpid_never_answers_an_errno (i : SyscallInput) (m : Model) (tid : word)
    (h : m_tid m = some tid) (henv : bv_unsigned tid < PID_MAX_ENVELOPE) :
    ¬ getpid_spec i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  set_tid_address_never_answers_an_errno i m tid h henv

/-- Syscall 172 reaches the draw: the number is modeled and the arm is
`getpid_spec`.
kernel: kernel/sys.c:getpid@v6.18.46 -/
theorem dispatch_172_draws_a_live_tid (i : SyscallInput) (m : Model)
    (hno : bv_unsigned i.in_sysno = 172) (h : m_tid m = none) (o : outcome SyscallEffect) :
    syscall_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 := by
  unfold syscall_spec dispatch
  rw [hno]
  exact getpid_first_call_draws_a_live_tid i m h o

/-- Syscall 178 too: the arm is `gettid_spec`.
kernel: kernel/sys.c:gettid@v6.18.46 -/
theorem dispatch_178_draws_a_live_tid (i : SyscallInput) (m : Model)
    (hno : bv_unsigned i.in_sysno = 178) (h : m_tid m = none) (o : outcome SyscallEffect) :
    syscall_spec i m o ↔
      ∃ tid : word, o = Ok (mkEffect tid [] []) (with_tid tid m) []
        ∧ 0 < bv_unsigned tid ∧ bv_unsigned tid < 4194304 := by
  unfold syscall_spec dispatch
  rw [hno]
  exact gettid_first_call_draws_a_live_tid i m h o

/-! ## `setsid` (157)

`ksys_setsid` (kernel/sys.c:1268-1301, Linux v6.18.46) seeds `err =
-EPERM` (:1274), fails if the caller already leads a session (:1278) or if
a process group named by its pid still has a live task (:1284), and
otherwise sets the leader bit (:1287) and answers the caller's tgid
(:1273, :1292).  Neither test reads state the model carries, so the first
call admits both answers; the leader bit, once set, is never cleared, so a
call after a success admits one. -/

/-- The whole first call: `-EPERM`, or a session id strictly inside the
envelope with the tid recorded and the leader bit set.  The session id is
`pid_vnr(task_pid(group_leader))` (kernel/sys.c:1271-1273), the caller's
own pid — hence the same envelope `getpid` draws from — and the recorded
bit is `group_leader->signal->leader = 1` (:1287).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:pid_vnr@v6.18.46 -/
theorem setsid_first_call_is_eperm_or_a_session_id (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) (o : outcome SyscallEffect) :
    setsid_spec i m o ↔
      (o = Ok (mkEffect (errno_ret EPERM) [] []) m []
       ∨ ∃ t : word, o = Ok (mkEffect t [] []) (with_setsid_succeeded (with_tid t m)) []
           ∧ 0 < bv_unsigned t ∧ bv_unsigned t < 4194304) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_norm

/-- `-EPERM` is admitted on a first call: `pid_task(sid, PIDTYPE_PGID)`
finds a task whenever the launching shell put this process in its own
group (kernel/sys.c:1284; `pid_task`, kernel/pid.c:414-425).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:pid_task@v6.18.46 -/
theorem setsid_first_call_may_be_eperm (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    setsid_spec i m (Ok (mkEffect (errno_ret EPERM) [] []) m []) :=
  (setsid_first_call_is_eperm_or_a_session_id i m hs h _).mpr (Or.inl rfl)

/-- ...and so is the envelope's first id, 1: `pid_min` starts there
(kernel/pid.c:226).  The `conform --mutate setsid:ret=1 -- setsid` case of
`testing/syscall-check/tests/proc_creation.c` is the probe half.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem setsid_first_call_may_answer_one (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    setsid_spec i m (Ok (mkEffect 1 [] []) (with_setsid_succeeded (with_tid 1 m)) []) :=
  (setsid_first_call_is_eperm_or_a_session_id i m hs h _).mpr
    (Or.inr ⟨1, rfl, by decide, by decide⟩)

/-- ...and the envelope's last, `2^22 - 1` (`idr_alloc_cyclic`'s exclusive
`end`, lib/idr.c:102, over `pid_max ≤ PID_MAX_LIMIT`).
kernel: kernel/sys.c:ksys_setsid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem setsid_first_call_may_answer_the_envelope_top (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    setsid_spec i m
      (Ok (mkEffect 4194303 [] []) (with_setsid_succeeded (with_tid 4194303 m)) []) :=
  (setsid_first_call_is_eperm_or_a_session_id i m hs h _).mpr
    (Or.inr ⟨4194303, rfl, by decide, by decide⟩)

/-- 0 is neither answer: not `-EPERM`, and not a pid any live task holds
(kernel/pid.c:226 and :199, Linux v6.18.46).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem setsid_zero_rejected (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    ¬ setsid_spec i m (Ok (mkEffect 0 [] []) (with_setsid_succeeded (with_tid 0 m)) []) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_refute

/-- ...and neither is `2^22`, the exclusive end.
kernel: kernel/sys.c:ksys_setsid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem setsid_envelope_end_rejected (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    ¬ setsid_spec i m
        (Ok (mkEffect 4194304 [] []) (with_setsid_succeeded (with_tid 4194304 m)) []) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_refute

/-- `-EPERM` is the only errno: `ksys_setsid` seeds `err = -EPERM`
(kernel/sys.c:1274) and no path assigns another, so `-EACCES` is a lie.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_eacces_rejected (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) (m' : Model) (evs : List event) :
    ¬ setsid_spec i m (Ok (mkEffect (errno_ret EACCES) [] []) m' evs) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_refute

/-- `setsid` takes no arguments and writes no user memory:
`SYSCALL_DEFINE0(setsid)` (kernel/sys.c:1303-1306) is `return
ksys_setsid();`, and `ksys_setsid` (kernel/sys.c:1268-1301) touches only
the task's own pid links.
kernel: kernel/sys.c:setsid,ksys_setsid@v6.18.46 -/
theorem setsid_writes_no_user_memory (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) (t a : word) (b : byte)
    (m' : Model) (evs : List event) :
    ¬ setsid_spec i m (Ok (mkEffect t [(a, [b])] []) m' evs) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_refute

/-- Read as a forcing statement: a first call that answers a value inside
the envelope RECORDED it, both the tid and the leader bit, and emitted
nothing.  The envelope bound excludes the `-EPERM` arm, whose register
value is `2^64 - 1`.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_first_call_success_records (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) (t : word) (m' : Model)
    (evs : List event) (henv : bv_unsigned t < 4194304)
    (hspec : setsid_spec i m (Ok (mkEffect t [] []) m' evs)) :
    m' = with_setsid_succeeded (with_tid t m) ∧ evs = [] := by
  rcases (setsid_first_call_is_eperm_or_a_session_id i m hs h _).mp hspec with ho | ⟨t', ho, -, -⟩
  · injection ho with he _ _
    injection he with hv
    rw [hv] at henv
    exact absurd henv (by decide)
  · injection ho with he hm hev
    injection he with hv
    subst hv
    exact ⟨hm, hev⟩

/-- So a kernel answering a session id while the model records NOTHING is
lying: the leader bit is written before the answer (kernel/sys.c:1287,
:1292).
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_success_must_record (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    ¬ setsid_spec i m (Ok (mkEffect 1234 [] []) m []) := by
  intro hspec
  have hm := (setsid_first_call_success_records i m hs h 1234 m [] (by decide) hspec).1
  have e : m_setsid_succeeded m = true := congrArg m_setsid_succeeded hm
  rw [hs] at e
  cases e

/-- ...and so is one recording the tid but not the bit: the bit is what
makes the NEXT call fail, and a model without it would allow a second
success (`reject --mutate setsid#1:ret=1234 --mutate setsid#2:ret=1234 --
setsid2` in `testing/syscall-check/tests/proc_creation.c`).
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_success_must_set_the_leader_bit (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    ¬ setsid_spec i m (Ok (mkEffect 1234 [] []) (with_tid 1234 m) []) := by
  intro hspec
  have hm := (setsid_first_call_success_records i m hs h 1234 _ [] (by decide) hspec).1
  have e : m_setsid_succeeded m = true := congrArg m_setsid_succeeded hm
  rw [hs] at e
  cases e

/-- ...and one setting the bit without recording the tid: the session id
IS the tid, so a later `getpid` would be free to answer another number.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:pid_vnr@v6.18.46 -/
theorem setsid_success_must_record_the_tid (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = none) :
    ¬ setsid_spec i m (Ok (mkEffect 1234 [] []) (with_setsid_succeeded m) []) := by
  intro hspec
  have hm := (setsid_first_call_success_records i m hs h 1234 _ [] (by decide) hspec).1
  have e : m_tid m = some 1234 := congrArg m_tid hm
  rw [h] at e
  cases e

/-- A first `setsid` AFTER a `getpid` or `set_tid_address` pinned the tid:
`-EPERM`, or exactly that tid — `pid_vnr(task_pid(group_leader))` is the
number `getpid` already answered (kernel/sys.c:1271-1273 against :1001).
The two envelope bounds stay as conjuncts because the statement is about
every recorded value, not only the ones the model can reach.
kernel: kernel/sys.c:ksys_setsid,getpid; kernel/pid.c:pid_vnr@v6.18.46 -/
theorem setsid_after_a_pinned_tid_answers_it (i : SyscallInput) (m : Model) (t0 : word)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = some t0) (o : outcome SyscallEffect) :
    setsid_spec i m o ↔
      (o = Ok (mkEffect (errno_ret EPERM) [] []) m []
       ∨ (o = Ok (mkEffect t0 [] []) (with_setsid_succeeded (with_tid t0 m)) []
           ∧ 0 < bv_unsigned t0 ∧ bv_unsigned t0 < 4194304)) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_norm

/-- Two identities is the lie the `reject --mutate set_tid_address:ret=1234
--mutate setsid:ret=1235 -- tidpin` case tells: with 1234 recorded, a
session id of 1235 is refused.
kernel: kernel/sys.c:ksys_setsid,getpid; kernel/pid.c:pid_vnr@v6.18.46 -/
theorem setsid_cannot_answer_a_second_identity (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = false) (h : m_tid m = some 1234) (m' : Model)
    (evs : List event) :
    ¬ setsid_spec i m (Ok (mkEffect 1235 [] []) m' evs) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs, h]
  sys_refute

/-- After a SUCCESS every call is `-EPERM`, whatever else the model holds:
`ksys_setsid` tests `group_leader->signal->leader` first (kernel/sys.c:1278)
and nothing in the tree clears the bit it set (:1287 is its only writer;
`SYSCALL_DEFINE2(setpgid)` refuses a leader at :1157-1159).
kernel: kernel/sys.c:ksys_setsid,setpgid@v6.18.46 -/
theorem setsid_after_a_success_is_eperm (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = true) (o : outcome SyscallEffect) :
    setsid_spec i m o ↔ o = Ok (mkEffect (errno_ret EPERM) [] []) m [] := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs]
  sys_norm

/-- A repeat success is refused — the `reject --mutate setsid#1:ret=1234
--mutate setsid#2:ret=1234 -- setsid2` case.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_repeat_success_rejected (i : SyscallInput) (m : Model)
    (hs : m_setsid_succeeded m = true) (m' : Model) (evs : List event) :
    ¬ setsid_spec i m (Ok (mkEffect 1234 [] []) m' evs) := by
  simp only [setsid_spec.eq_1, bind_get_model_iff, hs]
  sys_refute

/-- ...and it is the BIT that refuses it, not the recorded tid: on a model
whose bit is set while `m_tid` is still `none`, a success is still
refused.  This is the distinction Rocq's `setsid_checker_bit_alone_rejects_success`
(`Checks/ProcessCreation.v`) draws over the checker.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_bit_alone_rejects_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setsid_spec i (with_setsid_succeeded demo_model) (Ok (mkEffect 1234 [] []) m' evs) := by
  sys_refute

/-- A FAILED call latches nothing: `demo_model` is the state a `-EPERM`
leaves behind, and a call from it may still succeed — the `conform
--mutate setsid#1:ret=-EPERM --mutate setsid#2:ret=1234 -- setsid2` case.
The process-group test can stop firing once the group it named empties
(kernel/sys.c:1284), so recording the failure would forbid a run Linux
allows.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:pid_task@v6.18.46 -/
theorem setsid_after_a_failure_may_succeed (i : SyscallInput) :
    setsid_spec i demo_model
      (Ok (mkEffect 1234 [] []) (with_setsid_succeeded (with_tid 1234 demo_model)) []) := by
  sys_norm

/-- `setsid` never declines: both tests answer, and the model says which
answers it cannot tell apart rather than failing closed.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_never_declines (i : SyscallInput) (m : Model) : ¬ setsid_spec i m Unmodeled := by
  sys_simp_pass +decide
  repeat' split
  all_goals sys_refute

/-- Syscall 157 is `setsid_spec`, through the table.
kernel: kernel/sys.c:setsid,ksys_setsid@v6.18.46 -/
theorem dispatch_157_is_setsid (i : SyscallInput) (m : Model)
    (hno : bv_unsigned i.in_sysno = 157) (hs : m_setsid_succeeded m = false)
    (h : m_tid m = none) (o : outcome SyscallEffect) :
    syscall_spec i m o ↔
      (o = Ok (mkEffect (errno_ret EPERM) [] []) m []
       ∨ ∃ t : word, o = Ok (mkEffect t [] []) (with_setsid_succeeded (with_tid t m)) []
           ∧ 0 < bv_unsigned t ∧ bv_unsigned t < 4194304) := by
  unfold syscall_spec dispatch
  rw [hno]
  exact setsid_first_call_is_eperm_or_a_session_id i m hs h o

/-! ## The four readers: `getuid` (174), `geteuid` (175), `getgid` (176), `getegid` (177)

Each is `return from_kuid_munged(current_user_ns(), current_uid())` for
its own field (kernel/sys.c:1027-1049, Linux v6.18.46).  In the init user
namespace the mapping is the identity — `init_user_ns.uid_map` is one
extent from 0 of count 4294967295 (kernel/user.c:38-46) — so the answer is
the stored id, and `from_kuid_munged` cannot fail (kernel/user_namespace.c:466-474, Linux v6.18.46). -/

/-- `getuid` answers the real uid of ANY credential state, moves nothing
and emits nothing: `current_uid()` is `current_cred()->uid`.
kernel: kernel/sys.c:getuid; kernel/user_namespace.c:from_kuid_munged@v6.18.46 -/
theorem getuid_reads_the_real_uid (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getid_spec Creds.cr_uid i m o ↔ o = Ok (mkEffect (m_creds m).cr_uid [] []) m [] := by
  sys_norm

/-- `geteuid`, `getgid` and `getegid` likewise, each its own field.
kernel: kernel/sys.c:geteuid,getgid,getegid; kernel/user_namespace.c:from_kuid_munged,from_kgid_munged@v6.18.46 -/
theorem the_other_readers_read_their_own_field (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    (getid_spec Creds.cr_euid i m o ↔ o = Ok (mkEffect (m_creds m).cr_euid [] []) m [])
    ∧ (getid_spec Creds.cr_gid i m o ↔ o = Ok (mkEffect (m_creds m).cr_gid [] []) m [])
    ∧ (getid_spec Creds.cr_egid i m o ↔ o = Ok (mkEffect (m_creds m).cr_egid [] []) m []) := by
  sys_norm

/-- Each reader reads ITS OWN field, told apart on six different ids.  The
harness cannot distinguish the two readers it can call — the devcontainer
runs as uid 1000, gid 1000, so `getuid` and `getgid` agree there
(`testing/syscall-check/tests/creds_spec.c`'s `read` case).
rocq-twin: each_reader_reads_its_own_field
kernel: kernel/sys.c:getuid,geteuid,getgid,getegid@v6.18.46 -/
theorem each_reader_reads_its_own_field (i : SyscallInput) (o : outcome SyscallEffect) :
    (getid_spec Creds.cr_uid i split_ids_model o ↔ o = Ok (mkEffect 1000 [] []) split_ids_model [])
    ∧ (getid_spec Creds.cr_euid i split_ids_model o ↔ o = Ok (mkEffect 1001 [] []) split_ids_model [])
    ∧ (getid_spec Creds.cr_gid i split_ids_model o ↔ o = Ok (mkEffect 2000 [] []) split_ids_model [])
    ∧ (getid_spec Creds.cr_egid i split_ids_model o ↔ o = Ok (mkEffect 2001 [] []) split_ids_model []) := by
  sys_norm

/-- `getgid` answering the uid is a lie...
kernel: kernel/sys.c:getgid@v6.18.46 -/
theorem getgid_does_not_answer_the_uid (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getid_spec Creds.cr_gid i split_ids_model (Ok (mkEffect 1000 [] []) m' evs) := by
  sys_refute

/-- ...`getegid` answering the effective uid too...
kernel: kernel/sys.c:getegid@v6.18.46 -/
theorem getegid_does_not_answer_the_euid (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getid_spec Creds.cr_egid i split_ids_model (Ok (mkEffect 1001 [] []) m' evs) := by
  sys_refute

/-- ...and `geteuid` answering the saved uid, which no reader reports
(`getresuid` would, and it has no arm).
kernel: kernel/sys.c:geteuid@v6.18.46 -/
theorem geteuid_does_not_answer_the_suid (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getid_spec Creds.cr_euid i split_ids_model (Ok (mkEffect 1002 [] []) m' evs) := by
  sys_refute

/-- A reader writes no user memory: it takes no pointer.
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem getuid_writes_no_user_memory (i : SyscallInput) (m : Model) (v a : word) (b : byte)
    (m' : Model) (evs : List event) :
    ¬ getid_spec Creds.cr_uid i m (Ok (mkEffect v [(a, [b])] []) m' evs) := by
  sys_refute

/-- A reader never declines, whichever field and whatever the state.
kernel: kernel/sys.c:getuid,geteuid,getgid,getegid@v6.18.46 -/
theorem getid_never_declines (sel : Creds → word) (i : SyscallInput) (m : Model) :
    ¬ getid_spec sel i m Unmodeled := by
  sys_refute

/-- A reader never answers an errno: every id a run can hold is below
`2^32` (`Run.valid_id`, kept by the setters below), and `from_kuid_munged`
turns even an unmappable id into the overflow id, never an errno
(kernel/user_namespace.c:466-474, Linux v6.18.46).  The register value of
`-EPERM` is `2^64 - 1`, outside that bound.
kernel: kernel/sys.c:getuid; kernel/user_namespace.c:from_kuid_munged@v6.18.46 -/
theorem getuid_never_answers_an_errno (i : SyscallInput) (m : Model)
    (hid : bv_unsigned (m_creds m).cr_uid < 4294967296) (m' : Model) (evs : List event) :
    ¬ getid_spec Creds.cr_uid i m (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  intro hspec
  have ho := (getuid_reads_the_real_uid i m _).mp hspec
  injection ho with he _ _
  injection he with hv
  rw [← hv] at hid
  exact absurd hid (by decide)

/-- Syscall 174 is `getuid`, through the table...
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem sysno_174_is_getuid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 174 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        split_ids_model o
      ↔ o = Ok (mkEffect 1000 [] []) split_ids_model [] := by
  sys_norm

/-- ...175 `geteuid`...
kernel: kernel/sys.c:geteuid@v6.18.46 -/
theorem sysno_175_is_geteuid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 175 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        split_ids_model o
      ↔ o = Ok (mkEffect 1001 [] []) split_ids_model [] := by
  sys_norm

/-- ...176 `getgid`...
kernel: kernel/sys.c:getgid@v6.18.46 -/
theorem sysno_176_is_getgid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 176 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        split_ids_model o
      ↔ o = Ok (mkEffect 2000 [] []) split_ids_model [] := by
  sys_norm

/-- ...and 177 `getegid`.  Junk in the argument registers is ignored: none
of the four reads one.
kernel: kernel/sys.c:getegid@v6.18.46 -/
theorem sysno_177_is_getegid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 177 [7, 7, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        split_ids_model o
      ↔ o = Ok (mkEffect 2001 [] []) split_ids_model [] := by
  sys_norm

/-! ## `setuid` (146) and `setgid` (144)

`__sys_setuid` (kernel/sys.c:651-696, Linux v6.18.46), in order:
`make_kuid` and `uid_valid` (:659-661) refuse `(uid_t)-1` with `-EINVAL`;
`prepare_creds` (:663-665) may answer `-ENOMEM`; `ns_capable_setid`
(:669) decides between the privileged assignment of all three ids (:670,
:680) with `set_user` when the real uid moves (:671-674), and the
unprivileged rule that the argument be the real or the saved id (:676-677)
with only the effective id moving (:680); the refusal is `-EPERM` (:668).
`__sys_setgid` (:479-513) is the same shape without `set_user`. -/

/-- `(uid_t)-1` is `-EINVAL` for EVERY credential state, before anything
allocates: `make_kuid(ns, uid)` maps it to an id `uid_valid` refuses
(kernel/sys.c:659-661; include/linux/uidgid.h:103-106).
kernel: kernel/sys.c:__sys_setuid; include/linux/uidgid.h:uid_valid@v6.18.46 -/
theorem setuid_minus_one_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 4294967295 i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- ...and `setgid((gid_t)-1)` likewise: `__sys_setgid` (kernel/sys.c:487-489, Linux v6.18.46)
refuses what `gid_valid` (include/linux/uidgid.h:108-111) refuses.
kernel: kernel/sys.c:__sys_setgid; include/linux/uidgid.h:gid_valid@v6.18.46 -/
theorem setgid_minus_one_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    setid_spec cred_gids set_cred_gids false 4294967295 i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- That call can never answer `-ENOMEM`: the `-EINVAL` return
(kernel/sys.c:661) precedes `prepare_creds` (:663).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_minus_one_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 4294967295 i m
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- ...nor succeed, even for root.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_minus_one_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 4294967295 i root_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- One below it, `0xfffffffe`, is the LARGEST VALID uid: `uid_valid` is
`!uid_eq(kuid, INVALID_UID)` and nothing else, so root installs it in all
three slots like any other id (kernel/sys.c:670 and :680), and `set_user`
runs since the real uid moves.
kernel: kernel/sys.c:__sys_setuid,set_user; include/linux/uidgid.h:uid_valid@v6.18.46 -/
theorem privileged_setuid_to_the_largest_valid_uid_installs_it (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 4294967294 i root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 4294967294 4294967294 4294967294 0 0 0 demo_groups)
                demo_model) []) := by
  sys_norm

/-- ...and `getuid` on the state that leaves READS IT BACK as the value:
`init_user_ns`'s map is one extent of count `4294967295` from 0
(kernel/user.c:38-46), so `from_kuid_munged` maps `0xfffffffe` to itself
rather than to the overflow id, and the register holds it below the errno
band.
kernel: kernel/sys.c:getuid; kernel/user_namespace.c:from_kuid_munged@v6.18.46 -/
theorem getuid_reads_the_largest_valid_uid (i : SyscallInput) (o : outcome SyscallEffect) :
    getid_spec Creds.cr_uid i
        (with_creds (Creds.mkCreds 4294967294 4294967294 4294967294 0 0 0 demo_groups) demo_model)
        o ↔
      o = Ok (mkEffect 4294967294 [] [])
            (with_creds (Creds.mkCreds 4294967294 4294967294 4294967294 0 0 0 demo_groups)
              demo_model) [] := by
  sys_norm

/-- PRIVILEGED `setuid(1000)` from root: `-ENOMEM` or `-EAGAIN` from the
environment, or real, effective and saved all become 1000
(kernel/sys.c:670 and :680) with the group ids untouched — the transition
that gives root away for good, since `cap_emulate_setxuid`
(security/commoncap.c:1110-1136) then clears `cap_permitted`.
rocq-twin: privileged_setuid_moves_all_three_ids
kernel: kernel/sys.c:__sys_setuid,set_user; security/commoncap.c:cap_emulate_setxuid@v6.18.46 -/
theorem privileged_setuid_moves_all_three_ids (i : SyscallInput) (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1000 i root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- A privileged caller is never refused: `-EPERM` is set (kernel/sys.c:668)
and then overwritten on the capable branch.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_eperm_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i root_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- A success that moved only the effective id — the UNPRIVILEGED shape —
is a lie for root: `new->suid = new->uid = kuid` (kernel/sys.c:670) runs
on the capable branch.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_effective_only_rejected (i : SyscallInput) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i root_model
        (Ok (mkEffect 0 [] []) (with_creds (Creds.mkCreds 0 1000 0 0 0 0 demo_groups) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- ...and so is a success that left the model as it was.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_unchanged_model_rejected (i : SyscallInput) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i root_model (Ok (mkEffect 0 [] []) root_model evs) := by
  intro hspec
  sys_refute at hspec

/-- PRIVILEGED `setuid` to the SAVED uid still moves all three ids: the
capable branch (kernel/sys.c:669-674) runs whatever the argument is, and
the real-or-saved rule (:676) is the `else` of it, never consulted for a
capable caller.  On `root_split_model` the two orders disagree — a spec
that asked the real-or-saved rule first would move the effective id alone
and allow no `-EAGAIN` — and the kernel's order installs 5 everywhere and
runs `set_user` because the real uid moved.
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
theorem privileged_setuid_to_the_saved_uid_moves_all_three_ids (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 5 i root_split_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_split_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_split_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 5 5 5 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- ...so the effective-only shape is refused there too.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_to_the_saved_uid_effective_only_rejected (i : SyscallInput)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 5 i root_split_model
        (Ok (mkEffect 0 [] []) (with_creds (Creds.mkCreds 0 5 5 0 0 0 demo_groups) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- `-EAGAIN` follows the REAL uid, not the effective one.  PRIVILEGED
`setuid(0)` from the set-uid-root shape (real 5, effective 0) moves the
real uid onto the effective one: `set_user` runs, because the test guarding
it is `!uid_eq(kuid, old->uid)` against the REAL uid (kernel/sys.c:671-672)
and 0 differs from 5 — the effective uid, already 0, plays no part.  So
`-EAGAIN` is admitted, and the installation lands on `root_model`'s ids.
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
theorem privileged_setuid_moving_the_real_uid_onto_the_effective_admits_eagain
    (i : SyscallInput) (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 0 i suid_root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) suid_root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) suid_root_model [])
       ∨ o = Ok (mkEffect 0 [] []) root_model []) := by
  sys_norm

/-- ...and `setuid(5)` from the same shape names the REAL uid: the effective
and saved ids move to 5 (kernel/sys.c:670, :680), `set_user` is skipped
(:671) and `set_cred_ucounts` takes its fast path because `new->uid` is the
uid its ucounts already hold (kernel/cred.c:541-542), so `-EAGAIN` is
refused while `-ENOMEM` and the installation remain.  A spec that compared
the argument with the EFFECTIVE uid would answer these two calls the other
way round.
kernel: kernel/sys.c:__sys_setuid; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem privileged_setuid_keeping_the_real_uid_admits_no_eagain (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 5 i suid_root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) suid_root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 5 5 5 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- ...stated as the refusal.
kernel: kernel/sys.c:__sys_setuid; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem privileged_setuid_keeping_the_real_uid_eagain_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 5 i suid_root_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `-EAGAIN` in the one place it is admissible: a USER-id setter,
privileged, moving the real uid.  `set_user` runs only under
`!uid_eq(kuid, old->uid)` (kernel/sys.c:671-672) and `set_cred_ucounts`
allocates only when `new->uid` moved (kernel/cred.c:541-545); the
`--mutate setuid:ret=-EAGAIN` cases of
`testing/syscall-check/tests/creds_spec.c` are all rejections, because a
probe cannot reach a privileged setter.
rocq-twin: eagain_only_when_a_privileged_setuid_moves_the_real_uid
kernel: kernel/sys.c:__sys_setuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem eagain_only_when_a_privileged_setuid_moves_the_real_uid (i : SyscallInput) :
    setid_spec cred_uids set_cred_uids true 1000 i root_model
      (Ok (mkEffect (errno_ret EAGAIN) [] []) root_model []) := by
  sys_norm

/-- Privileged, but the real uid does not move (`setuid(0)` from root):
`set_user` is skipped and `set_cred_ucounts` takes its fast path, so
`-EAGAIN` is refused while `-ENOMEM` and the (unchanged) success remain.
kernel: kernel/sys.c:__sys_setuid; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem privileged_setuid_to_the_real_uid_admits_no_eagain (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 0 i root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] []) root_model []) := by
  sys_norm

/-- ...stated as the refusal.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_to_the_real_uid_eagain_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 0 i root_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- PRIVILEGED `setgid(1000)` from root: `-ENOMEM`, or all three group ids
become 1000 (kernel/sys.c:497-498) with the user ids untouched; there is
no `set_user` on the group side, so no `-EAGAIN`.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem privileged_setgid_moves_all_three_gids (i : SyscallInput) (o : outcome SyscallEffect) :
    setid_spec cred_gids set_cred_gids false 1000 i root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 1000 1000 1000 demo_groups) demo_model) []) := by
  sys_norm

/-- The group setter on the same shape as the `-EAGAIN` case above: refused,
since `__sys_setgid` (kernel/sys.c:479-513, Linux v6.18.46) calls neither
`set_user` nor `set_cred_ucounts`.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem privileged_setgid_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setid_spec cred_gids set_cred_gids false 1000 i root_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- UNPRIVILEGED `setuid` to the REAL uid moves the effective id and
nothing else (kernel/sys.c:676-680): on six split ids, 1000 becomes the
effective id, the saved id 1002 stays.
rocq-twin: unprivileged_setuid_moves_only_the_effective_id
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_the_real_uid_moves_the_effective_id (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1000 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1000 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- ...and to the SAVED uid likewise — a disjunct dead in every state a
probe can produce, since a launch makes the two agree.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_the_saved_uid_moves_the_effective_id (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1002 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- The PRIVILEGED shape of that answer — all three uids become 1002 — is
refused for the unprivileged caller: only :680 runs for it, never :670.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_the_saved_uid_moves_only_the_effective_id (i : SyscallInput)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1002 i split_ids_model
        (Ok (mkEffect 0 [] [])
          (with_creds (Creds.mkCreds 1002 1002 1002 2000 2001 2002 demo_groups) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- An unprivileged caller naming an id it does not hold: `-EPERM` — or
`-ENOMEM`, because `__sys_setuid` (kernel/sys.c:663-665, Linux v6.18.46) allocates
its new credentials BEFORE its permission test (:676-677).  That ordering is observable and is the
opposite of `setresuid`'s.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_a_new_uid_is_eperm_or_enomem (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1003 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model []) := by
  sys_norm

/-- ...so it never succeeds (`reject --mutate setuid:ret=0 -- setuid-other`).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_a_new_uid_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1003 i split_ids_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The CURRENT EFFECTIVE uid is not a permitted target when it is neither
the real nor the saved id: the test is `!uid_eq(kuid, old->uid) &&
!uid_eq(kuid, new->suid)` (kernel/sys.c:676), and `new->suid` is the old
saved id.  So `setuid(1001)` on split ids is refused.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_to_the_effective_uid_is_refused (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1001 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model []) := by
  sys_norm

/-- An unprivileged `setuid` never answers `-EAGAIN`: `set_user` is on the
capable branch alone (kernel/sys.c:669-674).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i split_ids_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `setuid(uid)` from an ordinary launch, where real, effective and saved
agree: `-ENOMEM`, or a success that changes no id — the `setuid-self`
case of `testing/syscall-check/tests/creds_spec.c`.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_self_from_a_launch_state (i : SyscallInput) (o : outcome SyscallEffect) :
    setid_spec cred_uids set_cred_uids true 1000 i demo_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
       ∨ o = Ok (mkEffect 0 [] []) demo_model []) := by
  sys_norm

/-- The real uid is always a permitted target: `-EPERM` there is the lie
of `reject --mutate setuid:ret=-EPERM -- setuid-self`.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_self_eperm_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i demo_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- UNPRIVILEGED `setgid` to the SAVED gid moves the effective gid only
(kernel/sys.c:499-500), and leaves the uid triple alone.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem unprivileged_setgid_to_the_saved_gid_moves_the_effective_gid (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setid_spec cred_gids set_cred_gids false 2002 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1001 1002 2000 2002 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- No id setter writes user memory: each takes ids by value and touches
only `struct cred`.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_writes_no_user_memory (i : SyscallInput) (v a : word) (b : byte) (m' : Model)
    (evs : List event) :
    ¬ setid_spec cred_uids set_cred_uids true 1000 i root_model
        (Ok (mkEffect v [(a, [b])] []) m' evs) := by
  sys_refute

/-- `setuid` and `setgid` never decline, whatever the triple, the argument
or the state: every path of `__sys_setuid` and `__sys_setgid` returns.
kernel: kernel/sys.c:__sys_setuid,__sys_setgid@v6.18.46 -/
theorem setid_never_declines (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (i : SyscallInput) (m : Model) :
    ¬ setid_spec get put user v i m Unmodeled := by
  sys_simp_pass +decide
  repeat' split
  all_goals sys_refute

/-! ## `setresuid` (147) and `setresgid` (149)

`__sys_setresuid` (kernel/sys.c:708-781, Linux v6.18.46), in order: the
three `-EINVAL` tests (:721-728) that nothing reaches in the init
namespace; the no-op fast path (:732-737) returning 0 before any
allocation; the permission test (:739-747), `-EPERM` when an id is new and
the caller is not capable, BEFORE `prepare_creds` (:749-751) since commit
659c0ce1cb9e; then the installation of every named id (:753-765), with
`set_user` when the real uid moves (:755-758).  `__sys_setresgid`
(:810-870) is the same shape without `set_user`. -/

/-- `setresuid(-1, -1, -1)` is 0 for EVERY credential state: each `-1`
reads as "keep this id" (kernel/sys.c:732-736), the no-op test passes, and
the call returns before `prepare_creds`.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_all_minus_one_is_a_no_op (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 4294967295 4294967295 i m o ↔
      o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- ...and so is `setresgid(-1, -1, -1)` (kernel/sys.c:832-837).
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_all_minus_one_is_a_no_op (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    setresid_spec cred_gids set_cred_gids false 4294967295 4294967295 4294967295 i m o ↔
      o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- Spelling the current ids out is still the no-op path
(`setresuid-same` in `testing/syscall-check/tests/creds_spec.c`): the test
is on values, not on `-1`.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_naming_the_current_ids_is_a_no_op (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 1000 1001 1002 i split_ids_model o ↔
      o = Ok (mkEffect 0 [] []) split_ids_model [] := by
  sys_norm

/-- The no-op path never allocates, so `-ENOMEM` is a lie there
(`reject --mutate setresuid:ret=-ENOMEM -- setresuid-noop`)...
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_no_op_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 4294967295 4294967295 i m
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- ...and so is `-EAGAIN`, since `set_user` is past it.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_no_op_eagain_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 4294967295 4294967295 i m
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `-EINVAL` is unreachable: `(ruid != (uid_t) -1) && !uid_valid(kruid)`
(kernel/sys.c:721) is false for every argument in the init user
namespace, where `make_kuid` is the identity and `uid_valid` refuses only
`(uid_t) -1` (kernel/user_namespace.c:422-426; include/linux/uidgid.h:103-106).
kernel: kernel/sys.c:__sys_setresuid; kernel/user_namespace.c:make_kuid; include/linux/uidgid.h:uid_valid@v6.18.46 -/
theorem setresuid_einval_is_unreachable (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 1002 4294967295 i split_ids_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- An unprivileged caller naming ONE new id among three current ones is
`-EPERM`, and nothing else: the `*_new` tests (kernel/sys.c:739-744) fire
and `ns_capable_setid` (:746) is false.
kernel: kernel/sys.c:__sys_setresuid; kernel/capability.c:ns_capable_setid@v6.18.46 -/
theorem unprivileged_setresuid_to_a_new_euid_is_eperm (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 1003 4294967295 i split_ids_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model [] := by
  sys_norm

/-- `__sys_setresuid` (kernel/sys.c:745-751, Linux v6.18.46) refuses at :747 and
allocates only at :749,
so unlike `setuid` a refused call never answers `-ENOMEM`.  The probe's
`reject --mutate setresuid:ret=-ENOMEM -- seteuid-root` pins the same
refusal from a launch state (`unprivileged_seteuid_root_is_eperm` below);
this one states it on the split fixture, which no probe reaches.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_setresuid_refusal_admits_no_enomem (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 1003 4294967295 i split_ids_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- A new REAL uid is refused the same way (`ruid_new`, kernel/sys.c:739-740)...
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_setresuid_to_a_new_ruid_is_eperm (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 1003 4294967295 4294967295 i split_ids_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model [] := by
  sys_norm

/-- ...and a new SAVED uid too (`suid_new`, kernel/sys.c:743-744): each
position is tested against all three current ids.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_setresuid_to_a_new_suid_is_eperm (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 4294967295 1003 i split_ids_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model [] := by
  sys_norm

/-- An UNPRIVILEGED `setresuid` moving the REAL uid onto a held id — the
saved one — is permitted (`ruid_new` is false, kernel/sys.c:739-740) and
may fail `-EAGAIN`: `set_user` runs under `!uid_eq(kruid, old->uid)`
(:755-756) with no capability test in front of it, so the per-uid
allocation is the same for an ordinary user as for root.  The effective
and saved ids, passed as `-1`, stay.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem unprivileged_setresuid_moving_the_real_uid_admits_eagain (i : SyscallInput)
    (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 1002 4294967295 4294967295 i split_ids_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) split_ids_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1002 1001 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- musl's `seteuid(0)` is `setresuid(-1, 0, -1)`: from an ordinary launch
it is `-EPERM` and nothing else (`seteuid-root` in
`testing/syscall-check/tests/creds_spec.c`).
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_seteuid_root_is_eperm (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 0 4294967295 i demo_model o ↔
      o = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [] := by
  sys_norm

/-- UNPRIVILEGED `setresuid` REARRANGING ids the process already holds:
permitted (every `*_new` is false, kernel/sys.c:739-744), and only the
named id moves (:761-762) — here the saved uid becomes the effective one.
rocq-twin: unprivileged_setresuid_may_rearrange_held_ids
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_setresuid_may_rearrange_held_ids (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 1002 4294967295 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- The real uid did not move, so `-EAGAIN` is refused there while `-ENOMEM`
(past `prepare_creds`) is admitted.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem unprivileged_setresuid_rearranging_admits_no_eagain (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 1002 4294967295 i split_ids_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `setresuid(1000, 1000, 1000)` from root reaches the allocating branch:
`-ENOMEM`, `-EAGAIN` — the real uid moves, and `__sys_setresuid`
(kernel/sys.c:755-758) calls `set_user` there — or all three ids installed.
rocq-twin: setresuid_reaches_its_allocating_branch
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem setresuid_reaches_its_allocating_branch (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 1000 1000 1000 i root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- The group twin on the identical shape: `-ENOMEM` or the installation,
and no `-EAGAIN`: `__sys_setresgid` (kernel/sys.c:810-870) never calls
`set_user`.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_on_the_same_shape (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_gids set_cred_gids false 1000 1000 1000 i root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 1000 1000 1000 demo_groups) demo_model) []) := by
  sys_norm

/-- ...stated as the refusal.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ setresid_spec cred_gids set_cred_gids false 1000 1000 1000 i root_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The UNPRIVILEGED group side moving the REAL gid onto a held one — the
saved gid — is permitted (`rgid_new` is false, kernel/sys.c:839-840) and
installs it (:853-854) with the other two untouched; the environment's
only errno is `-ENOMEM`, since `__sys_setresgid` has no `set_user` to
call.  This is the group twin of
`unprivileged_setresuid_moving_the_real_uid_admits_eagain`, and the two
differ exactly in the `-EAGAIN` disjunct.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem unprivileged_setresgid_moving_the_real_gid (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_gids set_cred_gids false 2002 4294967295 4294967295 i split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1001 1002 2002 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- ...stated as the refusal: `-EAGAIN` on a group setter is a lie
whatever the caller's privilege and whichever gid moves.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem unprivileged_setresgid_moving_the_real_gid_admits_no_eagain (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ setresid_spec cred_gids set_cred_gids false 2002 4294967295 4294967295 i split_ids_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- Privileged, but keeping the real uid: `setresuid(-1, 1000, -1)` from
root moves the EFFECTIVE uid alone.  Each `-1` leaves its slot as it was
(kernel/sys.c:753 and :763 are the guards; :761-762 the one write), so
the saved uid stays 0 — the shape `setuid(1000)` from root would never
leave — and the only environment errno is `-ENOMEM`.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem privileged_setresuid_keeping_the_real_uid (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_uids set_cred_uids true 4294967295 1000 4294967295 i root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 1000 0 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- ...and `set_user` is skipped (kernel/sys.c:755) while `set_cred_ucounts`
takes its fast path (kernel/cred.c:541-542), so `-EAGAIN` is refused.
kernel: kernel/sys.c:__sys_setresuid; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem privileged_setresuid_keeping_the_real_uid_eagain_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 1000 4294967295 i root_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- A success whose SAVED uid followed the effective one is the `setuid`
answer wearing `setresuid`'s name: `new->suid` is written only under
`suid != (uid_t) -1` (kernel/sys.c:763-764).
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem privileged_setresuid_keeping_the_real_uid_leaves_the_saved_uid (i : SyscallInput)
    (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 4294967295 1000 4294967295 i root_model
        (Ok (mkEffect 0 [] [])
          (with_creds (Creds.mkCreds 0 1000 1000 0 0 0 demo_groups) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- `setresgid(-1, -1, g)` parks a group in the SAVED gid and touches
nothing else — dropbear's way of keeping the utmp group in reach.  Unlike
`setuid`, these calls never move an id the caller did not name
(kernel/sys.c:853-858).
rocq-twin: setresgid_parks_a_group_in_the_saved_id
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_parks_a_group_in_the_saved_id (i : SyscallInput) (o : outcome SyscallEffect) :
    setresid_spec cred_gids set_cred_gids false 4294967295 4294967295 22 i root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 0 0 22 demo_groups) demo_model) []) := by
  sys_norm

/-- A success that also moved the effective gid is a lie: `new->egid` is
written only under `egid != (gid_t) -1` (kernel/sys.c:855-856).
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_parking_moves_nothing_else (i : SyscallInput) (evs : List event) :
    ¬ setresid_spec cred_gids set_cred_gids false 4294967295 4294967295 22 i root_model
        (Ok (mkEffect 0 [] [])
          (with_creds (Creds.mkCreds 0 0 0 0 22 22 demo_groups) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- No `setres*id` writes user memory.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_writes_no_user_memory (i : SyscallInput) (v a : word) (b : byte) (m' : Model)
    (evs : List event) :
    ¬ setresid_spec cred_uids set_cred_uids true 1000 1000 1000 i root_model
        (Ok (mkEffect v [(a, [b])] []) m' evs) := by
  sys_refute

/-- `setresuid` and `setresgid` never decline: every path returns.
kernel: kernel/sys.c:__sys_setresuid,__sys_setresgid@v6.18.46 -/
theorem setresid_never_declines (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (i : SyscallInput) (m : Model) :
    ¬ setresid_spec get put user r e s i m Unmodeled := by
  sys_simp_pass +decide
  repeat' split
  all_goals sys_refute

/-! ## Through the dispatcher

The table applies the setters to `uid32` of each argument register:
`uid_t` is 32 bits, and `SYSCALL_DEFINEx`'s `__SC_CAST` narrows the
register to it before the body runs (include/linux/syscalls.h:132,
Linux v6.18.46).  So a0 with junk in its high half is the id in its low
half, and the sign-extended `-1` musl passes for `(uid_t)-1` is
`0xffffffff` to the kernel. -/

/-- Syscall 146 with a0 = 1000 from root is the privileged `setuid(1000)`.
kernel: kernel/sys.c:setuid,__sys_setuid,set_user@v6.18.46 -/
theorem sysno_146_is_setuid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 146 [1000, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- ...and a0 = `2^32 + 1000` is the SAME call: the high half is discarded
by the `uid_t` parameter.
kernel: kernel/sys.c:setuid,__sys_setuid,set_user; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_146_narrows_the_uid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 146 [4294968296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) root_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []) := by
  sys_norm

/-- a0 = `2^33 - 1`: a low half of all ones under a high half that is
neither zero nor its sign extension.  The narrowing alone explains the
answer, `-EINVAL` for every state — the one invalid `uid_t` — where a
comparison of the whole register against either spelling of `-1` would
have let the call through to the setter.
kernel: kernel/sys.c:setuid,__sys_setuid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_146_high_half_over_all_ones_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 146 [8589934591, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The sign-extended `-1` in a0 is `(uid_t)-1`: `-EINVAL` for every state.
kernel: kernel/sys.c:setuid,__sys_setuid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_146_minus_one_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 146 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Syscall 146 with a0 = 1000 from the LAUNCH state is the unprivileged
`setuid` to the caller's own real uid: `-ENOMEM`, or a success that moves
nothing (`setuid-self` in `testing/syscall-check/tests/creds_spec.c`).
On this state the uid triple and the gid triple DIFFER — 1000 against
1002 — so an arm that handed `setid_spec` the gid triple would refuse the
call `-EPERM` here, which `sysno_146_is_setuid`, from root, cannot see.
kernel: kernel/sys.c:setuid,__sys_setuid@v6.18.46 -/
theorem sysno_146_from_a_launch_state_is_setuid_self (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 146 [1000, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
       ∨ o = Ok (mkEffect 0 [] []) demo_model []) := by
  sys_norm

/-- Syscall 144 with a0 = 1000 from root is the privileged `setgid(1000)`.
kernel: kernel/sys.c:setgid,__sys_setgid@v6.18.46 -/
theorem sysno_144_is_setgid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 144 [1000, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 1000 1000 1000 demo_groups) demo_model) []) := by
  sys_norm

/-- Syscall 144 with a0 = 1002 from the LAUNCH state is the unprivileged
`setgid` to the caller's own real gid (`setgid-self` in
`testing/syscall-check/tests/creds_spec.c`): the group-side reading of
`sysno_146_from_a_launch_state_is_setuid_self`, and the pin that tells
arm 144's triple from arm 146's — 1002 is held as a gid and by no uid.
kernel: kernel/sys.c:setgid,__sys_setgid@v6.18.46 -/
theorem sysno_144_from_a_launch_state_is_setgid_self (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 144 [1002, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model []
       ∨ o = Ok (mkEffect 0 [] []) demo_model []) := by
  sys_norm

/-- `gid_t` is narrowed by `__SC_CAST` exactly as `uid_t` is: a0 =
`2^32 + 1000` on arm 144 is `setgid(1000)`.
kernel: kernel/sys.c:setgid,__sys_setgid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_144_narrows_the_gid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 144 [4294968296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 1000 1000 1000 demo_groups) demo_model) []) := by
  sys_norm

/-- ...and the sign-extended `-1` in a0 is `(gid_t)-1`: `-EINVAL` for every
state, before the caller's privilege is looked at (kernel/sys.c:487-489).
kernel: kernel/sys.c:setgid,__sys_setgid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_144_minus_one_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 144 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- THE ID SETTERS DO NOT DROP THE SUPPLEMENTARY LIST.  `setgid(4242)` from
root through the table leaves a state whose group list is still
`demo_groups`, and `getgroups(0, NULL)` through the table on that state
counts it — 3.  `prepare_creds` copies the whole `struct cred` and takes a
reference on the same `group_info` (kernel/cred.c:219-223), and
`__sys_setgid` writes the three gids and nothing else (kernel/sys.c:498);
a `set_cred_gids` that forgot `cr_groups` would make the second call
answer 0.  Rocq's example of the same name, in
`theories/LinuxProcessSem/Checks/Cases/Kernel/Groups.v`, runs the same two
calls through the executable checker; `Checks/Cases/Kernel/Groups.lean`'s
header says why the twin is here and not there.
kernel: kernel/sys.c:__sys_setgid; kernel/groups.c:getgroups; kernel/cred.c:prepare_creds@v6.18.46 -/
theorem setgid_keeps_the_supplementary_group_list (o₁ o₂ : outcome SyscallEffect) :
    (syscall_spec (SyscallInput.mkInput 144 [4242, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model o₁ ↔
      (o₁ = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o₁ = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 4242 4242 4242 demo_groups) demo_model) []))
    ∧ (syscall_spec (SyscallInput.mkInput 158 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (with_creds (Creds.mkCreds 0 0 0 4242 4242 4242 demo_groups) demo_model) o₂ ↔
      o₂ = Ok (mkEffect 3 [] [])
             (with_creds (Creds.mkCreds 0 0 0 4242 4242 4242 demo_groups) demo_model) []) := by
  constructor <;> sys_norm

/-- ...stated as the refusal: a `setgid` success whose state LOST the list
is not one the table admits.
kernel: kernel/sys.c:__sys_setgid; kernel/cred.c:prepare_creds@v6.18.46 -/
theorem setgid_dropping_the_supplementary_list_rejected (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 144 [4242, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        root_model
        (Ok (mkEffect 0 [] []) (with_creds (Creds.mkCreds 0 0 0 4242 4242 4242 []) demo_model) evs) := by
  intro hspec
  sys_refute at hspec

/-- Syscall 147 with `(-1, 1002, -1)` on split ids is the rearrangement.
kernel: kernel/sys.c:setresuid,__sys_setresuid@v6.18.46 -/
theorem sysno_147_is_setresuid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 147 [4294967295, 1002, 4294967295, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- Three sign-extended `-1`s in a0..a2 are the no-op, for every state:
each register narrows to `(uid_t)-1`.  The probe's `setresuid-noop`
(`testing/syscall-check/tests/creds_spec.c`) passes the ZERO-extended
`0xffffffff` instead — the shape `sysno_147_is_setresuid` reads — so this
is the half no probe passes; to the kernel the two are one argument.
kernel: kernel/sys.c:setresuid,__sys_setresuid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_147_sign_extended_minus_ones_are_the_no_op (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 147 [Z_to_bv 64 (-1), Z_to_bv 64 (-1), Z_to_bv 64 (-1), 0, 0, 0]
                   (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- Syscall 147 with `(1002, -1, -1)` on split ids MOVES THE REAL UID onto
the saved one, and through the table that is where `-EAGAIN` enters: the
arm's `user` flag is what admits it, and `sysno_147_is_setresuid` keeps
the real uid so it cannot see the flag.  Spec-level twin:
`unprivileged_setresuid_moving_the_real_uid_admits_eagain`.
kernel: kernel/sys.c:setresuid,__sys_setresuid,set_user@v6.18.46 -/
theorem sysno_147_moving_the_real_uid_admits_eagain (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 147 [1002, 4294967295, 4294967295, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) split_ids_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
        ∨ o = Ok (mkEffect (errno_ret EAGAIN) [] []) split_ids_model [])
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1002 1001 1002 2000 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- Syscall 149 with `(-1, -1, 22)` from root parks the group.
kernel: kernel/sys.c:setresgid,__sys_setresgid@v6.18.46 -/
theorem sysno_149_is_setresgid (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 149 [4294967295, 4294967295, 22, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) root_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) root_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 0 0 0 0 0 22 demo_groups) demo_model) []) := by
  sys_norm

/-- Syscall 149 with `(2002, -1, -1)` on split ids: the group arm moving
the REAL gid onto the saved one, unprivileged.  No `-EAGAIN` — the group
side has no `set_user` — so this is the one shape that tells arm 149's
`user := false` from arm 147's, and it reads a0 against the GID triple:
2002 is held as a gid and by no uid, so an arm handed the uid triple
would refuse it `-EPERM`.  Spec-level twin:
`unprivileged_setresgid_moving_the_real_gid`.
kernel: kernel/sys.c:setresgid,__sys_setresgid@v6.18.46 -/
theorem sysno_149_moving_the_real_gid_admits_no_eagain (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 149 [2002, 4294967295, 4294967295, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) split_ids_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model []
       ∨ o = Ok (mkEffect 0 [] [])
              (with_creds (Creds.mkCreds 1000 1001 1002 2002 2001 2002 demo_groups) demo_model) []) := by
  sys_norm

/-- Three sign-extended `-1`s on arm 149 are the group no-op for every
state: each register narrows to `(gid_t)-1`, as on arm 147.
kernel: kernel/sys.c:setresgid,__sys_setresgid; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_149_sign_extended_minus_ones_are_the_no_op (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 149 [Z_to_bv 64 (-1), Z_to_bv 64 (-1), Z_to_bv 64 (-1), 0, 0, 0]
                   (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm


/-! ## prlimit64 (261): the RLIMIT_CORE record, read and written

The fixtures are the Prelude's — `rlim_bytes`, `rlim_out` (sixteen
writable bytes at 4096), `rlim_src_at` (a readable source at 8192) and
`rlim_pinned` (the record `{3, 7}`) — and Rocq's `rlim_model` is
`demo_model`; the inputs and the short and page-zero views the pins
build on them are defined in place below.  Every kernel line was read at Linux v6.18.46 (commit
1f99e9ab748f); `SYSCALL_DEFINE4(prlimit64)` is kernel/sys.c:1729-1792 and
`do_prlimit` kernel/sys.c:1500-1561 there. -/

/-- The read call: `prlimit64(0, RLIMIT_CORE, NULL, 4096)` with the
landing zone writable. -/
def rlim_read_in : SyscallInput :=
  SyscallInput.mkInput 261 [0, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out

/-- The set call: `prlimit64(0, RLIMIT_CORE, 8192, NULL)` over a readable
view `mem` of the source struct. -/
def rlim_set_in (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 261 [0, 4, 8192, 0, 0, 0] mem (fun _ => none)

/-- The read's landing zone one byte shy of sixteen: `access_ok` admits
it, the walk does not. -/
def rlim_out_short : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4111 then some 0 else none

/-- The set's source one byte shy of sixteen. -/
def rlim_src_short : word → Option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a 8207 then some 0 else none

attribute [local sys_simp low] rlim_read_in.eq_1 rlim_set_in.eq_1

/-- The projections read the two `__u64`s little-endian, in declaration
order and EIGHT BYTES WIDE each: `struct rlimit64` is `rlim_cur` then
`rlim_max` (include/uapi/linux/resource.h:50-53, Linux v6.18.46), moved
as laid out by the `copy_to_user` in `SYSCALL_DEFINE4(prlimit64)`
(kernel/sys.c:1786, Linux v6.18.46), and riscv64 is little-endian — so a
byte in position 1 is worth 256 and one in position 7, or 15, is worth
2^56.  The last two conjuncts are what separate an eight-byte projection
from a narrower one; every other fixture in this file is nonzero only in
positions 0, 1, 8 and 9 and would let a narrower one pass.
kernel: kernel/sys.c:prlimit64,rlim_to_rlim64@v6.18.46 -/
theorem rlim64_projections_are_little_endian :
    rlim64_soft (rlim_bytes 3 7) = 3 ∧ rlim64_hard (rlim_bytes 3 7) = 7
      ∧ rlim64_soft [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 256
      ∧ rlim64_hard [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] = 256
      ∧ rlim64_soft [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] = 72057594037927936
      ∧ rlim64_hard [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = 72057594037927936 := by
  decide

/-- `rlim64_wf` is exactly `do_prlimit`'s `rlim_cur > rlim_max` refusal
(kernel/sys.c:1511-1512) on a sixteen-byte pair: equal limits pass, an
inverted pair fails — one inverted only in its high bytes too, soft 2^56
over hard 1 — and fifteen or seventeen bytes are no pair at all.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem rlim64_wf_reads_the_kernel_invariant :
    rlim64_wf (rlim_bytes 3 7) = true ∧ rlim64_wf (rlim_bytes 7 7) = true
      ∧ rlim64_wf (rlim_bytes 0 0) = true
      ∧ rlim64_wf (List.replicate 16 255) = true
      ∧ rlim64_wf (rlim_bytes 1 0) = false
      ∧ rlim64_wf [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0] = false
      ∧ rlim64_wf ((rlim_bytes 3 7).take 15) = false
      ∧ rlim64_wf (rlim_bytes 3 7 ++ [0]) = false := by
  decide

/-- THE FIRST READ, in full: 0 returned, some sixteen bytes satisfying
`rlim64_wf` landing at `old_rlim`, the pair recorded, no event — and
nothing else.  `do_prlimit` copies the task's pair out (kernel/sys.c:1533-1534, Linux v6.18.46)
and `SYSCALL_DEFINE4(prlimit64)` delivers it (:1784-1787); which pair the
task holds is inherited and not the kernel source's to say, so the
environment chooses it here.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-one -/
theorem prlimit64_first_read_iff (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 0 4096 rlim_read_in demo_model o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) (with_rlimit_core bs demo_model) []
        ∧ rlim64_wf bs = true := by
  sys_norm

/-- The first read pins whatever well-formed pair the environment reports.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-one
rocq-twin: prlimit64_first_read_pins -/
theorem prlimit64_first_read_pins :
    prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
      (Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) (with_rlimit_core (rlim_bytes 3 7) demo_model) []) := by
  sys_norm

/-- …but not an inverted pair: no Linux reports soft > hard, because
`do_prlimit` refuses to store one (kernel/sys.c:1511-1512).
kernel: kernel/sys.c:do_prlimit@v6.18.46
rocq-twin: prlimit64_read_soft_over_hard_rejected -/
theorem prlimit64_read_soft_over_hard_rejected (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect 0 [(4096, rlim_bytes 1 0)] []) m' evs) := by
  sys_refute

/-- …nor half a struct, nor a struct and a byte: the copy-out is
`sizeof(old64)` (kernel/sys.c:1786, Linux v6.18.46).
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64:trunc-writes:8 -- read-one -/
theorem prlimit64_read_wrong_width_rejected (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect 0 [(4096, (rlim_bytes 3 7).take 8)] []) m' evs)
    ∧ ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect 0 [(4096, rlim_bytes 3 7 ++ [0])] []) m' evs) := by
  constructor <;> sys_refute

/-- …nor a read that returns 1, nor one that returns -EFAULT and delivers
the pair anyway: `do_prlimit` answers 0 (:1504, :1532-1537) and a fault
delivers nothing (:1786-1787).
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64:ret=1 -- read-one -/
theorem prlimit64_read_wrong_return_rejected (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect 1 [(4096, rlim_bytes 3 7)] []) m' evs)
    ∧ ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect (errno_ret EFAULT) [(4096, rlim_bytes 3 7)] []) m' evs) := by
  constructor <;> sys_refute

/-- …and a read that recorded a pair other than the one it delivered is
refused: the record IS the delivery.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_read_records_what_it_delivers (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
        (Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) (with_rlimit_core (rlim_bytes 2 7) demo_model) evs) := by
  sys_refute

/-- ONCE PINNED, a read repeats the record exactly, and nothing else is
admitted.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-two -/
theorem prlimit64_pinned_read_iff (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 0 4096 rlim_read_in rlim_pinned o ↔
      o = Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned [] := by
  sys_norm

/-- The pinned pair, repeated.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-two
rocq-twin: prlimit64_pinned_read_repeats -/
theorem prlimit64_pinned_read_repeats :
    prlimit64_spec 0 4 0 4096 rlim_read_in rlim_pinned
      (Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned []) := by
  sys_norm

/-- The defector is WELL-FORMED — `{2, 7}` would have pinned as a first
answer — so it is refused for disagreeing with the record, not for being
a bad pair.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46
rocq-twin: prlimit64_pinned_read_defector_rejected -/
theorem prlimit64_pinned_read_defector_rejected (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in rlim_pinned
        (Ok (mkEffect 0 [(4096, rlim_bytes 2 7)] []) m' evs) := by
  sys_refute

/-- …and that same defector is admissible as a FIRST answer, which is
what attributes the refusal above to the record alone.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-one -/
theorem prlimit64_defector_is_itself_admissible_first :
    prlimit64_spec 0 4 0 4096 rlim_read_in demo_model
      (Ok (mkEffect 0 [(4096, rlim_bytes 2 7)] []) (with_rlimit_core (rlim_bytes 2 7) demo_model) []) := by
  sys_norm

/-- A landing zone past `TASK_SIZE` fails `access_ok` — `__access_ok`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46), the gate `_inline_copy_to_user`
asks (include/linux/uaccess.h:195, Linux v6.18.46) — so -EFAULT is exact and no byte
moves, for every starting model.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-fault -/
theorem prlimit64_read_access_ok_fault (m : Model) (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 0 9223372036854775808
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- …and a fault that delivered the pair anyway is refused.
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64:smuggle-write:a3:16 -- read-fault -/
theorem prlimit64_read_access_ok_fault_delivers_nothing (m m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 9223372036854775808
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        m (Ok (mkEffect (errno_ret EFAULT) [(9223372036854775808, rlim_bytes 3 7)] []) m' evs) := by
  sys_refute

/-- A landing zone `access_ok` ADMITS but memory does not wholly back is
declined, not faulted: the copy-out may be partial, and the model cannot
say how much landed.  One byte short of sixteen is the whole difference.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed --mutate prlimit64:wmem-hide:a3+15:1 -- read-one -/
theorem prlimit64_read_one_byte_short_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 0 4096
        (SyscallInput.mkInput 261 [0, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out_short) m o ↔
      o = Unmodeled := by
  sys_norm

/-- The landing zone fixtures are what the two pins above say they are:
sixteen bytes, and fifteen.
model: `rlim_out_short` at its boundary against `rlim_out`. -/
theorem rlim_out_short_is_one_byte_shy :
    rlim_out 4111 = some 0 ∧ rlim_out_short 4111 = none ∧ rlim_out_short 4110 = some 0
      ∧ rlim_src_short 8206 = some 0 ∧ rlim_src_short 8207 = none := by
  decide

/-- THE SET, in full: dropbear's own call.  Zero the soft limit and write
the hard limit back unchanged; the sixteen bytes are recorded as a copy-in
(`_inline_copy_from_user`, include/linux/uaccess.h:159-185, Linux v6.18.46, has loaded
them), the record MOVES to what was set, 0 is returned — and nothing else
is admitted.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set -/
theorem prlimit64_set_iff (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] []))
             (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [] := by
  sys_norm

/-- The recorded pair moves: 3 becomes 0.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set
rocq-twin: prlimit64_set_new_soft_replaces_the_record -/
theorem prlimit64_set_new_soft_replaces_the_record :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned
      (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) []) := by
  sys_norm

/-- A set that kept the OLD record, or dropped its copy-in, is refused.
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64#2:drop-copyins -- set -/
theorem prlimit64_set_must_record_and_must_copy_in (evs : List event) :
    ¬ prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) rlim_pinned evs)
    ∧ ¬ prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned
        (Ok (mkEffect 0 [] []) (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) evs) := by
  constructor <;> sys_refute

/-- A set that returned -EPERM is refused: `do_prlimit` consults
`capable(CAP_SYS_RESOURCE)` only when the hard limit RISES
(kernel/sys.c:1526-1528, Linux v6.18.46), and this one leaves it at 7.
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64#2:ret=-EPERM -- set -/
theorem prlimit64_set_unchanged_hard_needs_no_capability (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EPERM) [] [])) m' evs) := by
  sys_refute

/-- A pointer past `TASK_SIZE` fails `access_ok` before `copy_from_user`
issues a load (`_inline_copy_from_user`, include/linux/uaccess.h:168, Linux v6.18.46), so
the -EFAULT carries no copy-in provenance and the record is untouched.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set-fault -/
theorem prlimit64_set_access_ok_fault_iff (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 9223372036854775808 0
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        rlim_pinned o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) rlim_pinned [] := by
  sys_norm

/-- The fault, with no copy-in.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set-fault
rocq-twin: prlimit64_set_access_ok_fault_has_no_copyins -/
theorem prlimit64_set_access_ok_fault_has_no_copyins :
    prlimit64_spec 0 4 9223372036854775808 0
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        rlim_pinned (Ok (mkEffect (errno_ret EFAULT) [] []) rlim_pinned []) := by
  sys_norm

/-- Claiming the unreachable struct as read is refused.
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64#2:smuggle-copyin:a2:16 -- set-fault
rocq-twin: prlimit64_set_access_ok_fault_rejects_copyins -/
theorem prlimit64_set_access_ok_fault_rejects_copyins (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 9223372036854775808 0
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        rlim_pinned
        (Ok (with_copyins [(9223372036854775808, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-- A source `access_ok` admits but memory does not wholly back is
declined: which bytes the kernel read is not something the ledger can
state.  One byte short of sixteen.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed --mutate prlimit64#2:mem-hide:a2+15:1 -- set -/
theorem prlimit64_set_one_byte_short_is_unmodeled (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in rlim_src_short) rlim_pinned o ↔ o = Unmodeled := by
  sys_norm

/-- `{soft = 9, hard = 7}` is -EINVAL — `do_prlimit`'s first test on the
new pair (kernel/sys.c:1511-1512, Linux v6.18.46), before any capability or LSM question —
AND the sixteen bytes are still recorded as read, because
`SYSCALL_DEFINE4(prlimit64)` copied them in before anything else
(:1744-1745).  The record does not move.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set-einval -/
theorem prlimit64_set_soft_over_hard_is_einval (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 9 7)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned [] := by
  sys_norm

/-- The test is strict and the boundary is one: `{soft = 8, hard = 7}` —
one over the hard limit — is already -EINVAL, `rlim_cur > rlim_max`
(kernel/sys.c:1511-1512, Linux v6.18.46) being `>` and not `>=` or `> max + 1`;
the probe's own pair is `{1, 0}`.  The copy-in stays, the record does not
move.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set-einval -/
theorem prlimit64_set_soft_one_over_hard_is_einval (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 8 7)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned [] := by
  sys_norm

/-- -EINVAL is decided BEFORE the hard limit is compared: `{soft = 9,
hard = 5}` against the recorded hard 7 is `do_prlimit`'s first test
failing (kernel/sys.c:1511-1512, Linux v6.18.46), fifteen lines before
the `capable(CAP_SYS_RESOURCE)` question a changed hard limit raises
(:1526-1528) — so the answer is -EINVAL with the copy-in, not the decline
this spec makes of a changed hard limit.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem prlimit64_set_soft_over_hard_precedes_the_hard_change (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 9 5)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned [] := by
  sys_norm

/-- …so the -EINVAL WITHOUT the copy-in is refused, and so is a kernel
that accepted the inverted pair.
probe: testing/syscall-check/tests/prlimit64_spec.c#reject --mutate prlimit64#2:drop-copyins -- set-einval -/
theorem prlimit64_set_soft_over_hard_rejections (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 9 7)) rlim_pinned
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs)
    ∧ ¬ prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 9 7)) rlim_pinned
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  constructor <;> sys_refute

/-- Equal limits are NOT inverted: `{7, 7}` is a legal set, `rlim_cur >
rlim_max` being strict (kernel/sys.c:1511).
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem prlimit64_set_equal_limits_is_legal (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 7 7)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] []))
             (with_rlimit_core (rlim_bytes 7 7) rlim_pinned) [] := by
  sys_norm

/-- LOWERING the hard limit is declined — a deliberate bound, argued on
`Kernel.Sys.prlimit64_spec` — and so is RAISING it, which `do_prlimit`
decides by `capable(CAP_SYS_RESOURCE)` (kernel/sys.c:1526-1528, Linux v6.18.46), a
credential this model does not carry.  The copy-in is not recorded on a
decline: an `Unmodeled` outcome carries no ledger.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- set-lower -/
theorem prlimit64_set_changing_hard_is_unmodeled (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 6)) rlim_pinned o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 8)) rlim_pinned o ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- A set BEFORE any read is declined: with no record there is no hard
limit to compare against, even though the kernel performs the set.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- set-first -/
theorem prlimit64_set_before_read_is_unmodeled (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) demo_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the decline precedes the pointer: a set before any read is
declined even from a pointer the kernel would fault on, and even for a
pair the kernel would refuse -EINVAL.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- fault-first -/
theorem prlimit64_set_before_read_precedes_the_pointer (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4 9223372036854775808 0
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 4 8192 0 (rlim_set_in (rlim_src_at 9 7)) demo_model o ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- A read AFTER a set reports the pair the set installed.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set-again
rocq-twin: prlimit64_read_after_set_reports_the_set_pair -/
theorem prlimit64_read_after_set_reports_the_set_pair :
    prlimit64_spec 0 4 0 4096 rlim_read_in (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
      (Ok (mkEffect 0 [(4096, rlim_bytes 0 7)] []) (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) []) := by
  sys_norm

/-- …and the pair that was there before it is now refused.
kernel: kernel/sys.c:do_prlimit@v6.18.46
rocq-twin: prlimit64_read_after_set_rejects_the_old_pair -/
theorem prlimit64_read_after_set_rejects_the_old_pair (m' : Model) (evs : List event) :
    ¬ prlimit64_spec 0 4 0 4096 rlim_read_in (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
        (Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) m' evs) := by
  sys_refute

/-- THE DECLINES, each for every starting model and every outcome.  A
nonzero `pid` — the model has no other task to name, so it can decide
neither `find_task_by_vpid`'s -ESRCH (kernel/sys.c:1751-1755, Linux v6.18.46) nor
`check_prlimit_permission` (kernel/sys.c:1707-1727, Linux v6.18.46); the kernel's own
`current == task` fast path (:1713-1714) makes a pid naming THIS process
behave like 0, but the model cannot tell which pid that is.  The second
conjunct's 2^32 is no pid at all to the kernel: `pid_t` is `int`
(include/uapi/asm-generic/posix_types.h:28, Linux v6.18.46), so the
`__SC_CAST` narrowing makes it 0 and Linux takes the `current` path with
no lookup — the `pid-high` probe records that — while this spec reads the
full register, as Rocq's does, and declines it.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- pid-self -/
theorem prlimit64_nonzero_pid_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    (prlimit64_spec 1 4 0 4096
        (SyscallInput.mkInput 261 [1, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 4294967296 4 0 4096
        (SyscallInput.mkInput 261 [4294967296, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o
          ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- Every resource but `RLIMIT_CORE` (4) is declined: `RLIMIT_STACK` (3),
which the model fixes elsewhere; `RLIMIT_NOFILE` (7), whose soft limit
the model HOLDS and whose pair it does not — this is the fact that closes
the window `Checks/Cases/Fs/File.lean`'s `sysno_261_nofile_declines`
holds open, that no arm writes `m_nofile`; `RLIM_NLIMITS` (16) and far
past it, which `do_prlimit` refuses -EINVAL (kernel/sys.c:1506-1507, Linux v6.18.46); and
`(1 << 32) | RLIMIT_CORE`, which the kernel's `unsigned int` cast makes
`RLIMIT_CORE` and this spec, reading the full register, does not.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- res-nofile -/
theorem prlimit64_other_resources_are_unmodeled (m : Model) (o : outcome SyscallEffect) :
    (prlimit64_spec 0 3 0 4096
        (SyscallInput.mkInput 261 [0, 3, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 7 0 4096
        (SyscallInput.mkInput 261 [0, 7, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 7 8192 0 (rlim_set_in (rlim_src_at 0 7)) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 16 0 4096
        (SyscallInput.mkInput 261 [0, 16, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 4294967300 0 4096
        (SyscallInput.mkInput 261 [0, 4294967300, 0, 4096, 0, 0] (fun _ => none) rlim_out) m o
          ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- Both pointers NULL is declined, and so is both non-NULL.  The first
is a decline of SCOPE, not of emptiness: Linux and qemu-user both answer
the no-op 0 and nothing is observable, and the arm is kept closed (Rocq
`prlimit64_spec`, item (4)) so that the two-pointer shape beside it stays
declined for its own reason — the read-modify-write whose failing
copy-out leaves the new limit committed (kernel/sys.c:1784-1787 after
:1535-1536, Linux v6.18.46).  The `both-null` probe case records the
first conjunct and the `rmw` case, fail-closed too, the second.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- both-null -/
theorem prlimit64_pointer_pairing_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4 0 0
        (SyscallInput.mkInput 261 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 0 4 8192 4096
        (SyscallInput.mkInput 261 [0, 4, 8192, 4096, 0, 0] (rlim_src_at 3 7) rlim_out) m o
          ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- Sixteen bytes readable and writable at address 0: the view a mapped
page zero would give. -/
def rlim_page_zero : word → Option byte :=
  fun a => if bv_ltu a 16 then some 0 else none

/-- The both-NULL decline is on the pointer VALUES, not on what backs them:
with `rlim_page_zero` on both views the call is still declined, for every
model.  Otherwise a NULL `old_rlim` would be read as a landing zone at 0,
which no kernel does: `SYSCALL_DEFINE4(prlimit64)` copies in only under
`if (new_rlim)` and out only under `if (!ret && old_rlim)`
(kernel/sys.c:1743-1748 and :1784-1787, Linux v6.18.46), and NULL fails
both tests.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- both-null -/
theorem prlimit64_both_null_declines_whatever_backs_page_zero (m : Model) (o : outcome SyscallEffect) :
    prlimit64_spec 0 4 0 0
        (SyscallInput.mkInput 261 [0, 4, 0, 0, 0, 0] rlim_page_zero rlim_page_zero) m o ↔ o = Unmodeled := by
  sys_norm

/-- The width `access_ok` is handed is sixteen, the walk's the same
sixteen, and the top of the address space tells them apart.  A landing
zone at `TASK_SIZE - 15` fails `__access_ok`'s `addr <= limit - size`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46): -EFAULT before
any copy, for every model.  One byte lower, `TASK_SIZE - 16`, passes it,
and with nothing writable there the walk declines (the `read-past` and
`read-top` probe cases, one per conjunct).
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- read-top -/
theorem prlimit64_read_at_the_top_of_the_address_space (m : Model) (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4 0 140737488355313
        (SyscallInput.mkInput 261 [0, 4, 0, 140737488355313, 0, 0] (fun _ => none) (fun _ => none)) m o
          ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [])
    ∧ (prlimit64_spec 0 4 0 140737488355312
        (SyscallInput.mkInput 261 [0, 4, 0, 140737488355312, 0, 0] (fun _ => none) (fun _ => none)) m o
          ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- …and the SET arm hands `access_ok` the same sixteen: a source at
`TASK_SIZE - 15` is -EFAULT with no copy-in, on the pinned model, and
`TASK_SIZE - 16` with nothing readable there is the walk's decline.
Without this the set arm's range test had no width pin: at 2^63
(`prlimit64_set_access_ok_fault_iff`) every width fails, and
`rlim_src_short` pins the walk's sixteen, not the range test's.  No probe
reaches either address (`set-fault` uses 2^63); the kernel line is the
access_ok test that `_inline_copy_from_user` (include/linux/uaccess.h:159-185,
Linux v6.18.46) asks at :168, on the copy-in `SYSCALL_DEFINE4(prlimit64)`
makes first (kernel/sys.c:1744-1745, Linux v6.18.46).
kernel: kernel/sys.c:prlimit64; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem prlimit64_set_at_the_top_of_the_address_space (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4 140737488355313 0
        (SyscallInput.mkInput 261 [0, 4, 140737488355313, 0, 0, 0] (fun _ => none) (fun _ => none)) rlim_pinned o
          ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) rlim_pinned [])
    ∧ (prlimit64_spec 0 4 140737488355312 0
        (SyscallInput.mkInput 261 [0, 4, 140737488355312, 0, 0, 0] (fun _ => none) (fun _ => none)) rlim_pinned o
          ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- The declines precede the pointer, in this spec's own order: a nonzero
pid or a foreign resource is declined even from a pointer the kernel would
fault on.  Linux answers -EFAULT to both (`SYSCALL_DEFINE4(prlimit64)`'s
copy-in at kernel/sys.c:1744-1745, Linux v6.18.46, runs first); item (3) of the Rocq argument names
and costs the gap, and this pin is what keeps it a DECLINE rather than a
wrong answer.
probe: testing/syscall-check/tests/prlimit64_spec.c#fail-closed -- res-huge-fault -/
theorem prlimit64_declines_precede_the_fault (m : Model) (o : outcome SyscallEffect) :
    (prlimit64_spec 0 4095 9223372036854775808 0
        (SyscallInput.mkInput 261 [0, 4095, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔ o = Unmodeled)
    ∧ (prlimit64_spec 999 4 9223372036854775808 0
        (SyscallInput.mkInput 261 [999, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- Through the table: 261 is `prlimit64`, `a0..a3` its four arguments.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- read-two -/
theorem sysno_261_is_prlimit64 (o : outcome SyscallEffect) :
    syscall_spec rlim_read_in rlim_pinned o ↔
      o = Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned [] := by
  sys_norm

/-- …and the set through the table, `a2` the source.
probe: testing/syscall-check/tests/prlimit64_spec.c#conform -- set -/
theorem sysno_261_set_through_the_table (o : outcome SyscallEffect) :
    syscall_spec (rlim_set_in (rlim_src_at 0 7)) rlim_pinned o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] []))
             (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [] := by
  sys_norm

/-! ## uname (160): the name envelope, the record, and the wrapped destination

`uts_out` and `uts_out_short` (the Prelude's) are the 390-byte landing
zone at 4096 and the same zone one byte shy; Rocq's `uts_model` is
`demo_model`.  The name fixtures below are the ones Rocq's Prelude
defines over the Sys file, name for name, plus the ones the mutation
gate asked for.  Every kernel line was read at Linux v6.18.46 (commit
1f99e9ab748f); `SYSCALL_DEFINE1(newuname)` is kernel/sys.c:1351-1366
there.

Two things about the proofs, recorded so the next file does not
rediscover them.  A 390-byte literal is past `decide`'s default
recursion depth, so every pin that evaluates one carries
`maxRecDepth 8192`.  And `sys_norm`'s ground pass cannot afford one at
all — evaluating `utsname_wf` on a 390-byte list inside `simp` exceeds
its step budget — so the two `iff` pins are proved with the name
SYMBOLIC (`uname_first_copy_iff` over the environment's choice,
`uname_recorded_name_is_repeated` over any recorded `bs`) and every
concrete answer and refutation is DERIVED from them, the fixture's
well-formedness decided by the kernel rather than rewritten by `simp`.
The kernel claim each pin makes is unchanged by that route. -/

/-- A `struct new_utsname` from its six members, the two pinned ones
filled in. -/
def uts_name_of (nodename release version domainname : List Int) : List byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal nodename
  ++ uts_literal release
  ++ uts_literal version
  ++ uts_literal uts_machine_chars
  ++ uts_literal domainname

/-- Two admissible names differing only in `release`. -/
def uts_demo   : List byte := uts_name_of [] uts_release_a [] []
def uts_demo_b : List byte := uts_name_of [] uts_release_b [] []

/-- "Linuy": a `sysname` no kernel holds.  `init_uts_ns` writes the member
once (init/version-timestamp.c:14, Linux v6.18.46) and no syscall touches it. -/
def uts_bad_sysname : List byte :=
  uts_literal [76, 105, 110, 117, 121]
  ++ uts_literal [] ++ uts_literal uts_release_a ++ uts_literal []
  ++ uts_literal uts_machine_chars ++ uts_literal []

/-- "riscv32": a `machine` this kernel reports only to a PER_LINUX32
personality (kernel/sys.c:1310-1317, Linux v6.18.46), which the process this
model describes does not carry — the launcher premise stated on
`uts_machine_chars`. -/
def uts_bad_machine : List byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal [] ++ uts_literal uts_release_a ++ uts_literal []
  ++ uts_literal [114, 105, 115, 99, 118, 51, 50] ++ uts_literal []

/-- Sixty-five 'A's: a member with no terminator, in each of the four free
positions in turn. -/
def uts_unterminated_release : List byte :=
  uts_literal uts_sysname_chars ++ uts_literal []
  ++ List.replicate 65 (Z_to_bv 8 65)
  ++ uts_literal [] ++ uts_literal uts_machine_chars ++ uts_literal []
def uts_unterminated_nodename : List byte :=
  uts_literal uts_sysname_chars ++ List.replicate 65 (Z_to_bv 8 65)
  ++ uts_literal uts_release_a
  ++ uts_literal [] ++ uts_literal uts_machine_chars ++ uts_literal []
def uts_unterminated_version : List byte :=
  uts_literal uts_sysname_chars ++ uts_literal []
  ++ uts_literal uts_release_a
  ++ List.replicate 65 (Z_to_bv 8 65) ++ uts_literal uts_machine_chars ++ uts_literal []
def uts_unterminated_domainname : List byte :=
  uts_literal uts_sysname_chars ++ uts_literal []
  ++ uts_literal uts_release_a
  ++ uts_literal [] ++ uts_literal uts_machine_chars ++ List.replicate 65 (Z_to_bv 8 65)

/-- Every free member at its full 64 characters, terminated in byte 64
exactly: the longest name the envelope admits. -/
def uts_full_member : List byte := List.replicate 64 (Z_to_bv 8 65) ++ [uts_nul]
def uts_full_free : List byte :=
  uts_literal uts_sysname_chars ++ uts_full_member ++ uts_full_member
  ++ uts_full_member ++ uts_literal uts_machine_chars ++ uts_full_member

/-- A `nodename` with bytes AFTER an early NUL — "a", NUL, "b" — which
`sethostname` produces by copying `len` bytes verbatim (kernel/sys.c:1436, Linux v6.18.46). -/
def uts_embedded_nul : List byte := uts_name_of [97, 0, 98] uts_release_a [] []

/-- The pinned model: `uts_demo` recorded on `demo_model`. -/
def uts_pinned : Model := with_utsname uts_demo demo_model

/-- The `uname` call at 4096 over a writable view `wmem`. -/
def uts_in (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 160 [4096, 0, 0, 0, 0, 0] (fun _ => none) wmem

attribute [local sys_simp low] uts_in.eq_1

set_option maxRecDepth 8192 in
/-- The fixtures are 390 bytes each, as `struct new_utsname` is
(include/uapi/linux/utsname.h:25-32, Linux v6.18.46: six members of 65);
that 390 is `NEW_UTSNAME_SIZE` is `Checks/Cases/Sys/Uapi/Sched.lean`'s pin.
model: the fixtures' lengths, decided. -/
theorem uts_fixtures_are_390_bytes :
    uts_demo.length = 390 ∧ uts_demo_b.length = 390 ∧ uts_bad_sysname.length = 390
      ∧ uts_bad_machine.length = 390 ∧ uts_unterminated_release.length = 390
      ∧ uts_unterminated_nodename.length = 390 ∧ uts_unterminated_version.length = 390
      ∧ uts_unterminated_domainname.length = 390 ∧ uts_full_free.length = 390
      ∧ uts_embedded_nul.length = 390 := by
  decide

set_option maxRecDepth 8192 in
/-- The members land where `struct new_utsname` puts them: `uts_field`
reads `sysname` at 0, `release` at 2 and `machine` at 4, and the literal
builder zero-fills to 65 — "Linux" is five characters and sixty NULs,
and `machine` is `UTS_MACHINE`'s "riscv64" (arch/riscv/Makefile:31, Linux v6.18.46),
seven characters and fifty-eight NULs, pinned byte for byte.
kernel: include/uapi/linux/utsname.h:__NEW_UTS_LEN; kernel/sys.c:newuname@v6.18.46 -/
theorem uts_fields_are_the_struct_members :
    uts_field 0 uts_demo = uts_literal uts_sysname_chars
      ∧ uts_field 2 uts_demo = uts_literal uts_release_a
      ∧ uts_field 4 uts_demo = uts_literal uts_machine_chars
      ∧ (uts_literal uts_sysname_chars).length = 65
      ∧ (uts_literal uts_sysname_chars).take 6 = [76, 105, 110, 117, 120, 0]
      ∧ (uts_literal uts_machine_chars).take 8 = [114, 105, 115, 99, 118, 54, 52, 0]
      ∧ (uts_literal []).all (fun b => bv_eqb b uts_nul) = true
      ∧ uts_eqb (uts_field 1 uts_demo) (uts_literal []) = true
      ∧ uts_eqb (uts_field 1 uts_demo) (uts_literal [1]) = false
      ∧ uts_eqb (uts_field 1 uts_demo) ((uts_literal []).take 64) = false := by
  decide

set_option maxRecDepth 8192 in
/-- THE ENVELOPE, decided on the fixtures.  Admitted: both releases, the
longest terminated members, and a member with bytes after an early NUL.
Refused: a `sysname` that is not "Linux" (`UTS_SYSNAME`, include/linux/uts.h:9,
written once by `init_uts_ns`), a `machine` that is not "riscv64"
(`UTS_MACHINE`, arch/riscv/Makefile:31), and an unterminated member in
ANY of the four free positions — `sethostname` and `setdomainname` clear
the tail from `len` (kernel/sys.c:1437, :1491) and `override_release`
writes at most 65 bytes from a zeroed buffer (:1331, :1344-1346), so byte
64 of each is NUL on every path.  Each position has its own fixture so
that a predicate testing the wrong member index is refused here.
kernel: kernel/sys.c:newuname,sethostname,setdomainname,override_release,override_architecture@v6.18.46 -/
theorem utsname_wf_reads_the_kernel_envelope :
    utsname_wf uts_demo = true ∧ utsname_wf uts_demo_b = true
      ∧ utsname_wf uts_full_free = true ∧ utsname_wf uts_embedded_nul = true
      ∧ utsname_wf uts_bad_sysname = false ∧ utsname_wf uts_bad_machine = false
      ∧ utsname_wf uts_unterminated_release = false
      ∧ utsname_wf uts_unterminated_nodename = false
      ∧ utsname_wf uts_unterminated_version = false
      ∧ utsname_wf uts_unterminated_domainname = false := by
  decide

set_option maxRecDepth 8192 in
/-- …and the width is exact: 389 bytes is not a `struct new_utsname` and
neither is 391, while every byte of the four free members but the last is
FREE — all-'L' in bytes 0..63 of `release` is admitted, which is what
distinguishes a terminator test from a padding test.
kernel: kernel/sys.c:newuname,sethostname,override_release; include/uapi/linux/utsname.h:__NEW_UTS_LEN@v6.18.46 -/
theorem utsname_wf_width_and_free_bytes :
    utsname_wf (uts_demo.take 389) = false ∧ utsname_wf (uts_demo ++ [uts_nul]) = false
      ∧ utsname_wf (uts_name_of [] (List.replicate 64 76) [] []) = true
      ∧ utsname_wf (List.replicate 390 76) = false
      ∧ utsname_wf (List.replicate 390 uts_nul) = false := by
  decide

set_option maxRecDepth 8192 in
/-- THE FIRST uname, in full: 0 returned, some 390 bytes inside the
envelope landing at `name`, the name recorded, no event — and nothing
else.  `SYSCALL_DEFINE1(newuname)` copies the whole struct (kernel/sys.c:1356-1359, Linux v6.18.46)
and the kernel source does not say which release or hostname a machine
runs, so the environment chooses it here.
probe: testing/syscall-check/tests/uname_spec.c#conform -- once -/
theorem uname_first_copy_iff (o : outcome SyscallEffect) :
    uname_spec 4096 (uts_in uts_out) demo_model o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) (with_utsname bs demo_model) []
        ∧ utsname_wf bs = true := by
  sys_norm

set_option maxRecDepth 8192 in
/-- ONCE RECORDED, whatever the name, a later uname repeats the record
exactly and nothing else is admitted: a machine has one kernel for the
life of a process, and `SYSCALL_DEFINE1(newuname)` reads the same
`utsname()` each time (kernel/sys.c:1356, Linux v6.18.46).
probe: testing/syscall-check/tests/uname_spec.c#conform -- twice -/
theorem uname_recorded_name_is_repeated (bs : List byte) (o : outcome SyscallEffect) :
    uname_spec 4096 (uts_in uts_out) (with_utsname bs demo_model) o ↔
      o = Ok (mkEffect 0 [(4096, bs)] []) (with_utsname bs demo_model) [] := by
  sys_norm

/-- A name outside the envelope is refused as a FIRST answer, whatever
model and events come with it: the `utsname_wf` conjunct of
`uname_first_copy_iff`, read as a refutation.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_first_copy_refuses (bs : List byte) (hbs : utsname_wf bs = false)
    (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model (Ok (mkEffect 0 [(4096, bs)] []) m' evs) := by
  intro h
  obtain ⟨bs', heq, hwf⟩ := (uname_first_copy_iff _).1 h
  sys_simp_pass +decide at heq
  obtain ⟨hb, -, -⟩ := heq
  subst hb
  rw [hbs] at hwf
  exact Bool.false_ne_true hwf

/-- The first uname pins whatever name the environment reports.
probe: testing/syscall-check/tests/uname_spec.c#conform -- once
rocq-twin: uname_first_copy_pins -/
theorem uname_first_copy_pins :
    uname_spec 4096 (uts_in uts_out) demo_model
      (Ok (mkEffect 0 [(4096, uts_demo)] []) (with_utsname uts_demo demo_model) []) :=
  (uname_first_copy_iff _).2 ⟨uts_demo, rfl, utsname_wf_reads_the_kernel_envelope.1⟩

set_option maxRecDepth 8192 in
/-- …but not a name the kernel cannot hold: "Linuy" is a conformance
failure, not an unusual machine.
probe: testing/syscall-check/tests/uname_spec.c#reject --mutate uname:poison-writes:76 -- once
rocq-twin: uname_wrong_sysname_rejected -/
theorem uname_wrong_sysname_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_bad_sysname)] []) m' evs) :=
  uname_first_copy_refuses uts_bad_sysname (by decide) m' evs

set_option maxRecDepth 8192 in
/-- …nor a "riscv32" machine, which this kernel reports only under
PER_LINUX32 (kernel/sys.c:1310-1317, :1363-1364).
kernel: kernel/sys.c:newuname,override_architecture@v6.18.46 -/
theorem uname_wrong_machine_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_bad_machine)] []) m' evs) :=
  uname_first_copy_refuses uts_bad_machine (by decide) m' evs

set_option maxRecDepth 8192 in
/-- …and not an unterminated member either, in any of the four free
positions.  The release's CONTENT is free — `uts_demo` and `uts_demo_b`
are both admissible — so this rejection attributes to the terminator
conjunct alone.
probe: testing/syscall-check/tests/uname_spec.c#reject --mutate uname:trunc-writes:325,grow-writes:65 -- once
rocq-twin: uname_unterminated_release_rejected -/
theorem uname_unterminated_release_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_unterminated_release)] []) m' evs)
    ∧ ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_unterminated_nodename)] []) m' evs)
    ∧ ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_unterminated_version)] []) m' evs)
    ∧ ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_unterminated_domainname)] []) m' evs) :=
  ⟨uname_first_copy_refuses _ (by decide) m' evs, uname_first_copy_refuses _ (by decide) m' evs,
   uname_first_copy_refuses _ (by decide) m' evs, uname_first_copy_refuses _ (by decide) m' evs⟩

set_option maxRecDepth 8192 in
/-- …nor 389 bytes, which is not a `struct new_utsname`, nor a copy
landing one byte past `name`.
probe: testing/syscall-check/tests/uname_spec.c#reject --mutate uname:trunc-writes:389 -- once -/
theorem uname_wrong_width_or_place_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_demo.take 389)] []) m' evs)
    ∧ ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4097, uts_demo)] []) m' evs) := by
  refine ⟨uname_first_copy_refuses _ (by decide) m' evs, ?_⟩
  intro h
  obtain ⟨bs, heq, -⟩ := (uname_first_copy_iff _).1 h
  sys_simp_pass +decide at heq

/-- …nor a uname that returned 1, or an errno, with the struct delivered:
the modeled path returns a literal 0 (kernel/sys.c:1365, Linux v6.18.46).
probe: testing/syscall-check/tests/uname_spec.c#reject --mutate uname:ret=1 -- once -/
theorem uname_wrong_return_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 1 [(4096, uts_demo)] []) m' evs)
    ∧ ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [(4096, uts_demo)] []) m' evs) := by
  constructor <;>
  · intro h
    obtain ⟨bs, heq, -⟩ := (uname_first_copy_iff _).1 h
    sys_simp_pass +decide at heq

set_option maxRecDepth 8192 in
/-- …and a uname that recorded a name other than the one it delivered is
refused: the record IS the delivery.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_records_what_it_delivers (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) demo_model
        (Ok (mkEffect 0 [(4096, uts_demo)] []) (with_utsname uts_demo_b demo_model) evs) := by
  intro h
  obtain ⟨bs, heq, -⟩ := (uname_first_copy_iff _).1 h
  sys_simp_pass +decide at heq
  obtain ⟨hb, hm, -⟩ := heq
  subst hb
  exact absurd hm (by decide)

/-- ONCE PINNED, a later uname repeats the record exactly, and nothing
else is admitted: `uname_recorded_name_is_repeated` at `uts_demo`.
probe: testing/syscall-check/tests/uname_spec.c#conform -- twice -/
theorem uname_pinned_copy_iff (o : outcome SyscallEffect) :
    uname_spec 4096 (uts_in uts_out) uts_pinned o ↔
      o = Ok (mkEffect 0 [(4096, uts_demo)] []) uts_pinned [] :=
  uname_recorded_name_is_repeated uts_demo o

/-- The pinned name, repeated.
probe: testing/syscall-check/tests/uname_spec.c#conform -- twice
rocq-twin: uname_pinned_copy_repeats -/
theorem uname_pinned_copy_repeats :
    uname_spec 4096 (uts_in uts_out) uts_pinned
      (Ok (mkEffect 0 [(4096, uts_demo)] []) uts_pinned []) :=
  (uname_pinned_copy_iff _).2 rfl

set_option maxRecDepth 8192 in
/-- The defector is itself WELL-FORMED — `uts_demo_b` would have pinned
as a first answer — so it is refused for disagreeing with the record, not
for being a bad name.  That is the conjunct a per-call `choose` would
have dropped.
kernel: kernel/sys.c:newuname@v6.18.46
rocq-twin: uname_pinned_copy_defector_rejected -/
theorem uname_pinned_copy_defector_rejected (m' : Model) (evs : List event) :
    ¬ uname_spec 4096 (uts_in uts_out) uts_pinned
        (Ok (mkEffect 0 [(4096, uts_demo_b)] []) m' evs) := by
  intro h
  have heq := (uname_pinned_copy_iff _).1 h
  sys_simp_pass +decide at heq

set_option maxRecDepth 8192 in
/-- …and offered as a FIRST answer the defector is accepted, and pins
itself.
probe: testing/syscall-check/tests/uname_spec.c#conform -- once
rocq-twin: uname_defector_is_itself_admissible_first -/
theorem uname_defector_is_itself_admissible_first :
    uname_spec 4096 (uts_in uts_out) demo_model
      (Ok (mkEffect 0 [(4096, uts_demo_b)] []) (with_utsname uts_demo_b demo_model) []) :=
  (uname_first_copy_iff _).2 ⟨uts_demo_b, rfl, utsname_wf_reads_the_kernel_envelope.2.1⟩

/-- A destination past `TASK_SIZE` fails `access_ok` — `__access_ok`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46), which `_inline_copy_to_user`
asks at include/linux/uaccess.h:195, Linux v6.18.46 — so -EFAULT is exact
(kernel/sys.c:1358-1359, Linux v6.18.46) and no byte moves, for every starting model.
probe: testing/syscall-check/tests/uname_spec.c#conform -- fault
rocq-twin: uname_access_ok_fault -/
theorem uname_access_ok_fault (m : Model) (o : outcome SyscallEffect) :
    uname_spec 9223372036854775808
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- The width `access_ok` is handed is 390: a destination at
`TASK_SIZE - 389` fails `__access_ok`'s `addr <= limit - size`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46) and is -EFAULT
before any copy, for every model; `TASK_SIZE - 390` passes it and, with
nothing writable there, is the walk's decline.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem uname_at_the_top_of_the_address_space (m : Model) (o : outcome SyscallEffect) :
    (uname_spec 140737488354939
        (SyscallInput.mkInput 160 [140737488354939, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
          ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [])
    ∧ (uname_spec 140737488354938
        (SyscallInput.mkInput 160 [140737488354938, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
          ↔ o = Unmodeled) := by
  constructor <;> sys_norm

set_option maxRecDepth 8192 in
/-- A range `access_ok` ADMITS but memory does not wholly back is
declined, not faulted: `copy_to_user` would commit a prefix and then
answer -EFAULT, and the model cannot say how long that prefix is.  One
byte short of 390 is the whole difference, for every starting model.
probe: testing/syscall-check/tests/uname_spec.c#fail-closed --mutate uname:wmem-hide:a0+389:1 -- once
rocq-twin: uname_one_byte_short_is_unmodeled -/
theorem uname_one_byte_short_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    uname_spec 4096 (uts_in uts_out_short) m o ↔ o = Unmodeled := by
  sys_norm

/-- …and so is `uname(NULL)`: `access_ok` admits `[0, 390)` and the copy
faults, so the kernel's -EFAULT is not the range verdict the model can
give.
probe: testing/syscall-check/tests/uname_spec.c#fail-closed -- nullbuf -/
theorem uname_null_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    uname_spec 0 (SyscallInput.mkInput 160 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The destination is gated on the WRITABLE view: a readable-only view
of the zone declines.
probe: testing/syscall-check/tests/uname_spec.c#fail-closed --mutate uname:wmem-hide:a0:390 -- once -/
theorem uname_gates_on_the_writable_view (m : Model) (o : outcome SyscallEffect) :
    uname_spec 4096 (SyscallInput.mkInput 160 [4096, 0, 0, 0, 0, 0] uts_out (fun _ => none)) m o
      ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 8192 in
/-- THE WRAPPING DESTINATION, pinned in both directions.  `uname_spec`
asks `State.access_okb` BEFORE it walks `State.read_bytes_map`, and
these four say why that order is the arm and not a style choice.  No
probe can reach it: the harness's `in_wmem` answers `none` at and above
the reservation end.

What the bare walk says: "wholly writable", because the word arithmetic
wraps 2^64 - 4 round onto the 386 mapped bytes at 0.  Pinning it beside
the two below is what stops them going vacuous.
model: the walk's word arithmetic, a fact about `read_bytes_map` alone.
rocq-twin: uname_wrap_would_pass_the_bare_walk -/
theorem uname_wrap_would_pass_the_bare_walk :
    read_bytes_map uts_wrap_mem uts_wrap_name (Z_to_bv 64 390) ≠ none := by
  decide

/-- `__access_ok` refuses it: `addr <= limit - size` fails
(include/asm-generic/access_ok.h:40).
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: uname_wrap_name_is_not_access_ok -/
theorem uname_wrap_name_is_not_access_ok : access_okb uts_wrap_name 390 = false := by
  decide

set_option maxRecDepth 8192 in
/-- -EFAULT with nothing written is the answer, and nothing else is:
`copy_to_user`'s gate refuses the range before a byte moves and
`SYSCALL_DEFINE1(newuname)` returns -EFAULT (kernel/sys.c:1358-1359).
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: uname_wrapping_destination_faults -/
theorem uname_wrapping_destination_faults (m : Model) (o : outcome SyscallEffect) :
    uname_spec uts_wrap_name
        (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem) m o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

set_option maxRecDepth 8192 in
/-- THE NEGATIVE HALF: the effect an unguarded arm would have accepted —
0 returned with the 390 bytes stored at 2^64 - 4 and, once the word
wrapped, at 0 — is refused.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: uname_wrapping_destination_rejects_the_copy -/
theorem uname_wrapping_destination_rejects_the_copy (m m' : Model) (evs : List event) :
    ¬ uname_spec uts_wrap_name
        (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem) m
        (Ok (mkEffect 0 [(uts_wrap_name, uts_demo)] []) m' evs) := by
  intro h
  rw [uname_wrapping_destination_faults] at h
  sys_simp_pass +decide at h

/-- Through the table: 160 is `uname`, `a0` its destination.  The table
lookup is a computation, so the pinned `iff` transfers by definitional
unfolding alone.
probe: testing/syscall-check/tests/uname_spec.c#conform -- twice -/
theorem sysno_160_is_uname (o : outcome SyscallEffect) :
    syscall_spec (uts_in uts_out) uts_pinned o ↔
      o = Ok (mkEffect 0 [(4096, uts_demo)] []) uts_pinned [] :=
  uname_pinned_copy_iff o

/-- …and the fault through the table.
probe: testing/syscall-check/tests/uname_spec.c#conform -- fault -/
theorem sysno_160_fault_through_the_table (m : Model) (o : outcome SyscallEffect) :
    syscall_spec
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        m o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-! ## prctl (167): PR_CAPBSET_READ and nothing else

Rocq states these in `Checks/ProcessCreation.v`, not in the mirror file:
`prctl_modeled_options_are` by reflexivity on the list;
`prctl_option_unmodeled` and `prctl_tagged_addr_ctrl_unmodeled` over the
DISPATCHER, for every input and model whose `int32 a0` is outside the
list; and `prctl_checker_option_zero_unmodeled`, `prctl_checker_capbset_read`
and `prctl_checker_tagged_addr_ctrl_unmodeled` over the executable
checker.  So every pin here cites the kernel.  The dispatcher-level
universal is twinned in two halves, because `tools/check_decline_registers.py`
reads a `syscall_spec … Unmodeled` statement over `in_sysno` only in the
shapes of its registers and would refuse one with a membership hypothesis
between the number and the conclusion:
`prctl_option_outside_the_register_is_unmodeled` is the universal over
`prctl_spec` — every option outside `prctl_modeled_options`, every `arg2`,
input and model — and `sysno_167_option_is_an_int` is the `int32` the arm
applies before it; `sysno_167_set_tagged_addr_ctrl_declines` is the
tagged-address case through the table.  `SYSCALL_DEFINE5(prctl)` is
kernel/sys.c:2518-2877 at Linux v6.18.46 (commit 1f99e9ab748f) and
`cap_task_prctl` security/commoncap.c:1291-1431. -/

/-- The register is exactly `PR_CAPBSET_READ` (23, include/uapi/linux/prctl.h:71):
the whole modeled surface of the multiplexer, written down.
kernel: include/uapi/linux/prctl.h:PR_CAPBSET_READ@v6.18.46 -/
theorem prctl_modeled_options_are : prctl_modeled_options = [23] := by decide

/-- `prctl(PR_CAPBSET_READ, 0)` answers 1, for every input and every
model, touching neither: `cap_task_prctl`'s first arm is
`!!cap_raised(old->cap_bset, arg2)` (security/commoncap.c:1298-1301, Linux v6.18.46)
under the unnarrowed bounding set `State.creds_privileged` already
assumes, and `security_task_prctl` returns that nonzero answer before
kernel/sys.c's `switch` runs (security/security.c:3882-3883 and kernel/sys.c:2525-2527, Linux v6.18.46).
probe: testing/syscall-check/tests/prctl_spec.c#conform -- low -/
theorem prctl_capbset_read_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    prctl_spec 23 0 i m o ↔ o = Ok (mkEffect 1 [] []) m [] := by
  sys_norm

/-- The boundary is INCLUSIVE: `cap_valid(40)` holds (`CAP_LAST_CAP`,
include/uapi/linux/capability.h:421-425, Linux v6.18.46), so capability 40 answers 1.
THAT IS A CLAIM ABOUT KERNELS FROM v5.9 ON: the same header ends at 37
through v5.7 and at 39 at v5.8, so a supported kernel before v5.9 answers
-EINVAL here where this pin proves 1 —
linux-process-semantics@ff0313ba4f:bugs/prctl-capbset-read-arm-admits-linux-alone.md records it.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- last -/
theorem prctl_capbset_read_last_cap_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    prctl_spec 23 40 i m o ↔ o = Ok (mkEffect 1 [] []) m [] := by
  sys_norm

/-- …and 41 is not a capability: -EINVAL (security/commoncap.c:1299-1300, Linux v6.18.46),
nothing written, the model untouched.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- above -/
theorem prctl_capbset_read_above_last_cap_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    prctl_spec 23 41 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- `cap_valid` tests the FULL `unsigned long`: 2^32 and ~0 are -EINVAL,
not the answers for capabilities 0 and 63.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- wide -/
theorem prctl_capbset_read_wide_arg2_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (prctl_spec 23 4294967296 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
    ∧ (prctl_spec 23 (Z_to_bv 64 (-1)) i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  constructor <;> sys_norm

/-- A narrowed bounding set — 0 for a valid capability — is outside this
model; `!!cap_raised` is never 2; and no errno is admitted at or below
`CAP_LAST_CAP`.
probe: testing/syscall-check/tests/prctl_spec.c#reject --mutate prctl:ret=0 -- low -/
theorem prctl_capbset_read_wrong_answers_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ prctl_spec 23 0 i m (Ok (mkEffect 0 [] []) m' evs)
    ∧ ¬ prctl_spec 23 0 i m (Ok (mkEffect 2 [] []) m' evs)
    ∧ ¬ prctl_spec 23 0 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs)
    ∧ ¬ prctl_spec 23 40 i m (Ok (mkEffect 0 [] []) m' evs) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- Above the boundary neither 1 nor 0 nor -EPERM is an answer: -EINVAL is
the only errno `cap_valid` raises.
probe: testing/syscall-check/tests/prctl_spec.c#reject --mutate prctl:ret=1 -- above -/
theorem prctl_capbset_read_above_last_cap_rejections (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ prctl_spec 23 41 i m (Ok (mkEffect 1 [] []) m' evs)
    ∧ ¬ prctl_spec 23 41 i m (Ok (mkEffect 0 [] []) m' evs)
    ∧ ¬ prctl_spec 23 41 i m (Ok (mkEffect (errno_ret EPERM) [] []) m' evs)
    ∧ ¬ prctl_spec 23 4294967296 i m (Ok (mkEffect 1 [] []) m' evs) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- The answer writes no user memory and changes no state: a smuggled
write, or a model that moved, is refused.
probe: testing/syscall-check/tests/prctl_spec.c#reject --mutate prctl:smuggle-write:a0:1 -- low -/
theorem prctl_capbset_read_touches_nothing (i : SyscallInput) (evs : List event) :
    ¬ prctl_spec 23 0 i demo_model (Ok (mkEffect 1 [(4096, [0])] []) demo_model evs)
    ∧ ¬ prctl_spec 23 0 i demo_model (Ok (mkEffect 1 [] []) rlim_pinned []) := by
  constructor <;> sys_refute

/-- EVERY OTHER OPTION IS DECLINED, for every input and model: option 0
(no such option); `PR_GET_DUMPABLE` (3) and `PR_SET_DUMPABLE` (4), the
two `prctl`'s own `switch` answers first (kernel/sys.c:2551-2556, Linux v6.18.46);
`PR_CAPBSET_DROP` (24, include/uapi/linux/prctl.h:72, Linux v6.18.46), the
neighbour of 23, whose decline is what separates the option EQUALITY from
a bound; and `PR_SET_TAGGED_ADDR_CTRL`
(55, include/uapi/linux/prctl.h:244, Linux v6.18.46), the one that reaches riscv's
`set_tagged_addr_ctrl` (arch/riscv/kernel/process.c:285, Linux v6.18.46) and whose
decline is half of why `State.access_okb` is exact.  The gate precedes
the argument: option 55 with a valid capability in `arg2` is still
declined.  The `tagged` probe case records the (55, 0) conjunct and the
`dumpable` case the (3, 0) one; the rest are judged on the source.
probe: testing/syscall-check/tests/prctl_spec.c#fail-closed --expect-unmodeled prctl -- tagged -/
theorem prctl_other_options_are_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    (prctl_spec 0 0 i m o ↔ o = Unmodeled)
    ∧ (prctl_spec 3 0 i m o ↔ o = Unmodeled)
    ∧ (prctl_spec 4 1 i m o ↔ o = Unmodeled)
    ∧ (prctl_spec 55 0 i m o ↔ o = Unmodeled)
    ∧ (prctl_spec 24 0 i m o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and the option gate precedes the capability bound: `PR_GET_DUMPABLE`
(3) with 41 in `arg2`, and `PR_SET_DUMPABLE` (4) with 2^32, are declined,
not -EINVAL.  For `PR_CAPBSET_READ` the bound is the `cap_valid` inside
that case of `cap_task_prctl` (security/commoncap.c:1298-1301, Linux v6.18.46),
and neither option here reaches a `cap_valid` at all — the options that
do are `PR_CAPBSET_DROP`, whose test sits in `cap_prctl_drop`
(security/commoncap.c:1260-1268, Linux v6.18.46, at :1266, reached from
:1303-1304), and `PR_CAP_AMBIENT` (:1401): `PR_GET_DUMPABLE` never reads
`arg2` (kernel/sys.c:2551-2553, Linux v6.18.46), and what `PR_SET_DUMPABLE`
makes of 2^32 is the option's own business, declined with it.
kernel: security/commoncap.c:cap_task_prctl,cap_prctl_drop@v6.18.46 -/
theorem prctl_option_gate_precedes_the_capability_bound (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    (prctl_spec 3 41 i m o ↔ o = Unmodeled) ∧ (prctl_spec 4 4294967296 i m o ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- The option gate reads the register the TABLE hands it, so a value the
table has not narrowed is declined here — 2^32 | 23 is not 23 to this
spec.  `sysno_167_option_is_an_int` below is where the narrowing is shown
to happen, in the arm.
kernel: kernel/sys.c:prctl; security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem prctl_spec_reads_the_option_it_is_given (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    prctl_spec 4294967319 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- THE REGISTER IS THE GATE: for every option outside
`prctl_modeled_options`, every `arg2`, input and model, `prctl_spec`
declines.  This is Rocq's `prctl_option_unmodeled` (Checks/ProcessCreation.v)
stated over the spec, so that `prctl_modeled_options_are` above pins the
modeled surface rather than a list nothing reads; the `int32` the arm
applies first is `sysno_167_option_is_an_int`.  Linux answers each of
these options, in `SYSCALL_DEFINE5(prctl)`'s own `switch`
(kernel/sys.c:2518-2877, Linux v6.18.46) or in an LSM hook before it;
none is modeled.
kernel: kernel/sys.c:prctl@v6.18.46 -/
theorem prctl_option_outside_the_register_is_unmodeled (option_ arg2 : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : bv_unsigned option_ ∉ prctl_modeled_options) :
    prctl_spec option_ arg2 i m o ↔ o = Unmodeled := by
  have hne : (bv_unsigned option_ == PR_CAPBSET_READ) = false := by
    simp only [prctl_modeled_options, List.mem_singleton] at h
    exact beq_eq_false_iff_ne.mpr h
  simp only [prctl_spec, hne, Bool.not_false, ↓reduceIte]
  exact unmodeled_iff _ _ _

/-- `PR_SET_TAGGED_ADDR_CTRL` through the table — Rocq's
`prctl_tagged_addr_ctrl_unmodeled`, the case the tagging argument needs —
in the concrete shape `tools/check_decline_registers.py` reads as a
per-argument decline of a modeled number.
probe: testing/syscall-check/tests/prctl_spec.c#fail-closed --expect-unmodeled prctl -- tagged -/
theorem sysno_167_set_tagged_addr_ctrl_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 167 [55, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := by
  sys_norm

/-- Through the table: 167 is `prctl`, `a0` the option and `a1` the
capability; `a2..a4` are read by nothing on this arm, so junk there
changes nothing.  The input is the `junk` run's own six words —
`CAP_LAST_CAP` in `a1`, then -1, 0x5555555555555555 and
0xdeadbeefdeadbeef (testing/syscall-check/traces/prctl_spec/018.jsonl) —
so the pin states the recorded pair, not a shape of its own.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- junk -/
theorem sysno_167_is_prctl (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 167
        [23, 40, 18446744073709551615, 6148914691236517205, 16045690984833335023, 0]
        (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect 1 [] []) m [] := by
  sys_norm

/-- The OPTION IS AN `int`: the table applies `int32`, so 2^32 | 23
reaches the spec as `PR_CAPBSET_READ` and is answered (`__SC_CAST`,
include/linux/syscalls.h:132, Linux v6.18.46, applied by riscv's `__SYSCALL_DEFINEx`,
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  Measured
under qemu-system, where the `hiopt` probe case sees the kernel.  THE 1
IS LINUX'S ANSWER ALONE: QEMU's user-mode `do_prctl` switches on the
whole 64-bit `abi_long` and answers -EINVAL to 2^32 | 23, so at this
shape the arm proves an answer outside the supported intersection;
linux-process-semantics@ff0313ba4f:bugs/prctl-capbset-read-arm-admits-linux-alone.md records it and what
it costs.  The other half of the asymmetry — `arg2` is NOT narrowed —
is `sysno_167_capability_is_an_unsigned_long` below, one claim per pin
so that each cites the probe case whose recorded run returned its
answer — and states that run's own argument pair: `hiopt` asks for
`CAP_LAST_CAP` (40) in `a1`
(testing/syscall-check/traces/prctl_spec/017.jsonl), so 40 it is here;
capability 0 through a narrowed option is the `low` case's pair, not
this one's.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- hiopt -/
theorem sysno_167_option_is_an_int (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 167 [4294967319, 40, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect 1 [] []) m [] := by
  sys_norm

/-- The refusal that pins the other side of the same pair: a kernel
answering -EINVAL to `prctl(2^32 | PR_CAPBSET_READ, CAP_LAST_CAP)` is
rejected, because the arm proves 1 there.  That -EINVAL is exactly what
QEMU's user-mode `do_prctl` answers (the bugs entry above), so this pin
is where the model's Linux-alone answer is visible as a rejection: the
probe's mutated run records the verdict `reject`, and a repair that hands
the option register through whole would turn this pin into a decline
rather than delete it.
probe: testing/syscall-check/tests/prctl_spec.c#reject --mutate prctl:ret=-EINVAL -- hiopt -/
theorem sysno_167_option_is_an_int_rejects_the_unnarrowed_answer (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 167 [4294967319, 40, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- THE CAPABILITY IS AN `unsigned long`: the table narrows nothing in
`a1`, so 2^32 reaches `cap_valid` whole and fails its upper bound —
`((x) >= 0 && (x) <= CAP_LAST_CAP)` (include/uapi/linux/capability.h:425,
Linux v6.18.46) on an `unsigned long`, a 64-bit unsigned comparison — in
`cap_task_prctl`'s `PR_CAPBSET_READ` arm (security/commoncap.c:1298-1300,
Linux v6.18.46): -EINVAL through the table, beside
`sysno_167_option_is_an_int` above where the option IS narrowed.  The
`wide` probe case measures this half under qemu-system.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- wide -/
theorem sysno_167_capability_is_an_unsigned_long (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 167 [23, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The `wide` run's second record, `prctl(PR_CAPBSET_READ, ~0UL)`
(testing/syscall-check/traces/prctl_spec/011.jsonl, both records -22):
the same 64-bit comparison, on a word whose low half 0xffffffff names no
capability under any narrowing either, so unlike 2^32 it separates
nothing about `a1`'s width — it is pinned because the run recorded it,
and the probe refuses the forged 1 at this occurrence with
`prctl#2:ret=1`.
probe: testing/syscall-check/tests/prctl_spec.c#conform -- wide -/
theorem sysno_167_capability_all_ones_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 167 [23, 18446744073709551615, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- `PR_GET_DUMPABLE` through the table declines — the probe's `dumpable`
mode is `prctl(3, 0)`, the option `prctl`'s own `switch` answers first,
with the task's dumpable flag (kernel/sys.c:2551-2553, Linux v6.18.46) — in the direct
shape `tools/check_decline_registers.py` reads as a per-argument decline
of a modeled number.  (`PR_SET_DUMPABLE`, 4, is the spec-level conjunct
of `prctl_other_options_are_unmodeled`; no probe runs it.)
probe: testing/syscall-check/tests/prctl_spec.c#fail-closed --expect-unmodeled prctl -- dumpable -/
theorem sysno_167_get_dumpable_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 167 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := by
  sys_norm

/-- …and a forged plausible answer there — 1, `SUID_DUMP_USER`, what
`get_dumpable` reports for an ordinary process — is still refused: the
option gate precedes it.
probe: testing/syscall-check/tests/prctl_spec.c#fail-closed --mutate prctl:ret=1 --expect-unmodeled prctl -- dumpable -/
theorem sysno_167_get_dumpable_rejects_a_forged_answer (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 167 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys
