import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Kernel.Sys — what the id, session, pid, uname, prlimit64 and prctl checkers answer, read off against Linux

Pins over `Checks.Sys.Kernel.Sys`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Sys.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Sys.v` — the getpid,
gettid, getuid-family, setuid/setgid, setresuid/setresgid and setsid
arms first (ticket C-Kernel-Sys-ids), and the uname, prlimit64 and prctl
arms appended after them (ticket C-Kernel-Sys-uname-prlimit-prctl).  Rocq's worked
cases on these arms (`Checks/Cases/Kernel/Sys.v`) are stated over the
SPEC and are twinned in `Checks/Cases/Kernel/Sys.lean`; so this file
mirrors nothing, exactly as `Checks/Cases/Checks/Sys/Kernel/Fork.lean`
does not: these are the Lean tree's tests for what the twin ports, placed
where every pin in this tree lives so that `tools/check_lean_pins.py`
reads them and the twin holds only definitions and their lemmas.  Not
part of the trusted specification: this file is QA on the definitions,
written to be READ, and every claim in it is a claim about what the
kernel does, with the citation beside it.  Every kernel line below was
read at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT A CHECKER PIN IS FOR.  The four proof obligations each arm carries
tie the checker to the spec, in both directions, for every input.  What
they cannot say is that either side agrees with Linux: change the spec
and the checker the same wrong way and every obligation still closes.
Each pin below therefore names a CONCRETE answer — a return the kernel
gives, accepted with the model the kernel would leave; a return it
cannot give, refused — so that the wrong change fails here.  Beside each
accepted answer is the lie a kernel cannot tell, refuted on its own.

The fixtures are `Checks/Cases/Kernel/Sys.lean`'s: `split_ids_model`,
whose six ids are pairwise distinct so that a checker wired to the wrong
field is told apart; `root_model`; `root_split_model` (real 0, effective
0, saved 5), the one shape on which the ORDER of `setuid`'s capability
test and its real-or-saved rule is observable; and `suid_root_model`
(real 5, effective 0, saved 0), on which "the real uid moves" and "the
effective uid moves" come apart for a privileged caller.  The setsid and
pid pins run on `demo_model`, whose tid slot is empty and whose session
bit is clear (`m_tid_demo_model`, `m_setsid_succeeded_demo_model`).
The uname and prlimit64 pins run on the Prelude's and
`Checks/Cases/Kernel/Sys.lean`'s fixtures — the 390-byte names, the
writable zones, `uts_pinned` and `rlim_pinned` — the same closed data
the spec pins there are stated over, so that a checker answer and a spec
answer on one fixture can be read side by side; the prctl pins are
over a symbolic model, since the checker reads none.

Every pin on a fixture closes by `rfl`: the checker is a Boolean program
over closed data, and computing it IS the test.  Where a pin is stated
over a symbolic model it is closed by the same rewrites the twin's
completeness proofs use.

A word on the errnos a refusal offers.  The evidence rule reads every
errno a POSITIVE statement names — and `= CheckReject` is positive, it
asserts an answer — against the text of the cited kernel symbols.  So
an -EAGAIN refusal cites `set_user`, the one function that spells it,
beside the setter that does or does not call it; and where the point is
that a syscall has NO errno but one (the readers; setsid outside -EPERM)
the refused value is written as the register word it would occupy,
named in the prose, since no function on that syscall's path spells the
constant.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Sys

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys

section Pids

/-! ## getpid (172) and gettid (178): the one recorded tid

`SYSCALL_DEFINE0(getpid)` (kernel/sys.c:999-1002, v6.18.46) returns
`task_tgid_vnr(current)`, and `SYSCALL_DEFINE0(gettid)`
(kernel/sys.c:1005-1008, v6.18.46) returns `task_pid_vnr(current)`; for the one-thread
process the model carries they are one number, drawn by `alloc_pid`
(kernel/pid.c:163-309, v6.18.46) at the process's creation and never moved.  The
checkers are `check_set_tid_address` under two names, so the pins here
are the ones that distinguish a first draw from a later reading. -/

/-- A first getpid records the trace's tid: 1 is inside the envelope
(`pid_min` starts at 1, kernel/pid.c:226) and becomes the recorded tid.
kernel: kernel/sys.c:getpid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_getpid_records_the_first_draw :
    check_getpid (mkEffect 1 [] []) demo_model = CheckOk (with_tid 1 demo_model) [] := rfl

/-- …and tid 0 is refused on it: no live task has pid 0 (`alloc_pid`
draws from `pid_min = 1`, kernel/pid.c:226, into an end-exclusive range,
:238-239).
kernel: kernel/sys.c:getpid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_getpid_refuses_tid_zero :
    check_getpid (mkEffect 0 [] []) demo_model = CheckReject := rfl

/-- A later gettid repeats the recorded tid, and the model does not move:
`task_pid_vnr` (include/linux/pid.h:244-247) reads the pid the task holds.
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_gettid_repeats_the_recorded_tid :
    check_gettid (mkEffect 7 [] []) (with_tid 7 demo_model) = CheckOk (with_tid 7 demo_model) [] := rfl

/-- …and another tid, even one inside the envelope, is refused: the pid of
a task is one number.
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_gettid_refuses_another_tid :
    check_gettid (mkEffect 8 [] []) (with_tid 7 demo_model) = CheckReject := rfl

/-- getpid and gettid read the SAME slot: a tid recorded by one is what
the other must repeat.  `task_tgid_vnr` (include/linux/pid.h:296-299) and
`task_pid_vnr` (:244-247) read the same `struct pid` of a thread-group
leader.
kernel: kernel/sys.c:getpid,gettid; include/linux/pid.h:task_tgid_vnr,task_pid_vnr@v6.18.46 -/
theorem check_getpid_repeats_what_gettid_recorded :
    check_getpid (mkEffect 7 [] []) (with_tid 7 demo_model) = CheckOk (with_tid 7 demo_model) [] := rfl

/-- A session id `setsid` recorded is what getpid answers afterwards:
`ksys_setsid` returns the caller's own pid (kernel/sys.c:1271-1273 and
:1292), the number `task_tgid_vnr` reads.
kernel: kernel/sys.c:getpid,ksys_setsid; include/linux/pid.h:task_tgid_vnr@v6.18.46 -/
theorem check_getpid_repeats_the_session_id_setsid_recorded :
    check_getpid (mkEffect 1234 [] []) (with_setsid_succeeded (with_tid 1234 demo_model))
      = CheckOk (with_setsid_succeeded (with_tid 1234 demo_model)) [] := rfl

/-- An errno is refused: `SYSCALL_DEFINE0(getpid)` has no failing path
(kernel/sys.c:999-1002); the -EINVAL `alloc_pid` sets for a bad requested
tid (kernel/pid.c:198-199) is on a path a pid reader never enters.
kernel: kernel/sys.c:getpid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_getpid_refuses_an_errno :
    check_getpid (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject := rfl

end Pids

section Readers

/-! ## getuid, geteuid, getgid, getegid (174-177): one field each

`SYSCALL_DEFINE0(getuid)` returns
`from_kuid_munged(current_user_ns(), current_uid())`
(kernel/sys.c:1027-1031, v6.18.46), and its three siblings the effective uid, the
real gid and the effective gid (kernel/sys.c:1033-1049, v6.18.46).  In the initial
user namespace the mapping is the identity, and no reader has a failing
path.  On `split_ids_model` the six ids are 1000, 1001, 1002, 2000, 2001
and 2002, so each reader's answer names its field and no other. -/

variable (a : word) (b : byte)

/-- getuid answers the real uid, and the model does not move.
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem check_getuid_reads_the_real_uid :
    check_getid Creds.cr_uid (mkEffect 1000 [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and refuses the effective uid: `current_uid()` is `cred->uid`, not
`cred->euid`, which `geteuid` reads (kernel/sys.c:1033-1037).
kernel: kernel/sys.c:getuid,geteuid@v6.18.46 -/
theorem check_getuid_refuses_the_effective_uid :
    check_getid Creds.cr_uid (mkEffect 1001 [] []) split_ids_model = CheckReject := rfl

/-- geteuid answers the effective uid.
kernel: kernel/sys.c:geteuid@v6.18.46 -/
theorem check_geteuid_reads_the_effective_uid :
    check_getid Creds.cr_euid (mkEffect 1001 [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and refuses the saved uid, which no reader returns.
kernel: kernel/sys.c:geteuid@v6.18.46 -/
theorem check_geteuid_refuses_the_saved_uid :
    check_getid Creds.cr_euid (mkEffect 1002 [] []) split_ids_model = CheckReject := rfl

/-- getgid answers the real gid.
kernel: kernel/sys.c:getgid@v6.18.46 -/
theorem check_getgid_reads_the_real_gid :
    check_getid Creds.cr_gid (mkEffect 2000 [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and refuses the real uid: a checker wired to `cr_uid` for syscall
176 fails here.
kernel: kernel/sys.c:getgid,getuid@v6.18.46 -/
theorem check_getgid_refuses_the_real_uid :
    check_getid Creds.cr_gid (mkEffect 1000 [] []) split_ids_model = CheckReject := rfl

/-- getegid answers the effective gid.
kernel: kernel/sys.c:getegid@v6.18.46 -/
theorem check_getegid_reads_the_effective_gid :
    check_getid Creds.cr_egid (mkEffect 2001 [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and refuses the effective uid: `current_egid()` is `cred->egid`, and
a checker reading `cr_euid` for syscall 177 fails here.
kernel: kernel/sys.c:getegid,geteuid@v6.18.46 -/
theorem check_getegid_refuses_the_effective_uid :
    check_getid Creds.cr_egid (mkEffect 1001 [] []) split_ids_model = CheckReject := rfl

/-- On root the real uid reads 0, the model unmoved.
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem check_getuid_on_root_reads_zero :
    check_getid Creds.cr_uid (mkEffect 0 [] []) root_model = CheckOk root_model [] := rfl

/-- An errno's register word is refused: `2^64 - 1` is what -EPERM
occupies, and a reader has no failing path — `from_kuid_munged`
(kernel/user_namespace.c:466-474) turns even an unmappable id into the
overflow id, never an errno.  Written as the word rather than as
`errno_ret EPERM` because no function on a reader's path spells any
errno, and the evidence rule reads the constants a positive statement
names against the cited text.
kernel: kernel/sys.c:getuid; kernel/user_namespace.c:from_kuid_munged@v6.18.46 -/
theorem check_getuid_refuses_an_errno_word :
    check_getid Creds.cr_uid (mkEffect 18446744073709551615 [] []) split_ids_model = CheckReject := rfl

/-- A write ledger beside the right answer is refused: a reader touches
no user memory (kernel/sys.c:1027-1031 is one `return`).
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem check_getuid_refuses_a_write_ledger :
    check_getid Creds.cr_uid (mkEffect 1000 [(a, [b])] []) split_ids_model = CheckReject := rfl

/-- …and a zeros ledger.
kernel: kernel/sys.c:getuid@v6.18.46 -/
theorem check_getuid_refuses_a_zeros_ledger :
    check_getid Creds.cr_uid (mkEffect 1000 [] [(a, 8)]) split_ids_model = CheckReject := rfl

end Readers

section Setuid

/-! ## setuid (146) on an unprivileged caller

`__sys_setuid` (kernel/sys.c:651-696, v6.18.46): -EINVAL for an id `make_kuid`
refuses (:659-661), before anything is allocated; `prepare_creds`
(:663-665), the -ENOMEM; then a caller without `CAP_SETUID` may name its
real or saved uid, which becomes the effective one (:676-678, falling
through to the install at :680-691), and every other id is -EPERM (:668,
reached by the `goto error` at :677).  `set_user` is called only on the
capable arm (:672), so an unprivileged call never shows -EAGAIN.  On
`split_ids_model` the uids are real 1000, effective 1001, saved 1002. -/

variable (a : word) (b : byte)

/-- setuid to the real uid installs it as the effective uid and leaves
the saved uid: `new->euid = kuid` (:680) after the real-or-saved test.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_the_real_uid_installs_it_as_effective :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1000 1002 2000 2001 2002 demo_groups) split_ids_model) [] := rfl

/-- setuid to the saved uid installs it as the effective uid the same way.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_the_saved_uid_installs_it_as_effective :
    check_setid cred_uids set_cred_uids true 1002 (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) split_ids_model) [] := rfl

/-- The effective uid ALONE does not qualify: 1001 is neither the real nor
the saved uid, so the test at :676 fails and the answer is -EPERM.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_the_effective_uid_alone_is_eperm :
    check_setid cred_uids set_cred_uids true 1001 (mkEffect (errno_ret EPERM) [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- …and success is refused there: a checker that let a caller "keep" its
effective uid through setuid fails here.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_the_effective_uid_alone_refuses_success :
    check_setid cred_uids set_cred_uids true 1001 (mkEffect 0 [] []) split_ids_model = CheckReject := rfl

/-- A foreign uid is -EPERM for an unprivileged caller.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_a_foreign_uid_is_eperm :
    check_setid cred_uids set_cred_uids true 1003 (mkEffect (errno_ret EPERM) [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- …success is refused…
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_a_foreign_uid_refuses_success :
    check_setid cred_uids set_cred_uids true 1003 (mkEffect 0 [] []) split_ids_model = CheckReject := rfl

/-- …-ENOMEM is accepted, since `prepare_creds` (:663-665) runs BEFORE the
permission test, so an unprivileged caller can be told -ENOMEM instead of
-EPERM…
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_a_foreign_uid_accepts_enomem :
    check_setid cred_uids set_cred_uids true 1003 (mkEffect (errno_ret ENOMEM) [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- …and -EAGAIN is refused: `set_user` (kernel/sys.c:523-534) is reached
only from the capable arm (:669-675), and the `goto error` at :677
returns before `set_cred_ucounts` (kernel/cred.c:533-551, v6.18.46), the
other -EAGAIN of this path (:686), is called.
kernel: kernel/sys.c:__sys_setuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setuid_to_a_foreign_uid_refuses_eagain :
    check_setid cred_uids set_cred_uids true 1003 (mkEffect (errno_ret EAGAIN) [] []) split_ids_model
      = CheckReject := rfl

/-- -EAGAIN is refused on the installing arm too: naming the saved uid
moves only the effective uid (:680), so `set_user` is not called, and
`set_cred_ucounts` (kernel/cred.c:533-551, v6.18.46) returns 0 from its
fast path (:541-542) because `new->uid` is unchanged.
kernel: kernel/sys.c:__sys_setuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setuid_unprivileged_install_refuses_eagain :
    check_setid cred_uids set_cred_uids true 1002 (mkEffect (errno_ret EAGAIN) [] []) split_ids_model
      = CheckReject := rfl

/-- The id `-1` (`(uid_t) -1`, the word 4294967295) is -EINVAL:
`make_kuid` maps it to `INVALID_UID` and `uid_valid` refuses it
(:659-661).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_minus_one_is_einval :
    check_setid cred_uids set_cred_uids true 4294967295 (mkEffect (errno_ret EINVAL) [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- …and -ENOMEM is refused there: the -EINVAL test precedes
`prepare_creds` (:659-661 before :663), so no allocation can fail first.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_minus_one_refuses_enomem :
    check_setid cred_uids set_cred_uids true 4294967295 (mkEffect (errno_ret ENOMEM) [] []) split_ids_model
      = CheckReject := rfl

/-- …as are -EPERM…
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_minus_one_refuses_eperm :
    check_setid cred_uids set_cred_uids true 4294967295 (mkEffect (errno_ret EPERM) [] []) split_ids_model
      = CheckReject := rfl

/-- …and success, even for root: the test is on the id, before the
credentials are consulted.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_minus_one_refuses_success_for_root :
    check_setid cred_uids set_cred_uids true 4294967295 (mkEffect 0 [] []) root_model = CheckReject := rfl

/-- A write ledger beside the success return is refused: `setuid` writes
no user memory.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_refuses_a_write_ledger :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect 0 [(a, [b])] []) split_ids_model = CheckReject := rfl

/-- …and a zeros ledger beside an errno.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_refuses_a_zeros_ledger :
    check_setid cred_uids set_cred_uids true 1003 (mkEffect (errno_ret EPERM) [] [(a, 8)]) split_ids_model
      = CheckReject := rfl

/-- -EPERM is refused on the real-uid arm: :676 passes for the caller's
real uid, so the `goto error` at :677 is never reached and only
`prepare_creds` (:663-665) can fail — given the spec preamble's LSM
premise on the hook at :682 and `set_cred_ucounts`' fast path
(kernel/cred.c:541-542, v6.18.46) on an unmoved real uid.  A checker
whose installing arm admitted -EPERM beside -ENOMEM fails here.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_to_the_real_uid_refuses_eperm :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect (errno_ret EPERM) [] []) split_ids_model
      = CheckReject := rfl

/-- The -EINVAL gate from the other side: `(uid_t)-2` is a valid id.
`init_user_ns`'s uid map is one extent of count 4294967295 from 0
(kernel/user.c:37-47, v6.18.46), so `make_kuid` (kernel/user_namespace.c:422,
v6.18.46) maps every 32-bit value but -1, and `uid_valid`
(include/linux/uidgid.h:103, v6.18.46) refuses that one alone (:659-661).
root installs it as all three uids…
kernel: kernel/sys.c:__sys_setuid; kernel/user_namespace.c:make_kuid; include/linux/uidgid.h:uid_valid@v6.18.46 -/
theorem check_setuid_root_installs_minus_two :
    check_setid cred_uids set_cred_uids true 4294967294 (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 4294967294 4294967294 4294967294 0 0 0 demo_groups)
          root_model) [] := rfl

/-- …and -EINVAL is refused for it.  A gate widened to every id above
`2^31` fails here.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_minus_two_refuses_einval :
    check_setid cred_uids set_cred_uids true 4294967294 (mkEffect (errno_ret EINVAL) [] []) root_model
      = CheckReject := rfl

end Setuid

section SetuidPrivileged

/-! ## setuid on a privileged caller

The capable arm (:669-675) installs the id as all three uids and calls
`set_user` (:672) when the real uid moves; `set_user` (kernel/sys.c:523-534,
v6.18.46) answers -EAGAIN when `alloc_uid` fails (:527-529) and for no
other reason — the RLIMIT_NPROC test is `flag_nproc_exceeded` (:536-553),
which sets a flag and never fails.  The path's second -EAGAIN is
`set_cred_ucounts` (kernel/cred.c:533-551, v6.18.46), called at :686 on
every arm that reaches it, and it too fails only when the real uid moved:
its fast path (:541-542) returns 0 while `new->uid` is the old one. -/

/-- root's setuid installs the id as real, effective and saved uid.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_root_installs_all_three :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) root_model) [] := rfl

/-- …-EAGAIN is accepted, since the real uid moves and `set_user` runs…
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
theorem check_setuid_root_moving_the_real_uid_accepts_eagain :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckOk root_model [] := rfl

/-- …-ENOMEM is accepted, from `prepare_creds`…
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_root_accepts_enomem :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect (errno_ret ENOMEM) [] []) root_model
      = CheckOk root_model [] := rfl

/-- …and -EPERM is refused: a capable caller is never refused an id —
`root_model` is capable by `State.creds_privileged`'s premises (init user
namespace, default securebits, no file or ambient capabilities), and
"never" reads under the spec preamble's LSM premise, `cap_task_fix_setuid`
(security/commoncap.c:1149-1186, v6.18.46) returning 0 and SafeSetID's
-EACCES lying outside the model.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_root_refuses_eperm :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect (errno_ret EPERM) [] []) root_model
      = CheckReject := rfl

/-- root's setuid(0) does not move the real uid, so `set_user` is not
called (`if (!uid_eq(kuid, old->uid))`, :671), and `set_cred_ucounts`
(kernel/cred.c:533-551, v6.18.46), still called at :686, returns 0 from
its fast path (:541-542) because `new->uid` is unchanged: -EAGAIN is
refused.
kernel: kernel/sys.c:__sys_setuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setuid_root_to_itself_refuses_eagain :
    check_setid cred_uids set_cred_uids true 0 (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckReject := rfl

/-- On `root_split_model` (real 0, effective 0, saved 5) setuid(5) takes
the CAPABLE arm and installs 5 as all three uids — not, as the
real-or-saved rule would, as the effective uid alone: the capability test
(:669) is read before that rule (:676).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_root_split_takes_the_capable_arm :
    check_setid cred_uids set_cred_uids true 5 (mkEffect 0 [] []) root_split_model
      = CheckOk (with_creds (Creds.mkCreds 5 5 5 0 0 0 demo_groups) root_split_model) [] := rfl

/-- …and -EAGAIN is accepted there, since the real uid moves from 0 to 5.
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
theorem check_setuid_root_split_accepts_eagain :
    check_setid cred_uids set_cred_uids true 5 (mkEffect (errno_ret EAGAIN) [] []) root_split_model
      = CheckOk root_split_model [] := rfl

/-- On `suid_root_model` (real 5, effective 0, saved 0) setuid(5) is the
capable arm again, and the real uid does NOT move, so -EAGAIN is refused
even though the effective uid changes: `set_user` is keyed on the real
uid (:671), not the effective one, and `set_cred_ucounts`
(kernel/cred.c:533-551, v6.18.46), called at :686, keys its fast path
(:541-542) on `new->uid` too.
kernel: kernel/sys.c:__sys_setuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setuid_suid_root_to_its_real_uid_refuses_eagain :
    check_setid cred_uids set_cred_uids true 5 (mkEffect (errno_ret EAGAIN) [] []) suid_root_model
      = CheckReject := rfl

/-- …and installs 5 as all three.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_suid_root_installs_all_three :
    check_setid cred_uids set_cred_uids true 5 (mkEffect 0 [] []) suid_root_model
      = CheckOk (with_creds (Creds.mkCreds 5 5 5 0 0 0 demo_groups) suid_root_model) [] := rfl

/-- The other direction on the same model: setuid(0) moves the real uid
from 5 to 0, so `set_user` runs (:671-672) and -EAGAIN is accepted.
kernel: kernel/sys.c:__sys_setuid,set_user@v6.18.46 -/
theorem check_setuid_suid_root_to_zero_accepts_eagain :
    check_setid cred_uids set_cred_uids true 0 (mkEffect (errno_ret EAGAIN) [] []) suid_root_model
      = CheckOk suid_root_model [] := rfl

end SetuidPrivileged

section Setgid

/-! ## setgid (144): the same shape without the `set_user` call

`__sys_setgid` (kernel/sys.c:479-513, v6.18.46) has `setuid`'s -EINVAL, -ENOMEM,
capable and real-or-saved arms and no `set_user` call: the capable arm
(:497-498) assigns the three gids and allocates nothing, so -EAGAIN is
never shown.  On `split_ids_model` the gids are 2000, 2001, 2002. -/

/-- setgid to the saved gid installs it as the effective gid and leaves
the uids alone.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_to_the_saved_gid_installs_it_as_effective :
    check_setid cred_gids set_cred_gids false 2002 (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1001 1002 2000 2002 2002 demo_groups) split_ids_model) [] := rfl

/-- The effective gid alone is -EPERM, as for setuid.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_to_the_effective_gid_alone_is_eperm :
    check_setid cred_gids set_cred_gids false 2001 (mkEffect (errno_ret EPERM) [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- root's setgid installs the gid as all three…
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_root_installs_all_three :
    check_setid cred_gids set_cred_gids false 3000 (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 0 0 0 3000 3000 3000 demo_groups) root_model) [] := rfl

/-- …accepts -ENOMEM from `prepare_creds`…
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_root_accepts_enomem :
    check_setid cred_gids set_cred_gids false 3000 (mkEffect (errno_ret ENOMEM) [] []) root_model
      = CheckOk root_model [] := rfl

/-- …and REFUSES -EAGAIN where `setuid` would accept it: `__sys_setgid`
(kernel/sys.c:479-513) calls neither `set_user` nor `set_cred_ucounts`
(kernel/cred.c:533-551, v6.18.46) even when the real gid moves, since a
gid does not change the ucounts' uid.  This is the pin that
separates the two setters' errno sets; a checker built with `user = true`
for syscall 144 fails here.
kernel: kernel/sys.c:__sys_setgid,set_user@v6.18.46 -/
theorem check_setgid_root_refuses_eagain :
    check_setid cred_gids set_cred_gids false 3000 (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckReject := rfl

/-- The gid `-1` is -EINVAL, as for setuid (`gid_valid`, :488-489).
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_minus_one_is_einval :
    check_setid cred_gids set_cred_gids false 4294967295 (mkEffect (errno_ret EINVAL) [] []) root_model
      = CheckOk root_model [] := rfl

/-- Success is refused for the effective gid alone: :499 tests `old->gid`
and `old->sgid`, never `egid`.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_to_the_effective_gid_alone_refuses_success :
    check_setid cred_gids set_cred_gids false 2001 (mkEffect 0 [] []) split_ids_model
      = CheckReject := rfl

/-- …and for a foreign gid.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem check_setgid_to_a_foreign_gid_refuses_success :
    check_setid cred_gids set_cred_gids false 3000 (mkEffect 0 [] []) split_ids_model
      = CheckReject := rfl

end Setgid

section Setresuid

/-! ## setresuid (147)

`__sys_setresuid` (kernel/sys.c:708-781, v6.18.46) resolves each `-1` to the
current id, answers 0 to a call that changes nothing BEFORE it allocates
(:732-737), refuses with -EPERM a caller without the capability that
names an id it does not already hold (:739-747), and only then allocates
(:749-751, the -ENOMEM) and installs (:753-765), calling `set_user`
(:755-758) when the real uid moves.  -1 is the word 4294967295. -/

variable (a : word) (b : byte)

/-- setresuid(-1, -1, -1) is a no-op: 0, model unmoved.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_all_minus_one_is_a_noop :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295 (mkEffect 0 [] [])
      split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and -ENOMEM is refused there: the no-op returns at :737, before
`prepare_creds` at :749, so no allocation can fail.  A checker that ran
the errno arm on a no-op fails here.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_noop_refuses_enomem :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295
      (mkEffect (errno_ret ENOMEM) [] []) split_ids_model = CheckReject := rfl

/-- …as is -EPERM: an unprivileged caller may always name what it holds.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_noop_refuses_eperm :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckReject := rfl

/-- Naming the three current ids outright is the same no-op: the test at
:733-736 compares the resolved ids, not the arguments.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_naming_the_current_ids_is_a_noop :
    check_setresid cred_uids set_cred_uids true 1000 1001 1002 (mkEffect 0 [] []) split_ids_model
      = CheckOk split_ids_model [] := rfl

/-- …and refuses -ENOMEM likewise.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_naming_the_current_ids_refuses_enomem :
    check_setresid cred_uids set_cred_uids true 1000 1001 1002 (mkEffect (errno_ret ENOMEM) [] [])
      split_ids_model = CheckReject := rfl

/-- setresuid(-1, 1002, -1) moves the effective uid to the saved one,
which an unprivileged caller may do (:739-744 are all false, so
:745-747 does not fire).
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_to_the_saved_uid_installs_the_effective :
    check_setresid cred_uids set_cred_uids true 4294967295 1002 4294967295 (mkEffect 0 [] [])
      split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) split_ids_model) [] := rfl

/-- …-ENOMEM is accepted, from `prepare_creds`…
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_effective_move_accepts_enomem :
    check_setresid cred_uids set_cred_uids true 4294967295 1002 4294967295
      (mkEffect (errno_ret ENOMEM) [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and -EAGAIN is refused: the real uid did not move, so `set_user`
(:755-758) is not called and `set_cred_ucounts` (kernel/cred.c:533-551,
v6.18.46) returns 0 from its fast path (:541-542).
kernel: kernel/sys.c:__sys_setresuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setresuid_effective_move_refuses_eagain :
    check_setresid cred_uids set_cred_uids true 4294967295 1002 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject := rfl

/-- …and -EPERM is refused: every id named is one the caller holds, so
:739-744 are all false and :745-747 does not fire, and nothing past it
spells -EPERM — `prepare_creds` (:749-751) answers -ENOMEM, `set_user`
(:755-758) and `set_cred_ucounts` (:771; kernel/cred.c:533-551, v6.18.46)
-EAGAIN, and `commit_creds` (kernel/cred.c:392-459, v6.18.46) always 0.
A checker whose installing arm admitted -EPERM beside -ENOMEM fails here.
kernel: kernel/sys.c:__sys_setresuid,set_user; kernel/cred.c:prepare_creds,set_cred_ucounts,commit_creds@v6.18.46 -/
theorem check_setresuid_effective_move_refuses_eperm :
    check_setresid cred_uids set_cred_uids true 4294967295 1002 4294967295
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckReject := rfl

/-- setresuid(1002, -1, -1) moves the REAL uid to the saved one, which an
unprivileged caller may do, and `set_user` runs: -EAGAIN is accepted…
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_real_move_accepts_eagain :
    check_setresid cred_uids set_cred_uids true 1002 4294967295 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and success installs it, the other two ids kept.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_real_move_installs_it :
    check_setresid cred_uids set_cred_uids true 1002 4294967295 4294967295 (mkEffect 0 [] [])
      split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1002 1001 1002 2000 2001 2002 demo_groups) split_ids_model) [] := rfl

/-- A foreign uid is -EPERM for an unprivileged caller…
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_to_a_foreign_uid_is_eperm :
    check_setresid cred_uids set_cred_uids true 1003 4294967295 4294967295
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- …and -ENOMEM is REFUSED there, unlike under `setuid`: the permission
test (:745-747) precedes `prepare_creds` (:749-751) in `setresuid`, where
`setuid` allocates first.  A checker that copied `setuid`'s order fails
here.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_to_a_foreign_uid_refuses_enomem :
    check_setresid cred_uids set_cred_uids true 1003 4294967295 4294967295
      (mkEffect (errno_ret ENOMEM) [] []) split_ids_model = CheckReject := rfl

/-- …and success is refused.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_to_a_foreign_uid_refuses_success :
    check_setresid cred_uids set_cred_uids true 1003 4294967295 4294967295 (mkEffect 0 [] [])
      split_ids_model = CheckReject := rfl

/-- root's setresuid(1000, -1, -1) installs the real uid alone…
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_root_installs_the_real_uid_alone :
    check_setresid cred_uids set_cred_uids true 1000 4294967295 4294967295 (mkEffect 0 [] [])
      root_model = CheckOk (with_creds (Creds.mkCreds 1000 0 0 0 0 0 demo_groups) root_model) [] := rfl

/-- …and accepts -EAGAIN, the real uid having moved.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_root_real_move_accepts_eagain :
    check_setresid cred_uids set_cred_uids true 1000 4294967295 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckOk root_model [] := rfl

/-- …and -EPERM is refused: a capable caller is never refused an id —
`ns_capable_setid` (:746) is the second conjunct of the one -EPERM test
(:745-747), and no function after it spells -EPERM.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_root_real_move_refuses_eperm :
    check_setresid cred_uids set_cred_uids true 1000 4294967295 4294967295
      (mkEffect (errno_ret EPERM) [] []) root_model = CheckReject := rfl

/-- root's setresuid(-1, -1, 5) installs the saved uid alone — the call
that builds `root_split_model` — and the real uid staying put, `set_user`
(:755-758) is not called and `set_cred_ucounts` (kernel/cred.c:533-551,
v6.18.46), called at :771, returns 0 from its fast path (:541-542):
-EAGAIN is refused.
kernel: kernel/sys.c:__sys_setresuid,set_user; kernel/cred.c:set_cred_ucounts@v6.18.46 -/
theorem check_setresuid_root_saved_move_refuses_eagain :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 5
      (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckReject := rfl

/-- …and its success lands on that fixture's credentials.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_root_saved_move_builds_root_split :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 5 (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 0 0 5 0 0 0 demo_groups) root_model) [] := rfl

/-- A write ledger beside the no-op's 0 is refused.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_refuses_a_write_ledger :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295
      (mkEffect 0 [(a, [b])] []) split_ids_model = CheckReject := rfl

/-- A rotation of the three held ids needs no privilege: each `*_new`
(:739-744) compares its id against ALL of uid, euid and suid, so none is
new and :745-747 does not fire.  A checker that copied `setuid`'s
slot-wise test (:676) fails here.  The real uid moves, so `set_user`
runs (:755-758)…
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_rotation_installs_all_three :
    check_setresid cred_uids set_cred_uids true 1002 1000 1001 (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1002 1000 1001 2000 2001 2002 demo_groups)
          split_ids_model) [] := rfl

/-- …and -EAGAIN is accepted for it.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_rotation_accepts_eagain :
    check_setresid cred_uids set_cred_uids true 1002 1000 1001 (mkEffect (errno_ret EAGAIN) [] [])
      split_ids_model = CheckOk split_ids_model [] := rfl

/-- root's setresuid(-1, -1, -1) is the same no-op: the test at :733-737
reads the resolved ids and never the capability.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_root_noop_is_a_noop :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295 (mkEffect 0 [] [])
      root_model = CheckOk root_model [] := rfl

/-- …and root's no-op refuses -ENOMEM as well: the no-op test (:733-737)
is read before `ns_capable_setid` (:746) and `prepare_creds` (:749-751)
alike.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem check_setresuid_root_noop_refuses_enomem :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295
      (mkEffect (errno_ret ENOMEM) [] []) root_model = CheckReject := rfl

/-- …and the no-op refuses -EAGAIN: `set_user` (:756) is behind the no-op
return (:737) too.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_noop_refuses_eagain :
    check_setresid cred_uids set_cred_uids true 4294967295 4294967295 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject := rfl

/-- A foreign uid refuses -EAGAIN as it refuses -ENOMEM: :745-747 returns
before `set_user` (:756) can run.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem check_setresuid_to_a_foreign_uid_refuses_eagain :
    check_setresid cred_uids set_cred_uids true 1003 4294967295 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject := rfl

end Setresuid

section Setresgid

/-! ## setresgid (149): the same without the `set_user` call

`__sys_setresgid` (kernel/sys.c:810-870, v6.18.46) is `setresuid`'s shape — no-op
(:832-837), -EPERM (:845-847), `prepare_creds` (:849-851), install — with
no `set_user` call. -/

/-- root's setresgid(-1, -1, 3000) installs the saved gid alone…
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_root_installs_the_saved_gid_alone :
    check_setresid cred_gids set_cred_gids false 4294967295 4294967295 3000 (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 0 0 0 0 0 3000 demo_groups) root_model) [] := rfl

/-- …and root's setresgid(3000, -1, -1), which moves the REAL gid, still
refuses -EAGAIN: `set_user` is not on the gid setter's path.  A checker
built with `user = true` for syscall 149 fails here.
kernel: kernel/sys.c:__sys_setresgid,set_user@v6.18.46 -/
theorem check_setresgid_root_real_move_refuses_eagain :
    check_setresid cred_gids set_cred_gids false 3000 4294967295 4294967295
      (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckReject := rfl

/-- …while -ENOMEM is accepted, from `prepare_creds` (:849-851).
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_root_real_move_accepts_enomem :
    check_setresid cred_gids set_cred_gids false 3000 4294967295 4294967295
      (mkEffect (errno_ret ENOMEM) [] []) root_model = CheckOk root_model [] := rfl

/-- An unprivileged caller naming a foreign gid is -EPERM (:845-847).
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_to_a_foreign_gid_is_eperm :
    check_setresid cred_gids set_cred_gids false 4294967295 4294967295 3000
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckOk split_ids_model [] := rfl

/-- setresgid(-1, 2002, -1) moves the effective gid to the saved one
without privilege: :839-844 are all false for a held id.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_to_the_saved_gid_installs_the_effective :
    check_setresid cred_gids set_cred_gids false 4294967295 2002 4294967295 (mkEffect 0 [] [])
      split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1001 1002 2000 2002 2002 demo_groups)
          split_ids_model) [] := rfl

/-- …and -EPERM is refused there: :845-847 is the only -EPERM on the
path and does not fire for a held gid; past it only `prepare_creds`
(:849-851) can fail.
kernel: kernel/sys.c:__sys_setresgid; kernel/cred.c:prepare_creds@v6.18.46 -/
theorem check_setresgid_to_the_saved_gid_refuses_eperm :
    check_setresid cred_gids set_cred_gids false 4294967295 2002 4294967295
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckReject := rfl

/-- A foreign gid refuses -ENOMEM: -EPERM (:845-847) precedes
`prepare_creds` (:849-851), as in `setresuid`.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_to_a_foreign_gid_refuses_enomem :
    check_setresid cred_gids set_cred_gids false 4294967295 4294967295 3000
      (mkEffect (errno_ret ENOMEM) [] []) split_ids_model = CheckReject := rfl

/-- …and success is refused, as under `setresuid`.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem check_setresgid_to_a_foreign_gid_refuses_success :
    check_setresid cred_gids set_cred_gids false 4294967295 4294967295 3000 (mkEffect 0 [] [])
      split_ids_model = CheckReject := rfl

end Setresgid

section Setsid

/-! ## setsid (157)

`ksys_setsid` (kernel/sys.c:1268-1301, v6.18.46) seeds `err = -EPERM` (:1274),
refuses a session leader (:1278-1279) and a caller whose pid is already a
process-group id (:1284-1285), and otherwise makes the caller a session
leader (:1287-1290) and returns its own pid (:1292).  The model carries
neither the session-leader bit nor the process-group table, so -EPERM is
accepted on every model; a session id is accepted only while no call has
succeeded, and only as the tid the process holds. -/

variable (m : Model) (a : word) (b : byte)

/-- -EPERM is accepted on a first call, the model unmoved.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_eperm_accepted_on_a_first_call :
    check_setsid (mkEffect (errno_ret EPERM) [] []) demo_model = CheckOk demo_model [] := rfl

/-- -EPERM is accepted on EVERY model, before and after a success: the
process-group test at :1284 reads a table the model does not carry, and
after a success the caller is a session leader (:1278-1279).
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_eperm_accepted_on_every_model :
    check_setsid (mkEffect (errno_ret EPERM) [] []) m = CheckOk m [] := by
  simp only [check_setsid, bv_eqb_refl, ↓reduceIte]

/-- A session id inside the envelope is accepted on a first call, and the
post-model records it as the tid and sets the leader bit: the session id
is the caller's own pid (:1271-1273, :1292), a number `alloc_pid`
(kernel/pid.c:163-309) stored.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_setsid_records_a_session_id :
    check_setsid (mkEffect 1234 [] []) demo_model
      = CheckOk (with_setsid_succeeded (with_tid 1234 demo_model)) [] := rfl

/-- 0 is refused: no task has pid 0 (`alloc_pid` draws from `pid_min = 1`,
kernel/pid.c:226).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_setsid_refuses_zero :
    check_setsid (mkEffect 0 [] []) demo_model = CheckReject := rfl

/-- The envelope's end, `2^22`, is refused: `pid_max` is at most
`PID_MAX_LIMIT` (include/linux/threads.h:34-35), `4 * 1024 * 1024` on a
64-bit kernel — a new namespace starts there (kernel/pid_namespace.c:110,
v6.18.46) and the sysctl's ceiling `pid_max_max` is it (kernel/pid.c:65
and :749) — and `alloc_pid`'s draw (kernel/pid.c:238-239) passes
`pid_max` as the exclusive end of `idr_alloc_cyclic` (lib/idr.c:119,
v6.18.46).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_setsid_refuses_the_envelope_end :
    check_setsid (mkEffect 4194304 [] []) demo_model = CheckReject := rfl

/-- Any errno but -EPERM is refused: `err` is seeded to -EPERM (:1274)
and no path assigns another.  The word offered is `2^64 - 13`, the
register value of -EACCES, written as the word because no function on
`setsid`'s path spells another errno constant for the evidence rule to
read.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_refuses_another_errno_word :
    check_setsid (mkEffect 18446744073709551603 [] []) demo_model = CheckReject := rfl

/-- A write ledger beside a session id is refused: the effect's shape is
judged before the return, and `ksys_setsid` touches only the task's own
pid links.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_refuses_a_write_beside_a_session_id :
    check_setsid (mkEffect 1234 [(a, [b])] []) demo_model = CheckReject := rfl

/-- …and a zeros ledger beside -EPERM.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_refuses_a_zeros_ledger_beside_eperm :
    check_setsid (mkEffect (errno_ret EPERM) [] [(a, 8)]) demo_model = CheckReject := rfl

/-- After a success the same session id is refused: :1287 set the
caller's `signal->leader`, the session-leader bit, and :1278-1279 sends
every later call to -EPERM.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_after_a_success_refuses_a_second :
    check_setsid (mkEffect 1234 [] []) (with_setsid_succeeded (with_tid 1234 demo_model)) = CheckReject := rfl

/-- …and -EPERM is what it answers.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_after_a_success_is_eperm :
    check_setsid (mkEffect (errno_ret EPERM) [] []) (with_setsid_succeeded (with_tid 1234 demo_model))
      = CheckOk (with_setsid_succeeded (with_tid 1234 demo_model)) [] := rfl

/-- The leader bit alone refuses a session id, whatever the tid slot
holds: the bit, not the recorded tid, is what `:1278-1279` reads.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_bit_alone_refuses_a_session_id :
    check_setsid (mkEffect 1234 [] []) (with_setsid_succeeded demo_model) = CheckReject := rfl

/-- With tid 7 recorded (by an earlier getpid, say), the session id must
be 7: `ksys_setsid` returns the caller's own pid (:1292).
kernel: kernel/sys.c:ksys_setsid; include/linux/pid.h:task_tgid_vnr@v6.18.46 -/
theorem check_setsid_answers_the_recorded_tid :
    check_setsid (mkEffect 7 [] []) (with_tid 7 demo_model)
      = CheckOk (with_setsid_succeeded (with_tid 7 (with_tid 7 demo_model))) [] := rfl

/-- …and 8 is refused: a session id other than the caller's pid is a lie.
kernel: kernel/sys.c:ksys_setsid; include/linux/pid.h:task_tgid_vnr@v6.18.46 -/
theorem check_setsid_refuses_another_id_after_a_recorded_tid :
    check_setsid (mkEffect 8 [] []) (with_tid 7 demo_model) = CheckReject := rfl

/-- The envelope's last id, `2^22 - 1`, is accepted: the draw at
kernel/pid.c:238-239 is end-exclusive, so it is the largest id a kernel
at `PID_MAX_LIMIT` hands out.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_setsid_accepts_the_envelopes_last_id :
    check_setsid (mkEffect 4194303 [] []) demo_model
      = CheckOk (with_setsid_succeeded (with_tid 4194303 demo_model)) [] := rfl

end Setsid

section NeverDeclines

/-! ## The checkers never decline

Each pin is stated through the checker's soundness half
and the spec's own never-declines pin, as `Checks/Cases/Checks/Sys/Kernel/
Fork.lean` states it: a `CheckUnmodeled` answer would put the spec at
`Unmodeled`, which the spec pin refuses because the kernel function has
no path the model leaves open.  The kernel line backs the claim here as
it backs the spec pin; a `model:` line would hide a modeled-surface claim
behind a model fact.  The setsid and reader pins are then read off the
checker alone, with no lemma of the twin in the proof. -/

variable (eff : SyscallEffect) (m : Model)

/-- getpid never declines: `SYSCALL_DEFINE0(getpid)` (kernel/sys.c:999-1002)
is one `return`.
kernel: kernel/sys.c:getpid@v6.18.46 -/
theorem check_getpid_never_declines : check_getpid eff m ≠ CheckUnmodeled :=
  fun h => getpid_never_declines
    (SyscallInput.mkInput 172 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_getpid_sound_unmodeled _ eff m h)

/-- gettid never declines (kernel/sys.c:1005-1008).
kernel: kernel/sys.c:gettid@v6.18.46 -/
theorem check_gettid_never_declines : check_gettid eff m ≠ CheckUnmodeled :=
  fun h => gettid_never_declines
    (SyscallInput.mkInput 178 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_gettid_sound_unmodeled _ eff m h)

/-- No reader declines, whichever field it reads: the four
`SYSCALL_DEFINE0`s (kernel/sys.c:1027-1049) are each one `return`.
kernel: kernel/sys.c:getuid,geteuid,getgid,getegid@v6.18.46 -/
theorem check_getid_never_declines (sel : Creds → word) : check_getid sel eff m ≠ CheckUnmodeled :=
  fun h => getid_never_declines sel
    (SyscallInput.mkInput 174 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_getid_sound_unmodeled sel eff m _ h)

/-- The same fact read off the reader alone: it is `check_ret_only`, whose
every arm is `CheckOk` or `CheckReject`.
kernel: kernel/sys.c:getuid,geteuid,getgid,getegid@v6.18.46 -/
theorem check_getid_never_declines_directly (sel : Creds → word) :
    check_getid sel eff m ≠ CheckUnmodeled := by
  unfold check_getid check_ret_only
  split
  · split <;> exact nofun
  · exact nofun

/-- setuid and setgid never decline, for every id and every model: every
path of `__sys_setuid` (kernel/sys.c:651-696) and `__sys_setgid`
(:479-513) is one of the arms the checker reads.
kernel: kernel/sys.c:__sys_setuid,__sys_setgid@v6.18.46 -/
theorem check_setid_never_declines (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) : check_setid get put user v eff m ≠ CheckUnmodeled :=
  fun h => setid_never_declines get put user v
    (SyscallInput.mkInput 146 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_setid_sound_unmodeled get put user v eff m _ h)

/-- setresuid and setresgid never decline: every path of
`__sys_setresuid` (kernel/sys.c:708-781) and `__sys_setresgid`
(:810-870) is one of the checker's three answers.
kernel: kernel/sys.c:__sys_setresuid,__sys_setresgid@v6.18.46 -/
theorem check_setresid_never_declines (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) : check_setresid get put user r e s eff m ≠ CheckUnmodeled :=
  fun h => setresid_never_declines get put user r e s
    (SyscallInput.mkInput 147 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_setresid_sound_unmodeled get put user r e s eff m _ h)

/-- setsid never declines: `ksys_setsid` (kernel/sys.c:1268-1301) answers
-EPERM or the caller's pid, and the checker accepts the first on every
model.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_never_declines : check_setsid eff m ≠ CheckUnmodeled :=
  fun h => setsid_never_declines
    (SyscallInput.mkInput 157 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_setsid_sound_unmodeled _ eff m h)

/-- The same fact read off the setsid checker alone, with no lemma of the
twin in the proof: the pin above dies with `check_setsid_sound_unmodeled`,
this one with the checker.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem check_setsid_never_declines_directly : check_setsid eff m ≠ CheckUnmodeled := by
  unfold check_setsid
  split
  · split
    · exact nofun
    · split
      · exact nofun
      -- The third condition carries `match m_tid m`, which `split` opens
      -- before the `if` around it; the second `split` then reaches the `if`.
      · split <;> split <;> exact nofun
  · exact nofun

end NeverDeclines

section Witness

/-! ## The witnesses

Each witness is one outcome its spec accepts at every model, which is
what the progress argument consumes.  They are pinned here at their
shapes on the fixtures, and each shape is one the checker accepts. -/

variable (m : Model)

/-- The setsid witness is -EPERM, the answer accepted before and after a
success.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_witness_is_eperm :
    setsid_witness demo_model = Ok (mkEffect (errno_ret EPERM) [] []) demo_model [] := rfl

/-- The setsid witness never declines: it is a `ret_outcome`, which is an
`Ok`.
model: `ret_outcome r m` is `Ok (mkEffect r [] []) m []` by definition; no kernel behaviour is claimed -/
theorem setsid_witness_never_declines : setsid_witness m ≠ Unmodeled := by
  intro h
  unfold setsid_witness ret_outcome at h
  cases h

/-- The reader's witness is the selected field: geteuid's on
`split_ids_model` is 1001.
kernel: kernel/sys.c:geteuid@v6.18.46 -/
theorem getid_witness_reads_the_field :
    getid_witness Creds.cr_euid split_ids_model = Ok (mkEffect 1001 [] []) split_ids_model [] := rfl

/-- The setuid witness for the id `-1` is -EINVAL (:659-661)…
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setid_witness_minus_one_is_einval :
    setid_witness 4294967295 demo_model = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := rfl

/-- …and for any other id -ENOMEM, the failure every remaining arm can
show (`prepare_creds`, :663-665).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setid_witness_otherwise_is_enomem :
    setid_witness 1000 demo_model = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [] := rfl

/-- The checker accepts the setuid witness's -ENOMEM on the unprivileged
fixture (the caller names its real uid, and `prepare_creds` can fail).
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem check_setuid_accepts_the_witness_enomem :
    check_setid cred_uids set_cred_uids true 1000 (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- The setresuid witness on a no-op is 0 (:732-737)…
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresid_witness_noop_is_zero :
    setresid_witness cred_uids 4294967295 4294967295 4294967295 split_ids_model
      = Ok (mkEffect 0 [] []) split_ids_model [] := rfl

/-- …on a foreign id for an unprivileged caller -EPERM (:745-747)…
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresid_witness_foreign_is_eperm :
    setresid_witness cred_uids 1003 4294967295 4294967295 split_ids_model
      = Ok (mkEffect (errno_ret EPERM) [] []) split_ids_model [] := rfl

/-- …and on a permitted move -ENOMEM (:749-751).
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresid_witness_move_is_enomem :
    setresid_witness cred_uids 1002 4294967295 4294967295 split_ids_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) split_ids_model [] := rfl

end Witness

-- lean-port sentinel: ticket V-Kernel-Sys-ids appends below this line

section V_Kernel_Sys_ids

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## V-Kernel-Sys-ids — the id and session arms over the real table

WHAT IS TWINNED HERE.  The header's "this file mirrors nothing" was
true of the checker pins above, which were written before
`checked_table` carried a row for any of these numbers.  This section is
the registration's, and it does mirror: the seven examples of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sys.v` and the six
`setsid_checker_*` examples of `theories/LinuxProcessSem/Checks/ProcessCreation.v`
are all stated through Rocq's `check_syscall`, and each is restated here
through the Lean `check_syscall`, over `checked_table` itself, under its
Rocq name with `_over_the_real_table` after it (K6b's convention).
`Checks/Cases/Kernel/Sys.lean` twins the first seven over the SPEC, and
`Checks/ProcessCreation.lean` names the spec pins that carry the six
setsid ones; a pin here is the same answer read off the table.  Rocq
states the setsid six at `pc_model`; they are stated here at
`demo_model`, which `Checks/ProcessCreation.lean`'s `pc_model` docstring
says it equals in every field but the supplementary groups, a field
`check_setsid` does not read, so that this file need not import the run.

WHAT A PIN HERE ADDS to the checker pins above is the ARM's claim: that
the lookup at each number finds this ticket's arm rather than the
dispatcher's decline, that the arm hands its checker the register the
kernel reads, and that it hands it the id NARROWED.  The setters'
parameters are `uid_t` / `gid_t` (kernel/sys.c:515, :698, :783 and :872,
Linux v6.18.46), 32-bit, and riscv64's wrapper casts each register to
that type (`__SC_CAST`, include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), while the
checkers compare at full width: `check_setid`'s docstring says the
narrowing is the registration's, and the `*_narrow*` pins below state
it in both directions — a register whose upper half is set is answered
as its low half through the table, and as the whole word by the checker
itself, so an arm that dropped `uid32` fails the first and a checker
that grew its own narrowing leaves the second to say so.

POLARITY is the sections' above: the evidence line is `kernel:` on every
pin about the kernel's answer, `CheckOk` and `CheckReject` alike, and
`model:` on a pin about the table's own contents. -/

/-- Syscall `n` with `a0`-`a2` as given, the other three argument
registers zero and no readable or writable memory: Rocq's
`mkInput n [a0; a1; a2; 0; 0; 0] (fun _ => None) (fun _ => None)`, the
input every example twinned below is stated at. -/
def sys_ids_in (n : Int) (a0 a1 a2 : word) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 n) [a0, a1, a2, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The lookup the dispatcher performs at each of the eleven numbers
finds that number's arm, whatever the argument registers hold.
model: `lookup_ca` over `checked_table` at closed numbers; the table's own
contents, not a kernel claim. -/
theorem lookup_sys_ids_in (a0 a1 a2 : word) :
    lookup_ca checked_table (bv_unsigned (sys_ids_in 144 a0 a1 a2).in_sysno) = some arm_setgid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 146 a0 a1 a2).in_sysno) = some arm_setuid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 147 a0 a1 a2).in_sysno)
      = some arm_setresuid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 149 a0 a1 a2).in_sysno)
      = some arm_setresgid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 157 a0 a1 a2).in_sysno) = some arm_setsid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 172 a0 a1 a2).in_sysno) = some arm_getpid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 174 a0 a1 a2).in_sysno) = some arm_getuid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 175 a0 a1 a2).in_sysno) = some arm_geteuid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 176 a0 a1 a2).in_sysno) = some arm_getgid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 177 a0 a1 a2).in_sysno) = some arm_getegid
    ∧ lookup_ca checked_table (bv_unsigned (sys_ids_in 178 a0 a1 a2).in_sysno)
      = some arm_gettid :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The seven examples of `Checks/Cases/Kernel/Sys.v`, through `check_syscall` -/

/-- `each_reader_reads_its_own_field` over the real table: on six
different ids each reader answers its own field of `current_cred()`
(`SYSCALL_DEFINE0(getuid)` at kernel/sys.c:1027, `geteuid` :1033,
`getgid` :1039, `getegid` :1045, Linux v6.18.46), and a reader answering
another field's value is refused — which is what fixes that 175 and 177
are not wired to each other's selector, nor 176 to the uid.
kernel: kernel/sys.c:getuid,geteuid,getgid,getegid@v6.18.46 -/
theorem each_reader_reads_its_own_field_over_the_real_table :
    check_syscall (sys_ids_in 174 0 0 0) (mkEffect 1000 [] []) split_ids_model
      = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 175 0 0 0) (mkEffect 1001 [] []) split_ids_model
      = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 176 0 0 0) (mkEffect 2000 [] []) split_ids_model
      = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 177 0 0 0) (mkEffect 2001 [] []) split_ids_model
      = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 176 0 0 0) (mkEffect 1000 [] []) split_ids_model = CheckReject
    ∧ check_syscall (sys_ids_in 177 0 0 0) (mkEffect 1001 [] []) split_ids_model = CheckReject
    ∧ check_syscall (sys_ids_in 175 0 0 0) (mkEffect 1002 [] []) split_ids_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `privileged_setuid_moves_all_three_ids` over the real table: root's
`setuid(1000)` takes the capable arm of `__sys_setuid` (kernel/sys.c:669-672,
Linux v6.18.46), which writes the real and saved uid and then the
effective one (:680), so a success leaves all three at 1000 and the group
ids alone.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem privileged_setuid_moves_all_three_ids_over_the_real_table :
    check_syscall (sys_ids_in 146 1000 0 0) (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) [] :=
  rfl

/-- `eagain_only_when_a_privileged_setuid_moves_the_real_uid` over the
real table: -EAGAIN comes only from `set_user` (kernel/sys.c:523-534,
Linux v6.18.46), which `__sys_setuid` calls on its capable arm when the
real uid moves (:671-672) and `__sys_setgid` never calls, so it is
accepted for root's `setuid(1000)` and refused for root's `setgid(1000)`,
for root's `setuid(0)`, and for an unprivileged caller; -ENOMEM
(`prepare_creds` failing, :663-665, and in `__sys_setgid` :491-493) is
accepted on the group setter too.
kernel: kernel/sys.c:__sys_setuid,__sys_setgid,set_user@v6.18.46 -/
theorem eagain_only_when_a_privileged_setuid_moves_the_real_uid_over_the_real_table :
    check_syscall (sys_ids_in 146 1000 0 0) (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckOk root_model []
    ∧ check_syscall (sys_ids_in 144 1000 0 0) (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckReject
    ∧ check_syscall (sys_ids_in 146 0 0 0) (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckReject
    ∧ check_syscall (sys_ids_in 146 1000 0 0) (mkEffect (errno_ret EAGAIN) [] []) split_ids_model
      = CheckReject
    ∧ check_syscall (sys_ids_in 144 1000 0 0) (mkEffect (errno_ret ENOMEM) [] []) root_model
      = CheckOk root_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `unprivileged_setuid_moves_only_the_effective_id` over the real
table: an unprivileged caller naming its real (1000) or saved (1002) uid
moves the effective uid alone (kernel/sys.c:676-680, Linux v6.18.46),
and naming an id it does not hold (1003) is -EPERM, so a success is
refused.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem unprivileged_setuid_moves_only_the_effective_id_over_the_real_table :
    check_syscall (sys_ids_in 146 1000 0 0) (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1000 1002 2000 2001 2002 demo_groups) demo_model) []
    ∧ check_syscall (sys_ids_in 146 1002 0 0) (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []
    ∧ check_syscall (sys_ids_in 146 1003 0 0) (mkEffect 0 [] []) split_ids_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- `setresgid_parks_a_group_in_the_saved_id` over the real table:
`setresgid(-1, -1, 22)` by root writes `new->sgid` alone
(kernel/sys.c:853-858, Linux v6.18.46).  The three registers are the
three parameters in order (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, same version): an arm
reading 22 as the real or effective gid would move that id instead.
kernel: kernel/sys.c:__sys_setresgid@v6.18.46 -/
theorem setresgid_parks_a_group_in_the_saved_id_over_the_real_table :
    check_syscall (sys_ids_in 149 4294967295 4294967295 22) (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 0 0 0 0 0 22 demo_groups) demo_model) [] :=
  rfl

/-- `setresuid_reaches_its_allocating_branch` over the real table: root's
`setresuid(1000, 1000, 1000)` installs all three; -EAGAIN is admissible
there because the real uid moves and this is the user setter
(`set_user`, called at kernel/sys.c:753-759, Linux v6.18.46), and refused
on the group twin, which has no `set_user`; -ENOMEM (`prepare_creds`,
:749-751, and in `__sys_setresgid` :849-851) is admissible on both.
kernel: kernel/sys.c:__sys_setresuid,__sys_setresgid,set_user@v6.18.46 -/
theorem setresuid_reaches_its_allocating_branch_over_the_real_table :
    check_syscall (sys_ids_in 147 1000 1000 1000) (mkEffect 0 [] []) root_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []
    ∧ check_syscall (sys_ids_in 147 1000 1000 1000) (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckOk root_model []
    ∧ check_syscall (sys_ids_in 149 1000 1000 1000) (mkEffect (errno_ret EAGAIN) [] []) root_model
      = CheckReject
    ∧ check_syscall (sys_ids_in 149 1000 1000 1000) (mkEffect (errno_ret ENOMEM) [] []) root_model
      = CheckOk root_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `unprivileged_setresuid_may_rearrange_held_ids` over the real table:
`setresuid(-1, 1002, -1)` on six different ids names only ids the caller
holds, so it passes the permission test (kernel/sys.c:739-747, Linux
v6.18.46) and moves the effective uid alone; the real uid does not move,
so -ENOMEM is admissible and -EAGAIN is not; and naming one id the
caller does not hold (1003) is -EPERM, so a success is refused.  1002
sits in `a1`: an arm reading it as the real uid would install
(1002, 1001, 1002) instead.
kernel: kernel/sys.c:__sys_setresuid,set_user@v6.18.46 -/
theorem unprivileged_setresuid_may_rearrange_held_ids_over_the_real_table :
    check_syscall (sys_ids_in 147 4294967295 1002 4294967295) (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []
    ∧ check_syscall (sys_ids_in 147 4294967295 1002 4294967295)
        (mkEffect (errno_ret ENOMEM) [] []) split_ids_model = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 147 4294967295 1002 4294967295)
        (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject
    ∧ check_syscall (sys_ids_in 147 4294967295 1003 4294967295) (mkEffect 0 [] []) split_ids_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The six `setsid_checker_*` examples of `Checks/ProcessCreation.v`

`ksys_setsid` (kernel/sys.c:1268-1301, Linux v6.18.46) seeds `err =
-EPERM` (:1274) and returns the caller's own pid on success (:1292); the
model carries the pid as its tid slot and a success as its session bit. -/

/-- `setsid_checker_first_call_eperm` over the real table: -EPERM on a
first call is accepted and moves nothing (the process-group test at
:1284-1285 reads a table the model does not carry).
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_checker_first_call_eperm_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect (errno_ret EPERM) [] []) demo_model
      = CheckOk demo_model [] :=
  rfl

/-- `setsid_checker_first_call_session_id` over the real table: a session
id on a first call is recorded as the tid and sets the session bit.
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem setsid_checker_first_call_session_id_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect 1234 [] []) demo_model
      = CheckOk (with_setsid_succeeded (with_tid 1234 demo_model)) [] :=
  rfl

/-- `setsid_checker_rejects_zero` over the real table: no task has pid 0
(`alloc_pid` draws from `pid_min = 1`, kernel/pid.c:226, Linux v6.18.46).
kernel: kernel/sys.c:ksys_setsid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem setsid_checker_rejects_zero_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect 0 [] []) demo_model = CheckReject :=
  rfl

/-- `setsid_checker_after_success_rejects_success` over the real table:
after a success the caller is a session leader, and :1278-1279 refuses
it, so a second session id is a lie.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_checker_after_success_rejects_success_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect 1234 [] [])
      (with_setsid_succeeded (with_tid 1234 demo_model)) = CheckReject :=
  rfl

/-- `setsid_checker_after_success_eperm` over the real table: …and
-EPERM is what it answers, the model unmoved.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_checker_after_success_eperm_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect (errno_ret EPERM) [] [])
      (with_setsid_succeeded (with_tid 1234 demo_model))
      = CheckOk (with_setsid_succeeded (with_tid 1234 demo_model)) [] :=
  rfl

/-- `setsid_checker_bit_alone_rejects_success` over the real table: the
session bit alone refuses a success, with the tid slot still empty — the
refusal is the leader test's (:1278-1279), not the recorded pid's.
kernel: kernel/sys.c:ksys_setsid@v6.18.46 -/
theorem setsid_checker_bit_alone_rejects_success_over_the_real_table :
    check_syscall (sys_ids_in 157 0 0 0) (mkEffect 1234 [] []) (with_setsid_succeeded demo_model)
      = CheckReject :=
  rfl

/-! ### The pid readers through the table

Rocq states no `check_syscall` example at 172 or 178; these two pin that
each number reaches the set_tid_address checker, which a reader-shaped
arm would not: a first answer is recorded as the tid, and a later one
must repeat it. -/

/-- getpid (172): a first answer is recorded as the tid; an errno is
refused, since `SYSCALL_DEFINE0(getpid)` (kernel/sys.c:999-1002, Linux
v6.18.46) has no failing path.  The errno offered is -EINVAL, which
`alloc_pid` spells (kernel/pid.c:197-199) on a path a pid reader never
enters.
kernel: kernel/sys.c:getpid; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem getpid_records_the_first_draw_over_the_real_table :
    check_syscall (sys_ids_in 172 0 0 0) (mkEffect 1 [] []) demo_model
      = CheckOk (with_tid 1 demo_model) []
    ∧ check_syscall (sys_ids_in 172 0 0 0) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- gettid (178): the recorded tid is repeated, and another refused
(`task_pid_vnr`, include/linux/pid.h:244-247, Linux v6.18.46, reads the
pid the task holds).
kernel: kernel/sys.c:gettid; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem gettid_repeats_the_recorded_tid_over_the_real_table :
    check_syscall (sys_ids_in 178 0 0 0) (mkEffect 7 [] []) (with_tid 7 demo_model)
      = CheckOk (with_tid 7 demo_model) []
    ∧ check_syscall (sys_ids_in 178 0 0 0) (mkEffect 8 [] []) (with_tid 7 demo_model)
      = CheckReject :=
  ⟨rfl, rfl⟩

/-! ### The narrowing, through the table and without it -/

/-- setuid (146) at `0x1_FFFF_FFFF` and at a register of all ones: both
narrow to `(uid_t)-1`, which `__sys_setuid` refuses with -EINVAL before
it consults the credentials (kernel/sys.c:659-661, Linux v6.18.46), so
-EINVAL is accepted and -EPERM, the answer to an id the caller does not
hold, is refused.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:__sys_setuid,setuid@v6.18.46 -/
theorem setuid_narrows_its_argument_over_the_real_table :
    check_syscall (sys_ids_in 146 8589934591 0 0) (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (sys_ids_in 146 8589934591 0 0) (mkEffect (errno_ret EPERM) [] []) demo_model
      = CheckReject
    ∧ check_syscall (sys_ids_in 146 18446744073709551615 0 0) (mkEffect (errno_ret EINVAL) [] [])
        demo_model = CheckOk demo_model []
    ∧ check_syscall (sys_ids_in 146 18446744073709551615 0 0) (mkEffect (errno_ret EPERM) [] [])
        demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …while the checker itself, handed the whole word, reads `0x1_FFFF_FFFF`
as an id the unprivileged caller does not hold: -EPERM accepted, -EINVAL
refused.  The two statements together are what put the narrowing in the
arm.
kernel: kernel/sys.c:__sys_setuid@v6.18.46 -/
theorem setuid_checker_itself_reads_the_whole_word :
    check_setid cred_uids set_cred_uids true 8589934591 (mkEffect (errno_ret EPERM) [] [])
      demo_model = CheckOk demo_model []
    ∧ check_setid cred_uids set_cred_uids true 8589934591 (mkEffect (errno_ret EINVAL) [] [])
      demo_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- setgid (144) at `0x1_0000_07D0`: narrowed, the id is 2000, the real
gid of `split_ids_model`, so the unprivileged caller may install it as
its effective gid (kernel/sys.c:499-500, Linux v6.18.46): success
accepted with that model, -EPERM refused.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:__sys_setgid,setgid@v6.18.46 -/
theorem setgid_narrows_a_held_gid_over_the_real_table :
    check_syscall (sys_ids_in 144 4294969296 0 0) (mkEffect 0 [] []) split_ids_model
      = CheckOk (with_creds (Creds.mkCreds 1000 1001 1002 2000 2000 2002 demo_groups) demo_model) []
    ∧ check_syscall (sys_ids_in 144 4294969296 0 0) (mkEffect (errno_ret EPERM) [] [])
        split_ids_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- …while the checker itself, handed the whole word, holds no such gid:
-EPERM accepted, success refused.
kernel: kernel/sys.c:__sys_setgid@v6.18.46 -/
theorem setgid_checker_itself_reads_the_whole_word :
    check_setid cred_gids set_cred_gids false 4294969296 (mkEffect (errno_ret EPERM) [] [])
      split_ids_model = CheckOk split_ids_model []
    ∧ check_setid cred_gids set_cred_gids false 4294969296 (mkEffect 0 [] []) split_ids_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- setresuid (147) and setresgid (149) with `0x1_FFFF_FFFF` in all three
registers: each narrows to `(uid_t)-1`, "leave this id alone"
(kernel/sys.c:721-728 and :823-828, Linux v6.18.46), so the call asks
for nothing and is the no-op 0 (:732-737 and :832-837), and -EPERM is
refused.  One register left wide would name an id the unprivileged
caller does not hold, and flip both answers.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:__sys_setresuid,__sys_setresgid,setresuid,setresgid@v6.18.46 -/
theorem setresid_narrows_all_three_over_the_real_table :
    check_syscall (sys_ids_in 147 8589934591 8589934591 8589934591) (mkEffect 0 [] [])
      split_ids_model = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 147 8589934591 8589934591 8589934591)
        (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckReject
    ∧ check_syscall (sys_ids_in 149 8589934591 8589934591 8589934591) (mkEffect 0 [] [])
      split_ids_model = CheckOk split_ids_model []
    ∧ check_syscall (sys_ids_in 149 8589934591 8589934591 8589934591)
        (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …while the checker itself, handed the whole words, reads three ids
the caller does not hold: -EPERM accepted, 0 refused.
kernel: kernel/sys.c:__sys_setresuid@v6.18.46 -/
theorem setresuid_checker_itself_reads_the_whole_word :
    check_setresid cred_uids set_cred_uids true 8589934591 8589934591 8589934591
      (mkEffect (errno_ret EPERM) [] []) split_ids_model = CheckOk split_ids_model []
    ∧ check_setresid cred_uids set_cred_uids true 8589934591 8589934591 8589934591
      (mkEffect 0 [] []) split_ids_model = CheckReject :=
  ⟨rfl, rfl⟩

end V_Kernel_Sys_ids

section Uname

/-! ## uname (160): the copy, the record, the fault and the decline

`SYSCALL_DEFINE1(newuname)` (kernel/sys.c:1351-1366, Linux v6.18.46) is
one `copy_to_user` of the 390-byte `struct new_utsname`
(include/uapi/linux/utsname.h:25-32, Linux v6.18.46): -EFAULT when it
fails (:1358-1359), 0 otherwise (:1365).  The checker is asked here what
the spec pins in `Checks/Cases/Kernel/Sys.lean` answer, on the same
fixtures — `uts_in uts_out` is the call at 4096 over the writable 390-byte
zone, `demo_model` holds no record and `uts_pinned` holds `uts_demo` —
and every refusal beside an acceptance is one the kernel could not
produce.  A 390-byte literal in a statement — `uts_demo` and its
variants, `utsname_default`, `uts_demo.take 389` — is past the default
recursion depth, so every pin whose statement carries one sets
`maxRecDepth 8192`; the walk over `uts_out`, a function and not a
literal, needs none (`check_uname_refuses_another_errno`,
`check_uname_one_byte_short_declines`). -/

set_option maxRecDepth 8192 in
/-- THE FIRST COPY: 0 returned, `uts_demo` written at 4096, the name
recorded.  The bytes are the environment's — `init_uts_ns` is inherited,
not the syscall's to choose — and the checker accepts any member of the
envelope as the first answer, then records it.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_first_copy_records_the_name :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo)] []) demo_model
      = CheckOk (with_utsname uts_demo demo_model) [] := rfl

set_option maxRecDepth 8192 in
/-- …and the other admissible name is accepted first too, and pins
itself: which release the environment reports is not the source's to
say.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_first_copy_accepts_the_other_release :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo_b)] []) demo_model
      = CheckOk (with_utsname uts_demo_b demo_model) [] := rfl

set_option maxRecDepth 8192 in
/-- The envelope's pinned members are enforced on the first copy: a
`sysname` other than "Linux" (`init_uts_ns` writes it once,
init/version-timestamp.c:14, Linux v6.18.46), and a `machine` other than
"riscv64" (`override_architecture` rewrites it only for a PER_LINUX32
personality, kernel/sys.c:1310-1317, Linux v6.18.46 — that no process
here carries one is the launcher premise `Sys/Kernel/Sys.lean` states on
`uts_machine_chars`), are refused.
kernel: kernel/sys.c:newuname,override_architecture@v6.18.46 -/
theorem check_uname_first_copy_refuses_a_foreign_sysname_or_machine :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_bad_sysname)] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_bad_machine)] []) demo_model
      = CheckReject := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- Every free member must be NUL-terminated inside its 65 bytes: a
member of sixty-five 'A's, in each of the four free positions, is
refused.  `sethostname` and `setdomainname` bound their copies at
`__NEW_UTS_LEN` and write the terminator (kernel/sys.c:1436-1437 and
:1490-1491, Linux v6.18.46), and the release and version are the build's
`UTS_RELEASE`/`UTS_VERSION` literals, both shorter.
kernel: kernel/sys.c:newuname,sethostname,setdomainname@v6.18.46 -/
theorem check_uname_first_copy_refuses_an_unterminated_member :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_unterminated_release)] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_unterminated_nodename)] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_unterminated_version)] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_unterminated_domainname)] []) demo_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The envelope's two edges are inside it: every free member at its
full 64 characters with the terminator in byte 64, and a `nodename` with
bytes after an early NUL — the shape `sethostname` leaves when it copies
`len` bytes verbatim (kernel/sys.c:1436, Linux v6.18.46) — are both
accepted first.
kernel: kernel/sys.c:newuname,sethostname@v6.18.46 -/
theorem check_uname_first_copy_accepts_the_envelope_edges :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_full_free)] []) demo_model
      = CheckOk (with_utsname uts_full_free demo_model) []
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_embedded_nul)] []) demo_model
      = CheckOk (with_utsname uts_embedded_nul demo_model) [] := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- A LATER COPY repeats the record and moves nothing: the `uts_namespace`
the task reads (`utsname()`, kernel/sys.c:1356, Linux v6.18.46) is one
struct, and no syscall this model carries writes it.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_pinned_copy_repeats :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo)] []) uts_pinned
      = CheckOk uts_pinned [] := rfl

set_option maxRecDepth 8192 in
/-- …and a name that is admissible on its own but differs from the record
— `uts_demo_b`, another release — is refused on the pinned model: the
record IS the answer.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_pinned_copy_refuses_a_defector :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo_b)] []) uts_pinned
      = CheckReject := rfl

/-- A destination past `TASK_SIZE` fails `access_ok` — `__access_ok`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46), asked by
`_inline_copy_to_user` at include/linux/uaccess.h:195, Linux v6.18.46 —
so -EFAULT with nothing written is accepted on every model, the model
untouched.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_access_ok_fault (m : Model) :
    check_uname
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        9223372036854775808 (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m [] := rfl

set_option maxRecDepth 8192 in
/-- …and a copy delivered there is refused, as is a fault that carries a
write: `copy_to_user` moves nothing past a failed `access_ok`.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem check_uname_access_ok_fault_refuses_a_copy (m : Model) :
    check_uname
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        9223372036854775808 (mkEffect 0 [(9223372036854775808, uts_demo)] []) m
      = CheckReject
    ∧ check_uname
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        9223372036854775808 (mkEffect (errno_ret EFAULT) [(9223372036854775808, uts_demo)] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-- THE WIDTH `access_ok` IS ASKED WITH is the whole struct, 390 bytes: at
`TASK_SIZE` - 389 the destination fails `__access_ok`'s
`addr <= limit - size` (include/asm-generic/access_ok.h:40, Linux v6.18.46)
and -EFAULT with nothing written is accepted on every model; one byte
lower it passes, and the walk over a view holding nothing there is the
decline, for every effect.  A checker asking 389 bytes would decline at
both addresses; one asking 391 would accept the fault at both.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_access_ok_width (eff : SyscallEffect) (m : Model) :
    check_uname
        (SyscallInput.mkInput 160 [140737488354939, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        140737488354939 (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m []
    ∧ check_uname
        (SyscallInput.mkInput 160 [140737488354938, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        140737488354938 eff m
      = CheckUnmodeled := ⟨rfl, rfl⟩

/-- `uname(NULL)` is the same decline: `access_ok` admits `[0, 390)`, and
the copy's fault there is the model's to state only if it knew nothing is
mapped at 0, which it does not (`uname_null_is_unmodeled`,
`Checks/Cases/Kernel/Sys.lean`).  The kernel's -EFAULT is not accepted.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_null_declines (eff : SyscallEffect) (m : Model) :
    check_uname (SyscallInput.mkInput 160 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) 0 eff m
      = CheckUnmodeled
    ∧ check_uname (SyscallInput.mkInput 160 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) 0
        (mkEffect (errno_ret EFAULT) [] []) m
      = CheckUnmodeled := ⟨rfl, rfl⟩

/-- -EFAULT is the one errno: `SYSCALL_DEFINE1(newuname)` has no other
failing return (kernel/sys.c:1351-1366), so -EINVAL — written as the
register word 22 would occupy, since no function on the path spells it —
is refused at the fault address, and so is -EFAULT where `access_ok`
admits the destination and the zone is writable.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_refuses_another_errno (m : Model) :
    check_uname
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        9223372036854775808 (mkEffect (errno_ret 22) [] []) m
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect (errno_ret EFAULT) [] []) uts_pinned
      = CheckReject := ⟨rfl, rfl⟩

/-- A range `access_ok` admits but the writable view does not wholly back
is DECLINED, not faulted: `copy_to_user` would commit a prefix and then
fail, and the model cannot say how long the prefix is.  One byte short of
390, on every model.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem check_uname_one_byte_short_declines (eff : SyscallEffect) (m : Model) :
    check_uname (uts_in uts_out_short) 4096 eff m = CheckUnmodeled := rfl

/-- …and so is a destination backed by the readable view alone: the gate
is the WRITABLE view.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem check_uname_gates_on_the_writable_view (eff : SyscallEffect) (m : Model) :
    check_uname (SyscallInput.mkInput 160 [4096, 0, 0, 0, 0, 0] uts_out (fun _ => none)) 4096 eff m
      = CheckUnmodeled := rfl

/-- THE WRAPPING DESTINATION: the last four bytes of the address space,
with 386 more mapped at 0 so that the bare word walk would pass.
`__access_ok`'s `addr <= limit - size` refuses it
(include/asm-generic/access_ok.h:40, Linux v6.18.46) before the walk is
consulted, so -EFAULT with nothing written is accepted, on every model.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_wrapping_destination_faults (m : Model) :
    check_uname (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem)
        uts_wrap_name (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m [] := rfl

set_option maxRecDepth 8192 in
/-- …and the copy an unguarded checker would have accepted — 0 with the
390 bytes stored from 2^64 - 4 round onto 0 — is refused.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_wrapping_destination_refuses_the_copy (m : Model) :
    check_uname (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem)
        uts_wrap_name (mkEffect 0 [(uts_wrap_name, uts_demo)] []) m
      = CheckReject := rfl

set_option maxRecDepth 8192 in
/-- THE EFFECT'S SHAPE, refused member by member on the pinned model: a
return of 1; the write at 4097 rather than at the pointer; 389 bytes
rather than `sizeof(struct new_utsname)`; two writes; no write at all; a
zeroing; a copy-in ledger; an unmapping; a copy.  `SYSCALL_DEFINE1(newuname)` returns 0 or
-EFAULT and issues one `copy_to_user` of the whole struct at `name`
(kernel/sys.c:1358-1365, Linux v6.18.46), reading no user memory.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_refuses_a_misshapen_effect :
    check_uname (uts_in uts_out) 4096 (mkEffect 1 [(4096, uts_demo)] []) uts_pinned = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4097, uts_demo)] []) uts_pinned = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo.take 389)] []) uts_pinned
        = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo), (4486, [0])] []) uts_pinned
        = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [] []) uts_pinned = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo)] [(4486, 1)]) uts_pinned
        = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (with_copyins [(4096, 390)] (mkEffect 0 [(4096, uts_demo)] []))
        uts_pinned = CheckReject
    ∧ check_uname (uts_in uts_out) 4096
        (SyscallEffect.mkEffectU 0 [(4096, uts_demo)] [] [(4096, 4096)] [] []) uts_pinned = CheckReject
    ∧ check_uname (uts_in uts_out) 4096
        (SyscallEffect.mkEffectU 0 [(4096, uts_demo)] [] [] [MemCopy.mkCopy 0 4096 390] []) uts_pinned
      = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A FAULT IS NEVER A SUCCESS: at a destination `__access_ok`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46) refuses, a return
of 0 with nothing written is refused on every model — `newuname` returns
-EFAULT when the copy fails (kernel/sys.c:1358-1359, Linux v6.18.46), and
the `fault` probe case records no other answer.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_uname_fault_is_never_a_success (m : Model) :
    check_uname
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        9223372036854775808 (mkEffect 0 [] []) m
      = CheckReject := rfl

set_option maxRecDepth 8192 in
/-- THE WIDTH on the EMPTY model, where only `utsname_wf`'s length conjunct
stands and `listN_eqb` has no record to compare against: 389 bytes and 391
are refused on the first copy; 391 is refused on the record too.
`sizeof(struct new_utsname)` is 390 (include/uapi/linux/utsname.h:25-32,
Linux v6.18.46), and `copy_to_user` moves exactly that (kernel/sys.c:1358,
Linux v6.18.46).
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_first_copy_refuses_a_wrong_width :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo.take 389)] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo ++ [uts_nul])] []) demo_model
      = CheckReject
    ∧ check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, uts_demo ++ [uts_nul])] []) uts_pinned
      = CheckReject := ⟨rfl, rfl, rfl⟩

end Uname

section Prlimit64

/-! ## prlimit64 (261): the RLIMIT_CORE record, read and written

`SYSCALL_DEFINE4(prlimit64)` is kernel/sys.c:1729-1792 and `do_prlimit`
kernel/sys.c:1500-1561 at Linux v6.18.46.  The fixtures are the Prelude's
and `Checks/Cases/Kernel/Sys.lean`'s: `rlim_read_in` is
`prlimit64(0, RLIMIT_CORE, NULL, 4096)` over the writable landing zone,
`rlim_set_in mem` is `prlimit64(0, RLIMIT_CORE, 8192, NULL)` over a
readable source, `rlim_pinned` holds `{3, 7}` and `demo_model` holds no
pair. -/

/-- THE FIRST READ records the pair delivered: 0 returned, sixteen bytes
at 4096, the pair recorded.  `do_prlimit` copies the task's pair out
(kernel/sys.c:1533-1534) and `SYSCALL_DEFINE4(prlimit64)` delivers it
(:1784-1787); which pair the task inherited is the environment's.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_first_read_records_the_pair :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 3 7)] []) demo_model
      = CheckOk (with_rlimit_core (rlim_bytes 3 7) demo_model) [] := rfl

/-- …but not an inverted pair: no Linux holds soft > hard, because
`do_prlimit` refuses to store one (kernel/sys.c:1511-1512).
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem check_prlimit64_first_read_refuses_soft_over_hard :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 1 0)] []) demo_model
      = CheckReject := rfl

/-- THE FIRST READ is held to sixteen bytes too, where only `rlim64_wf`'s
length test stands, there being no recorded pair to compare against:
fifteen bytes, or seventeen, at 4096 are refused.  `SYSCALL_DEFINE4(prlimit64)`
copies `sizeof(old64)` (kernel/sys.c:1786-1787, Linux v6.18.46), the two
`__u64` of `struct rlimit64` (include/uapi/linux/resource.h:50-53, Linux
v6.18.46).
kernel: kernel/sys.c:prlimit64@v6.18.46 -/
theorem check_prlimit64_first_read_refuses_a_wrong_width :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, (rlim_bytes 3 7).take 15)] [])
        demo_model = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 3 7 ++ [0])] [])
        demo_model = CheckReject := ⟨rfl, rfl⟩

/-- A LATER READ repeats the record and moves nothing; a pair that is
well-formed on its own but differs from the record — soft 2 against the
recorded 3 — is refused: the task holds one pair.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_pinned_read_repeats_and_refuses_a_defector :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 2 7)] []) rlim_pinned
      = CheckReject := ⟨rfl, rfl⟩

/-- THE READ'S SHAPE, refused member by member: a return of 1; -EFAULT
beside the whole pair (a `copy_to_user` that landed all sixteen bytes
returned 0, so :1786-1787 leaves `ret` at 0; a fault lands at most a
prefix, which the one-byte-short pins decline); the
write at 4097; eight bytes or seventeen rather than `sizeof(old64)`
(:1786); a copy-in ledger on a call that reads no user memory; an
unmapping; a copy.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_read_refuses_a_misshapen_effect :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 1 [(4096, rlim_bytes 3 7)] []) rlim_pinned
      = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096
        (mkEffect (errno_ret EFAULT) [(4096, rlim_bytes 3 7)] []) rlim_pinned = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4097, rlim_bytes 3 7)] []) rlim_pinned
      = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, (rlim_bytes 3 7).take 8)] [])
        rlim_pinned = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 3 7 ++ [0])] [])
        rlim_pinned = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096
        (with_copyins [(4096, 16)] (mkEffect 0 [(4096, rlim_bytes 3 7)] [])) rlim_pinned
      = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096
        (SyscallEffect.mkEffectU 0 [(4096, rlim_bytes 3 7)] [] [(4096, 4096)] [] []) rlim_pinned
      = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096
        (SyscallEffect.mkEffectU 0 [(4096, rlim_bytes 3 7)] [] [] [MemCopy.mkCopy 0 4096 16] [])
        rlim_pinned = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A read whose destination is past `TASK_SIZE` is -EFAULT with nothing
written (`__access_ok`, include/asm-generic/access_ok.h:31-41, Linux
v6.18.46, asked by `_inline_copy_to_user` at include/linux/uaccess.h:195,
Linux v6.18.46, before the copy at kernel/sys.c:1786-1787), on the pinned
model as on the empty one, the model untouched; the pair delivered there
anyway is refused.
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_prlimit64_read_access_ok_fault :
    check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 9223372036854775808 (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 9223372036854775808 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 9223372036854775808 (mkEffect 0 [(9223372036854775808, rlim_bytes 3 7)] []) rlim_pinned
      = CheckReject := ⟨rfl, rfl, rfl⟩

/-- THE WIDTH `access_ok` IS ASKED WITH is `sizeof(struct rlimit64)`, 16
(include/uapi/linux/resource.h:50-53, Linux v6.18.46): a destination at
`TASK_SIZE` - 15 fails `__access_ok`'s `addr <= limit - size`
(include/asm-generic/access_ok.h:40, Linux v6.18.46) and -EFAULT with
nothing written is accepted, on any model; at `TASK_SIZE` - 16 it passes
and the walk over a view holding nothing there declines, for every
effect.  The set arm asks the same width of its source, the `access_ok`
`_inline_copy_from_user` asks before any load (include/linux/uaccess.h:168,
Linux v6.18.46), on the pinned record.
kernel: kernel/sys.c:prlimit64; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_prlimit64_access_ok_width (eff : SyscallEffect) (m : Model) :
    check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 140737488355313, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 140737488355313 (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m []
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 140737488355312, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 140737488355312 eff m
      = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 140737488355313, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 140737488355313 0 (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 140737488355312, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 140737488355312 0 eff rlim_pinned
      = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl⟩

/-- A landing zone `access_ok` admits and the writable view does not
wholly back — one byte short of sixteen — is declined, for every effect
and model.
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem check_prlimit64_read_one_byte_short_declines (eff : SyscallEffect) (m : Model) :
    check_prlimit64 (SyscallInput.mkInput 261 [0, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out_short)
        0 4 0 4096 eff m
      = CheckUnmodeled := rfl

/-- THE SET: `{0, 7}` over the record `{3, 7}`.  The sixteen bytes are
recorded as a copy-in (`_inline_copy_from_user`, include/linux/uaccess.h:159-185,
Linux v6.18.46, has loaded them at kernel/sys.c:1744-1745), the record moves
to what was set (:1535-1536), 0 is returned.
kernel: kernel/sys.c:prlimit64,do_prlimit; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem check_prlimit64_set_moves_the_record :
    check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) rlim_pinned
      = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [] := rfl

/-- A set that dropped its copy-in, or claimed a copy-in of another
width or address, or returned 1, or wrote user memory, is refused.
kernel: kernel/sys.c:prlimit64,do_prlimit; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem check_prlimit64_set_refuses_a_misshapen_effect :
    check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0 (mkEffect 0 [] []) rlim_pinned
      = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8192, 8)] (mkEffect 0 [] [])) rlim_pinned = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8200, 16)] (mkEffect 0 [] [])) rlim_pinned = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect 1 [] [])) rlim_pinned = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect 0 [(4096, [0])] [])) rlim_pinned = CheckReject
      := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A set that returned -EPERM is refused: `do_prlimit` consults
`capable(CAP_SYS_RESOURCE)` only when the hard limit RISES
(kernel/sys.c:1526-1528), and this one leaves it at 7.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_unchanged_hard_refuses_eperm :
    check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EPERM) [] [])) rlim_pinned
      = CheckReject := rfl

/-- A set whose source is past `TASK_SIZE` fails `access_ok` before
`copy_from_user` issues a load (include/linux/uaccess.h:168, Linux
v6.18.46): -EFAULT with NO copy-in is accepted and the record stands;
the same -EFAULT claiming the unreachable struct as read is refused.
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem check_prlimit64_set_access_ok_fault :
    check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 9223372036854775808 0 (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 9223372036854775808 0
        (with_copyins [(9223372036854775808, 16)] (mkEffect (errno_ret EFAULT) [] [])) rlim_pinned
      = CheckReject := ⟨rfl, rfl⟩

/-- A source `access_ok` admits and memory does not wholly back — one
byte short of sixteen — is declined on the pinned model, for every
effect: which bytes the kernel loaded is not the ledger's to state.
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem check_prlimit64_set_one_byte_short_declines (eff : SyscallEffect) :
    check_prlimit64 (rlim_set_in rlim_src_short) 0 4 8192 0 eff rlim_pinned = CheckUnmodeled := rfl

/-- `{9, 7}` is -EINVAL — `do_prlimit`'s first test on the new pair
(kernel/sys.c:1511-1512), before any capability question — WITH the
copy-in, since `SYSCALL_DEFINE4(prlimit64)` loaded the bytes first
(:1744-1745); the record does not move.  `{8, 7}` is the same one over.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_soft_over_hard_is_einval :
    check_prlimit64 (rlim_set_in (rlim_src_at 9 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 8 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned
      = CheckOk rlim_pinned [] := ⟨rfl, rfl⟩

/-- …and -EINVAL without the copy-in, or an acceptance of the inverted
pair, is refused; equal limits `{7, 7}` are legal, `rlim_cur > rlim_max`
being strict (:1511).
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_soft_over_hard_refusals_and_the_boundary :
    check_prlimit64 (rlim_set_in (rlim_src_at 9 7)) 0 4 8192 0
        (mkEffect (errno_ret EINVAL) [] []) rlim_pinned = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 9 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) rlim_pinned = CheckReject
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 7 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) rlim_pinned
      = CheckOk (with_rlimit_core (rlim_bytes 7 7) rlim_pinned) [] := ⟨rfl, rfl, rfl⟩

/-- -EINVAL is decided BEFORE the hard limit is compared: `{9, 5}`
against the recorded hard 7 is the first test failing (:1511-1512),
fifteen lines before the capability question a changed hard limit raises
(:1526-1528) — -EINVAL with the copy-in, not a decline.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_soft_over_hard_precedes_the_hard_change :
    check_prlimit64 (rlim_set_in (rlim_src_at 9 5)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned
      = CheckOk rlim_pinned [] := rfl

/-- A HARD LIMIT THAT MOVES is declined, for every effect, for two
reasons.  Up (`{0, 9}`): whether the caller holds `CAP_SYS_RESOURCE`
(kernel/sys.c:1526-1528) is not a fact of this model, so neither the 0
nor the -EPERM is provable.  Down (`{0, 5}`): `do_prlimit` asks
`capable` only when the hard limit RISES (:1526) and stores a lowered one
(:1535-1536), so Linux answers 0 — `security_task_setrlimit` (:1530) is
0 under the no-LSM position `prlimit64_spec` states — and the decline is
the spec's deliberate bound ("lowering it is a deliberate bound rather
than a necessity", `Sys/Kernel/Sys.lean`), admitted by no arm.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_moving_hard_declines (eff : SyscallEffect) :
    check_prlimit64 (rlim_set_in (rlim_src_at 0 9)) 0 4 8192 0 eff rlim_pinned = CheckUnmodeled
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 0 5)) 0 4 8192 0 eff rlim_pinned = CheckUnmodeled
      := ⟨rfl, rfl⟩

/-- A set on a model with NO recorded pair is declined, for every
effect: the hard-limit comparison has nothing to compare against.
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_on_an_empty_record_declines (eff : SyscallEffect) :
    check_prlimit64 (rlim_set_in (rlim_src_at 0 7)) 0 4 8192 0 eff demo_model = CheckUnmodeled := rfl

/-- THE FOUR GATES decline before any memory is read, for every effect
and model: a pid other than 0 (`find_task_by_vpid`, kernel/pid.c:438-441,
Linux v6.18.46, resolves it to another task at kernel/sys.c:1751, or to
-ESRCH at :1752-1755) — 1, and 2^32, which the `__SC_CAST` to `pid_t`
makes 0 for the kernel while the spec, handed the whole register by
`arm_prlimit64`, declines it (`prlimit64_nonzero_pid_is_unmodeled`,
`Checks/Cases/Kernel/Sys.lean`); a resource other than `RLIMIT_CORE` (4,
include/uapi/asm-generic/resource.h:20, Linux v6.18.46) — 5, `RLIMIT_RSS`,
and 2^32 + 4, read whole the same way; both pointers NULL; both pointers
set.
kernel: kernel/sys.c:prlimit64@v6.18.46 -/
theorem check_prlimit64_gates_decline (eff : SyscallEffect) (m : Model) :
    check_prlimit64 (SyscallInput.mkInput 261 [1, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        1 4 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [4294967296, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        4294967296 4 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64 (SyscallInput.mkInput 261 [0, 5, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        0 5 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4294967300, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        0 4294967300 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64 (SyscallInput.mkInput 261 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 0 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 8192, 4096, 0, 0] (rlim_src_at 3 7) rlim_out)
        0 4 8192 4096 eff m = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A FAULT IS NEVER A SUCCESS: at a destination `__access_ok` refuses, 0
with nothing written is refused on every model, and so is -EINVAL —
`do_prlimit`'s word for a resource at or past `RLIM_NLIMITS`
(kernel/sys.c:1506-1507, Linux v6.18.46) or a pair with soft above hard
(:1511-1512), neither of which a read of `RLIMIT_CORE` presents; the only
answer left is `copy_to_user`'s -EFAULT (:1786-1787).  The `read-fault`
probe case records both lies as rejects.
kernel: kernel/sys.c:prlimit64,do_prlimit; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem check_prlimit64_read_fault_is_never_a_success (m : Model) :
    check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 9223372036854775808 (mkEffect 0 [] []) m
      = CheckReject
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4 0 9223372036854775808 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-- THE EMPTY-RECORD DECLINE PRECEDES THE POINTER: a set before any read is
declined even from a source `__access_ok` refuses — where Linux is certain
to answer -EFAULT, the copy-in at kernel/sys.c:1744-1745 (Linux v6.18.46)
running before anything else — for that -EFAULT and for every other
effect, and even for a pair `do_prlimit` would refuse -EINVAL
(:1511-1512).  A checker that walked or asked `access_ok` before the record
gate would accept the -EFAULT here (the `fault-first` probe case).
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_set_on_an_empty_record_precedes_the_pointer (eff : SyscallEffect) :
    check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 9223372036854775808 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4 9223372036854775808 0 eff demo_model
      = CheckUnmodeled
    ∧ check_prlimit64 (rlim_set_in (rlim_src_at 9 7)) 0 4 8192 0
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl⟩

/-- THE PID AND RESOURCE GATES PRECEDE THE POINTER: 999, and 4095, are
declined even beside a pointer the kernel would fault on — the source at
kernel/sys.c:1744-1745 (Linux v6.18.46), the destination at :1786-1787 —
for every effect and model, in either pointer slot.
kernel: kernel/sys.c:prlimit64@v6.18.46 -/
theorem check_prlimit64_gates_precede_the_fault (eff : SyscallEffect) (m : Model) :
    check_prlimit64
        (SyscallInput.mkInput 261 [999, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        999 4 9223372036854775808 0 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4095, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        0 4095 9223372036854775808 0 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [999, 4, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        999 4 0 9223372036854775808 eff m = CheckUnmodeled
    ∧ check_prlimit64
        (SyscallInput.mkInput 261 [0, 4095, 0, 9223372036854775808, 0, 0] (fun _ => none) (fun _ => none))
        0 4095 0 9223372036854775808 eff m = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl⟩

/-- RESOURCES ON BOTH SIDES of `RLIMIT_CORE` (4) are declined, for every
effect and model: `RLIMIT_STACK` (3) below it — the conjunct a `≤ 4` gate
would fail — `RLIMIT_NOFILE` (7) on the read arm and on the set arm, and
`RLIM_NLIMITS` (16), which `do_prlimit` refuses -EINVAL
(kernel/sys.c:1506-1507, Linux v6.18.46).
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_other_resources_decline (eff : SyscallEffect) (m : Model) :
    check_prlimit64 (SyscallInput.mkInput 261 [0, 3, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        0 3 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64 (SyscallInput.mkInput 261 [0, 7, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        0 7 0 4096 eff m = CheckUnmodeled
    ∧ check_prlimit64 (SyscallInput.mkInput 261 [0, 7, 8192, 0, 0, 0] (rlim_src_at 0 7) (fun _ => none))
        0 7 8192 0 eff rlim_pinned = CheckUnmodeled
    ∧ check_prlimit64 (SyscallInput.mkInput 261 [0, 16, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        0 16 0 4096 eff m = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl⟩

/-- EIGHT BYTES on the EMPTY model, where only `rlim64_wf` stands: `{3, 7}`
cut to eight is refused — but its missing tail reads as hard 0, so the
soft > hard test would refuse it on its own; eight zero bytes (soft 0,
hard 0) are refused by the width alone, and that is the conjunct a
`rlim64_wf` admitting two widths would fail.  `SYSCALL_DEFINE4(prlimit64)`
copies `sizeof(old64)` (kernel/sys.c:1786-1787, Linux v6.18.46).
kernel: kernel/sys.c:prlimit64@v6.18.46 -/
theorem check_prlimit64_first_read_refuses_eight_bytes :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, (rlim_bytes 3 7).take 8)] [])
        demo_model = CheckReject
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, List.replicate 8 0)] [])
        demo_model = CheckReject := ⟨rfl, rfl⟩

/-- THE SIGN OF THE COMPARE, at `RLIM64_INFINITY` (`~0ULL`,
include/uapi/linux/resource.h:48, Linux v6.18.46): the boot default
`{0, RLIM_INFINITY}` (`INIT_RLIMITS`, include/asm-generic/resource.h:17,
Linux v6.18.46) is accepted on the first read and recorded; `{INFINITY, 7}`
is refused on the first read — soft above hard under `do_prlimit`'s
unsigned `rlim_cur > rlim_max` (kernel/sys.c:1511-1512, Linux v6.18.46) —
and set over `{3, 7}` is -EINVAL with the copy-in, its acceptance refused.
A signed compare in `rlim64_wf` or the set arm flips all four; no other
fixture in this file carries a byte above 7 in either member.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_infinity_is_unsigned :
    check_prlimit64 rlim_read_in 0 4 0 4096
        (mkEffect 0 [(4096, List.replicate 8 0 ++ List.replicate 8 255)] []) demo_model
      = CheckOk (with_rlimit_core (List.replicate 8 0 ++ List.replicate 8 255) demo_model) []
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096
        (mkEffect 0 [(4096, List.replicate 8 255 ++ [7, 0, 0, 0, 0, 0, 0, 0])] []) demo_model
      = CheckReject
    ∧ check_prlimit64 (rlim_set_in (bytes_at 8192 (List.replicate 8 255 ++ [7, 0, 0, 0, 0, 0, 0, 0])))
        0 4 8192 0 (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned
      = CheckOk rlim_pinned []
    ∧ check_prlimit64 (rlim_set_in (bytes_at 8192 (List.replicate 8 255 ++ [7, 0, 0, 0, 0, 0, 0, 0])))
        0 4 8192 0 (with_copyins [(8192, 16)] (mkEffect 0 [] [])) rlim_pinned
      = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- THE BOTH-NULL DECLINE is on the pointer VALUES, not on what backs them:
with sixteen bytes mapped at 0 on both views the call is still declined,
for every effect and model.  `check_prlimit64_gates_decline`'s both-NULL
conjunct backs nothing at 0, so a checker missing the gate would decline
there anyway (the walk at 0 fails, `access_okb 0 16` holds); this one is
where the gate is the only thing declining.  `SYSCALL_DEFINE4(prlimit64)`
copies in only under `if (new_rlim)` and out only under
`if (!ret && old_rlim)` (kernel/sys.c:1743-1748 and :1784-1787, Linux
v6.18.46).
kernel: kernel/sys.c:prlimit64@v6.18.46 -/
theorem check_prlimit64_both_null_declines_whatever_backs_page_zero (eff : SyscallEffect) (m : Model) :
    check_prlimit64 (SyscallInput.mkInput 261 [0, 4, 0, 0, 0, 0] rlim_page_zero rlim_page_zero)
        0 4 0 0 eff m = CheckUnmodeled := rfl

/-- A READ AFTER A SET reports the pair the set installed and refuses the
one there before it: the task holds one pair, and `do_prlimit`'s store
(kernel/sys.c:1535-1536, Linux v6.18.46) replaces it.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_read_after_set_reports_the_set_pair :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 0 7)] [])
        (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
      = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) []
    ∧ check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim_bytes 3 7)] [])
        (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
      = CheckReject := ⟨rfl, rfl⟩

end Prlimit64

section Prctl

/-! ## prctl (167): PR_CAPBSET_READ and nothing else

`SYSCALL_DEFINE5(prctl)` opens (kernel/sys.c:2518-2530, Linux v6.18.46) by
handing every option, at :2525-2527, to the LSM hook `security_task_prctl`
(security/security.c:3871-3887, Linux v6.18.46), and for
`PR_CAPBSET_READ` (23) `cap_task_prctl` (security/commoncap.c:1291-1431,
Linux v6.18.46) answers -EINVAL unless `cap_valid(arg2)` and
`!!cap_raised(old->cap_bset, arg2)` otherwise (:1298-1301).  The
checker reads no input and no memory, so every pin here is over a
symbolic model, and the ones over a symbolic effect say the gate is
read before the effect is. -/

variable (eff : SyscallEffect) (m : Model)

/-- `prctl(PR_CAPBSET_READ, 0)` answers 1 and moves nothing: `!!cap_raised`
under the unnarrowed bounding set the model assumes
(security/commoncap.c:1301).  The boundary is inclusive: 40 is
`CAP_LAST_CAP` (include/uapi/linux/capability.h:421-423, Linux v6.18.46)
and answers 1 too.
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_capbset_read_answers_one :
    check_prctl 23 0 (mkEffect 1 [] []) m = CheckOk m []
    ∧ check_prctl 23 40 (mkEffect 1 [] []) m = CheckOk m [] := ⟨rfl, rfl⟩

/-- 41 is not a capability: -EINVAL (security/commoncap.c:1299-1300),
nothing written, the model untouched; and `cap_valid` tests the FULL
`unsigned long` (include/uapi/linux/capability.h:425), so 2^32 and ~0 are
-EINVAL, not the answers for capabilities 0 and 63.
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_capbset_read_above_last_cap_is_einval :
    check_prctl 23 41 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_prctl 23 4294967296 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_prctl 23 (Z_to_bv 64 (-1)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
      := ⟨rfl, rfl, rfl⟩

/-- A narrowed bounding set — 0 for a valid capability — is outside this
model; `!!cap_raised` is never 2; no errno is admitted at or below
`CAP_LAST_CAP` — not -EINVAL at 0, and not, at the accepted edge 40, the
-EPERM that `cap_task_prctl` raises for other options only
(security/commoncap.c:1337, :1355, :1359, :1378, :1415).
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_capbset_read_refuses_wrong_answers :
    check_prctl 23 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_prctl 23 0 (mkEffect 2 [] []) m = CheckReject
    ∧ check_prctl 23 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_prctl 23 40 (mkEffect 0 [] []) m = CheckReject
    ∧ check_prctl 23 40 (mkEffect (errno_ret EPERM) [] []) m = CheckReject
      := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Above the boundary neither 1 nor 0 nor -EPERM is an answer: -EINVAL
is the only errno `cap_valid` raises, and `cap_task_prctl`'s -EPERM arms
belong to other options (security/commoncap.c:1337, :1355, :1359, :1378,
:1415).
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_capbset_read_above_last_cap_refusals :
    check_prctl 23 41 (mkEffect 1 [] []) m = CheckReject
    ∧ check_prctl 23 41 (mkEffect 0 [] []) m = CheckReject
    ∧ check_prctl 23 41 (mkEffect (errno_ret EPERM) [] []) m = CheckReject
    ∧ check_prctl 23 4294967296 (mkEffect 1 [] []) m = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- The answer touches nothing: a write, a zeroing, a copy-in, an
unmapping or a copy beside the 1 is refused, and the model handed back is the one given — on the
pinned rlimit fixture as on any other.
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_capbset_read_touches_nothing :
    check_prctl 23 0 (mkEffect 1 [(4096, [0])] []) m = CheckReject
    ∧ check_prctl 23 0 (mkEffect 1 [] [(4096, 1)]) m = CheckReject
    ∧ check_prctl 23 0 (with_copyins [(4096, 8)] (mkEffect 1 [] [])) m = CheckReject
    ∧ check_prctl 23 0 (SyscallEffect.mkEffectU 1 [] [] [(4096, 4096)] [] []) m = CheckReject
    ∧ check_prctl 23 0 (SyscallEffect.mkEffectU 1 [] [] [] [MemCopy.mkCopy 0 4096 8] []) m = CheckReject
    ∧ check_prctl 23 0 (mkEffect 1 [] []) rlim_pinned = CheckOk rlim_pinned []
      := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- EVERY OTHER OPTION IS DECLINED, before the effect is read: option 0;
`PR_GET_DUMPABLE` (3) and `PR_SET_DUMPABLE` (4), two options `prctl`'s own
`switch` answers itself once `cap_task_prctl`'s `default` has returned
-ENOSYS for them (kernel/sys.c:2551-2560); `PR_CAPBSET_DROP` (24,
include/uapi/linux/prctl.h:72, Linux v6.18.46), the neighbour of 23; and
`PR_SET_TAGGED_ADDR_CTRL` (55, include/uapi/linux/prctl.h:244, Linux
v6.18.46).
kernel: kernel/sys.c:prctl@v6.18.46 -/
theorem check_prctl_other_options_decline :
    check_prctl 0 0 eff m = CheckUnmodeled
    ∧ check_prctl 3 0 eff m = CheckUnmodeled
    ∧ check_prctl 4 1 eff m = CheckUnmodeled
    ∧ check_prctl 24 0 eff m = CheckUnmodeled
    ∧ check_prctl 55 0 eff m = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- …and the option gate precedes the capability bound: `PR_GET_DUMPABLE`
with 41, and `PR_SET_DUMPABLE` with 2^32, are declined, not -EINVAL —
neither option reaches `cap_valid` (include/uapi/linux/capability.h:425,
Linux v6.18.46): `prctl`'s own `switch` answers both (kernel/sys.c:2551-2560,
Linux v6.18.46).
kernel: kernel/sys.c:prctl; security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_option_gate_precedes_the_capability_bound :
    check_prctl 3 41 eff m = CheckUnmodeled
    ∧ check_prctl 4 4294967296 eff m = CheckUnmodeled := ⟨rfl, rfl⟩

/-- The checker reads the option it is GIVEN: 2^32 | 23 is not 23 here.
The `int32` the arm applies before the checker is the registration's
(`sysno_167_option_is_an_int` in `Checks/Cases/Kernel/Sys.lean`).
kernel: kernel/sys.c:prctl@v6.18.46 -/
theorem check_prctl_reads_the_option_it_is_given :
    check_prctl 4294967319 0 eff m = CheckUnmodeled := rfl

/-- THE REGISTER IS THE GATE: for every option outside
`prctl_modeled_options`, every `arg2`, effect and model, the checker
declines — the mirror of the spec's
`prctl_option_outside_the_register_is_unmodeled`.
kernel: kernel/sys.c:prctl@v6.18.46 -/
theorem check_prctl_option_outside_the_register_declines (option_ arg2 : word)
    (h : bv_unsigned option_ ∉ prctl_modeled_options) :
    check_prctl option_ arg2 eff m = CheckUnmodeled := by
  have hne : (bv_unsigned option_ == PR_CAPBSET_READ) = false := by
    simp only [prctl_modeled_options, List.mem_singleton] at h
    exact beq_eq_false_iff_ne.mpr h
  simp only [check_prctl, hne, Bool.not_false, ↓reduceIte]

/-- …and ON its option the checker never declines, for every `arg2`:
`cap_task_prctl`'s `PR_CAPBSET_READ` arm returns on every path
(security/commoncap.c:1298-1301).
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem check_prctl_never_declines_on_its_option (arg2 : word) :
    check_prctl 23 arg2 eff m ≠ CheckUnmodeled := by
  intro h
  have hg : (bv_unsigned (23 : word) == PR_CAPBSET_READ) = true := by decide
  unfold check_prctl at h
  rw [hg] at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · exact check_ret_only_no_unmodeled _ _ _ _ h
  · exact check_ret_only_no_unmodeled _ _ _ _ h

end Prctl

section WitnessSecondThird

/-! ## The witnesses of uname, prlimit64 and prctl

Each is one outcome its spec accepts at every model.  Where the spec
draws a fresh record the witness supplies a closed member of the
envelope, and the pins say which. -/

set_option maxRecDepth 8192 in
/-- The first uname's witness is `utsname_default` — "Linux", "riscv64"
and four empty members — written at 4096 and recorded; on the pinned
model the witness repeats the record.  `utsname_default` is 390 bytes,
as `struct new_utsname` is (include/uapi/linux/utsname.h:25-32, Linux
v6.18.46).
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_witness_draws_utsname_default :
    uname_witness 4096 (uts_in uts_out) demo_model
      = Ok (mkEffect 0 [(4096, utsname_default)] []) (with_utsname utsname_default demo_model) []
    ∧ uname_witness 4096 (uts_in uts_out) uts_pinned
      = Ok (mkEffect 0 [(4096, uts_demo)] []) uts_pinned []
    ∧ utsname_default.length = 390 := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- …and the checker accepts the witness's first answer: the two are the
same executable reading of the spec.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem check_uname_accepts_the_witness :
    check_uname (uts_in uts_out) 4096 (mkEffect 0 [(4096, utsname_default)] []) demo_model
      = CheckOk (with_utsname utsname_default demo_model) [] := rfl

/-- The uname witness faults past `TASK_SIZE` and declines one byte
short, as the spec does.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem uname_witness_faults_and_declines_with_the_spec (m : Model) :
    uname_witness 9223372036854775808
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ uname_witness 4096 (uts_in uts_out_short) m = Unmodeled := ⟨rfl, rfl⟩

/-- The first prlimit64 read's witness is `rlim64_zero`, the pair `{0, 0}`
— sixteen zero bytes, `rlim_bytes 0 0` — written at 4096 and recorded;
on the pinned model the witness repeats `{3, 7}`.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_witness_read_draws_rlim64_zero :
    prlimit64_witness 0 4 0 4096 rlim_read_in demo_model
      = Ok (mkEffect 0 [(4096, rlim64_zero)] []) (with_rlimit_core rlim64_zero demo_model) []
    ∧ rlim64_zero = rlim_bytes 0 0
    ∧ prlimit64_witness 0 4 0 4096 rlim_read_in rlim_pinned
      = Ok (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned [] := ⟨rfl, rfl, rfl⟩

/-- …and the checker accepts the witness's first read.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem check_prlimit64_accepts_the_witness_read :
    check_prlimit64 rlim_read_in 0 4 0 4096 (mkEffect 0 [(4096, rlim64_zero)] []) demo_model
      = CheckOk (with_rlimit_core rlim64_zero demo_model) [] := rfl

/-- The prlimit64 witness's set arm: `{0, 7}` moves the record with the
copy-in; `{9, 7}` is -EINVAL with the copy-in; a moving hard limit and a
set on the empty record decline; the both-NULL gate declines.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_witness_set_arms :
    prlimit64_witness 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) rlim_pinned
      = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] []))
           (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) []
    ∧ prlimit64_witness 0 4 8192 0 (rlim_set_in (rlim_src_at 9 7)) rlim_pinned
      = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) rlim_pinned []
    ∧ prlimit64_witness 0 4 8192 0 (rlim_set_in (rlim_src_at 0 9)) rlim_pinned = Unmodeled
    ∧ prlimit64_witness 0 4 8192 0 (rlim_set_in (rlim_src_at 0 7)) demo_model = Unmodeled
    ∧ prlimit64_witness 0 4 0 0
        (SyscallInput.mkInput 261 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) demo_model
      = Unmodeled := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The prctl witness is the spec's answer: 1 at and below `CAP_LAST_CAP`,
-EINVAL above it, a decline on another option.
kernel: security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem prctl_witness_answers (m : Model) :
    prctl_witness 23 0 m = Ok (mkEffect 1 [] []) m []
    ∧ prctl_witness 23 40 m = Ok (mkEffect 1 [] []) m []
    ∧ prctl_witness 23 41 m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ prctl_witness 3 0 m = Unmodeled := ⟨rfl, rfl, rfl, rfl⟩

end WitnessSecondThird

-- lean-port sentinel: ticket V-Kernel-Sys-uname-prlimit-prctl appends below this line

section V_Kernel_Sys_uname_prlimit_prctl

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Sys-uname-prlimit-prctl — uname, prlimit64 and prctl over the real table

WHAT IS TWINNED HERE.  The sections above address `check_uname`,
`check_prlimit64` and `check_prctl` directly, because `checked_table`
carried no row for 160, 167 or 261 when they were written.  This is the
registration.  Each of the ten uname and nine prlimit64 examples
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sys.v` states through
`check_syscall` is restated here through the Lean `check_syscall`, over
`checked_table` itself, at the Rocq input — `uts_in uts_out` and
`rlim_read_in` are Rocq's `mkInput 160 [4096; …] (fun _ => None) uts_out`
and `mkInput 261 [0; 4; 0; 4096; …] (fun _ => None) rlim_out` — under its
Rocq name with `_over_the_real_table` after it, K6b's convention for the
pins at which the real table first answers a call.  Rocq's `uts_model` and
`rlim_model` are both `demo_model`, and so is the model here.  Rocq states
no prctl example through `check_syscall`.

WHAT A PIN HERE ADDS to its checker-level twin above is the ROW's claim:
that the lookup finds the arm rather than the dispatcher's own decline,
and that the arm hands the checker the registers
`Checks/Arms/Kernel/Sys.lean`'s rows say, in the width they say.  The
twins fix the first; the section after them fixes the second, one pin
per register decision, each separating the row from the one a reader
would most plausibly write instead.

POLARITY is the sections' above: the evidence line is `kernel:` on every
pin about the kernel's answer, `CheckOk`, `CheckReject` and
`CheckUnmodeled` alike, and `model:` on a pin about the table's own
contents. -/

/-- The three lookups the dispatcher performs: each number finds its row.
model: `lookup_ca` over `checked_table` at closed numbers; the table's own
contents, not a kernel claim. -/
theorem lookup_uname_prctl_prlimit64 :
    lookup_ca checked_table 160 = some arm_uname
    ∧ lookup_ca checked_table 167 = some arm_prctl
    ∧ lookup_ca checked_table 261 = some arm_prlimit64 :=
  ⟨lookup_ca_checked_table_uname, lookup_ca_checked_table_prctl,
   lookup_ca_checked_table_prlimit64⟩

/-! ### The ten uname examples, through `check_syscall` -/

set_option maxRecDepth 8192 in
/-- `uname_first_copy_pins` over the real table: the first copy is where
the environment's kernel identity enters the model, and it becomes the
record.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_first_copy_pins_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_demo)] []) demo_model
      = CheckOk (with_utsname uts_demo demo_model) [] := rfl

set_option maxRecDepth 8192 in
/-- `uname_wrong_sysname_rejected` over the real table: `sysname` is
written once, by `init_uts_ns` (init/version-timestamp.c:14, Linux
v6.18.46), and no syscall touches it.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_wrong_sysname_rejected_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_bad_sysname)] []) demo_model
      = CheckReject := rfl

set_option maxRecDepth 8192 in
/-- `uname_unterminated_release_rejected` over the real table: the
release is the build's `UTS_RELEASE` literal, shorter than its 65 bytes,
so an unterminated one is refused.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_unterminated_release_rejected_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_unterminated_release)] []) demo_model
      = CheckReject := rfl

set_option maxRecDepth 8192 in
/-- `uname_pinned_copy_repeats` over the real table: a later copy repeats
the record and moves nothing.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_pinned_copy_repeats_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_demo)] []) uts_pinned
      = CheckOk uts_pinned [] := rfl

set_option maxRecDepth 8192 in
/-- `uname_pinned_copy_defector_rejected` over the real table: a
well-formed name that differs from the record is refused.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_pinned_copy_defector_rejected_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_demo_b)] []) uts_pinned
      = CheckReject := rfl

set_option maxRecDepth 8192 in
/-- `uname_defector_is_itself_admissible_first` over the real table: the
defector above is refused for disagreeing with the record and for no
other reason, since offered first it is accepted and pins itself.
kernel: kernel/sys.c:newuname@v6.18.46 -/
theorem uname_defector_is_itself_admissible_first_over_the_real_table :
    check_syscall (uts_in uts_out) (mkEffect 0 [(4096, uts_demo_b)] []) demo_model
      = CheckOk (with_utsname uts_demo_b demo_model) [] := rfl

/-- `uname_access_ok_fault` over the real table: a destination past
`TASK_SIZE` fails `__access_ok` (include/asm-generic/access_ok.h:31-41,
Linux v6.18.46), the gate `_inline_copy_to_user` asks
(include/linux/uaccess.h:195, Linux v6.18.46), so -EFAULT with nothing
written is exact.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem uname_access_ok_fault_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 160 [9223372036854775808, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := rfl

set_option maxRecDepth 8192 in
/-- `uname_one_byte_short_is_unmodeled` over the real table: a range
`access_ok` admits and the writable view does not wholly back is
declined, since `copy_to_user` would commit a prefix of a length the
model cannot state.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem uname_one_byte_short_is_unmodeled_over_the_real_table :
    check_syscall (uts_in uts_out_short) (mkEffect 0 [(4096, uts_demo)] []) demo_model
      = CheckUnmodeled := rfl

/-- `uname_wrapping_destination_faults` over the real table: the last four
bytes of the address space, 386 more mapped at 0; `__access_ok`'s
`addr <= limit - size` (include/asm-generic/access_ok.h:40, Linux
v6.18.46) refuses the range before a byte moves.
kernel: kernel/sys.c:newuname; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem uname_wrapping_destination_faults_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem)
        (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := rfl

set_option maxRecDepth 8192 in
/-- `uname_wrapping_destination_rejects_the_copy` over the real table: the
copy an unguarded arm would accept, 390 bytes stored from 2^64 - 4 round
onto 0, is one Linux cannot produce.
kernel: kernel/sys.c:newuname; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem uname_wrapping_destination_rejects_the_copy_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 160 [uts_wrap_name, 0, 0, 0, 0, 0] (fun _ => none) uts_wrap_mem)
        (mkEffect 0 [(uts_wrap_name, uts_demo)] []) demo_model
      = CheckReject := rfl

/-! ### The nine prlimit64 examples, through `check_syscall` -/

/-- `prlimit64_first_read_pins` over the real table: `do_prlimit` copies
the task's pair out and the syscall delivers it; which pair the task
inherited is the environment's, and it becomes the record.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_first_read_pins_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 3 7)] []) demo_model
      = CheckOk (with_rlimit_core (rlim_bytes 3 7) demo_model) [] := rfl

/-- `prlimit64_read_soft_over_hard_rejected` over the real table: no
Linux holds soft > hard, because `do_prlimit` refuses to store one
(kernel/sys.c:1511-1512, Linux v6.18.46).
kernel: kernel/sys.c:do_prlimit@v6.18.46 -/
theorem prlimit64_read_soft_over_hard_rejected_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 1 0)] []) demo_model
      = CheckReject := rfl

/-- `prlimit64_pinned_read_repeats` over the real table.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_pinned_read_repeats_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned
      = CheckOk rlim_pinned [] := rfl

/-- `prlimit64_pinned_read_defector_rejected` over the real table: a
well-formed pair that differs from the record is refused.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_pinned_read_defector_rejected_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 2 7)] []) rlim_pinned
      = CheckReject := rfl

/-- `prlimit64_set_new_soft_replaces_the_record` over the real table:
dropbear's call — zero the soft limit, the hard limit written back
unchanged — records the sixteen bytes as a copy-in and moves the record
to what was set.
kernel: kernel/sys.c:prlimit64,do_prlimit; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem prlimit64_set_new_soft_replaces_the_record_over_the_real_table :
    check_syscall (rlim_set_in (rlim_src_at 0 7)) (with_copyins [(8192, 16)] (mkEffect 0 [] []))
        rlim_pinned
      = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [] := rfl

/-- `prlimit64_set_access_ok_fault_has_no_copyins` over the real table: a
source past `TASK_SIZE` fails `access_ok` before `copy_from_user` issues a
load (include/linux/uaccess.h:168, Linux v6.18.46).
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem prlimit64_set_access_ok_fault_has_no_copyins_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
      = CheckOk rlim_pinned [] := rfl

/-- `prlimit64_set_access_ok_fault_rejects_copyins` over the real table:
the same -EFAULT claiming the unreachable struct as read is refused.
kernel: kernel/sys.c:prlimit64; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem prlimit64_set_access_ok_fault_rejects_copyins_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 261 [0, 4, 9223372036854775808, 0, 0, 0] (fun _ => none) (fun _ => none))
        (with_copyins [(9223372036854775808, 16)] (mkEffect (errno_ret EFAULT) [] [])) rlim_pinned
      = CheckReject := rfl

/-- `prlimit64_read_after_set_reports_the_set_pair` over the real table.
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_read_after_set_reports_the_set_pair_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 0 7)] [])
        (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
      = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [] := rfl

/-- `prlimit64_read_after_set_rejects_the_old_pair` over the real table:
with the example above, the whole content of "a set replaces the record".
kernel: kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem prlimit64_read_after_set_rejects_the_old_pair_over_the_real_table :
    check_syscall rlim_read_in (mkEffect 0 [(4096, rlim_bytes 3 7)] [])
        (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
      = CheckReject := rfl

/-! ### Which register, in which width

Each pin below is a call on which the row `Checks/Arms/Kernel/Sys.lean`
registers and the row a reader would most plausibly write instead give
different answers; the row's docstring carries the kernel argument. -/

set_option maxRecDepth 8192 in
/-- `uname(NULL)` with the landing zone's address in `a1`: the row reads
`a0`, the destination is NULL and the call declines
(`check_uname_null_declines`, above); a row reading `a1` would accept the
copy at 4096.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/sys.c:newuname@v6.18.46 -/
theorem uname_reads_a0_over_the_real_table :
    check_syscall (SyscallInput.mkInput 160 [0, 4096, 0, 0, 0, 0] (fun _ => none) uts_out)
        (mkEffect 0 [(4096, uts_demo)] []) demo_model
      = CheckUnmodeled := rfl

/-- `prctl(2^32 | 23, 40)`: the option is an `int`, so the low half is
`PR_CAPBSET_READ` and capability 40 is answered 1, on any model — the
probe's `hiopt` mode, recorded against the pinned kernel.  A row handing
the checker the whole register would decline it.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:prctl; security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem prctl_option_is_the_low_half_of_a0_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 167 [4294967319, 40, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) m
      = CheckOk m [] := rfl

/-- `prctl(23, 2^32)`: `arg2` is an `unsigned long`, read whole, and
`cap_valid` refuses 2^32 (`cap_task_prctl`, security/commoncap.c:1298-1301,
Linux v6.18.46), so -EINVAL is accepted and 1 refused; a row narrowing
`a1` too would see capability 0 and answer 1.
kernel: kernel/sys.c:prctl; security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem prctl_arg2_is_a1_read_whole_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 167 [23, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (SyscallInput.mkInput 167 [23, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-- `prctl(0, 23)`: option 0 is no option this model answers, so the call
declines; a row reading the option off `a1` would see `PR_CAPBSET_READ`
and accept 1.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/sys.c:prctl@v6.18.46 -/
theorem prctl_option_is_not_a1_over_the_real_table (m : Model) :
    check_syscall (SyscallInput.mkInput 167 [0, 23, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) m
      = CheckUnmodeled := rfl

/-- `prlimit64(2^32, RLIMIT_CORE, NULL, 4096)`: Linux's `pid_t` cast
makes the pid 0 and answers the read, but the row hands the checker the
whole register and the spec's first gate declines it — the probe's
`pid-high` mode, a `fail-closed` case.  A row narrowing `a0` would accept
the pair.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:prlimit64@v6.18.46 -/
theorem prlimit64_pid_is_read_whole_over_the_real_table :
    check_syscall (SyscallInput.mkInput 261 [4294967296, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        (mkEffect 0 [(4096, rlim_bytes 3 7)] []) demo_model
      = CheckUnmodeled := rfl

/-- `prlimit64(0, 2^32 | RLIMIT_CORE, NULL, 4096)`: the `unsigned int`
cast makes the resource `RLIMIT_CORE`, and the row declines it whole —
the probe's `res-high` mode, a `fail-closed` case.  A row narrowing `a1`
would accept the pair.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:prlimit64@v6.18.46 -/
theorem prlimit64_resource_is_read_whole_over_the_real_table :
    check_syscall (SyscallInput.mkInput 261 [0, 4294967300, 0, 4096, 0, 0] (fun _ => none) rlim_out)
        (mkEffect 0 [(4096, rlim_bytes 3 7)] []) demo_model
      = CheckUnmodeled := rfl

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so each row's
`ca_witness` is what it answers there; these fix that the row hands the
witness the reading it hands the checker. -/

/-- The narrowed option reaches the witness too: `prctl(2^32 | 23, 40)`
is exhibited as 1, the model untouched.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:prctl; security/commoncap.c:cap_task_prctl@v6.18.46 -/
theorem prctl_hiopt_witnesses_one_over_the_real_table (m : Model) :
    syscall_spec_witness
        (SyscallInput.mkInput 167 [4294967319, 40, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      = Ok (mkEffect 1 [] []) m [] := rfl

/-- …and the whole pid reaches the witness: `prlimit64(2^32, …)` is
exhibited as the decline.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/sys.c:prlimit64@v6.18.46 -/
theorem prlimit64_pid_high_witnesses_unmodeled_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 261 [4294967296, 4, 0, 4096, 0, 0] (fun _ => none) rlim_out) demo_model
      = Unmodeled := rfl

end V_Kernel_Sys_uname_prlimit_prctl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Sys
