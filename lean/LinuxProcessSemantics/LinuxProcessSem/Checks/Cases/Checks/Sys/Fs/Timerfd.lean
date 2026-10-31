import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Timerfd
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Timerfd
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Timerfd — what the timerfd_create checker accepts and refuses, read off against Linux

Pins over `Checks.Sys.Fs.Timerfd.check_timerfd_create`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Timerfd.v`, and over
`timerfd_create_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Fs/Timerfd.v`.  Not part of the
trusted specification: this file is QA on the checker, written to be READ,
and a claim in it is a claim about what the kernel does, with the
citation beside it, unless its evidence line is `model:` and says
otherwise.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

WHAT THIS TWINS.  Rocq keeps the checker's worked examples for this syscall
in `Checks/Cases/Fs/Timerfd.v`, beside the spec's, as three `Example`s over
`check_syscall` on inputs built by `tfd_in`: the flag bits outside the
mask, the admitted clocks' decline, and the narrowing of both arguments.
The Lean tree keeps spec pins and checker pins apart —
`Checks/Cases/Fs/Timerfd.lean` pins the spec, this file the checker — and
the first two are restated in the sections below on `check_timerfd_create`,
handed the two words directly, `Z_to_bv 64` of the uapi value already
narrowed.  Those sections were written while `checked_table` carried no
arm for 85, and the section at the end of this file, added with the arm's
registration (`Checks/Arms/Fs/Timerfd.lean`), restates all three through
`Checks/ExecutableSpecs.lean`'s `check_syscall` over the real table.  The
third example is the table's work — that the clock id is a0, the flag
word a1, and both narrow to 32 bits — which the checker cannot see; the
spec twin's register maps it, and the other two, to that file's pins of
the same facts on the relation, so the spec twin owes no theorem stated on
the checker.

WHY THIS FILE IS NOT `Checks/Cases/Fs/Timerfd.lean`.  That file is the
spec's mutation twin: `tools/lean_mutate.py` compiles each mutant of
`Sys/Fs/Timerfd.lean` against it and counts a mutant killed only when THAT
file fails to build.  Were the checker in its import closure, the checker
module would be compiled first, and the four lemmas of
`Checks/Sys/Fs/Timerfd.lean` relate the checker to the spec, so every
behaviour-changing spec mutant would fail there — filed as STILLBORN,
which the gate never counts — before a spec pin was read.  Measured with
the checker imported there (2026-09-19): STILLBORN 11, SURVIVED 10 of 21,
no spec pin exercised, gate green.  This file imports the spec twin and
nothing imports this file, so the spec twin's closure, and the committed
`tools/lean_mutation/scores/Fs.Timerfd.json` keyed on it, stay what they
were.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file tie
`check_timerfd_create` to `timerfd_create_spec` in both directions, and a
checker that declined every input, or accepted every one, would still meet
them if the spec were changed to match.  What the lemmas cannot see is a
lie told from OUTSIDE: an errno the kernel would not return, a descriptor
for a word it refuses, a ledger beside the bare return it does give, or a
return that agrees only in its low half, offered to the checker and
required to be refused.  That is what most pins below do, beside the answer
the kernel does give required to be `CheckOk` with the model unchanged and
no event; the others pin that every input Linux lets past the gate is
declined whatever effect is offered, which is what fail-closed means at the
checker.

WHAT MEASURES THESE PINS.  `tools/lean_mutate.py` builds a spec mutant
against `Checks/Cases/Fs/Timerfd.lean` alone, so no mutant of the checker
is compiled against this file.  The one measurement is the hand-run sweep
in the deep-review record of the PR that landed this file (2026-09-19):
sixty checker and witness mutants, the five relation lemmas stubbed out in
scratch so that the pins alone were judged.  Every mutant that changes a
checker answer died under the pins below.  The survivors were the ten
clock-id permutations the spec's allowlist already records as equivalent,
two that differ only on words at or above 2^32, which the table never
hands the checker, and the witness mutants, which only
`timerfd_create_witness_ok` reached in that sweep — it reaches them all,
since each half of the spec admits exactly one outcome, and the two value
pins at the end state the answer it fixes without re-running the lemma.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted and what is refused. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Timerfd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Timerfd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Timerfd

/-! ## The Rocq examples, one layer down

Every concrete check here is closed by `rfl`, bar
`einval_accept_returns_the_same_model`, which computes the accepted result
by `rfl` and reads it with `injection`: each statement is quantified over
`m`, which is what keeps `decide` out, and the checker is a closed
computation on both words once `m` is fixed — which it is by the
quantifier, since the checker reads no field of it.  The Rocq
`timerfd_model` fixture is what the quantifier replaces.

WHAT `CheckReject` PINS that the spec twin's relation pins cannot: those
say a descriptor is not admitted; these say the CHECKER refuses it, which
is the half a `--mutate` lie in
`testing/syscall-check/tests/timerfd_create.c` exercises against Rocq and
the half no conformance run reaches on its own, since no probe can make
Linux hand out a descriptor for a word the gate refuses.  The four lemmas
of `Checks/Sys/Fs/Timerfd.lean` relate the checker to the spec and never
either to Linux; an errno offered here and refused, or accepted, is what
ties the checker's answer to the kernel's. -/

/-- Bits 22, 15 and 20 outside `TFD_CLOEXEC|TFD_NONBLOCK`, with
`CLOCK_MONOTONIC`: the checker accepts the -EINVAL over the SAME model with
no event, and refuses a descriptor for each — the second conjunct of each
pair is what stops the first being vacuous.  Bit 31 is the probe's
(`dropped` pair); the all-ones word its `einval` case.  The return the six
conjuncts pin is `timerfd_create`'s at fs/timerfd.c:410 (Linux v6.18.46),
reached through the mask test at fs/timerfd.c:404.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem timerfd_create_dropped_flag_bits_are_einval (m : Model) :
    check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect 3 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 15))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 15))
        (mkEffect 3 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 20))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 20))
        (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The five admitted ids decline a descriptor rather than answer; the
alarm ids decline the -EPERM an unprivileged caller really gets
(`timerfd_create`, fs/timerfd.c:412-415, Linux v6.18.46) and the -EINVAL a
shortened whitelist would give; and `CLOCK_PROCESS_CPUTIME_ID` (2), in the
admitted set's own gap, takes the -EINVAL — the conjunct that makes the set
a SET and not the interval `0..CLOCK_BOOTTIME_ALARM`.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem timerfd_create_admitted_clocks_decline (m : Model) :
    check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME) (Z_to_bv 64 0) (mkEffect 3 [] []) m
      = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 0) (mkEffect 3 [] []) m
      = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_BOOTTIME) (Z_to_bv 64 0) (mkEffect 3 [] []) m
      = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0)
        (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_BOOTTIME_ALARM) (Z_to_bv 64 0)
        (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0)
        (mkEffect (errno_ret EPERM) [] []) m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_BOOTTIME_ALARM) (Z_to_bv 64 0)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 0)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Lies the checker must refuse, beyond descriptor 3

The `--mutate` lies of `testing/syscall-check/tests/timerfd_create.c`
(`prec`, `tai`, `abstime`, `dropped`), and the effect-shape lies that
probe does not stage, offered to the checker.  The harness can stage them
— `testing/syscall-check/main.ml`'s `smuggle-write`, `smuggle-zeros`,
`smuggle-unmap`, `smuggle-copy` and `smuggle-copyin` append a ledger entry
beside the kernel's return, and `clock_gettime_spec.c` uses four of them —
but `timerfd_create.c` presents return-value lies only, so until it grows
the matching `reject` cases these pins are what refuses a ledger beside the
-EINVAL.

Every `CheckReject` below is an answer a real KERNEL never gives — a real
kernel, not every supported implementation: QEMU v11.1.1's
`TARGET_NR_timerfd_create` (linux-user/syscall.c) runs the flag word
through `target_to_host_bitmask(arg2, fcntl_flags_tbl)`, which keeps the
bits the table names and drops every other, so for bits 31, 22 and 20 —
and 15, on a host whose `O_LARGEFILE` is 0 — the host `timerfd_create` sees
a clean word and hands out a descriptor.  The tree reads that as the
emulator's translation defect, a deviation from the kernel it emulates,
and not as a behavior of a supported implementation: the stance
`Checks/Cases/Fs/Pipe.lean` takes for `pipe2` and
`bugs/epoll-answers-are-linux-order-not-qemu-user.md` costs for
`epoll_create1`.  Nothing here adds to it.  Every `CheckUnmodeled` is the
fail-closed answer on an input Linux accepts, whatever effect was observed.

The Lean Uapi has no `TFD_CLOEXEC`/`TFD_NONBLOCK`/`TFD_TIMER_ABSTIME`/
`CLOCK_TAI` names, so they are spelled as `O_CLOEXEC`, `O_NONBLOCK`, `1`
and `11`: `TFD_TIMER_ABSTIME` is include/uapi/linux/timerfd.h:30 and
`CLOCK_TAI` is include/uapi/linux/time.h:64 (Linux v6.18.46). -/

/-- The probe's `prec` lie at the checker: the flag word is judged in the
first `if` of `timerfd_create` (fs/timerfd.c:404-410, Linux v6.18.46) and
the capability in the second (fs/timerfd.c:412-415), so for
`(CLOCK_REALTIME_ALARM, TFD_CLOEXEC|TFD_TIMER_ABSTIME)` the -EPERM a
capability-first model would answer is refused and the -EINVAL accepted.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem alarm_with_bad_flag_at_the_checker (m : Model) :
    check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 (O_CLOEXEC + 1))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 (O_CLOEXEC + 1))
        (mkEffect (errno_ret EPERM) [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `tai`, `abstime` and `dropped` lies at the checker: a
descriptor for clock 11 (`CLOCK_TAI`), a zero return or a descriptor for
`TFD_TIMER_ABSTIME` (bit 0) with `CLOCK_MONOTONIC`, and a descriptor for
bit 31 alone are refused; the -EINVAL is accepted for each word
(`timerfd_create`, fs/timerfd.c:404-410, Linux v6.18.46).
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem probe_reject_twins_at_the_checker (m : Model) :
    check_timerfd_create (Z_to_bv 64 11) (Z_to_bv 64 0) (mkEffect 3 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 11) (Z_to_bv 64 0) (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) (mkEffect 0 [] []) m
        = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) (mkEffect 3 [] []) m
        = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 31))
        (mkEffect 3 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 31))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The -EINVAL half admits ONE effect.  The wrong errno, a zero return,
and every ledger of `SyscallEffect` offered alone beside the right errno —
a write, a zero-fill, an unmap, a pre-effect copy and a copy-in — are each
refused for the same word: `timerfd_create` returns at fs/timerfd.c:410
(Linux v6.18.46) having touched nothing and read no user memory.  A
checker comparing the return and the stores alone passes the first three
conjuncts and fails the last three, which is why all five ledgers are
offered, as `Checks/Cases/Checks/Sys/Kernel/Groups.lean` offers them.  (A
changed model or an event cannot be OFFERED to the checker — they are its
output — and the `CheckOk m []` equations above already fix both.)
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem einval_half_admits_one_effect (m : Model) :
    check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect (errno_ret EPERM) [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect 0 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect (errno_ret EINVAL) [((0 : word), [(0 : byte)])] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect (errno_ret EINVAL) [] [((0 : word), (4096 : word))]) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [((0 : word), (4096 : word))] [] []) m
      = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 0 0 8] []) m
      = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [((0 : word), (8 : Nat))]) m
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What an accepted -EINVAL hands back, stated over TWO models so the claim
is not "`rfl` happened to see `m`": the post-model is the pre-model and the
events are none (`timerfd_create`, fs/timerfd.c:410, Linux v6.18.46,
returns before the `kzalloc` at fs/timerfd.c:417).  `rfl` cannot close a
statement over two models; the accepted result is computed once and
`injection` reads it.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem einval_accept_returns_the_same_model (m m' : Model) (evs : List event)
    (h : check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  have hm : check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl
  rw [hm] at h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- Past the gate the checker declines WHATEVER it is offered: an in-mask
flag word (`TFD_CLOEXEC|TFD_NONBLOCK`, and each alone) and each admitted
id.  `CheckUnmodeled` for every `eff`, never `CheckReject` — a privileged
runner's descriptor and an unprivileged one's -EPERM (`timerfd_create`,
fs/timerfd.c:412-415, Linux v6.18.46) grade the same, which is what
fail-closed means here.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem admitted_inputs_decline_every_effect (m : Model) (eff : SyscallEffect) :
    check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 TFD_CREATE_FLAGS) eff m
        = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 O_CLOEXEC) eff m
        = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 O_NONBLOCK) eff m
        = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME) (Z_to_bv 64 0) eff m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_BOOTTIME) (Z_to_bv 64 0) eff m = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0) eff m
        = CheckUnmodeled
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_BOOTTIME_ALARM) (Z_to_bv 64 0) eff m
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The extremes of both words, at the checker, spelled as the table hands
them on: `flag32` and `clockid32` keep the low 32 bits of the register
zero-extended, so `flags = -1` — an `int` after `__SC_CAST`
(`SYSCALL_DEFINE2(timerfd_create, int, clockid, int, flags)`,
fs/timerfd.c:394; include/linux/syscalls.h:132; Linux v6.18.46), whose 32
low bits the kernel reads as `-1` and the model as their unsigned value —
arrives as `2^32 - 1`, and the clock ids `-1` and `-6` — the latter the
`make_process_cpuclock(0, CPUCLOCK_SCHED)` encoding the spec twin pins —
as `2^32 - 1` and `2^32 - 6`.  The flag word carries bits outside the mask:
-EINVAL and no descriptor.  Both clock words are off the whitelist: -EINVAL
and no descriptor.  And `CLOCK_PROCESS_CPUTIME_ID` (2), in the admitted
set's gap, refuses a descriptor as it accepts the -EINVAL above
(fs/timerfd.c:404-410, Linux v6.18.46).  The checker itself compares the
whole 64-bit word, so to IT a word off the five, or with a bit outside the
mask, is -EINVAL whatever its high half; that Linux narrows first — so
`2^32` aliases onto a clean word and is accepted — is the spec twin's pin
on the table, not this one's.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem extreme_words_at_the_checker (m : Model) :
    check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 32 - 1))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 32 - 1))
        (mkEffect 3 [] []) m = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 0)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 0) (mkEffect 3 [] []) m
        = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 (2 ^ 32 - 6)) (Z_to_bv 64 0)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 (2 ^ 32 - 6)) (Z_to_bv 64 0) (mkEffect 3 [] []) m
        = CheckReject
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 0)
        (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The witness: which outcome it names

`timerfd_create_witness_ok` says the witness is admitted at every input,
which is the receptiveness field of the arm the registration builds.  Here
that lemma fixes the value completely — `err_ret EINVAL` is `pure` and the
other half is `Unmodeled`, so each half of `timerfd_create_spec` admits
exactly one outcome — but a reader has to re-derive that to know WHICH
outcome, so the two pins below name it. -/

/-- Off the whitelist the witness is the -EINVAL over the same model with no
event — clock 11 (`CLOCK_TAI`), and a flag bit outside the mask beside
`CLOCK_MONOTONIC` — the one outcome `timerfd_create_spec` admits there
(`timerfd_create`, fs/timerfd.c:404-410, Linux v6.18.46), so
`timerfd_create_witness_ok` has exactly this to exhibit.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem witness_off_the_whitelist_is_einval (m : Model) :
    timerfd_create_witness (Z_to_bv 64 11) (Z_to_bv 64 0) m
        = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ timerfd_create_witness (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22)) m
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] :=
  ⟨rfl, rfl⟩

/-- Past the gate the witness declines, as the checker does: `Unmodeled` is
itself an admitted outcome, so the descriptor the model cannot hold
(`timerfd_create` allocates it from fs/timerfd.c:417 on) is never
invented.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem witness_declines_where_the_checker_declines (m : Model) :
    timerfd_create_witness (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 0) m = Unmodeled
    ∧ timerfd_create_witness (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 TFD_CREATE_FLAGS) m
        = Unmodeled :=
  ⟨rfl, rfl⟩

-- lean-port sentinel: ticket V-Fs-Timerfd appends below this line

section V_Fs_Timerfd

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Timerfd — `timerfd_create` over the real table

WHAT IS TWINNED HERE.  The sections above state the first two Rocq
examples on the checker itself, because `checked_table` carried no row for
85 when they were written, and left the restatement through `check_syscall`
to the registration.  This is the registration.  Each of the three examples
`theories/LinuxProcessSem/Checks/Cases/Fs/Timerfd.v` states — every one
through `check_syscall` — is restated here through the Lean
`check_syscall`, over `checked_table` itself, at the Rocq input
`tfd_in clkid flags` (the clock id in `a0`, the flag word in `a1`), under
its Rocq name with `_over_the_real_table` after it, K6b's convention for
the pins at which the real table first answers a call.  Rocq fixes
`timerfd_model`; these hold at every model, as the sections above do, since
neither the lookup nor the arm reads one.

WHAT A PIN HERE ADDS to its checker-level twin above, where it has one,
is the ARM's claim:
that the lookup at 85 finds `arm_timerfd_create` rather than the
dispatcher's own decline, and that the arm hands the checker
`clockid32 (in_arg i 0)` and `flag32 (in_arg i 1)` — the clock id from
argument zero and the flag word from argument one, each narrowed to its
low 32 bits.  `timerfd_create_narrows_both_arguments_over_the_real_table`
carries the narrowing: bit 32 beside a clean word in either register is
declined, where the checker itself, handed the whole word, answers
-EINVAL (`the_checker_itself_reads_whole_words`, below), so an arm handing
it the whole register fails that theorem.  The swapped pins below carry
the order, one in each direction.

POLARITY: the evidence line is `kernel:` on every pin about the kernel's
answer, `CheckOk`, `CheckReject` and `CheckUnmodeled` alike, and `model:`
on a pin about the table's own contents or about the checker's contract
with the arm's reading, which the pin's own statement says. -/

/-- The lookup the dispatcher performs on a `tfd_in`, computed once:
`in_sysno` is `85` whatever the two words hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_tfd_in (clkid flags : Int) :
    lookup_ca checked_table (bv_unsigned (tfd_in clkid flags).in_sysno)
      = some arm_timerfd_create :=
  lookup_ca_checked_table_timerfd_create

/-! ### The three Rocq examples, through `check_syscall` -/

/-- `timerfd_create_dropped_flag_bits_are_einval` over the real table: one
bit outside `TFD_CLOEXEC|TFD_NONBLOCK` at each of bits 22, 15 and 20,
beside `CLOCK_MONOTONIC`, is refused with the -EINVAL of the mask test at
fs/timerfd.c:404-410 (Linux v6.18.46), the model untouched and no event,
and a descriptor for any of them is a lie, since that return comes before
`timerfd_create` reserves one at fs/timerfd.c:435.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem timerfd_create_dropped_flag_bits_are_einval_over_the_real_table (m : Model) :
    check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20)) (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `timerfd_create_admitted_clocks_decline` over the real table: the five
admitted ids with a zero flag word pass the gate at fs/timerfd.c:404-410
(Linux v6.18.46) and the kernel goes on: the two alarm ids meet the
`capable(CAP_WAKE_ALARM)` test at fs/timerfd.c:412-415, which gives an
unprivileged caller -EPERM, and every id that passes it then allocates
(fs/timerfd.c:417) and reserves a descriptor (fs/timerfd.c:435), any step
of which can fail for a reason the model does not read.  So a descriptor
and -EPERM are declined, as is the -EINVAL a shortened whitelist would
give; and `CLOCK_PROCESS_CPUTIME_ID` (2), in the admitted
set's gap, takes the -EINVAL.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem timerfd_create_admitted_clocks_decline_over_the_real_table (m : Model) :
    check_syscall (tfd_in CLOCK_REALTIME 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_BOOTTIME 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0) (mkEffect (errno_ret EPERM) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_PROCESS_CPUTIME_ID 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `timerfd_create_narrows_both_arguments` over the real table: both
parameters are `int` (`SYSCALL_DEFINE2(timerfd_create, int, clockid, int,
flags)`, fs/timerfd.c:394, Linux v6.18.46), and riscv64's
`__SYSCALL_DEFINEx` hands each to `__do_sys_timerfd_create` through
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88), so bit 32 of either register
is not a bit of the argument.  `2^32 + CLOCK_MONOTONIC` in `a0` is
`CLOCK_MONOTONIC`, and `2^32` in `a1` is the flag word 0: both are clean
calls, declined for a descriptor and for an -EINVAL alike.  `2^32 + 11`
narrows to 11, off the whitelist, and its -EINVAL is accepted.
kernel: include/linux/syscalls.h:__SC_CAST; fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem timerfd_create_narrows_both_arguments_over_the_real_table (m : Model) :
    check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32)) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (tfd_in (2 ^ 32 + 11) 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The checker's side of the narrowing: handed the two whole words the
theorem above hands the table, it answers -EINVAL for each, because it
compares the whole 64-bit word it is given, as Rocq's does.  Together with
the declines above this fixes where the narrowing lives: in the arm's
`clockid32`/`flag32` reading, not in the checker.  It is not the kernel's
answer at those registers — Linux narrows before it tests (`__SC_CAST`,
include/linux/syscalls.h:132, Linux v6.18.46), and both calls are clean —
which is why the evidence line is `model:`.  It would become a false claim
about Linux the day a `checked_table` row handed this checker the register
in place of the narrowed word; what refuses that row is
`timerfd_create_narrows_both_arguments_over_the_real_table`.
model: the checker's contract with the arm's reading; Linux narrows first (__SC_CAST, cited above) and does not answer -EINVAL at these register words -/
theorem the_checker_itself_reads_whole_words (m : Model) :
    check_timerfd_create (Z_to_bv 64 (2 ^ 32 + CLOCK_MONOTONIC))
        (Z_to_bv 64 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_timerfd_create (Z_to_bv 64 CLOCK_MONOTONIC)
        (Z_to_bv 64 (2 ^ 32)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- Bit 31 above `CLOCK_MONOTONIC` in `a0` is a bit OF the `int clockid`
(fs/timerfd.c:394, Linux v6.18.46): `__SC_CAST` keeps the low 32 bits,
which read as a negative id, off the whitelist at fs/timerfd.c:404-410, so
the -EINVAL is accepted and a descriptor refused.  An arm narrowing to 31
bits, which clears bit 31, would see `CLOCK_MONOTONIC` and decline both.
One reading the `int`'s magnitude would not, since `2^31 + CLOCK_MONOTONIC`
read as an `int` has magnitude `2^31 - 1`, off the whitelist too; the pin
below is the one that refuses it.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem bit_31_clock_is_einval_over_the_real_table (m : Model) :
    check_syscall (tfd_in (2 ^ 31 + CLOCK_MONOTONIC) 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in (2 ^ 31 + CLOCK_MONOTONIC) 0) (mkEffect 3 [] []) m
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- Clock id `-1` in `a0`, sign-extended as the C caller passes an `int`:
`__SC_CAST` keeps the low 32 bits, the `int` -1 (fs/timerfd.c:394, Linux
v6.18.46), off the whitelist at fs/timerfd.c:404-410, so the -EINVAL is
accepted and a descriptor refused.  An arm reading the `int`'s magnitude
would see `CLOCK_MONOTONIC` and decline both.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem negative_clock_is_einval_over_the_real_table (m : Model) :
    check_syscall (tfd_in (-1) 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (tfd_in (-1) 0) (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-! ### The probe's lies, through `check_syscall`

The `reject` cases of `testing/syscall-check/tests/timerfd_create.c` are
the answers the recorded corpus replays at the arm; `prec`, `tai`,
`abstime` and `dropped` are stated on the checker above
(`alarm_with_bad_flag_at_the_checker`, `probe_reject_twins_at_the_checker`)
and here through the table, which is where the replay meets them.  These pins
spell `TFD_CLOEXEC` as `O_CLOEXEC`, `TFD_TIMER_ABSTIME` as `1` and
`CLOCK_TAI` as `11`, because the Lean Uapi has none of those names, as the
section above says. -/

/-- `prec`: `(CLOCK_REALTIME_ALARM, TFD_CLOEXEC|TFD_TIMER_ABSTIME)` is
refused by the flag test at fs/timerfd.c:404-410 (Linux v6.18.46) before
the capability test at fs/timerfd.c:412-415 is reached, so the -EINVAL is
accepted and the -EPERM a capability-first model would answer is refused.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem prec_over_the_real_table (m : Model) :
    check_syscall (tfd_in CLOCK_REALTIME_ALARM (O_CLOEXEC + 1))
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM (O_CLOEXEC + 1))
        (mkEffect (errno_ret EPERM) [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-- `tai`, `abstime` and `dropped`: a descriptor for clock 11, a zero
return or a descriptor for `TFD_TIMER_ABSTIME` (bit 0) beside
`CLOCK_MONOTONIC`, and a descriptor for bit 31 are each refused, and the
-EINVAL of fs/timerfd.c:404-410 (Linux v6.18.46) is accepted for each.
The flag word `-1`, sign-extended into `a1` as the C caller passes it,
narrows to 32 set bits, also outside the mask.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem probe_reject_twins_over_the_real_table (m : Model) :
    check_syscall (tfd_in 11 0) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in 11 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC 1) (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC 1) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC 1) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 31)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (-1)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (tfd_in CLOCK_MONOTONIC (-1)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The swapped registers, stated once through the table

`O_CLOEXEC` is inside `TFD_CREATE_FLAGS` and off the clock whitelist, and
`CLOCK_MONOTONIC` (1) is on the whitelist and outside the mask, so the pair
separates an arm that reads the two registers the wrong way round, in both
directions. -/

/-- `timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC)` passes the gate at
fs/timerfd.c:404-410 (Linux v6.18.46), where the arm declines every
answer, -EINVAL included; an arm reading `a0` as the flag word and `a1` as
the clock id would see bit 0 and clock `O_CLOEXEC` and accept it.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem monotonic_cloexec_einval_declined_over_the_real_table (m : Model) :
    check_syscall (tfd_in CLOCK_MONOTONIC O_CLOEXEC) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := rfl

/-- The same two words the other way round: clock `O_CLOEXEC` is off the
whitelist and bit 0 is outside the mask, so the -EINVAL is accepted and a
descriptor refused; the swapped arm would see a legal call and decline.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem cloexec_monotonic_einval_accepted_over_the_real_table (m : Model) :
    check_syscall (tfd_in O_CLOEXEC CLOCK_MONOTONIC) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (tfd_in O_CLOEXEC CLOCK_MONOTONIC) (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl⟩

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 85; the witness pins above fix
`timerfd_create_witness` at bare words, these fix that the arm hands it the
same reading the checker gets. -/

/-- Clock 11 in `a0`: the witness exhibits the kernel's -EINVAL, the model
untouched, no event.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_11_witnesses_einval_over_the_real_table (m : Model) :
    syscall_spec_witness (tfd_in 11 0) m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- `CLOCK_MONOTONIC` with no flags: the witness exhibits the decline.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem monotonic_witnesses_unmodeled_over_the_real_table (m : Model) :
    syscall_spec_witness (tfd_in CLOCK_MONOTONIC 0) m = Unmodeled := rfl

/-- Bit 32 above `CLOCK_MONOTONIC` in `a0`: narrowed away, the clock id is
`CLOCK_MONOTONIC`, and the witness exhibits the decline — not the -EINVAL
it would exhibit for that whole word.
kernel: include/linux/syscalls.h:__SC_CAST; fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem bit_32_clock_witnesses_unmodeled_over_the_real_table (m : Model) :
    syscall_spec_witness (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0) m = Unmodeled := rfl

end V_Fs_Timerfd

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Timerfd
