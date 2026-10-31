import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Pipe — what the pipe2 CHECKER answers

Pins over `Checks.Sys.Fs.Pipe.check_pipe2`, the checker-level half of
`theories/LinuxProcessSem/Checks/Cases/Fs/Pipe.v`'s pipe2 examples.  Not
part of the trusted specification: this file is QA on the checker, written
to be READ.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f), read in
a checkout at that commit.

TWO LEAN FILES COVER ONE ROCQ FILE, and the split is by what is being
tested.  Rocq states its pipe2 examples through `check_syscall`, so each
one fixes two things at once: what the SPEC admits, and that the CHECKER's
verdict on a concrete effect is `CheckOk`, `CheckReject` or
`CheckUnmodeled`.  `Checks/Cases/Fs/Pipe.lean` carries the first half, as
`iff`s over every outcome of `pipe2_spec`, and was written while the tree
had no checker to state the second half on.  This file carries the second
half: the same calls, the same effects, and the checker's verdict on each,
so a checker that accepted everything, rejected everything or declined
everything fails here by name.  The KERNEL argument for every answer is
beside the spec-level pin of the same claim in that file and in the Rocq
example the mapping at the end of this header names; each docstring here
keeps only the reading its own verdict rests on.

HOW THESE ARE STATED.  The sections below were written while
`checked_table` carried no arm for 59, so each checker verdict they pin
but two applies the checker the way the dispatcher does:
`check_pipe2_row` below is the argument narrowing of Rocq's `arm_pipe2`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and of the row for 59
in `Sys/SyscallTable.lean`, spelled once, and each of those verdicts is
stated at a `pipe2_in` input, whose number is 59.  The two are
`the_checker_itself_reads_the_whole_word` and
`a_narrowed_fildes_would_accept_the_pair_at_4096`, which apply the
checker bare and through a row that narrows `fildes`, to state what a
checker or a row that narrowed differently would accept;
`the_row_is_the_arm` pins no verdict, taking the row's `CheckOk` at any
input as its hypothesis.  The arm is
registered now (`Checks/Arms/Fs/Pipe.lean`), and the section at the end
of this file, added with it, pins that the lookup at 59 finds that arm
and that its checker IS `check_pipe2_row` — so every `check_pipe2_row`
verdict above is the table's, and the table refuses what the two accept —
and restates the four Rocq pipe2 (59) `check_syscall` examples through
`check_syscall` itself.
The inputs are the fixtures of `Checks/Cases/Fs/Pipe.lean`, imported
rather than copied, so the two files cannot drift apart on an address or
a byte.  Every verdict on a closed input is closed by `rfl`, one per
conjunct where a pin states several: `Model` has no `DecidableEq`, so
`decide` cannot compare two verdicts, and the checker on a closed input
reduces to a constructor by evaluation alone.  Each `≠` pin on a closed
input rewrites with the `=` pin's verdict for the same call and then
tells the two constructors, or the two models, apart.  The section
"The scan wall" states its pins over any model their hypotheses
describe, and proves them, and the helper lemmas before them, by tactic
scripts.

WHAT IS NOT HERE.  No pin before the section at the end carries a
`probe:` line, although `testing/syscall-check/tests/pipe2_spec.c` runs
most of these shapes against the kernel; the evidence lines in those
sections are `kernel:` and `model:` readings.  A `= CheckReject` or
`= CheckUnmodeled` pin cannot cite the `reject --mutate` or `fail-closed`
case that matches it: `tools/check_lean_pin_evidence.py`'s polarity
reading, which classes a statement by `¬`, `≠`, `False` and the word
`Unmodeled`, reads such a verdict as positive, so the case would be
refused as the wrong polarity.  The `= CheckOk` pins meet no such
refusal: the section at the end cites a `conform` leg on the table twins
of four of them.  That section cites a `conform` leg on the pins whose
shape one runs and whose statement is an accepted answer, `model:` on the
three that state the registration itself, and `kernel:` on the rest,
`the_table_narrows_flags_to_int` and `the_table_passes_fildes_whole`
among them, whose statements carry a refusal beside the accepted answer.
The checker's four theorems
(`check_pipe2_sound_ok` and its three companions, in the checker's own
file) already say that `check_pipe2` and `pipe2_spec` agree on EVERY
input; what a pin adds is a concrete answer from outside, so that a change
made to both at once — the fault `Checks/ExecutableSpecs.lean`'s
biconditionals cannot see — still goes red here.

Two arms of the checker have no closed pin: the `fd_lookup … = some`
guards on the pair, which answer `CheckReject` when the descriptor
`alloc_fd` computed is not free.  `alloc_fd_aux` examines every candidate
it returns save the last — its 4096 steps hand back 4096 unexamined only
once every number in 0..4095 was held — so the read end's guard fires
only over a table holding all of 0..4096, and the write end's only over
one holding all of 0..4095 but at most one, whose hole the read end
fills: no table with fewer than 4096 live descriptors reaches the second
guard, none with fewer than 4097 the first.  A table at that wall is
`bugs/fd-allocation-ignores-rlimit-nofile.md`'s subject and `rfl` cannot
walk it, so the section "The scan wall" states both guards symbolically,
over any model that holds the numbers.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  This file mirrors no Rocq
file, so `tools/check_lean_cases_parity.py` would refuse a coverage
register here as a claim nothing could be held to.  The register for
`Checks/Cases/Fs/Pipe.v` belongs at the top of `Checks/Cases/Fs/Pipe.lean`,
which carries none yet — it is one of that checker's unclaimed twins, and
the block is the spec ticket's to add, since a checker ticket's files do
not include it.  The mapping is therefore prose, read by no guard, kept so
a reader can find the Rocq `Example` a verdict pin restates.  All seven
pipe2 examples of `Checks/Cases/Fs/Pipe.v` carry `rocq-twin:` lines in
`Checks/Cases/Fs/Pipe.lean`: the three that are facts about the model
with no `check_syscall` in them (`pipe2_wrap_would_pass_the_bare_walk`,
`pipe2_wrap_fildes_is_not_access_ok`, `pipe2_flat_fildes_is_access_ok`)
end there, and the four stated through `check_syscall` are restated below
as the checker's verdict.  The pins that restate a spec-level `iff` or
refusal of `Checks/Cases/Fs/Pipe.lean` as the verdict it implies have no
Rocq conjunct of their own; nor do the groups that are this file's own —
the checker's shape, the row's narrowing, `access_ok`'s edge, the lies
about the pair, the tables that do not begin at 3, the scan wall and the
witness.  It stops being complete the day a theorem restating a Rocq
conjunct is added without a line.

- `pipe2_wrapping_fildes_rejects_the_pair`: `wrapping_fildes_pair_is_rejected`,
  `pipe2_wrapping_fildes_rejects_the_pair_over_the_real_table`
- `pipe2_wrapping_fildes_is_efault`: `wrapping_fildes_is_efault`,
  `pipe2_wrapping_fildes_is_efault_over_the_real_table`
- `pipe2_unwrapped_fildes_still_installs_the_pair`: `fresh_pair_is_accepted`,
  `pipe2_unwrapped_fildes_still_installs_the_pair_over_the_real_table`
- `pipe2_unwrapped_fildes_rejects_efault`: `fresh_efault_is_rejected`,
  `pipe2_unwrapped_fildes_rejects_efault_over_the_real_table` -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Pipe

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (demo_model fixture_of)
-- Selective, because the spec-level file declares its own `pipe2_fdr`,
-- `pipe2_fds1`, `pipe2_fdw` and `pipe2_model` beside the checker's: a
-- wholesale `open` of both would make each of them ambiguous here.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe
  (pipe2_in pipe2_wrap_fildes pipe2_wrap_mem pipe2_flat_fildes pipe2_flat_mem
   pipe2_half_mem pipe2_seven_mem pipe2_dead_mem pipe2_high_fildes pipe2_high_mem
   pipe2_straddle_fildes pipe2_straddle_mem
   one_pipe_model two_pipe_model reused_id_model holes_model holes_after_model
   holes_probe_model holes_probe_after_model aliased_id_model)

/-! ## The dispatcher's application of the checker -/

/-- `check_pipe2` as the dispatcher applies it: `fildes` whole in a0,
`flags` narrowed to `int` by `pipe_flags32` from a1 — Rocq's `arm_pipe2`
and the row for 59 in `Sys/SyscallTable.lean`.  The registered arm's
checker is this application (`the_registration_checks_as_the_row`, in the
V-Fs-Pipe section at the end). -/
def check_pipe2_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m

/-- The two builders agree: the checker computes its post-state with its
own `pipe2_model`, the spec-level file reads the pins' literals through a
copy of the same definition, and the literals below are stated against the
checker's verdict.  Pinned so the copy cannot drift.
model: two definitions of the same builder, compared by unfolding. -/
theorem pipe2_model_agrees (m : Model) (id : word) :
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe.pipe2_model m id
      = pipe2_model m id := rfl

/-- The row IS the registry arm's application.  `check_pipe2_sound_ok`
lands in `pipe2_arm`'s `sa_spec` only if the row narrows each argument as
`Sys/Registry/Fs/Pipe.lean` does — a0 whole, a1 through `pipe_flags32` —
so a row that narrowed a0 too, took its flags from a0, or handed a1 over
whole fails here at `h` with a type mismatch.  This holds
`check_pipe2_row` to the registry's row for 59;
`the_registration_checks_as_the_row`, at the end, holds it to the checked
arm.  The narrowing is the kernel's own:
`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` (fs/pipe.c:1054,
Linux v6.18.46) takes the pointer whole and the flags as an `int`, so a1
reaches `do_pipe2` through `__SC_CAST` low-32 and a0 as it arrived.
kernel: fs/pipe.c:pipe2@v6.18.46 -/
theorem the_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_pipe2_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.Pipe.pipe2_arm).sa_spec i m (Ok eff m' evs) :=
  check_pipe2_sound_ok _ _ _ _ _ _ _ h

/-! ## The checker's own shape: the flag word first, then the destination,
then the effect -/

/-- An effect that zero-fills a range is one `pipe2_spec` never describes —
the call writes its two `int`s and nothing else — so the checker's wildcard
arm rejects it although the return value, the range and the bytes are the
kernel's: each empty ledger in the accepting arm is load-bearing.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_with_a_zero_fill_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [(0, 0)] [] [] [])
      demo_model
      = CheckReject := by
  rfl

/-- …and the same odd-shaped effect against a declined flag word is
`CheckUnmodeled`, not `CheckReject`: the outcome is computed before the
effect is looked at, as `__do_pipe_flags` reads `flags` before anything else.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem a_declined_call_is_declined_whatever_the_effect_shape :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 2048 pipe2_flat_mem)
      (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [(0, 0)] [] [] [])
      demo_model
      = CheckUnmodeled := by
  rfl

/-- An unmap in the effect is rejected on the accepting path too, beside the
kernel's return and the kernel's write: `do_pipe2` unmaps nothing.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_with_an_unmap_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []
        [(pipe2_flat_fildes, 1)] [] [])
      demo_model
      = CheckReject := by
  rfl

/-- A symbolic copy is rejected the same way: `do_pipe2` moves nothing
within user memory.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_with_a_copy_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [] []
        [MemCopy.mkCopy pipe2_flat_fildes pipe2_flat_fildes 8] [])
      demo_model
      = CheckReject := by
  rfl

/-- …and so is a copy-in ledger: `do_pipe2` has no `copy_from_user`, so a
range claimed as read from user memory is one the call never read.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_with_a_copyin_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [] [] []
        [(pipe2_flat_fildes, 8)])
      demo_model
      = CheckReject := by
  rfl

/-! ## `__do_pipe_flags`, first test: the mask

fs/pipe.c:987-988 at Linux v6.18.46:
`if (flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE))
return -EINVAL;` — the first statement of `__do_pipe_flags`, ahead of
`create_pipe_files` (:990), ahead of both `get_unused_fd_flags` (:994,
:999), and ahead of the only access through `fildes`, `do_pipe2`'s `copy_to_user`
(:1040) — and ahead of that copy's `access_ok`, so the flag word wins over
a refused range as over a dead one. -/

/-- Bit 30 is outside the mask: -EINVAL, model unchanged, accepted.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_einval_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- A kernel that dropped the bit and handed out the pair is refused; the
destination is writable, so it is the flag test alone that refuses it.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_pair_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- A decline for a flag word `__do_pipe_flags` answers at its first line is
refused: -EINVAL is the kernel's exact answer, not a coverage gap.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      ≠ CheckUnmodeled := by
  rw [unaccepted_bit_einval_is_accepted]; exact fun h => nomatch h

/-- Bit 0 (`O_WRONLY`) is outside the mask too: the residue is tested as a
whole, not bit 31 alone.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem bit_zero_einval_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- Bit 31 alone, the `int`'s sign bit: `flags & ~mask` is nonzero, so
-EINVAL — a model testing the word as a signed comparison would differ.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem sign_bit_einval_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 2147483648 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- The mask test runs before the destination is read: an unaccepted bit
over a destination with nothing writable is still -EINVAL, on the unchanged
model.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_beats_an_unwritable_destination :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and -EFAULT ahead of the mask test is the order Linux never takes:
rejected.  `do_pipe2` reaches `copy_to_user` (:1040) only after
`__do_pipe_flags` has returned 0.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags@v6.18.46 -/
theorem efault_ahead_of_the_mask_test_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-- The mask test runs before `access_ok` too: an unaccepted bit over the
WRAPPING destination — the range `__access_ok` refuses — is still -EINVAL
on the unchanged model.  The dead destination above passes `access_ok`
and fails only at the copy, so it cannot tell a checker that tested the
range first from one that tested the flag word first; this one can.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem unaccepted_bit_beats_a_refused_range :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 1073741824 pipe2_wrap_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and the -EFAULT a range-first checker would answer there is rejected:
`__do_pipe_flags` returns at :988 before `do_pipe2` reaches :1040.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem efault_ahead_of_the_mask_test_on_a_refused_range_is_rejected :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 1073741824 pipe2_wrap_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-- An unaccepted bit beside an accepted one (`2^30 | O_NONBLOCK`) is
-EINVAL, not the decline the accepted bit alone would draw: the mask test
is first.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_beside_accepted_einval_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073743872 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- The same call is not declined for the accepted bit it also carries.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_beside_accepted_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073743872 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      ≠ CheckUnmodeled := by
  rw [unaccepted_bit_beside_accepted_einval_is_accepted]; exact fun h => nomatch h

/-- The sign is part of the answer: `__do_pipe_flags` returns `-EINVAL`
(:988), and a kernel handing back 22 is refused.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_positive_einval_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect 22 [] []) demo_model
      = CheckReject := by
  rfl

/-! ## `__do_pipe_flags`, the accepted bits: declined

`O_NONBLOCK`, `O_CLOEXEC`, `O_DIRECT` and `O_NOTIFICATION_PIPE` pass the
mask (fs/pipe.c:987-988, Linux v6.18.46) and each changes what follows.
`__do_pipe_flags` hands the word to `create_pipe_files` (:990), which gives
the write end `O_NONBLOCK | O_DIRECT` of it (:945) and the read end
`O_NONBLOCK` (:956), and calls `watch_queue_init` (:936) when
`O_NOTIFICATION_PIPE` is set — the stub at
include/linux/watch_queue.h:126-129 (Linux v6.18.46) answers -ENOPKG
without `CONFIG_WATCH_QUEUE`; it then passes the word to both
`get_unused_fd_flags` calls (:994, :999), whose `O_CLOEXEC` is the
close-on-exec bit of the reservation (`alloc_fd`, fs/file.c:606, Linux
v6.18.46).  The model states none of it, so the checker declines before
it reads the effect. -/

/-- `O_NONBLOCK` (2048): declined, on the pair.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem nonblock_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 2048 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- …and on -EINVAL, which a mask test reading the bit as unaccepted would
answer: the decline is not a rejection of the wrong errno either.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem nonblock_einval_is_declined_not_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 2048 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- `O_CLOEXEC` (524288): declined.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem cloexec_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 524288 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- `O_DIRECT` (16384): declined.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem direct_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 16384 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- `O_NOTIFICATION_PIPE` (128, `O_EXCL`): declined, and the -ENOPKG a
kernel without `CONFIG_WATCH_QUEUE` answers (include/linux/watch_queue.h,
the stub `watch_queue_init`) is declined rather than rejected — the
constant is spelled as its numeral, 65, because the model has no name for
it.
kernel: fs/pipe.c:__do_pipe_flags; include/linux/watch_queue.h:watch_queue_init@v6.18.46 -/
theorem notification_pipe_enopkg_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 128 pipe2_flat_mem)
      (mkEffect (errno_ret 65) [] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- All four accepted bits at once (542848): declined.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem all_accepted_bits_are_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 542848 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-! ## The row narrows `flags` to an `int` and hands `fildes` over whole

`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` (fs/pipe.c:1054,
v6.18.46): riscv64's `__SYSCALL_DEFINEx` narrows a1 through `__SC_CAST`
before `__do_pipe_flags` sees it, and the row applies `pipe_flags32` for
exactly that reason; a0 is a pointer and arrives as it is. -/

/-- a1 = 2^32 is `flags = 0`: the pair is accepted through the row.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem the_row_narrows_flags_to_int :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- …and a model reading all 64 bits would answer -EINVAL to it: rejected.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem the_row_narrows_flags_einval_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject := by
  rfl

/-- …and the checker ITSELF, handed the same word without the row, answers
-EINVAL to it: `__do_pipe_flags` tests the residue of whatever word it is
given (:987-988), and the `int` narrowing is `__SC_CAST`'s, one frame up —
as the narrowing here is the row's, one definition up.  The pin above
would hold of a checker that masked only the low 32 bits; this one does
not, so the two together fix where the narrowing lives.
kernel: fs/pipe.c:__do_pipe_flags; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem the_checker_itself_reads_the_whole_word :
    check_pipe2 (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem) pipe2_flat_fildes 4294967296
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- a1 = 2^32 + 2^30: the high word is gone and bit 30 stays, -EINVAL.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem the_row_keeps_the_low_bits :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 5368709120 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- a1 = 2^32 + O_NONBLOCK is `O_NONBLOCK`: declined through the row.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem the_row_narrows_to_nonblock_and_declines :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 4294969344 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- a0 above 2^32 reaches the checker whole: the pair lands at
`2^32 + 4096`, and the model holds the pipe.
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem the_row_passes_fildes_whole :
    check_pipe2_row (pipe2_in pipe2_high_fildes 0 pipe2_high_mem)
      (mkEffect 0 [(pipe2_high_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- A destination backed at BOTH 4096 and `2^32 + 4096`.  This file's own:
`pipe2_high_mem` backs the high range alone, and under it a checker that
narrowed a0 would see a DEAD range at 4096 and reject the pair for the
wrong reason — the pin that once stood here passed under the checker its
docstring said it refused.  With both ranges backed the narrowed checker
accepts the pair at 4096 and the row refuses it, which is the difference
the next three pins state. -/
def pipe2_both_mem : word → Option byte :=
  fun a => if (4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4096 + 8)
              ∨ (2 ^ 32 + 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 2 ^ 32 + 4096 + 8)
           then some (Z_to_bv 8 0) else none

/-- The row a checker narrowing a0 as it narrows a1 would have — the wrong
row, stated so that what it accepts can be shown beside what the right
one refuses. -/
def narrowed_fildes_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_pipe2 i (abi_low32 (in_arg i 0)) (pipe_flags32 (in_arg i 1)) eff m

/-- A checker that narrowed a0 to 32 bits would accept the pair at 4096
over the doubly backed destination…
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem a_narrowed_fildes_would_accept_the_pair_at_4096 :
    narrowed_fildes_row (pipe2_in pipe2_high_fildes 0 pipe2_both_mem)
      (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- …and the row rejects that same pair, by the address comparison of the
pair arm and not by a dead range: 4096 is writable here.
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem the_row_rejects_the_pair_at_the_narrowed_address :
    check_pipe2_row (pipe2_in pipe2_high_fildes 0 pipe2_both_mem)
      (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- …while accepting the pair at the whole address over the same
destination, so the two verdicts differ in the address alone.
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem the_row_accepts_the_pair_at_the_whole_address :
    check_pipe2_row (pipe2_in pipe2_high_fildes 0 pipe2_both_mem)
      (mkEffect 0 [(pipe2_high_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- a1 with only its high half set is `flags = 0` once narrowed: the pair.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem high_half_flags_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes (Z_to_bv 64 0xFFFFFFFF00000000) pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-! ## The wrapping destination: `access_ok` refuses the range

`do_pipe2` copies both descriptors as one `int fildes[2]` (fs/pipe.c:1040,
Linux v6.18.46), and `copy_to_user`'s `access_ok` (`__access_ok`,
include/asm-generic/access_ok.h:31-41, Linux v6.18.46) refuses a range whose eight bytes
run off the top of the address space before a byte moves; `do_pipe2` then
`fput`s both files and `put_unused_fd`s both reservations (:1041-1045) and
the call is -EFAULT with nothing installed.  The checker takes the same
guard, `State.access_okb`, and rejects the pair the bare walk would have
accepted. -/

/-- THE NEGATIVE HALF, AND THE ONE THAT MATTERS: the effect offered here is
EXACTLY the answer a checker walking the map without the guard would give —
return 0 with the two descriptor numbers stored as one 8-byte range at
`2^64 - 4` and, once the word wrapped, at 0 — and the checker rejects it.
Rocq's `pipe2_wrapping_fildes_rejects_the_pair`, restated on `check_pipe2`.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_pair_is_rejected :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (Z_to_bv 64 0) [(pipe2_wrap_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- …and the positive half, Linux's own answer: -EFAULT, no write, the
model unchanged.  Rocq's `pipe2_wrapping_fildes_is_efault`.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_is_efault :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- The refused range is Linux's exact -EFAULT and not a fail-closed
stand-in: one `access_ok` covers all eight bytes (:1040), so there is no
partial write to decline over.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      ≠ CheckUnmodeled := by
  rw [wrapping_fildes_is_efault]; exact fun h => nomatch h

/-- The three errnos `__do_pipe_flags` can answer before the copy is
attempted are accepted on the wrapping destination too — -EMFILE from
`alloc_fd`'s `fd >= end` against the soft `RLIMIT_NOFILE`
(fs/file.c:591-593) — since a task short of two descriptors never
reaches `access_ok`.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem wrapping_fildes_emfile_is_accepted :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EMFILE) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- -ENFILE — `alloc_empty_file`'s `files_stat.max_files` test
(fs/file_table.c:248-255) on the two files `create_pipe_files` allocates
(fs/pipe.c:944, :956), or `create_pipe_files` handed no inode (:932-933) —
is accepted there for the same reason…
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem wrapping_fildes_enfile_is_accepted :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret ENFILE) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and -ENOMEM, those same file allocations failing for memory
(`alloc_empty_file`, fs/file_table.c:258-260; `alloc_path_pseudo`,
:400-402); `alloc_fdtable`'s (fs/file.c:242) joins them only on a table
that must grow past `max_fds` (:595), which a 64-slot fresh table handing
out 3 and 4 need not.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file_table.c:alloc_empty_file,alloc_path_pseudo; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem wrapping_fildes_enomem_is_accepted :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- An errno the arm admits beside a write it does not: the copy that
failed `access_ok` moved no byte, so the -EFAULT arm accepts an effect
with every ledger empty and nothing else.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_efault_with_a_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EFAULT) [(pipe2_wrap_fildes, [3, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- Return 0 with no write is rejected there too: `do_pipe2` returns 0
only past a `copy_to_user` that stored all eight bytes (:1040, :1051),
and `access_ok` refused this one.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_success_without_a_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect 0 [] []) demo_model
      = CheckReject := by
  rfl

/-- -EINVAL on a zero flag word is rejected on the wrapping destination as
on every other: the mask test passed (:987-988), and nothing after it
answers -EINVAL.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2@v6.18.46 -/
theorem wrapping_fildes_einval_is_rejected :
    check_pipe2_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject := by
  rfl

/-- The wrapping destination's -EFAULT and the flat destination's -EFAULT
differ in the model's view of the range only: on the flat one the copy is
admitted and -EFAULT is refused.  Rocq's
`pipe2_unwrapped_fildes_rejects_efault`.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem fresh_efault_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-! ## `access_ok`'s edge: the last eight bytes below `TASK_SIZE`, and the top of the word

`__access_ok` accepts `addr <= limit - size` (include/asm-generic/access_ok.h:40,
Linux v6.18.46), the limit being `TASK_SIZE`, which is `2^47` at the Sv48
the tree pins (`State/Geometry.lean`; `Checks/Cases/Uaccess.lean`'s
`task_size_is_the_sv48_top`; `bugs/va-size-declines-every-non-sv48-run.md`
records what the other sizes cost).  The limit is Linux's, and the model
draws it once for every arm in `State/Readers.lean`'s `access_okb`;
whether qemu-user's own range check stops at the same address is that
decision's question, settled in `Checks/Cases/Uaccess.lean`, not this
file's.  So the eight bytes ending exactly at
`TASK_SIZE` are a destination and the eight starting one byte higher are
not — the equality is on the accepted side — and a destination eight bytes
below `2^64` is refused by the limit and not by any wrapping: its eight
bytes fit under the word, so a guard written as `base + 8 ≤ 2^64` would
have taken the pair. -/

/-- `TASK_SIZE - 8`, the highest destination there is: the pair.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem task_size_minus_8_pair_is_accepted :
    check_pipe2_row (pipe2_in (Z_to_bv 64 0x7FFFFFFFFFF8) 0
        (fun a => if 0x7FFFFFFFFFF8 ≤ bv_unsigned a ∧ bv_unsigned a < 0x800000000000
                  then some (Z_to_bv 8 0) else none))
      (mkEffect 0 [(Z_to_bv 64 0x7FFFFFFFFFF8, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- …and -EFAULT there is rejected: the range is accepted whole, so the
guard that would refuse it is one byte off.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem task_size_minus_8_efault_is_rejected :
    check_pipe2_row (pipe2_in (Z_to_bv 64 0x7FFFFFFFFFF8) 0
        (fun a => if 0x7FFFFFFFFFF8 ≤ bv_unsigned a ∧ bv_unsigned a < 0x800000000000
                  then some (Z_to_bv 8 0) else none))
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-- `TASK_SIZE - 7`: the pair is rejected…
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem task_size_minus_7_pair_is_rejected :
    check_pipe2_row (pipe2_in (Z_to_bv 64 0x7FFFFFFFFFF9) 0
        (fun a => if 0x7FFFFFFFFFF9 ≤ bv_unsigned a ∧ bv_unsigned a < 0x800000000001
                  then some (Z_to_bv 8 0) else none))
      (mkEffect 0 [(Z_to_bv 64 0x7FFFFFFFFFF9, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- …and -EFAULT is the answer, the range being refused whole.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem task_size_minus_7_is_efault :
    check_pipe2_row (pipe2_in (Z_to_bv 64 0x7FFFFFFFFFF9) 0
        (fun a => if 0x7FFFFFFFFFF9 ≤ bv_unsigned a ∧ bv_unsigned a < 0x800000000001
                  then some (Z_to_bv 8 0) else none))
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- `2^64 - 8`, whose eight bytes do not wrap: the pair is rejected by the
limit alone…
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem top_of_word_fildes_pair_is_rejected :
    check_pipe2_row (pipe2_in (Z_to_bv 64 (2 ^ 64 - 8)) 0
        (fun a => if 2 ^ 64 - 8 ≤ bv_unsigned a then some (Z_to_bv 8 0) else none))
      (mkEffect 0 [(Z_to_bv 64 (2 ^ 64 - 8), [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- …and -EFAULT accepted.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem top_of_word_fildes_is_efault :
    check_pipe2_row (pipe2_in (Z_to_bv 64 (2 ^ 64 - 8)) 0
        (fun a => if 2 ^ 64 - 8 ≤ bv_unsigned a then some (Z_to_bv 8 0) else none))
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-! ### The other edge: a null `fildes`

`__access_ok(NULL, 8)` passes — `0 <= limit - 8` — so the range check
refuses nothing at the bottom of the address space, and whether the copy
lands is the page's business: unmapped, as `vm.mmap_min_addr` leaves it
on every default configuration, the copy faults and the call is -EFAULT;
mapped, a variant a root process with the sysctl at 0 can build, the pair
lands at 0.  The checker reads the map the same way, so a guard that
slipped in `0 < base`, or compared the base as a signed number, would
show here and nowhere above. -/

/-- The eight bytes at 0 unmapped: -EFAULT on the unchanged model.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem null_fildes_unbacked_is_efault :
    check_pipe2_row (pipe2_in 0 0 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and the pair there is rejected.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem null_fildes_unbacked_pair_is_rejected :
    check_pipe2_row (pipe2_in 0 0 pipe2_dead_mem)
      (mkEffect 0 [(0, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- The eight bytes at 0 mapped: the pair lands at 0 and the model holds
the pipe — the range check is not what stands between a process and its
zero page.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem null_fildes_backed_pair_is_accepted :
    check_pipe2_row (pipe2_in 0 0 (fun a => if bv_unsigned a < 8 then some (Z_to_bv 8 0) else none))
      (mkEffect 0 [(0, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-! ## The pair, on a destination the copy accepts

`__do_pipe_flags` reserves the read end first and the write end second
(fs/pipe.c:994-1006, Linux v6.18.46), each through `get_unused_fd_flags` —
`alloc_fd`, the first clear bit of `open_fds` at or above the `next_fd`
hint (fs/file.c:580-585, Linux v6.18.46), a hint `__put_unused_fd`
(:626-632) lowers to each descriptor freed below it, so the answer is the
lowest free number — and the
bit `alloc_fd` sets at :606 marks the first before the second scan runs, so
`fd[0] < fd[1]`.  `do_pipe2` then copies both as ONE `int fildes[2]`
(:1040) and installs both (:1047-1048).  On the demo process the pair is
(3, 4). -/

/-- Return 0, the pair (3, 4) stored as one 8-byte little-endian range at
`fildes`, both ends installed and an empty pipe bound: accepted, and the
post-state is `one_pipe_model`.  Rocq's
`pipe2_unwrapped_fildes_still_installs_the_pair`.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- The three injectable errnos are accepted on the unchanged model:
-EMFILE from `alloc_fd`'s `fd >= end` (fs/file.c:591-593), -ENFILE from
`alloc_empty_file`'s file limit (fs/file_table.c:248-255) under
`create_pipe_files`, or from `create_pipe_files` itself when
`get_pipe_inode` fails (fs/pipe.c:932-933), -ENOMEM from those same file
allocations (fs/file_table.c:258-260).
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem fresh_emfile_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EMFILE) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- -ENFILE the same way: `create_pipe_files` — its own :932-933, or
`alloc_empty_file`'s limit (fs/file_table.c:248-255, returned at :278)
under its :944 and :956 — answers before either descriptor is reserved
(ahead of :994).
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem fresh_enfile_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret ENFILE) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- -ENOMEM too: `alloc_empty_file` (fs/file_table.c:258-260) and
`alloc_path_pseudo` (:400-402) inside `create_pipe_files`, ahead of the
copy-out.  `alloc_fdtable`'s -ENOMEM (fs/file.c:242) is not this
fixture's: `alloc_fd` grows the table only at `fd >= max_fds` (:595), and
a fresh table holds `NR_OPEN_DEFAULT` = `BITS_PER_LONG` slots
(include/linux/fdtable.h:24), so 3 and 4 never grow it.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file_table.c:alloc_empty_file,alloc_path_pseudo; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_enomem_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- An injected errno leaves the model as it was: `CheckOk` carries the
post-state, and on -EMFILE it is the pre-state and not a model with a pipe
in it — the equality above fixes it, and this is the disequality a reader
looks for.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_emfile_with_a_pipe_installed_is_not_the_verdict :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EMFILE) [] []) demo_model
      ≠ CheckOk one_pipe_model [] := by
  rw [fresh_emfile_is_accepted]
  intro h
  injection h with hm
  exact absurd (congrArg (fun m => (m_pipes m).length) hm) (by decide)

/-- A fresh process is never declined: every answer to it is stated.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags@v6.18.46 -/
theorem fresh_pair_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      ≠ CheckUnmodeled := by
  rw [fresh_pair_is_accepted]; exact fun h => nomatch h

/-! ### The lies about the pair, each rejected

Each effect below differs from the accepted one in a single respect, so
the rejection names the conjunct that refused it. -/

/-- Return 1 with the kernel's write: `do_pipe2` returns `error`, which is
0 once the copy succeeded (fs/pipe.c:1040, :1051).
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_ret_one_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 1 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- -EMFILE beside the delivered pair: the errno fires inside
`__do_pipe_flags` (fs/pipe.c:994, :999), before the only copy-out
(:1040), so a kernel that both refused and delivered lied about one of
them.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_pair_emfile_beside_the_pair_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EMFILE) [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- Return 0 with no write at all: the ledger with the pair is what a
successful `copy_to_user` leaves, and the model installed nothing without
it.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_dropped_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [] []) demo_model
      = CheckReject := by
  rfl

/-- The same eight bytes as two ranges: the spec states ONE range because
the kernel issues ONE `copy_to_user` of `sizeof(fd)` (:1040).
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_split_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- The range shifted one byte up.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_shifted_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(4097, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- The pair and a second write of one byte beside it.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_smuggled_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0]), (pipe2_flat_fildes, [0])] [])
      demo_model
      = CheckReject := by
  rfl

/-- The pair and a zero-fill of one byte: the zeros ledger is empty in the
one accepted effect.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_smuggled_zeros_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [(pipe2_flat_fildes, 1)])
      demo_model
      = CheckReject := by
  rfl

/-- The accepted write with the model left as it was — the pair without the
pipe — is not the verdict: `CheckOk` carries the post-state, and the
equality above fixes it as `one_pipe_model`.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags@v6.18.46 -/
theorem fresh_pair_unchanged_model_is_not_the_verdict :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      ≠ CheckOk demo_model [] := by
  rw [fresh_pair_is_accepted]
  intro h
  injection h with hm
  exact absurd (congrArg (fun m => (m_pipes m).length) hm) (by decide)

/-- Four bytes only: `sizeof(fd)` is 8.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_truncated_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- Eight bytes of 255: the right range with the wrong contents.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_poisoned_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [255, 255, 255, 255, 255, 255, 255, 255])] []) demo_model
      = CheckReject := by
  rfl

/-- The ends swapped: `fd[0]` is the read end (fs/pipe.c:1005), reserved
first (:994), so it is the lower number.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_pair_swapped_ends_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [4, 0, 0, 0, 3, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- The same number twice: `alloc_fd` marks the first end in `open_fds`
(fs/file.c:606) before the second scan runs.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_pair_same_end_twice_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 3, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- (4, 5) over a table whose lowest free number is 3: `alloc_fd` answers
the first clear bit (fs/file.c:585), never one above it.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem fresh_pair_non_lowest_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [4, 0, 0, 0, 5, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- Nine bytes: the right range with one byte too many, the other side of
`fresh_pair_truncated_write_is_rejected`.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_nine_byte_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-! ### The errno-only arm: every ledger empty

An injected errno is accepted with NO ledger, because each fires inside
`__do_pipe_flags` before `do_pipe2` touches user memory (fs/pipe.c:994,
:999 against :1040, Linux v6.18.46).  The `fresh_pair_with_*` pins above refuse a ledger
beside the pair; these refuse one beside the errno, and an errno outside
the injected set on the writable destination, where nothing answers it. -/

/-- -ENOPKG, spelled 65 as `notification_pipe_enopkg_is_declined` spells
it: on a zero flag word no kernel answers it, since `watch_queue_init`
runs only under `O_NOTIFICATION_PIPE` (fs/pipe.c:935-936).
kernel: fs/pipe.c:__do_pipe_flags,create_pipe_files@v6.18.46 -/
theorem fresh_enopkg_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret 65) [] []) demo_model
      = CheckReject := by
  rfl

/-- -EPERM, spelled 1 the way `fresh_enopkg_is_rejected` spells -ENOPKG: no
test on the pipe2 path answers it, and the evidence reader asks a NAMED
errno to appear in the cited functions — the absence this pin states.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files@v6.18.46 -/
theorem fresh_eperm_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret 1) [] []) demo_model
      = CheckReject := by
  rfl

/-- -EMFILE beside a zero-fill of one byte.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_emfile_with_a_zero_fill_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [(pipe2_flat_fildes, 1)] [] [] []) demo_model
      = CheckReject := by
  rfl

/-- -EMFILE beside an unmap.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_emfile_with_an_unmap_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] [(pipe2_flat_fildes, 1)] [] []) demo_model
      = CheckReject := by
  rfl

/-- -EMFILE beside a symbolic copy.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_emfile_with_a_copy_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] []
        [MemCopy.mkCopy pipe2_flat_fildes pipe2_flat_fildes 8] []) demo_model
      = CheckReject := by
  rfl

/-- -EMFILE beside a copy-in ledger.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_emfile_with_a_copyin_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] [] [] [(pipe2_flat_fildes, 8)]) demo_model
      = CheckReject := by
  rfl

/-! ### An unaligned destination -/

/-- Eight bytes at 4097: `copy_to_user` of an `int[2]` carries no alignment
test — `__access_ok` compares the range's ends and nothing else — so the
pair lands and the model holds the pipe.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem unaligned_fildes_pair_is_accepted :
    check_pipe2_row (pipe2_in 4097 0
        (fun a => if 4097 ≤ bv_unsigned a ∧ bv_unsigned a < 4097 + 8 then some (Z_to_bv 8 0) else none))
      (mkEffect 0 [(4097, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-! ### The same pair across a page boundary -/

/-- Eight bytes at 8188 span two pages and the copy is one range still:
`copy_to_user` is one call over `sizeof(fd)` (fs/pipe.c:1040).
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem straddle_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_straddle_fildes 0 pipe2_straddle_mem)
      (mkEffect 0 [(pipe2_straddle_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- …so a write split at the page boundary is rejected.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem straddle_pair_split_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_straddle_fildes 0 pipe2_straddle_mem)
      (mkEffect 0 [(pipe2_straddle_fildes, [3, 0, 0, 0]), (8192, [4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-! ## A second pipe, and tables with holes

The pipe id counts creations (`State.pipe_new_id`) and the descriptors are
`alloc_fd`'s lowest free numbers, so the second pipe of the demo process is
(5, 6) with id 1, and a table with fd 3 free under a live fd 4 hands out 3
and 5. -/

/-- On `one_pipe_model`: (5, 6), pipe 1, the first pipe kept —
`two_pipe_model`.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem second_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [5, 0, 0, 0, 6, 0, 0, 0])] []) one_pipe_model
      = CheckOk two_pipe_model [] := by
  rfl

/-- The first pipe's numbers again, over a table that holds them: rejected.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem second_pair_first_numbers_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) one_pipe_model
      = CheckReject := by
  rfl

/-- The right pair with the new ends bound to the OLD pipe's id — one
`pipe_inode_info` where the kernel allocates two (`alloc_pipe_info` per
`create_pipe_files`) — is not the verdict: the post-state `CheckOk` carries
holds two pipes, `reused_id_model` one.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files,get_pipe_inode,alloc_pipe_info@v6.18.46 -/
theorem second_pair_reused_id_is_not_the_verdict :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [5, 0, 0, 0, 6, 0, 0, 0])] []) one_pipe_model
      ≠ CheckOk reused_id_model [] := by
  rw [second_pair_is_accepted]
  intro h
  injection h with hm
  exact absurd (congrArg (fun m => (m_pipes m).length) hm) (by decide)

/-- fd 3 free under a live fd 4: the read end fills the hole and the write
end skips the live number — (3, 5), `holes_after_model`.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 5, 0, 0, 0])] []) holes_model
      = CheckOk holes_after_model [] := by
  rfl

/-- Consecutive numbers over the same table — (3, 4) with 4 live — are
rejected.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_pair_consecutive_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) holes_model
      = CheckReject := by
  rfl

/-- The probe's `holes` table: three live pipe ends at 4, 5 and 6 with 3
freed, so the third pipe is (3, 7) with id 2.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_probe_pair_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 7, 0, 0, 0])] []) holes_probe_model
      = CheckOk holes_probe_after_model [] := by
  rfl

/-- …and (3, 4) over it, where 4 is live, is rejected.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_probe_pair_consecutive_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) holes_probe_model
      = CheckReject := by
  rfl

/-! ## Tables that do not begin at 3: descriptor 0, and descriptors past 255

`alloc_fd` starts its scan at `files->next_fd` (fs/file.c:580-582, Linux
v6.18.46), which `__put_unused_fd` lowers to each descriptor closed below
it (:630-631), so a process that closed standard input is handed 0 as its
read end; and both ends are copied as one `int fildes[2]` (fs/pipe.c:1040,
Linux v6.18.46) in the architecture's byte order — little-endian on riscv,
arch/riscv/include/uapi/asm/byteorder.h:10 (Linux v6.18.46) — so a
descriptor past 255 fills the second byte.  The tables here hold no 0, or
hold 256 numbers, where the sections above hand out single-byte numbers
from 3.  The two
256-entry pins raise `maxRecDepth` the way `Checks/Cases/Fs/Namei.lean`'s
255-byte names do: each `alloc_fd` scan examines every held candidate and
one more — 257 then 258 here — and the elaborator's `rfl` unfolds that
walk deeper than the default allows. -/

/-- Standard input closed: the read end is 0 and the write end the next
free number above it, 3.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,__put_unused_fd@v6.18.46 -/
theorem closed_stdin_pair_is_zero_and_three :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [0, 0, 0, 0, 3, 0, 0, 0])] [])
      (fixture_of (fds := [(1, .FdChannel 1), (2, .FdChannel 2)]))
      = CheckOk (fixture_of
          (fds := [(3, .FdPipe 0 true), (0, .FdPipe 0 false),
                   (1, .FdChannel 1), (2, .FdChannel 2)])
          (pipes := [(0, ([], 0))])) [] := by
  rfl

/-- …and a kernel that skipped the hole at 0 is refused.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd,__put_unused_fd@v6.18.46 -/
theorem closed_stdin_skipping_zero_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [])
      (fixture_of (fds := [(1, .FdChannel 1), (2, .FdChannel 2)]))
      = CheckReject := by
  rfl

/-- An empty table: 0 and 1.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem empty_table_pair_is_zero_and_one :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [0, 0, 0, 0, 1, 0, 0, 0])] []) (fixture_of (fds := []))
      = CheckOk (fixture_of (fds := [(1, .FdPipe 0 true), (0, .FdPipe 0 false)])
          (pipes := [(0, ([], 0))])) [] := by
  rfl

set_option maxRecDepth 8192 in
/-- Descriptors 0 through 255 held: the pair is (256, 257), each `int`
little-endian, so the second byte of each carries the 1.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem two_byte_fds_are_little_endian :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [0, 1, 0, 0, 1, 1, 0, 0])] [])
      (fixture_of (fds := (List.range 256).map (fun k => (nat_to_word k, FdEntry.FdDir))))
      = CheckOk (fixture_of
          (fds := (257, .FdPipe 0 true) :: (256, .FdPipe 0 false)
                    :: (List.range 256).map (fun k => (nat_to_word k, FdEntry.FdDir)))
          (pipes := [(0, ([], 0))])) [] := by
  rfl

set_option maxRecDepth 8192 in
/-- …and the same numbers written big-endian are refused.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem two_byte_fds_big_endian_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [0, 0, 1, 0, 0, 0, 1, 1])] [])
      (fixture_of (fds := (List.range 256).map (fun k => (nat_to_word k, FdEntry.FdDir))))
      = CheckReject := by
  rfl

/-! ## The scan wall: the two `fd_lookup … = some` guards

`State.alloc_fd` is `alloc_fd_aux fds 0 4096`, a scan that examines every
candidate it returns save the last: once 0..4095 are all held it hands
back 4096 UNEXAMINED, and the spec's `lowest_fd` then demands a freeness
the number may not have.  The checker tests that freeness — the two
`fd_lookup … = some` arms of `check_pipe2` — and where it fails answers
`CheckReject`, which is the wrong answer: Linux's `alloc_fd` has no such
wall (its scan is `find_next_fd` over the whole table, fs/file.c:585,
Linux v6.18.46) and, under a soft `RLIMIT_NOFILE` above the table, hands
out 4096 and 4097 and installs both.  That is
`bugs/fd-allocation-ignores-rlimit-nofile.md`'s priority-1 residual,
recorded there and pinned here so that moving the wall — raising the
fuel, or hoisting the guards to `CheckUnmodeled` with the spec — has to
move these pins with it.  pipe2's wall sits one number below every other
allocator's, because it allocates twice: with 0..4095 held and 4096 free
the read end takes 4096 (unexamined but free, so the first guard passes),
and the write end's scan, over a table now holding 0..4096, returns 4096
again — held, so the second guard fires.  With 0..4096 held the first
guard fires on its own.

No `rfl` walks a 4097-entry table, so the three pins are symbolic, over
ANY model holding the numbers: the hypotheses name the table's contents
and nothing else, `fixture_of (fds := (List.range 4097).map (fun k =>
(nat_to_word k, FdEntry.FdDir)))` is one model satisfying the first, and
`alloc_fd_aux_all_held` is the one fact about the scan they need.  The
three helper lemmas before them are Lean-only — Rocq's cases file has no
wall pin — and belong in `State/Fd.lean`, beside `alloc_fd_aux_le`; that
file is frozen, so they wait here until a `lean: base:` PR moves them. -/

/-- A scan whose every candidate is held runs out of fuel and returns the
candidate one past the last it examined: the wall, stated for any start
and any fuel.
model: `State.alloc_fd_aux`'s fuel exhaustion, the fact the wall pins rest on; home `State/Fd.lean` -/
theorem alloc_fd_aux_all_held (fds : List (word × FdEntry)) (fuel : Nat) (cand : word)
    (h : ∀ k : Nat, k < fuel → ∃ e, fd_lookup fds (cand + nat_to_word k) = some e) :
    alloc_fd_aux fds cand fuel = cand + nat_to_word fuel := by
  induction fuel generalizing cand with
  | zero =>
    simp only [alloc_fd_aux, nat_to_word_zero, BitVec.add_zero]
  | succ f ih =>
    obtain ⟨e, he⟩ := h 0 (Nat.succ_pos f)
    rw [nat_to_word_zero, BitVec.add_zero] at he
    simp only [alloc_fd_aux, he]
    rw [ih (cand + 1) (fun k hk => by
      obtain ⟨e', he'⟩ := h (k + 1) (Nat.succ_lt_succ hk)
      exact ⟨e', by rw [add_one_nat_to_word]; exact he'⟩)]
    exact add_one_nat_to_word cand f

/-- Looking up the descriptor just inserted finds it.
model: `State.fd_insert` read back at its own key; home `State/Fd.lean` -/
theorem fd_lookup_insert_same (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    fd_lookup (fd_insert fds fd e) fd = some e := by
  unfold fd_insert
  simp only [fd_lookup, bv_eqb_refl, ↓reduceIte]

/-- Looking up any other descriptor sees through the insertion.
model: `State.fd_insert` read back at another key, through its filter; home `State/Fd.lean` -/
theorem fd_lookup_insert_ne (fds : List (word × FdEntry)) (fd k : word) (e : FdEntry)
    (hne : k ≠ fd) : fd_lookup (fd_insert fds fd e) k = fd_lookup fds k := by
  have hk : bv_eqb fd k = false := by
    cases hb : bv_eqb fd k
    · rfl
    · exact absurd ((bv_eqb_eq fd k).mp hb).symm hne
  unfold fd_insert
  simp only [fd_lookup, hk, Bool.false_eq_true, ↓reduceIte]
  induction fds with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨a, e'⟩ := p
    simp only [List.filter_cons]
    cases ha : bv_eqb a fd
    · simp only [Bool.not_false, ↓reduceIte, fd_lookup, ih]
    · have hak : bv_eqb a k = false := by rw [(bv_eqb_eq a fd).mp ha]; exact hk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, fd_lookup, hak, ih]

/-- Descriptor numbers below the wall are distinct from the wall's.
model: `nat_to_word` is injective below `2^64`, read through `BitVec.toNat` -/
theorem nat_to_word_ne_of_lt (k : Nat) (hk : k < 4096) : nat_to_word k ≠ nat_to_word 4096 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  rw [nat_to_word_eq_ofNat, nat_to_word_eq_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- The scan's start, added to a step count, is the step count.
model: `Z_to_bv 64 0` is `0#64` -/
theorem zero_add_nat_to_word (k : Nat) : Z_to_bv 64 0 + nat_to_word k = nat_to_word k := by
  rw [show (Z_to_bv 64 0 : word) = 0#64 from rfl, BitVec.zero_add]

/-- The first guard: over a table holding all of 0..4096, Linux's own pair
(4097, 4098) — bytes `[1, 16, 0, 0, 2, 16, 0, 0]` — is rejected, since the
read end's scan returns 4096 unexamined and 4096 is held.  The recorded
wrong answer, pinned.
model: the scan wall of `State.alloc_fd`, bugs/fd-allocation-ignores-rlimit-nofile.md's priority-1 residual, on the read end -/
theorem wall_read_end_pair_is_rejected (m : Model)
    (hheld : ∀ k : Nat, k ≤ 4096 → ∃ e, fd_lookup (m_fds m) (nat_to_word k) = some e)
    (hpipes : m_pipes m = []) :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [1, 16, 0, 0, 2, 16, 0, 0])] []) m = CheckReject := by
  have hfdr : pipe2_fdr m = nat_to_word 4096 := by
    unfold pipe2_fdr alloc_fd
    rw [alloc_fd_aux_all_held (m_fds m) 4096 (Z_to_bv 64 0) (fun k hk => by
      obtain ⟨e, he⟩ := hheld k (Nat.le_of_lt hk)
      exact ⟨e, by rw [zero_add_nat_to_word]; exact he⟩)]
    exact zero_add_nat_to_word 4096
  obtain ⟨e, he⟩ := hheld 4096 (Nat.le_refl _)
  rw [← hfdr] at he
  show check_pipe2 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) pipe2_flat_fildes (pipe_flags32 0)
    (mkEffect 0 [(pipe2_flat_fildes, [1, 16, 0, 0, 2, 16, 0, 0])] []) m = CheckReject
  unfold check_pipe2
  have h1 : (bv_unsigned (bv_and (pipe_flags32 0)
      (bv_not (Z_to_bv 64 LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe.pipe2_flags_mask))) == 0) = true := by decide
  have h2 : w_is0 (pipe_flags32 0) = true := by decide
  have h3 : access_okb pipe2_flat_fildes 8 = true := by decide
  have h4 : read_bytes_map (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem).in_wmem pipe2_flat_fildes
      (Z_to_bv 64 8) = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2, hpipes, h3, h4]
  simp only [show pipe_lookup [] (pipe_new_id []) = none from rfl]
  simp only [he]

/-- The second guard, pipe2's own: over a table holding all of 0..4095
with 4096 free, Linux's pair (4096, 4097) — bytes `[0, 16, 0, 0, 1, 16, 0,
0]` — is rejected, since the write end's scan, over the table with 4096
now installed, returns 4096 again.  One number below the wall every
single allocator has, because this call allocates twice.
model: the scan wall of `State.alloc_fd` reached through the second allocation, bugs/fd-allocation-ignores-rlimit-nofile.md -/
theorem wall_write_end_pair_is_rejected (m : Model)
    (hheld : ∀ k : Nat, k < 4096 → ∃ e, fd_lookup (m_fds m) (nat_to_word k) = some e)
    (hfree : fd_lookup (m_fds m) (nat_to_word 4096) = none)
    (hpipes : m_pipes m = []) :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [0, 16, 0, 0, 1, 16, 0, 0])] []) m = CheckReject := by
  have hfdr : pipe2_fdr m = nat_to_word 4096 := by
    unfold pipe2_fdr alloc_fd
    rw [alloc_fd_aux_all_held (m_fds m) 4096 (Z_to_bv 64 0) (fun k hk => by
      obtain ⟨e, he⟩ := hheld k hk
      exact ⟨e, by rw [zero_add_nat_to_word]; exact he⟩)]
    exact zero_add_nat_to_word 4096
  have hfdw : ∀ id, pipe2_fdw m id = nat_to_word 4096 := by
    intro id
    unfold pipe2_fdw alloc_fd
    rw [alloc_fd_aux_all_held (pipe2_fds1 m id) 4096 (Z_to_bv 64 0) (fun k hk => by
      obtain ⟨e, he⟩ := hheld k hk
      refine ⟨e, ?_⟩
      rw [zero_add_nat_to_word]
      unfold pipe2_fds1
      rw [fd_lookup_insert_ne _ _ _ _ (by rw [hfdr]; exact nat_to_word_ne_of_lt k hk)]
      exact he)]
    exact zero_add_nat_to_word 4096
  have hg2 : ∀ id, fd_lookup (pipe2_fds1 m id) (pipe2_fdw m id) = some (.FdPipe id false) := by
    intro id
    rw [hfdw]
    unfold pipe2_fds1
    rw [hfdr]
    exact fd_lookup_insert_same _ _ _
  have hg1 : fd_lookup (m_fds m) (pipe2_fdr m) = none := by rw [hfdr]; exact hfree
  show check_pipe2 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) pipe2_flat_fildes (pipe_flags32 0)
    (mkEffect 0 [(pipe2_flat_fildes, [0, 16, 0, 0, 1, 16, 0, 0])] []) m = CheckReject
  unfold check_pipe2
  have h1 : (bv_unsigned (bv_and (pipe_flags32 0)
      (bv_not (Z_to_bv 64 LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe.pipe2_flags_mask))) == 0) = true := by decide
  have h2 : w_is0 (pipe_flags32 0) = true := by decide
  have h3 : access_okb pipe2_flat_fildes 8 = true := by decide
  have h4 : read_bytes_map (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem).in_wmem pipe2_flat_fildes
      (Z_to_bv 64 8) = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2, hpipes, h3, h4]
  simp only [show pipe_lookup [] (pipe_new_id []) = none from rfl]
  simp only [hg1, hg2]

/-- What the checker DOES grade at the wall, on any table: the injected
-EMFILE, which is Linux's answer there only at a soft limit of exactly
the table's size (`alloc_fd`'s `fd >= end`, fs/file.c:591-593) — so at
the wall the model admits Linux's refusal and refuses Linux's success.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem wall_emfile_is_accepted (m : Model) (hpipes : m_pipes m = []) :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EMFILE) [] []) m = CheckOk m [] := by
  show check_pipe2 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) pipe2_flat_fildes (pipe_flags32 0)
    (mkEffect (errno_ret EMFILE) [] []) m = CheckOk m []
  unfold check_pipe2
  have h1 : (bv_unsigned (bv_and (pipe_flags32 0)
      (bv_not (Z_to_bv 64 LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe.pipe2_flags_mask))) == 0) = true := by decide
  have h2 : w_is0 (pipe_flags32 0) = true := by decide
  have h3 : access_okb pipe2_flat_fildes 8 = true := by decide
  have h4 : read_bytes_map (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem).in_wmem pipe2_flat_fildes
      (Z_to_bv 64 8) = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
  have h5 : errno_ret_in LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe.pipe2_errnos (errno_ret EMFILE) = true := by decide
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2, hpipes, h3, h4]
  simp only [show pipe_lookup [] (pipe_new_id []) = none from rfl, h5, ↓reduceIte]

/-! ## The declines the checker makes on its own

The arms that answer `CheckUnmodeled` on a zero flag word do so for
reasons the spec-level file argues in full: a pipe table that already
binds the next id, and a destination whose first byte is writable but
whose eighth is not, where the kernel's copier stores a prefix the arm
does not state. -/

/-- A pipe table already binding the next id is declined on every effect:
no run builds it, and the arm says so rather than aliasing two pipes.
kernel: fs/pipe.c:do_pipe2,create_pipe_files@v6.18.46 -/
theorem aliased_id_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) aliased_id_model
      = CheckUnmodeled := by
  rfl

/-- Four writable bytes at `fildes` and a fault behind them: declined, on
the pair…
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem half_destination_pair_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- …and on the kernel's own -EFAULT, whose stored prefix the arm leaves
unstated.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem half_destination_efault_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- …and on -EFAULT beside the four-byte prefix — the probe's `partial`
case, the trace a hart really produces.  The decline is decided by the
destination before the effect is read, so the effect that is right is
declined with the ones that are wrong; a checker that read the effect
first would REJECT this real trace, which is the fault this pin is for.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem half_destination_prefix_and_efault_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem)
      (mkEffect (errno_ret EFAULT) [(pipe2_flat_fildes, [3, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- Seven writable bytes are a prefix too: `sizeof(fd)` is 8 (:1040).
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem seven_bytes_pair_is_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_seven_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- The last byte of a page, with nothing behind it: exactly ONE writable
byte.  This file's own — the spec-level fixtures stop at four and seven —
and the smallest prefix there is: the copier stores byte 0 and faults on
byte 1 — an 8-byte copy takes the byte-copy tail of
arch/riscv/lib/uaccess.S (:75-76 into :193-205), whose fixup at :212-213
returns the bytes not copied; `raw_copy_to_user`
(arch/riscv/include/asm/uaccess.h:430-433, Linux v6.18.46) is what reaches
it — so a one-byte prefix landed and the arm declines.  qemu-user stores
the two descriptors through two 4-byte `put_user_s32` calls
(linux-user/syscall.c `do_pipe`, QEMU v11.1.1), each all or nothing, so it
lands no one-byte prefix, which is the other admitted trace and the reason
the arm declines rather than picks one.  The probe of the first
byte is a probe of ONE byte; a checker probing two would answer -EFAULT
here as exact and pass every pin above. -/
def pipe2_one_byte_mem : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 8192 then some (Z_to_bv 8 0) else none

/-- One writable byte: the pair is declined…
kernel: fs/pipe.c:do_pipe2; arch/riscv/include/asm/uaccess.h:raw_copy_to_user@v6.18.46 -/
theorem last_byte_of_page_pair_is_declined :
    check_pipe2_row (pipe2_in 8191 0 pipe2_one_byte_mem)
      (mkEffect 0 [(8191, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- …and so is the bare -EFAULT, which leaves the stored byte unstated…
kernel: fs/pipe.c:do_pipe2; arch/riscv/include/asm/uaccess.h:raw_copy_to_user@v6.18.46 -/
theorem last_byte_of_page_efault_is_declined :
    check_pipe2_row (pipe2_in 8191 0 pipe2_one_byte_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckUnmodeled := by
  rfl

/-- …and so is -EFAULT beside the one-byte prefix, the trace a hart
produces.
kernel: fs/pipe.c:do_pipe2; arch/riscv/include/asm/uaccess.h:raw_copy_to_user@v6.18.46 -/
theorem last_byte_of_page_prefix_and_efault_is_declined :
    check_pipe2_row (pipe2_in 8191 0 pipe2_one_byte_mem)
      (mkEffect (errno_ret EFAULT) [(8191, [3])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-! ## A destination with nothing writable: -EFAULT, no prefix

`copy_to_user` over a range whose FIRST byte faults stores nothing, so the
kernel's -EFAULT with an unchanged model is the exact answer, and the
injectable errnos stay admitted ahead of it. -/

/-- -EFAULT on the unchanged model is accepted.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_destination_is_efault :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- -EMFILE ahead of the copy is accepted too.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem dead_destination_emfile_is_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect (errno_ret EMFILE) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- -ENFILE and -ENOMEM ahead of the copy likewise: the arm draws from
the whole injected set with -EFAULT added, not from -EFAULT and -EMFILE.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem dead_destination_enfile_and_enomem_are_accepted :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
        (mkEffect (errno_ret ENFILE) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
        (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckOk demo_model [] := ⟨rfl, rfl⟩

/-- -EINVAL on the dead destination is rejected: the flag word is zero, so
the one test that answers it passed (:987-988), and no arm after it does.
The wrapping destination has this pin; the dead one lacked it, and an
arm accepting any errno here would have passed every pin above.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2@v6.18.46 -/
theorem dead_destination_einval_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject := by
  rfl

/-- Return 0 with no write on the dead destination is rejected: `do_pipe2`
returns 0 only past a `copy_to_user` that stored all eight bytes (:1040,
:1051), and this one stored none.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_destination_success_without_a_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect 0 [] []) demo_model
      = CheckReject := by
  rfl

/-- The pair on a destination that holds no byte is rejected.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_destination_pair_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- A dead destination is not declined: nothing was stored, so there is no
prefix to leave unstated.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_destination_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      ≠ CheckUnmodeled := by
  rw [dead_destination_is_efault]; exact fun h => nomatch h

/-- -EFAULT beside a write is rejected here: the arm that admits the errno
admits no ledger with it, since nothing was stored.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_destination_efault_with_a_write_is_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [(pipe2_flat_fildes, [3, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- The probe is of the FIRST byte: a destination whose first byte faults
and whose other seven are writable is this case and not the prefix case —
the copy is refused at its first store, so -EFAULT on the unchanged model
is exact…
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem unwritable_first_byte_is_efault :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0
        (fun a => if 4097 ≤ bv_unsigned a ∧ bv_unsigned a < 4104 then some (Z_to_bv 8 0) else none))
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and not declined.  A probe of any byte, or of the last byte instead
of the first, would decline here.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem unwritable_first_byte_is_not_declined :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0
        (fun a => if 4097 ≤ bv_unsigned a ∧ bv_unsigned a < 4104 then some (Z_to_bv 8 0) else none))
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      ≠ CheckUnmodeled := by
  rw [unwritable_first_byte_is_efault]; exact fun h => nomatch h

/-- …and the pair there is rejected, as is -EFAULT beside a write: the
seven writable bytes behind the fault are never reached.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem unwritable_first_byte_pair_and_prefix_are_rejected :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0
        (fun a => if 4097 ≤ bv_unsigned a ∧ bv_unsigned a < 4104 then some (Z_to_bv 8 0) else none))
        (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject
    ∧ check_pipe2_row (pipe2_in pipe2_flat_fildes 0
        (fun a => if 4097 ≤ bv_unsigned a ∧ bv_unsigned a < 4104 then some (Z_to_bv 8 0) else none))
        (mkEffect (errno_ret EFAULT) [(4097, [4, 0, 0, 0])] []) demo_model
      = CheckReject := ⟨rfl, rfl⟩

/-! ## The witness — which outcome it names

`pipe2_witness_ok` says the witness is admitted at every input; what it
cannot say is WHICH admitted outcome the witness names, and a witness
that named -ENFILE, or -EFAULT on the refused range, would pass it
unchanged.  So each pin below reads the outcome off a fixture, through
the row's narrowing: the head of `pipe2_errnos` wherever the spec answers,
-EINVAL on an unaccepted bit, `Unmodeled` exactly where the checker
declines. -/

/-- `pipe2_witness` as the dispatcher applies it: the arguments of
`check_pipe2_row`. -/
def pipe2_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m

/-- On the writable destination the witness names -EMFILE, the head of the
injected set, on the unchanged model: the environment may always refuse
the pair for want of a descriptor (`alloc_fd`, fs/file.c:591-593).
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem witness_names_emfile_on_a_writable_destination :
    pipe2_witness_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model [] := by
  rfl

/-- On the refused range it names -EMFILE too, not the -EFAULT that arm
also admits — and so on a refused range whose bytes below the wrap are
unmapped, where a witness that skipped `access_ok` and read the map would
decline instead.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem witness_names_emfile_on_a_refused_range :
    pipe2_witness_row (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
    ∧ pipe2_witness_row (pipe2_in pipe2_wrap_fildes 0
          (fun a => if 2 ^ 64 - 4 ≤ bv_unsigned a then some (Z_to_bv 8 0) else none)) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model [] := ⟨rfl, rfl⟩

/-- On the dead destination, -EMFILE again.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem witness_names_emfile_on_a_dead_destination :
    pipe2_witness_row (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model [] := by
  rfl

/-- On an unaccepted bit the witness names -EINVAL, `__do_pipe_flags`'
first answer (:987-988).
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem witness_names_einval_on_an_unaccepted_bit :
    pipe2_witness_row (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem) demo_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [] := by
  rfl

/-- The witness declines exactly where the checker declines: an accepted
non-zero flag word, a pipe table binding the next id, a partially
writable destination.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2,create_pipe_files@v6.18.46 -/
theorem witness_declines_where_the_checker_declines :
    pipe2_witness_row (pipe2_in pipe2_flat_fildes 2048 pipe2_flat_mem) demo_model = Unmodeled
    ∧ pipe2_witness_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) aliased_id_model = Unmodeled
    ∧ pipe2_witness_row (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem) demo_model = Unmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- And the checker accepts what the witness offers, on the fixture where
both are stated: the concrete face of `pipe2_witness_ok`.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem the_checker_accepts_the_witness :
    check_pipe2_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
        (mkEffect (errno_ret EMFILE) [] []) demo_model
      = CheckOk demo_model []
    ∧ pipe2_witness_row (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model [] := ⟨rfl, rfl⟩

-- lean-port sentinel: ticket V-Fs-Pipe appends below this line

section V_Fs_Pipe

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Pipe — `pipe2` over the real table

WHAT IS TWINNED HERE.  The sections above state each Rocq example on
`check_pipe2_row`, because `checked_table` carried no row for 59 when they
were written.  This is the registration.  The four examples
`theories/LinuxProcessSem/Checks/Cases/Fs/Pipe.v` states through
`check_syscall` and whose call number is 59 — the file's other 18
`check_syscall` examples name other calls, and the rest of its pipe2
examples are facts about the model with no dispatcher in them, twinned in
`Checks/Cases/Fs/Pipe.lean` — are
restated here through the Lean `check_syscall`, over `checked_table`
itself, at the fixtures the sections above use, under their Rocq names
with `_over_the_real_table` after them, K6b's convention for the pins at
which the real table first answers a call.  Rocq states them at
`init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)`, which is
`demo_model` here.

WHAT A PIN HERE ADDS to its `check_pipe2_row` twin above is the ARM's
claim: that the lookup at 59 finds `arm_pipe2` rather than the
dispatcher's own decline, and that the arm hands the checker `fildes`
whole and the flag word narrowed.  `lookup_pipe2_in` states the first
half for every `pipe2_in` input, and `the_registration_checks_as_the_row`
the second for every input, the arm's checker being `check_pipe2_row`,
whose definition does the handing; so every `check_pipe2_row` verdict
above, each at a `pipe2_in` input, is the table's verdict too, and the two
pins the header names apply other functions.  The narrowing pins restate
the four verdicts that tell the registers apart, so a row that read the
wrong register or narrowed the wrong one fails here by name as well as
there.

EVIDENCE.  `probe:` on the four pins whose statement is an accepted answer
and whose shape a `conform` leg of `pipe2_spec.c` runs — `fresh`,
`wrapfildes`, `flagdrop` and `flagorder` — `model:` on the three that
state the registration itself (`lookup_pipe2_in`,
`the_registration_checks_as_the_row` and
`the_registration_witnesses_as_the_row`), each a fact about
`checked_table` and the row that no kernel or probe reading settles, and
`kernel:` on the other nine.  Three of those nine state the verdict of a
recorded leg: `unaccepted_bit_pair_is_rejected_over_the_real_table` that
of `flagdrop`'s `reject --mutate` leg,
`efault_ahead_of_the_mask_test_is_rejected_over_the_real_table` that of
`flagorder`'s, and `nonblock_is_declined_over_the_real_table` that of the
`fail-closed` leg `nonblock`.  `check_lean_pin_evidence.py` reads a
`= CheckReject` or `= CheckUnmodeled` verdict as positive, so it would
refuse each of those legs as the wrong polarity, for the reason the header
gives.  Each of the other six states an answer no recorded leg gives, or
one to a call no recorded leg makes: a pair across the wrap or at the
32-bit alias, -EFAULT over a writable `fildes`, -EMFILE, or any answer to
a flag word with bit 32 set. -/

/-- The lookup the dispatcher performs on a `pipe2_in`, computed once:
`in_sysno` is `59` whatever the two words and the memory hold, so this is
`rfl` for every input.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_pipe2_in (fildes flags : word) (wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (pipe2_in fildes flags wmem).in_sysno)
      = some arm_pipe2 :=
  rfl

/-- The registered arm's checker is `check_pipe2_row`, at every input, so
every `check_pipe2_row` verdict above is the verdict `arm_pipe2` gives.
Stated as a function equality rather than at a fixture, so that it cannot be
closed by agreeing on one input.
model: two definitions of the same application, compared by unfolding. -/
theorem the_registration_checks_as_the_row : arm_pipe2.ca_check = check_pipe2_row :=
  rfl

/-- …and its witness is `pipe2_witness_row`, likewise.
model: two definitions of the same application, compared by unfolding. -/
theorem the_registration_witnesses_as_the_row : arm_pipe2.ca_witness = pipe2_witness_row :=
  rfl

/-! ### The four Rocq examples, through `check_syscall` -/

/-- `pipe2_wrapping_fildes_rejects_the_pair` over the real table: the
effect a checker walking the map without `access_ok` would accept — return
0 and the pair stored across the wrap — is refused, because
`copy_to_user`'s `access_ok` (`__access_ok`,
include/asm-generic/access_ok.h:31-41, Linux v6.18.46) refuses a range
running off the top of the address space before a byte moves, and
`do_pipe2` then releases both reservations (fs/pipe.c:1041-1045, same
version).
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe2_wrapping_fildes_rejects_the_pair_over_the_real_table :
    check_syscall (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (Z_to_bv 64 0) [(pipe2_wrap_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- `pipe2_wrapping_fildes_is_efault` over the real table: -EFAULT, no
write, the model unchanged — `do_pipe2`'s `error = -EFAULT` at
fs/pipe.c:1045 (Linux v6.18.46), reached with nothing installed.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- wrapfildes -/
theorem pipe2_wrapping_fildes_is_efault_over_the_real_table :
    check_syscall (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- `pipe2_unwrapped_fildes_still_installs_the_pair` over the real table:
on a destination `access_ok` accepts, return 0 with (3, 4) stored as one
8-byte little-endian range at `fildes` is accepted, and the post-state is
`one_pipe_model` — both ends installed (fs/pipe.c:1047-1048, Linux
v6.18.46) at the two lowest free descriptors (`alloc_fd`, fs/file.c:570-613,
same version) and an empty pipe bound.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- fresh -/
theorem pipe2_unwrapped_fildes_still_installs_the_pair_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model [] := by
  rfl

/-- `pipe2_unwrapped_fildes_rejects_efault` over the real table: on the
same destination, which `access_ok` accepts, -EFAULT is refused.  The
model admits -EFAULT only as the answer of the one copy-out in `do_pipe2`
(fs/pipe.c:1040, Linux v6.18.46), and takes a copy into `in_wmem` to
complete.  Linux has an earlier source too, which the model refuses as
its Rocq twin does: `init_file` (fs/file_table.c:180-184, Linux v6.18.46)
returns whatever `security_file_alloc` answers, which a BPF LSM program
may make any errno, as `bpf_lsm_get_retval_range`
(kernel/bpf/bpf_lsm.c:447-467, Linux v6.18.46) allows, and
`create_pipe_files` (fs/pipe.c:944-950, Linux v6.18.46) hands it back
before the copy-out.
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe2_unwrapped_fildes_rejects_efault_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-! ### The mask and the order, through the table -/

/-- `pipe2(fildes, 1 << 30)`: bit 30 is outside `__do_pipe_flags`' mask,
so the answer is -EINVAL at fs/pipe.c:987-988 (Linux v6.18.46), the model
untouched.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- flagdrop -/
theorem unaccepted_bit_einval_is_accepted_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and a pair for that call is a lie: the gate at fs/pipe.c:987-988
(Linux v6.18.46) returns before `create_pipe_files`.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_pair_is_rejected_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 1073741824 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  rfl

/-- An unaccepted bit on a `fildes` with no writable byte is -EINVAL, the
model untouched: the mask is tested at fs/pipe.c:987 and the only access through
`fildes` is `do_pipe2`'s copy-out at :1040 (Linux v6.18.46), so the gate
answers first.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- flagorder -/
theorem unaccepted_bit_beats_an_unwritable_destination_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- …and -EFAULT for that call is a lie: it is the answer of a kernel that
reached the copy-out ahead of the gate.
kernel: fs/pipe.c:__do_pipe_flags,do_pipe2@v6.18.46 -/
theorem efault_ahead_of_the_mask_test_is_rejected_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
      (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := by
  rfl

/-- An accepted non-zero flag word is declined, whatever the answer:
`O_NONBLOCK` passes the gate and changes the files `create_pipe_files`
builds (fs/pipe.c:945 and :956, Linux v6.18.46), which the spec does not
state.
kernel: fs/pipe.c:__do_pipe_flags,create_pipe_files@v6.18.46 -/
theorem nonblock_is_declined_over_the_real_table :
    check_syscall (pipe2_in pipe2_flat_fildes 2048 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckUnmodeled := by
  rfl

/-! ### The registers, through the table

`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` (fs/pipe.c:1054,
Linux v6.18.46): the riscv64 wrapper narrows a1 through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, same version) and hands a0,
a pointer, over whole. -/

/-- a1 = 2^32 is `flags = 0` once narrowed: the pair is accepted, and the
-EINVAL of `__do_pipe_flags`' gate (fs/pipe.c:987-988, Linux v6.18.46) is
refused, since the gate sees 0.  An arm handing the checker the whole
register would accept that -EINVAL instead
(`the_checker_itself_reads_the_whole_word`, above).
kernel: include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,__do_pipe_flags,do_pipe2@v6.18.46 -/
theorem the_table_narrows_flags_to_int :
    check_syscall (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem)
      (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model []
    ∧ check_syscall (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem)
      (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-- a0 above 2^32 reaches the checker whole: over a destination backed at
both `2^32 + 4096` and 4096, the pair at the whole address is accepted and
the pair at the address a narrowing arm would compute is refused.
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem the_table_passes_fildes_whole :
    check_syscall (pipe2_in pipe2_high_fildes 0 pipe2_both_mem)
      (mkEffect 0 [(pipe2_high_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckOk one_pipe_model []
    ∧ check_syscall (pipe2_in pipe2_high_fildes 0 pipe2_both_mem)
      (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 59. -/

/-- A writable destination: the witness names -EMFILE, the head of
`pipe2_errnos` — the environment may always refuse the pair for want of a
descriptor (`alloc_fd`'s `fd >= end`, fs/file.c:591-593, Linux v6.18.46).
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem witness_names_emfile_over_the_real_table :
    syscall_spec_witness (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model [] := by
  rfl

/-- a1 = 2^32 + `O_NONBLOCK` narrows to `O_NONBLOCK`, and the witness
declines, as the checker does.
kernel: include/linux/syscalls.h:__SC_CAST; fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem witness_declines_the_narrowed_nonblock_over_the_real_table :
    syscall_spec_witness (pipe2_in pipe2_flat_fildes 4294969344 pipe2_flat_mem) demo_model
      = Unmodeled := by
  rfl

end V_Fs_Pipe

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Pipe
