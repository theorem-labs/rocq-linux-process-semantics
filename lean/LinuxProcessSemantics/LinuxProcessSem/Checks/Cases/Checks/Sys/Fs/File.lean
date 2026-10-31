import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.File — the dup and dup3 checkers, exercised

Pins over `Checks.Sys.Fs.File`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/File.v` and
`theories/LinuxProcessSem/Checks/Witness/Fs/File.v`.  Not part of the
trusted specification.

WHAT IS UNDER TEST is the ACCEPTOR, not the spec: `Checks/Cases/Fs/File.lean`
already reads `dup_spec` and `dup3_spec` off `fs/file.c` at every arm, and
the eight proofs in the checker's file tie `check_dup` and `check_dup3` to
those specs at every input.  What those proofs cannot say is which
concrete answer the checker gives — a checker that accepted everything
and a spec that admitted everything would satisfy all eight — so each pin
here offers the checker one concrete effect and pins the verdict:
`CheckOk` with the post-model spelled out and no event, `CheckReject`, or
`CheckUnmodeled`.  Every accepting pin is paired with the rejection of a
different return, so that "the model accepts this" is not the vacuous
reading of a checker that accepts everything; that pairing is the shape
Rocq's `theories/LinuxProcessSem/Checks/Cases/Fs/File.v` gives its
thirteen examples, whose conjuncts are the theorems of `LowestFree`,
`FileFdDeclines` and the four dup3 sections, one per conjunct, stated
over `check_dup`/`check_dup3` where Rocq states them over `check_syscall`
— until V-Fs-File registers the arms in `checked_table`, when these
restate over `check_syscall` as Rocq's do.  The `Rocq:` line in each
twin's docstring is the mapping: a `Checks/Cases/Checks/` file has no Rocq
file at its mirrored path, so `check_lean_cases_parity.py` lists it as
unmirrored and it carries no coverage header for that tool to read.  The
file that tool pairs with Rocq's `Checks/Cases/Fs/File.v` is
`Checks/Cases/Fs/File.lean`, and it carries no coverage header either, so
the tool lists it as unclaimed: no register holds Rocq's thirteen examples
to a Lean answer mechanically, and what ties them to these theorems is the
`Rocq:` line in each docstring, checked by review alone (the spec pins'
`rocq-twin:` lines are `check_lean_pin_evidence.py`'s, a name-existence
check).  The spec pins are there; the acceptor-level twins are here.  The
pins over the `CheckedArm` — the
register narrowing, the table finding the arms by their numbers, and the
three conjuncts that only exist THROUGH the dispatcher's `fd32` — `dup`'s
`dup-trunc` (`dup(2^32|2)` is `dup(2)`) and `d3-eq`'s "equal after
truncation" — go with the registration to V-Fs-File (#904).  The FLAGS
truncation is inside `dup3_flags_ok` itself, so `d3-flags-hi` is pinned
here.

The fixtures are `Checks/Cases/Fs/File.lean`'s, imported rather than
copied, so that the spec pins and the checker pins read the same tables:
`dup_model` (three channels, a read-only file at 3, the directory fd at 4,
lowest free 5, fd 9 closed), `dup_model_nofile4` (the same under a soft
RLIMIT_NOFILE of 4), `dup_model_closed0` (fd 0 closed), `dup_filew_model`
(a write-only file at 5), `dup_high_model` (a channel held at 100) and
`dup_kinds_model` (socket 5, pipe ends 6 and 7, /dev/null 8, /dev/urandom
9, lowest free 10).  Every ground pin is `rfl`: the checkers are
executable and the inputs are literals; the lemmas quantifying over `eff`
are `rfl` too, since each decline is decided before the effect is read.
The two -EINTR refusals are stated as `≠ CheckOk m' evs` for every `m'`
and `evs` and closed by `nofun`, because no function on either path
spells that errno for a `kernel:` line and the probe's rejecting case is
the evidence they cite.  The four lemmas of `Witness` that quantify over
the input compose the checker's own theorems instead.  Every kernel line is read at Linux
v6.18.46 (commit 1f99e9ab748f); the citations are the ones the spec pins
carry for the same arm, and the claim each pin adds is about the
checker's answer. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.File

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File

section LowestFree

/-! ## dup installs the copy at the lowest free descriptor

Rocq: `dup_installs_a_copy_at_the_lowest_free_fd`,
`dup_of_a_directory_fd_duplicates`.  The accepted post-model is the table
with the SAME entry consed at the returned descriptor and nothing else
moved, and the event list is empty; the return a kernel can never be made
to give — a free descriptor that is not the lowest, or one the process
holds — is refused.  That the lowest free slot is what `alloc_fd` returns,
and that a freed low slot is taken before a higher free one, is the
`dup_model_closed0` pair. -/

/-- dup(0) on `dup_model`: the copy of channel 0 lands at 5, the lowest
free descriptor, and nothing else changes.  Rocq: the first conjunct of
`dup_installs_a_copy_at_the_lowest_free_fd`.
kernel: fs/file.c:dup,fget_raw,get_unused_fd_flags,alloc_fd,fd_install@v6.18.46 -/
theorem dup_installs_a_copy_at_the_lowest_free_fd :
    check_dup 0 (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (.FdChannel 0)) dup_model) [] := rfl

/-- …and a kernel handing out 6, free but not the lowest, is refused.
Rocq: the second conjunct of `dup_installs_a_copy_at_the_lowest_free_fd`.
kernel: fs/file.c:dup,alloc_fd,find_next_fd@v6.18.46 -/
theorem dup_rejects_a_free_fd_that_is_not_the_lowest :
    check_dup 0 (mkEffect 6 [] []) dup_model = CheckReject := rfl

/-- …and one the process already holds — 2 is a channel — is refused
before the lowest-free test is reached.
kernel: fs/file.c:dup,alloc_fd,fd_install@v6.18.46 -/
theorem dup_rejects_an_fd_the_process_holds :
    check_dup 0 (mkEffect 2 [] []) dup_model = CheckReject := rfl

/-- A directory fd duplicates too: `FdDir` is nullary, so the copy carries
no position that could drift.  Rocq: `dup_of_a_directory_fd_duplicates`.
kernel: fs/file.c:dup,fget_raw,fd_install@v6.18.46 -/
theorem dup_of_a_directory_fd_duplicates :
    check_dup 4 (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 .FdDir) dup_model) [] := rfl

/-- …and lowest-free holds for the directory fd as for a channel.
kernel: fs/file.c:dup,alloc_fd,find_next_fd@v6.18.46 -/
theorem dup_of_a_directory_fd_rejects_a_non_lowest_fd :
    check_dup 4 (mkEffect 6 [] []) dup_model = CheckReject := rfl

/-- After `close(0)` the lowest free descriptor is 0, below every open
one: dup(1) takes slot 0, the probe's `dup-lowest` state.
kernel: fs/file.c:dup,alloc_fd,find_next_fd,__put_unused_fd@v6.18.46 -/
theorem dup_after_close_0_takes_slot_0 :
    check_dup 1 (mkEffect 0 [] []) dup_model_closed0
      = CheckOk (with_fds (fd_insert (m_fds dup_model_closed0) 0 (.FdChannel 1))
          dup_model_closed0) [] := rfl

/-- …and 5, the slot a scan that skipped the freed one would report, is
refused there.
kernel: fs/file.c:dup,alloc_fd,find_next_fd,__put_unused_fd@v6.18.46 -/
theorem dup_after_close_0_rejects_the_next_free_slot :
    check_dup 1 (mkEffect 5 [] []) dup_model_closed0 = CheckReject := rfl

/-- The kinds Rocq's fixture does not hold that dup DOES answer: /dev/null
opened read-write and /dev/urandom both duplicate at 10, `dup_kinds_model`'s
lowest free descriptor.
kernel: fs/file.c:dup,fget_raw,fd_install@v6.18.46 -/
theorem dup_of_devnull_and_urandom_duplicate :
    check_dup 8 (mkEffect 10 [] []) dup_kinds_model
        = CheckOk (with_fds (fd_insert (m_fds dup_kinds_model) 10 (.FdDevNull true true))
            dup_kinds_model) []
    ∧ check_dup 9 (mkEffect 10 [] []) dup_kinds_model
        = CheckOk (with_fds (fd_insert (m_fds dup_kinds_model) 10 .FdUrandom)
            dup_kinds_model) [] := ⟨rfl, rfl⟩

end LowestFree

section FileFdDeclines

/-! ## The offset-sharing gap declines whatever the kernel claims

Rocq: `dup_of_a_file_fd_declines_whatever_the_kernel_claims`.  A probe
pins one claimed return; the lemma pins all of them, which is what makes
it a fail-closed gap rather than a wrong answer: `check_dup` reads the
descriptor's kind before it reads the effect, so `eff` never matters.
The same `∀ eff` covers the kinds the Lean `FdEntry` has that Rocq's
fixture does not — a write-only file, a socket, both pipe ends. -/

/-- dup(3), a read-only FILE fd: `CheckUnmodeled` for every effect the
kernel could claim.  Rocq: `dup_of_a_file_fd_declines_whatever_the_kernel_claims`.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_file_fd_declines_whatever_the_kernel_claims (eff : SyscallEffect) :
    check_dup 3 eff dup_model = CheckUnmodeled := rfl

/-- …a WRITE-ONLY file fd the same, at `dup_filew_model`'s fd 5.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_filew_fd_declines_whatever_the_kernel_claims (eff : SyscallEffect) :
    check_dup 5 eff dup_filew_model = CheckUnmodeled := rfl

/-- …and the socket and both pipe ends of `dup_kinds_model`.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_socket_or_pipe_end_declines_whatever_the_kernel_claims (eff : SyscallEffect) :
    check_dup 5 eff dup_kinds_model = CheckUnmodeled
    ∧ check_dup 6 eff dup_kinds_model = CheckUnmodeled
    ∧ check_dup 7 eff dup_kinds_model = CheckUnmodeled := ⟨rfl, rfl, rfl⟩

end FileFdDeclines

section DupErrnos

/-! ## Which errnos dup may be handed, and which it may not

`dup_errnos` is -ENOMEM and -EMFILE, the table's own, read at Linux
v6.18.46: `alloc_fd`'s `fd >= end` (fs/file.c:591-592), `expand_files`'
`nr >= sysctl_nr_open` (fs/file.c:310-311) and `alloc_fdtable`'s
allocation failure (fs/file.c:242) and lowered-ceiling checks
(fs/file.c:194-197, 212-213).  WHAT THE TWO ACCEPTING PINS DO NOT SAY is
that Linux gives either answer on `dup_model`: it cannot.  Five
descriptors are held and the limit is 1024, so `alloc_fd` finds 5 below
`end`, and `expand_files` returns 0 at `nr < fdt->max_fds` (fs/file.c:299,
Linux v6.18.46) — `max_fds` is never below `NR_OPEN_DEFAULT`
(`init_files`, fs/file.c:534; `dup_fd`, fs/file.c:401; both Linux
v6.18.46) — before any of the failing sites is reached.  The acceptance is the
spec's: `dup_spec` offers `dup_errnos` on every allocating call, whatever
the table, and `check_dup_complete_ok` obliges the checker to accept what
the spec admits.  -EMFILE's undecided condition is the priority-2
divergence bugs/fd-allocation-ignores-rlimit-nofile.md records; -ENOMEM's
is the same admission with no entry of its own.  Everything else a
mutated kernel can hand back is refused: -ENFILE, because dup allocates
no `struct file`; -EBUSY, `do_dup2`'s errno, not on dup's path; -EINTR,
because nothing on the path sleeps interruptibly; -EBADF on an OPEN
descriptor, because validity is tracked, never injected.  And a CLOSED
descriptor is -EBADF before the table is consulted, so the table's errnos
are refused there — `fget_raw` runs before `get_unused_fd_flags`. -/

/-- The `alloc_fdtable` failure, accepted with the model unchanged — an
answer the spec admits here and Linux does not give on this table (the
section header says why): the pin fixes what the acceptor does with the
spec's admission, not a kernel answer on `dup_model`.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_accepts_enomem :
    check_dup 0 (mkEffect (errno_ret ENOMEM) [] []) dup_model = CheckOk dup_model [] := rfl

/-- The RLIMIT_NOFILE failure, accepted with the model unchanged — with
fd 5 under a limit of 1024, again the spec's admission and not Linux's
answer on this table; where the limit really bites is `Dup3Limit`'s
`dup_above_the_soft_limit_admits_the_slot_at_the_acceptor`.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem dup_accepts_emfile :
    check_dup 0 (mkEffect (errno_ret EMFILE) [] []) dup_model = CheckOk dup_model [] := rfl

/-- -ENFILE is the system-wide open-file limit, `alloc_empty_file`'s;
dup takes a second reference to an existing `struct file` and never
reaches it.
kernel: fs/file.c:dup,fget_raw; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem dup_rejects_enfile :
    check_dup 0 (mkEffect (errno_ret ENFILE) [] []) dup_model = CheckReject := rfl

/-- -EBUSY is `do_dup2`'s, on dup3's path, not dup's.
kernel: fs/file.c:dup,do_dup2@v6.18.46 -/
theorem dup_rejects_ebusy :
    check_dup 0 (mkEffect (errno_ret EBUSY) [] []) dup_model = CheckReject := rfl

/-- -EINTR is not accepted with any post-model: nothing between
`fget_raw` and `fd_install` sleeps interruptibly, and no function on the
path spells the errno — which is why this pin cites the probe's
rejecting case rather than a kernel site, and is stated as the refusal
of every `CheckOk` rather than as `CheckReject`.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=-EINTR -- dup-inject -/
theorem dup_rejects_eintr (m' : Model) (evs : List event) :
    check_dup 0 (mkEffect (errno_ret EINTR) [] []) dup_model ≠ CheckOk m' evs := nofun

/-- -EBADF on an OPEN descriptor: the model holds fd 0, so a kernel
claiming `fget_raw` found nothing is lying.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_rejects_ebadf_on_an_open_fd :
    check_dup 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := rfl

/-- A CLOSED descriptor is -EBADF, with the model unchanged.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_of_a_closed_fd_is_ebadf :
    check_dup 9 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model [] := rfl

/-- …and a kernel claiming it duplicated a closed descriptor is refused.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_of_a_closed_fd_rejects_success :
    check_dup 9 (mkEffect 5 [] []) dup_model = CheckReject := rfl

/-- …as is the table's -EMFILE there: `fget_raw` runs BEFORE
`get_unused_fd_flags`, so a bad descriptor never reaches a table that
could fail to grow.
kernel: fs/file.c:dup,fget_raw,get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem dup_of_a_closed_fd_rejects_emfile :
    check_dup 9 (mkEffect (errno_ret EMFILE) [] []) dup_model = CheckReject := rfl

/-- …and -ENOMEM.
kernel: fs/file.c:dup,fget_raw,get_unused_fd_flags,alloc_fdtable@v6.18.46 -/
theorem dup_of_a_closed_fd_rejects_enomem :
    check_dup 9 (mkEffect (errno_ret ENOMEM) [] []) dup_model = CheckReject := rfl

end DupErrnos

section EveryArmIsRetOnly

/-! ## Every accepting arm is a bare return, on every ledger

`dup` and `dup3` write no user memory and read none, so an effect
carrying a write, a zero-filled range, an unmapped range, a copy or a
copy-in is not one of theirs, whatever its return: the allocating
acceptor matches `mkEffectU ret [] [] [] [] []` and nothing else, and the
gates are `check_ret_only`.  Each of the five ledgers is refused on the
allocating arm, and each ARM — the allocator's two branches, dup's -EBADF
gate, dup3's four gates, its install and its replacement — refuses at
least one, so that a rewrite reading the return before the ledgers on
any one of them fails here. -/

/-- dup's allocating arm refuses a write beside the right return.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_effect_with_a_write_rejected :
    check_dup 0 (mkEffect 5 [(0x10000, [0])] []) dup_model = CheckReject := rfl

/-- …a zero-filled range…
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_effect_with_a_zero_range_rejected :
    check_dup 0 (mkEffect 5 [] [(0x10000, 16)]) dup_model = CheckReject := rfl

/-- …and a copy-in.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_effect_with_a_copyin_rejected :
    check_dup 0 (with_copyins [(0x10000, 4)] (mkEffect 5 [] [])) dup_model = CheckReject := rfl

/-- …an unmapped range…
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_effect_with_an_unmap_rejected :
    check_dup 0 (SyscallEffect.mkEffectU 5 [] [] [(0x10000, 4096)] [] []) dup_model
      = CheckReject := rfl

/-- …and a copy: the fourth and fifth ledgers, which `mkEffect` cannot
spell and no other pin here reaches.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_effect_with_a_copy_rejected :
    check_dup 0 (SyscallEffect.mkEffectU 5 [] [] [] [MemCopy.mkCopy 0x10000 0x11000 16] [])
      dup_model = CheckReject := rfl

/-- The errno-accepting branch refuses a write beside an errno it admits:
the ledgers are matched before the errno set is consulted, so an acceptor
that tested `errno_ret_in` first and returned `CheckOk` on the errno alone
would pass every other pin of `DupErrnos` and fail here.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_enomem_with_a_write_rejected :
    check_dup 0 (mkEffect (errno_ret ENOMEM) [(0x10000, [0])] []) dup_model = CheckReject := rfl

/-- dup's -EBADF gate refuses a write beside the right errno.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_ebadf_arm_rejects_a_write :
    check_dup 9 (mkEffect (errno_ret EBADF) [(0x10000, [0])] []) dup_model = CheckReject := rfl

/-- dup3's replacing arm refuses a write beside the right return.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_effect_with_a_write_rejected :
    check_dup3 0 1 0 (mkEffect 1 [(0x10000, [0])] []) dup_model = CheckReject := rfl

/-- …and a copy-in.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_effect_with_a_copyin_rejected :
    check_dup3 0 1 0 (with_copyins [(0x10000, 4)] (mkEffect 1 [] [])) dup_model
      = CheckReject := rfl

/-- …an unmapped range and a copy.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_effect_with_an_unmap_or_a_copy_rejected :
    check_dup3 0 1 0 (SyscallEffect.mkEffectU 1 [] [] [(0x10000, 4096)] [] []) dup_model
      = CheckReject
    ∧ check_dup3 0 1 0 (SyscallEffect.mkEffectU 1 [] [] [] [MemCopy.mkCopy 0x10000 0x11000 16] [])
        dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The free-`newfd` install refuses a write beside the right return.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_install_rejects_a_write :
    check_dup3 0 7 0 (mkEffect 7 [(0x10000, [0])] []) dup_model = CheckReject := rfl

/-- dup3's flag gate, limit gate and closed-`oldfd` gate each refuse a
write beside the errno they answer.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_gates_reject_a_write :
    check_dup3 0 1 4 (mkEffect (errno_ret EINVAL) [(0x10000, [0])] []) dup_model = CheckReject
    ∧ check_dup3 0 2000 0 (mkEffect (errno_ret EBADF) [(0x10000, [0])] []) dup_model = CheckReject
    ∧ check_dup3 9 1 0 (mkEffect (errno_ret EBADF) [(0x10000, [0])] []) dup_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- dup3's -EINVAL gate refuses a zero-filled range beside the right errno.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_einval_arm_rejects_a_zero_range :
    check_dup3 3 3 0 (mkEffect (errno_ret EINVAL) [] [(0x10000, 16)]) dup_model
      = CheckReject := rfl

end EveryArmIsRetOnly

section Dup3Replaces

/-! ## dup3 returns the descriptor it was given, replacing what was there

Rocq: `dup3_replaces_the_target_and_returns_it`,
`dup3_ignores_o_cloexec_but_not_another_bit`.  fd 1 stops naming channel
1 and names channel 0 — the entry moved is model-internal state no return
reveals, and the `CheckOk` post-model is the whole of it.  O_CLOEXEC
(524288) leaves the same state as flags 0; any other bit is `ksys_dup3`'s
-EINVAL, before anything else. -/

/-- dup3(0, 1, 0): 1, with channel 0's entry installed at 1.  Rocq: the
first conjunct of `dup3_replaces_the_target_and_returns_it`.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_replaces_the_target_and_returns_it :
    check_dup3 0 1 0 (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model) [] := rfl

/-- …and 5, the descriptor `dup` would have answered, is refused: the
given `newfd` is the only admissible return.  Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_rejects_the_lowest_free_fd :
    check_dup3 0 1 0 (mkEffect 5 [] []) dup_model = CheckReject := rfl

/-- O_CLOEXEC is accepted and leaves the same state as flags 0.  Rocq: the
first conjunct of `dup3_ignores_o_cloexec_but_not_another_bit`.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_ignores_o_cloexec :
    check_dup3 0 1 524288 (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model) [] := rfl

/-- …but another bit is -EINVAL, so claiming the successful return there
is refused.  Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_does_not_ignore_another_bit :
    check_dup3 0 1 4 (mkEffect 1 [] []) dup_model = CheckReject := rfl

/-- …and the -EINVAL is what is accepted there, with the model unchanged.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_bit_is_einval :
    check_dup3 0 1 4 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model [] := rfl

/-- O_CLOEXEC BESIDE another bit (524289) is -EINVAL too, and the
replacement is refused there: the test is `flags & ~O_CLOEXEC`, not
"flags is O_CLOEXEC or zero" — a predicate accepting exactly {0,
O_CLOEXEC} would pass every other flags pin of this file and fail here.
The probe's `d3-flags` third call.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_o_cloexec_beside_another_bit_is_einval :
    check_dup3 0 1 524289 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 0 1 524289 (mkEffect 1 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The high half of `flags` is discarded — `dup3(2, 1, 2^32)` is 1 — since
`dup3_flags_ok` tests the truncated word; the probe's `d3-flags-hi`.
kernel: fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_discards_the_high_half_of_flags :
    check_dup3 2 1 (Z_to_bv 64 4294967296) (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 2)) dup_model) [] := rfl

/-- …and -EINVAL is refused there.
kernel: fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_high_flags_rejects_einval :
    check_dup3 2 1 (Z_to_bv 64 4294967296) (mkEffect (errno_ret EINVAL) [] []) dup_model
      = CheckReject := rfl

/-- The errnos no dup3 arm admits: -ENOMEM (no table growth is needed for
an open `newfd`), -EMFILE (which `ksys_dup3` would have rewritten to
-EBADF anyway), -EBUSY (`do_dup2`'s, needing a second thread), and
-EBADF with both descriptors open.
kernel: fs/file.c:ksys_dup3,expand_files,alloc_fdtable,do_dup2@v6.18.46 -/
theorem dup3_rejects_every_injected_errno :
    check_dup3 0 1 0 (mkEffect (errno_ret ENOMEM) [] []) dup_model = CheckReject
    ∧ check_dup3 0 1 0 (mkEffect (errno_ret EMFILE) [] []) dup_model = CheckReject
    ∧ check_dup3 0 1 0 (mkEffect (errno_ret EBUSY) [] []) dup_model = CheckReject
    ∧ check_dup3 0 1 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and -EINTR, which no function on the path spells: stated as the
refusal of every `CheckOk`, on the probe's rejecting case.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINTR -- d3-basic -/
theorem dup3_rejects_eintr (m' : Model) (evs : List event) :
    check_dup3 0 1 0 (mkEffect (errno_ret EINTR) [] []) dup_model ≠ CheckOk m' evs := nofun

/-- A directory fd installed at 1: the entry is `FdDir`, the probe's
`d3-dir`.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_installs_a_directory_fd :
    check_dup3 4 1 0 (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 .FdDir) dup_model) [] := rfl

end Dup3Replaces

section Dup3Order

/-! ## The order of `ksys_dup3`'s gates, at the acceptor

Rocq: `dup3_eq_beats_the_file_fd_decline`,
`dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup`, and the closed
`oldfd` the probe's `d3-badold` reaches.  Which gate answers first is as
much a part of the syscall as its return: equality is -EINVAL before the
kind of the descriptor is read, the limit is -EBADF before `oldfd` is
looked up, and a FILE `oldfd` — the kind dup declines — is reached only
once those have passed. -/

/-- dup3(3, 3, 0) on a FILE fd is -EINVAL, not a decline: equality is
tested before every kind test.  Rocq: the first conjunct of
`dup3_eq_beats_the_file_fd_decline`.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_beats_the_file_fd_decline :
    check_dup3 3 3 0 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model [] := rfl

/-- …and dup2's answer there — `newfd` itself — is refused: dup3 is not
dup2.  Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3,dup2@v6.18.46 -/
theorem dup3_eq_rejects_dup2s_answer :
    check_dup3 3 3 0 (mkEffect 3 [] []) dup_model = CheckReject := rfl

/-- …and -EBADF, which a model testing `oldfd` first would give for a
CLOSED pair — 9 is closed — is refused there, where -EINVAL is what is
accepted: the equality test reads neither descriptor.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_rejects_ebadf :
    check_dup3 9 9 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject
    ∧ check_dup3 9 9 0 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model [] :=
  ⟨rfl, rfl⟩

/-- …and for the OPEN pair 3, 3, where -EBADF has no source at all.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_on_an_open_pair_rejects_ebadf :
    check_dup3 3 3 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := rfl

/-- Equality is tested before the limit: dup3(2000, 2000, 0), both past
`State.default_nofile`, and dup3(2^31, 2^31, 0), the probe's `d3-eq`
huge pair, are -EINVAL and not the limit's -EBADF.  Move the limit gate
ahead of the equality test and all four conjuncts flip; no other pin of
this file has an equal pair at or past the limit.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_beats_the_limit :
    check_dup3 2000 2000 0 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 2000 2000 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject
    ∧ check_dup3 2147483648 2147483648 0 (mkEffect (errno_ret EINVAL) [] []) dup_model
        = CheckOk dup_model []
    ∧ check_dup3 2147483648 2147483648 0 (mkEffect (errno_ret EBADF) [] []) dup_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- dup3(0, 0, 0), the lowest pair: -EINVAL, and the replacement — 0,
which a dup2 would answer — refused.
kernel: fs/file.c:ksys_dup3,dup2@v6.18.46 -/
theorem dup3_eq_at_fd_0_is_einval :
    check_dup3 0 0 0 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 0 0 0 (mkEffect 0 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The flag test precedes the free-`newfd` decline and the `oldfd`
lookup: dup3(2, 999, 1) — 999 free and at or above `NR_OPEN_DEFAULT`,
which would be `CheckUnmodeled` — and dup3(999, 1, 1) — 999 closed, which
would be -EBADF — are both -EINVAL.  999 is UNDER the limit of 1024, so
this pin says nothing about the limit gate; the next one does.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_beats_the_free_newfd_decline_and_the_lookup :
    check_dup3 2 999 1 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 999 1 1 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 2 999 1 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject
    ∧ check_dup3 999 1 1 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The flag test precedes the limit gate: dup3(0, 2000, 4), `newfd` past
`State.default_nofile` with a bad flag bit, is -EINVAL and not the limit's
-EBADF.  Move the limit gate ahead of the flag test and both conjuncts
flip.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_beats_the_limit :
    check_dup3 0 2000 4 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 0 2000 4 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- `newfd` past the limit is -EBADF, with `oldfd` open.  Rocq: the first
conjunct of `dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup`; 2000
is above `State.default_nofile`.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_is_ebadf :
    check_dup3 0 2000 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model [] := rfl

/-- …and with a FILE `oldfd`, whose kind the model refuses to duplicate:
still -EBADF, because the limit gate answers before the lookup.  Reorder
the checker to test the kind first and this turns into `CheckUnmodeled`.
Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup :
    check_dup3 3 2000 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model [] := rfl

/-- …and nothing succeeds past the limit.  Rocq: the third conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_rejects_success :
    check_dup3 0 2000 0 (mkEffect 2000 [] []) dup_model = CheckReject := rfl

/-- …nor is -EMFILE the answer there: the gate is -EBADF outright, and
`expand_files`' -EMFILE never surfaces.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_over_the_limit_rejects_emfile :
    check_dup3 0 2000 0 (mkEffect (errno_ret EMFILE) [] []) dup_model = CheckReject := rfl

/-- A closed `oldfd` under the limit is -EBADF, with the model unchanged;
the probe's `d3-badold`.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_closed_oldfd_is_ebadf :
    check_dup3 9 1 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model [] := rfl

/-- …and cannot succeed, nor be -EINVAL, nor -ENOMEM: `expand_files` runs
first but its error is read AFTER the lookup.
kernel: fs/file.c:ksys_dup3,expand_files,alloc_fdtable@v6.18.46 -/
theorem dup3_closed_oldfd_rejects_success_einval_and_enomem :
    check_dup3 9 1 0 (mkEffect 1 [] []) dup_model = CheckReject
    ∧ check_dup3 9 1 0 (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckReject
    ∧ check_dup3 9 1 0 (mkEffect (errno_ret ENOMEM) [] []) dup_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- A closed `oldfd` is -EBADF before the free-`newfd` decline: dup3(9,
100, 0), onto a free 100 at or above `NR_OPEN_DEFAULT`, is -EBADF with
the model kept and not `CheckUnmodeled` — the lookup finding nothing goes
to `Ebadf` (:1416-1418, :1426-1427) before `expand_files`' result is
read, whatever the table would have had to do for 100.  fd 1 in the pins
above is HELD, so this is the only closed-`oldfd` pin whose `newfd` the
decline could have claimed.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_closed_oldfd_beats_the_free_newfd_decline :
    check_dup3 9 100 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 9 100 0 (mkEffect 100 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- A FILE `oldfd` that passes the three gates declines whatever the
kernel claims, as dup's does: the offset-sharing gap, reached only after
the gates have answered.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_of_a_file_oldfd_declines_whatever_the_kernel_claims (eff : SyscallEffect) :
    check_dup3 3 1 0 eff dup_model = CheckUnmodeled := rfl

end Dup3Order

section Dup3FreeNewfd

/-! ## A free `newfd`: installed below the embedded table, declined at it

Rocq: `dup3_takes_a_free_newfd_below_the_embedded_table`,
`dup3_declines_a_free_newfd_above_the_embedded_table`,
`dup3_free_newfd_just_below_the_embedded_table`,
`dup3_declines_a_free_newfd_at_the_embedded_table`.  Below
`NR_OPEN_DEFAULT` (64) the copy is installed at the number given, not at
the lowest free one — the difference between dup3 and dup.  At or above
it, a FREE `newfd` is declined for every claimed return: Linux decides it
out of the table's current `max_fds` and the `nr_open` sysctl, neither of
which the model carries.  A HELD `newfd` above it is `do_dup2`'s
replacement and needs no growth, so `dup_high_model`'s fd 100 is
answered. -/

/-- dup3(0, 7, 0): 7, installed at the number given.  Rocq: the first
conjunct of `dup3_takes_a_free_newfd_below_the_embedded_table`.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_takes_a_free_newfd_below_the_embedded_table :
    check_dup3 0 7 0 (mkEffect 7 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 7 (.FdChannel 0)) dup_model) [] := rfl

/-- …and 5, the lowest free descriptor, is refused: dup3 is not dup.
Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_rejects_the_lowest_free_fd :
    check_dup3 0 7 0 (mkEffect 5 [] []) dup_model = CheckReject := rfl

/-- A free `newfd` at 100 is declined for every effect.  Rocq:
`dup3_declines_a_free_newfd_above_the_embedded_table`.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_declines_a_free_newfd_above_the_embedded_table (eff : SyscallEffect) :
    check_dup3 0 100 0 eff dup_model = CheckUnmodeled := rfl

/-- 63, adjacent to the bound from below, is answered.  Rocq:
`dup3_free_newfd_just_below_the_embedded_table`.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_just_below_the_embedded_table :
    check_dup3 0 63 0 (mkEffect 63 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 63 (.FdChannel 0)) dup_model) [] := rfl

/-- …and 64, the bound itself, is declined for every effect: the
comparison is strict, and an off-by-one in it would pass every other pin.
Rocq: `dup3_declines_a_free_newfd_at_the_embedded_table`.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_declines_a_free_newfd_at_the_embedded_table (eff : SyscallEffect) :
    check_dup3 0 64 0 eff dup_model = CheckUnmodeled := rfl

/-- A HELD `newfd` above the bound is answered: `dup_high_model` holds a
channel at 100, and dup3 onto it is `do_dup2`'s replacement, no growth
needed.  The pair with the decline above is what makes the free/held
distinction a distinction rather than a dead branch.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_onto_a_held_newfd_above_the_embedded_table_is_answered :
    check_dup3 0 100 0 (mkEffect 100 [] []) dup_high_model
      = CheckOk (with_fds (fd_insert (m_fds dup_high_model) 100 (.FdChannel 0))
          dup_high_model) [] := rfl

/-- …and -EBADF is refused there: 100 is under the limit and `oldfd` is
open.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_onto_a_held_newfd_above_the_embedded_table_rejects_ebadf :
    check_dup3 0 100 0 (mkEffect (errno_ret EBADF) [] []) dup_high_model = CheckReject := rfl

end Dup3FreeNewfd

section Dup3Limit

/-! ## The limit is read from the run

Rocq: `dup3_free_newfd_is_decided_by_the_run_s_limit`,
`dup3_limit_beats_an_fd_the_process_holds`.  The same input against
`dup_model` and `dup_model_nofile4` — same descriptors, soft RLIMIT_NOFILE
1024 against 4 — so only the limit can separate the answers: replace
`dup3_newfd_under_limit`'s `m_nofile m` with any constant and one side
breaks.  The comparison is strict: fd 4, held and AT the limit, is
-EBADF; fd 3, held and under it, is the ordinary replacement. -/

/-- Under the default limit a free 5 is installed.  Rocq: the first
conjunct of `dup3_free_newfd_is_decided_by_the_run_s_limit`.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_under_the_default_limit_is_installed :
    check_dup3 0 5 0 (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (.FdChannel 0)) dup_model) [] := rfl

/-- …and under a limit of 4 the same call is -EBADF, the model unchanged.
Rocq: the second conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_under_a_limit_of_4_is_ebadf :
    check_dup3 0 5 0 (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
      = CheckOk dup_model_nofile4 [] := rfl

/-- …and the install is refused there.  Rocq: the third conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_under_a_limit_of_4_rejects_success :
    check_dup3 0 5 0 (mkEffect 5 [] []) dup_model_nofile4 = CheckReject := rfl

/-- fd 3, held and under the limit of 4, is the ordinary replacement.
Rocq: the first conjunct of `dup3_limit_beats_an_fd_the_process_holds`.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_held_newfd_under_the_limit_is_replaced :
    check_dup3 0 3 0 (mkEffect 3 [] []) dup_model_nofile4
      = CheckOk (with_fds (fd_insert (m_fds dup_model_nofile4) 3 (.FdChannel 0))
          dup_model_nofile4) [] := rfl

/-- fd 4, held and AT the limit, is -EBADF: the gate beats the descriptor
the process holds, and the comparison is strict.  Rocq: the second
conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_limit_beats_an_fd_the_process_holds :
    check_dup3 0 4 0 (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
      = CheckOk dup_model_nofile4 [] := rfl

/-- …and the replacement a spec that only looked the fd up would return
is refused.  Rocq: the third conjunct.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_limit_rejects_the_replacement :
    check_dup3 0 4 0 (mkEffect 4 [] []) dup_model_nofile4 = CheckReject := rfl

/-- The default limit's own edge, on `dup_model`: 1023, free and under
1024, passes the gate and is declined at the embedded-table test; 1024,
AT it, is -EBADF, and the install there is refused.  The 2000 pins above
and the limit-of-4 pins are both far from 1024, so a `<=` in
`dup3_newfd_under_limit` read against the default limit is caught here
and nowhere else in this file.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_default_limit_edge :
    check_dup3 0 1023 0 (mkEffect 1023 [] []) dup_model = CheckUnmodeled
    ∧ check_dup3 0 1024 0 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 0 1024 0 (mkEffect 1024 [] []) dup_model = CheckReject := ⟨rfl, rfl, rfl⟩

/-- WHERE THE ALLOCATOR'S DIVERGENCE REACHES THE ACCEPTOR, stated so it is
visible: under a soft limit of 4 with fds 0-4 held, Linux answers dup(2)
with -EMFILE and nothing else — `alloc_fd`'s `fd >= end` (fs/file.c:591-592)
with `end = rlimit(RLIMIT_NOFILE)` from `__get_unused_fd_flags`
(fs/file.c:615-618) — while the model's `State.alloc_fd` reads no limit,
so `check_dup` admits the copy at 5 as well.  That is the priority-2
divergence bugs/fd-allocation-ignores-rlimit-nofile.md records, whose
spec-level twin is `Checks/Cases/Fs/File.lean`'s
`dup_above_the_soft_limit_still_admits_the_slot`: the kernel's own answer
is admitted, beside one it never gives.  dup3 has no such gap — its limit
gate is `Dup3Limit`'s, pinned on both sides above.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd@v6.18.46 -/
theorem dup_above_the_soft_limit_admits_the_slot_at_the_acceptor :
    check_dup 2 (mkEffect (errno_ret EMFILE) [] []) dup_model_nofile4
      = CheckOk dup_model_nofile4 []
    ∧ check_dup 2 (mkEffect 5 [] []) dup_model_nofile4
        = CheckOk (with_fds (fd_insert (m_fds dup_model_nofile4) 5 (.FdChannel 2))
            dup_model_nofile4) [] := ⟨rfl, rfl⟩

end Dup3Limit

section Witness

/-! ## The witness is the outcome the checker accepts

`dup_witness` and `dup3_witness` are one admitted outcome per input, as
data.  `dup_witness_ok`/`dup3_witness_ok` put each in its spec, and
the checkers' completeness theorems carry them to the checkers, so each
checker accepts its witness at every input and declines exactly where it
is `Unmodeled` — the two quantified lemmas at the end compose those
theorems.  What they cannot say is WHICH outcome the witness computes: a
witness that answered 0 on every arm is one the `_ok` lemma would still
prove, were the spec wrong the same way.  So the ground pins name it, one
per arm.  dup's witness takes the environment-failure branch, so its
answer on a modeled descriptor is -ENOMEM (`witness_errno`), never the
allocated descriptor; dup3's is the deterministic answer of each arm. -/

/-- dup's witness on an open channel: -ENOMEM, the `alloc_fdtable`
failure, with the model unchanged — the spec's admitted outcome, which
Linux does not give on this table (`DupErrnos`' header says why).
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_witness_on_a_channel_is_enomem :
    dup_witness 0 dup_model = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model [] := rfl

/-- …on a closed descriptor: -EBADF.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_witness_on_a_closed_fd_is_ebadf :
    dup_witness 9 dup_model = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := rfl

/-- …and on a file descriptor `Unmodeled`, the outcome the spec admits
there.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_witness_on_a_file_fd_is_unmodeled :
    dup_witness 3 dup_model = Unmodeled := rfl

/-- dup3's witness on an open `newfd`: the replacement, at the number
given.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_witness_replaces :
    dup3_witness 0 1 0 dup_model
      = Ok (mkEffect 1 [] []) (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model)
          [] := rfl

/-- …on a free `newfd` below the embedded table: installed at 7.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_witness_installs_a_free_newfd :
    dup3_witness 0 7 0 dup_model
      = Ok (mkEffect 7 [] []) (with_fds (fd_insert (m_fds dup_model) 7 (.FdChannel 0)) dup_model)
          [] := rfl

/-- …the equal pair: -EINVAL.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_witness_on_an_equal_pair_is_einval :
    dup3_witness 3 3 0 dup_model = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := rfl

/-- …past the limit: -EBADF.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_witness_over_the_limit_is_ebadf :
    dup3_witness 0 2000 0 dup_model = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := rfl

/-- …an equal pair past the limit: -EINVAL, the equality test first.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_witness_eq_beats_the_limit :
    dup3_witness 2000 2000 0 dup_model = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] :=
  rfl

/-- …a bad flag bit: -EINVAL; and a closed `oldfd`: -EBADF.  The two gate
answers no other witness pin names: without them a witness answering 0
on either arm would still satisfy `dup3_witness_ok` were the spec wrong
the same way.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_witness_on_a_bad_flag_or_a_closed_oldfd :
    dup3_witness 0 1 4 dup_model = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model []
    ∧ dup3_witness 9 1 0 dup_model = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] :=
  ⟨rfl, rfl⟩

/-- …63, adjacent to the embedded-table bound from below: installed,
where 64 (next) is `Unmodeled`, so the witness's bound is the checker's
and a shift of it by one in either direction fails here or there.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_witness_installs_just_below_the_embedded_table :
    dup3_witness 0 63 0 dup_model
      = Ok (mkEffect 63 [] []) (with_fds (fd_insert (m_fds dup_model) 63 (.FdChannel 0)) dup_model)
          [] := rfl

/-- …and on a free `newfd` at or above the embedded table, or a file
`oldfd` (the shared-offset gap `do_dup2`'s replacement would open),
`Unmodeled`.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_witness_declines_where_the_checker_does :
    dup3_witness 0 100 0 dup_model = Unmodeled ∧ dup3_witness 0 64 0 dup_model = Unmodeled
    ∧ dup3_witness 3 1 0 dup_model = Unmodeled := ⟨rfl, rfl, rfl⟩

/-- Wherever dup's witness is an outcome, the checker accepts exactly that
outcome: `dup_witness_ok` puts it in the spec and `check_dup_complete_ok`
carries it to the checker.
model: composes `dup_witness_ok` with `check_dup_complete_ok`; the ground pins above say which outcome -/
theorem dup_witness_is_accepted (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (hw : dup_witness oldfd m = Ok eff m' evs) :
    check_dup oldfd eff m = CheckOk m' evs := by
  have h := dup_witness_ok oldfd i m
  rw [hw] at h
  exact check_dup_complete_ok oldfd eff m m' evs i h

/-- …and wherever it is `Unmodeled`, the checker declines whatever effect
it is shown.
model: composes `dup_witness_ok` with `check_dup_complete_unmodeled`; the ground pins above say where -/
theorem dup_witness_decline_is_the_checkers (oldfd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (hw : dup_witness oldfd m = Unmodeled) :
    check_dup oldfd eff m = CheckUnmodeled := by
  have h := dup_witness_ok oldfd i m
  rw [hw] at h
  exact check_dup_complete_unmodeled oldfd m i eff h

/-- The same for dup3's witness.
model: composes `dup3_witness_ok` with `check_dup3_complete_ok`; the ground pins above say which outcome -/
theorem dup3_witness_is_accepted (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (hw : dup3_witness oldfd newfd flags m = Ok eff m' evs) :
    check_dup3 oldfd newfd flags eff m = CheckOk m' evs := by
  have h := dup3_witness_ok oldfd newfd flags i m
  rw [hw] at h
  exact check_dup3_complete_ok oldfd newfd flags eff m m' evs i h

/-- …and its declines.
model: composes `dup3_witness_ok` with `check_dup3_complete_unmodeled`; the ground pins above say where -/
theorem dup3_witness_decline_is_the_checkers (oldfd newfd flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput) (hw : dup3_witness oldfd newfd flags m = Unmodeled) :
    check_dup3 oldfd newfd flags eff m = CheckUnmodeled := by
  have h := dup3_witness_ok oldfd newfd flags i m
  rw [hw] at h
  exact check_dup3_complete_unmodeled oldfd newfd flags m i eff h

end Witness

-- lean-port sentinel: ticket V-Fs-File appends below this line

section V_Fs_File

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

/-! ## V-Fs-File — `dup` and `dup3` over the real table

WHAT IS TWINNED HERE.  The sections above state Rocq's thirteen examples
on the checkers themselves, because `checked_table` carried no row for 23
or 24 when they were written.  This is the registration
(`Checks/Arms/Fs/File.lean`), and each example
`theories/LinuxProcessSem/Checks/Cases/Fs/File.v` states through
`check_syscall` is restated here through the Lean `check_syscall`, over
`checked_table` itself, at Rocq's own input — `mkInput 23` or
`mkInput 24` with the descriptors in `a0` and `a1` and the flag word in
`a2` — under its Rocq name with `_over_the_real_table` after it, the
convention of the pins at which the real table first answers a call.

WHAT A PIN HERE ADDS to its checker-level twin above is the ARM's claim:
that the lookup at 23 and 24 finds `arm_dup` and `arm_dup3` rather than
the dispatcher's own decline, and that each arm hands its checker
`fd32` of `a0` (and of `a1`) — the low 32 bits — and `a2` whole.  The
thirteen examples use descriptors below 2^32, where `fd32` is the
identity, so they fix the first claim and not the second; the narrowing
section below fixes the second, with the conjuncts the section header of
this file sends here — `dup-trunc`'s `dup(2^32|2)` is `dup(2)` and
`d3-eq`'s equal-after-truncation — and one input per register that
separates a narrowing arm from one handing the checker the whole word,
beside the pins that fix the checker itself as reading the whole word, so
that where the narrowing lives is fixed from both sides.

POLARITY is the sections' above: the evidence line is `kernel:` or
`probe:` on every pin about the kernel's answer, `CheckOk` and
`CheckReject` alike, and `model:` on a pin about the table's contents or
the checker's contract with the arm.  Every kernel line is Linux v6.18.46
(commit 1f99e9ab748f).  The arm, checker and witness are executable, the inputs are literals,
and the declines quantified over the effect are decided before the
effect is read.  The uniqueness pair at the end is `decide` over a
closed descriptor list. -/

/-! ### The lookups -/

/-- The dispatcher's lookup on any syscall-23 input finds `arm_dup`,
whatever the argument registers and memory hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim -/
theorem lookup_dup_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 23 args mem wmem).in_sysno)
      = some arm_dup :=
  lookup_ca_checked_table_dup

/-- …and on any syscall-24 input, `arm_dup3`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim -/
theorem lookup_dup3_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 24 args mem wmem).in_sysno)
      = some arm_dup3 :=
  lookup_ca_checked_table_dup3

/-! ### Rocq's thirteen examples, through `check_syscall` -/

/-- `dup_installs_a_copy_at_the_lowest_free_fd` over the real table:
`dup(0)` binds a copy of channel 0 at 5, `dup_model`'s lowest free
descriptor, which is what `get_unused_fd_flags` → `alloc_fd`
(fs/file.c:570-613, Linux v6.18.46) hands out and `fd_install`
(fs/file.c:652-677) fills; 6, free but not the lowest, is refused.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,find_next_fd,fd_install@v6.18.46 -/
theorem dup_installs_a_copy_at_the_lowest_free_fd_over_the_real_table :
    check_syscall (SyscallInput.mkInput 23 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (.FdChannel 0)) dup_model) []
    ∧ check_syscall (SyscallInput.mkInput 23 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 6 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup_of_a_directory_fd_duplicates` over the real table: the directory
fd at 4 duplicates at 5 like a channel, `fget_raw` (fs/file.c:1088,
Linux v6.18.46) taking any open file.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-dir -/
theorem dup_of_a_directory_fd_duplicates_over_the_real_table :
    check_syscall (SyscallInput.mkInput 23 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 .FdDir) dup_model) [] := rfl

/-- …and lowest-free holds for it through the table too.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,find_next_fd@v6.18.46 -/
theorem dup_of_a_directory_fd_rejects_a_non_lowest_fd_over_the_real_table :
    check_syscall (SyscallInput.mkInput 23 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 6 [] []) dup_model = CheckReject := rfl

/-- `dup_of_a_file_fd_declines_whatever_the_kernel_claims` over the real
table: `dup(3)` on the read-only file fd is declined for every effect.
Linux duplicates it (`SYSCALL_DEFINE1(dup, …)`, fs/file.c:1457-1470,
Linux v6.18.46), and the two descriptors then share one `struct file`
and so one offset, which the model's copied entry cannot express.
kernel: fs/file.c:dup,fget_raw,fd_install@v6.18.46 -/
theorem dup_of_a_file_fd_declines_whatever_the_kernel_claims_over_the_real_table
    (eff : SyscallEffect) :
    check_syscall (SyscallInput.mkInput 23 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        eff dup_model = CheckUnmodeled := rfl

/-- `dup3_replaces_the_target_and_returns_it` over the real table:
`dup3(0, 1, 0)` returns 1 with channel 0 bound there — `do_dup2`'s store
over the slot's old file (fs/file.c:1300-1311, Linux v6.18.46) — and 5,
the number `dup` would have answered, is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_replaces_the_target_and_returns_it_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model) []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup3_ignores_o_cloexec_but_not_another_bit` over the real table:
`O_CLOEXEC` (524288) passes `ksys_dup3`'s `(flags & ~O_CLOEXEC) != 0`
test (fs/file.c:1405-1406, Linux v6.18.46) and the install is accepted;
bit 2 fails it, so a return of 1 is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_ignores_o_cloexec_but_not_another_bit_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 24 [0, 1, 524288, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model) []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 1, 4, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup3_eq_beats_the_file_fd_decline` over the real table: `oldfd ==
newfd` is -EINVAL at fs/file.c:1408-1409 (Linux v6.18.46), before the
lookup at :1416 reaches the file entry the model declines to duplicate,
so `dup3(3, 3, 0)`'s -EINVAL is accepted and a return of 3 refused.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_beats_the_file_fd_decline_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [3, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall (SyscallInput.mkInput 24 [3, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 3 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup3_takes_a_free_newfd_below_the_embedded_table` over the real
table: a free `newfd` of 7, under the limit and inside the table every
process starts with, is installed at the number given (`expand_files`,
fs/file.c:288, needing no growth, then `do_dup2`'s store at :1304, Linux
v6.18.46); 5, the lowest free descriptor, is refused.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_takes_a_free_newfd_below_the_embedded_table_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 7, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 7 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 7 (.FdChannel 0)) dup_model) []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 7, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup3_declines_a_free_newfd_above_the_embedded_table` over the real
table: a free `newfd` of 100 makes `expand_files` (fs/file.c:288, Linux
v6.18.46) consult the table's current `max_fds` and `sysctl_nr_open`,
neither of which the model carries, so every effect is declined.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_declines_a_free_newfd_above_the_embedded_table_over_the_real_table
    (eff : SyscallEffect) :
    check_syscall (SyscallInput.mkInput 24 [0, 100, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        eff dup_model = CheckUnmodeled := rfl

/-- `dup3_free_newfd_is_decided_by_the_run_s_limit` over the real table:
the same `dup3(0, 5, 0)` is installed under `dup_model`'s default limit
and is -EBADF under a soft `RLIMIT_NOFILE` of 4, `ksys_dup3`'s `newfd >=
rlimit(RLIMIT_NOFILE)` test (fs/file.c:1411-1412, Linux v6.18.46); a
return of 5 is refused there.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_is_decided_by_the_run_s_limit_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (.FdChannel 0)) dup_model) []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4 = CheckOk dup_model_nofile4 []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model_nofile4 = CheckReject := ⟨rfl, rfl, rfl⟩

/-- `dup3_limit_beats_an_fd_the_process_holds` over the real table: under
a limit of 4, `newfd` 3 is replaced and `newfd` 4 — open, the directory
fd — is -EBADF, the limit test at fs/file.c:1411-1412 (Linux v6.18.46)
preceding every look at the table and being strict; a return of 4 is
refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_limit_beats_an_fd_the_process_holds_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 3 [] []) dup_model_nofile4
      = CheckOk (with_fds (fd_insert (m_fds dup_model_nofile4) 3 (.FdChannel 0))
          dup_model_nofile4) []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4 = CheckOk dup_model_nofile4 []
    ∧ check_syscall (SyscallInput.mkInput 24 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 4 [] []) dup_model_nofile4 = CheckReject := ⟨rfl, rfl, rfl⟩

/-- `dup3_free_newfd_just_below_the_embedded_table` over the real table:
63, the last slot of the table every process starts with
(`NR_OPEN_DEFAULT`, `BITS_PER_LONG`, include/linux/fdtable.h, Linux
v6.18.46), is installed at the number given.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_just_below_the_embedded_table_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 63, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 63 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 63 (.FdChannel 0)) dup_model) [] := rfl

/-- `dup3_declines_a_free_newfd_at_the_embedded_table` over the real
table: 64, one past it, is where `expand_files` (fs/file.c:288, Linux
v6.18.46) may have to grow the table, and every effect is declined.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_declines_a_free_newfd_at_the_embedded_table_over_the_real_table
    (eff : SyscallEffect) :
    check_syscall (SyscallInput.mkInput 24 [0, 64, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        eff dup_model = CheckUnmodeled := rfl

/-- `dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup` over the real
table: `newfd` 2000 is past the default limit, so -EBADF at
fs/file.c:1411-1412 (Linux v6.18.46), for a channel `oldfd` and for the
file `oldfd` the model otherwise declines — the lookup at :1416 never
runs — and a return of 2000 is refused.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup_over_the_real_table :
    check_syscall (SyscallInput.mkInput 24 [0, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [3, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [0, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 2000 [] []) dup_model = CheckReject := ⟨rfl, rfl, rfl⟩

/-! ### The registers' 32 bits, through the table

`SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c:1457, Linux
v6.18.46) and `SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int,
newfd, int, flags)` (fs/file.c:1433) reach `__do_sys_dup`/`__do_sys_dup3`
through riscv64's `__SYSCALL_DEFINEx`, which casts each register to its
declared type with `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46): the high
half of a descriptor register is dropped before `fget_raw` or
`ksys_dup3` sees it.  The arms apply `fd32` to `a0` and `a1` for that
reason and hand `a2` over whole, `dup3_flags_ok` narrowing it itself. -/

/-- `dup(2^32 | 2)` is `dup(2)`: the copy of channel 2 lands at 5.  An arm
handing the checker the whole register would look up an fd no table
holds and accept -EBADF instead, which is refused.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-trunc -/
theorem dup_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 23 [4294967298, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 5 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (.FdChannel 2)) dup_model) []
    ∧ check_syscall
        (SyscallInput.mkInput 23 [4294967298, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `dup(-1)` is `dup(2^32 - 1)`, open in no table: -EBADF from
`fget_raw` (fs/file.c:1088, Linux v6.18.46) at fs/file.c:1459-1460,
before `get_unused_fd_flags` at :1463 could allocate or fail, so a
descriptor, -EMFILE and -ENOMEM are all refused.
kernel: fs/file.c:dup,fget_raw,get_unused_fd_flags,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_minus_one_is_ebadf_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall
        (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 3 [] []) dup_model = CheckReject
    ∧ check_syscall
        (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EMFILE) [] []) dup_model = CheckReject
    ∧ check_syscall
        (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret ENOMEM) [] []) dup_model = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- `dup(2^32 | 3)` is `dup(3)`, the file fd, and is declined for every
effect as `dup(3)` is — the decline reached only through the narrowing,
since the whole register is open in no table.
kernel: fs/file.c:dup,fget_raw,fd_install@v6.18.46 -/
theorem dup_of_an_aliased_file_fd_declines_over_the_real_table (eff : SyscallEffect) :
    check_syscall
        (SyscallInput.mkInput 23 [4294967299, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        eff dup_model = CheckUnmodeled := rfl

/-- `dup3(2^32, 0, 0)` compares the narrowed descriptors, finds them
equal and is -EINVAL at fs/file.c:1408-1409 (Linux v6.18.46); the -EBADF
a lookup of the whole register would give is refused.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_fds_are_compared_after_truncation_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 24 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The SECOND descriptor is narrowed too: `dup3(0, 2^32, 0)` is
`dup3(0, 0, 0)`, -EINVAL at fs/file.c:1408-1409 (Linux v6.18.46).  Left
wide, `2^32` is past every limit and the answer would be the -EBADF of
:1411-1412, which is refused; an arm narrowing `a0` alone fails here.
kernel: fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_newfd_is_narrowed_before_the_comparison_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 24 [0, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [0, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The narrowing ALIASES: `dup3(2^32 | 2, 1, 0)` is `dup3(2, 1, 0)` and
binds channel 2 at fd 1 (`do_dup2`'s store, fs/file.c:1304, Linux
v6.18.46); the -EBADF of an fd the whole register would not find is
refused.
kernel: fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_aliased_oldfd_installs_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 24 [4294967298, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 2)) dup_model) []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [4294967298, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- `a2` is handed over whole and narrowed inside `dup3_flags_ok`:
`dup3(2, 1, 2^32)` has `int flags` 0, passes fs/file.c:1405-1406 (Linux
v6.18.46) and returns 1; the -EINVAL of a flag test on 64 bits is
refused.
kernel: fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_discards_the_high_half_of_flags_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 24 [2, 1, 4294967296, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 1 [] []) dup_model
      = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 2)) dup_model) []
    ∧ check_syscall
        (SyscallInput.mkInput 24 [2, 1, 4294967296, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckReject := ⟨rfl, rfl⟩

/-- The checkers themselves read the whole descriptor word they are
given: `check_dup` at `2^32 | 2` looks up an fd no table holds and
accepts -EBADF, and `check_dup3` at `(2^32, 0)` finds the pair unequal,
`newfd` under the limit and `oldfd` absent, and accepts -EBADF too.
Linux narrows first; that narrowing is the arms', and the pins above
at the same words, through the table, give the kernel's answers, so
where the narrowing lives is fixed from both sides.
model: the checkers' contract with the arms; Linux narrows first (__SC_CAST) and answers otherwise at these register words -/
theorem the_checkers_themselves_read_the_whole_descriptor :
    check_dup 4294967298 (mkEffect (errno_ret EBADF) [] []) dup_model = CheckOk dup_model []
    ∧ check_dup3 4294967296 0 0 (mkEffect (errno_ret EBADF) [] []) dup_model
      = CheckOk dup_model [] := ⟨rfl, rfl⟩

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so each arm's
`ca_witness` is what it answers at 23 and 24; the witness pins above fix
`dup_witness` and `dup3_witness` at bare words, these fix that the arms
hand them the reading the checkers get. -/

/-- `dup(0)` through the table: the witness's -ENOMEM, the
`alloc_fdtable` failure branch `dup_witness_on_a_channel_is_enomem`
names, the model unchanged.
kernel: fs/file.c:dup,get_unused_fd_flags,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_witness_on_a_channel_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 23 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) dup_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model [] := rfl

/-- `dup(2^32 | 3)` through the table: narrowed to the file fd, the
witness exhibits the decline — where `dup_witness` at the bare word
exhibits the -EBADF of an fd no table holds (the next pin).
kernel: include/linux/syscalls.h:__SC_CAST; fs/file.c:dup,fget_raw,fd_install@v6.18.46 -/
theorem dup_witness_on_an_aliased_file_fd_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 23 [4294967299, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model = Unmodeled := rfl

/-- …the witness itself reads the whole word it is given.
model: the witness's contract with the arm; Linux narrows first (__SC_CAST) -/
theorem the_dup_witness_itself_reads_the_whole_word :
    dup_witness 4294967299 dup_model = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := rfl

/-- `dup3(2^32, 0, 0)` through the table: narrowed to an equal pair, the
witness exhibits the -EINVAL of fs/file.c:1408-1409 (Linux v6.18.46).
kernel: include/linux/syscalls.h:__SC_CAST; fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_witness_on_a_truncated_equal_pair_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 24 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := rfl

/-- `dup3(0, 1, 0)` through the table: the replacement, at the number
given.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_witness_replaces_over_the_real_table :
    syscall_spec_witness
        (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) dup_model
      = Ok (mkEffect 1 [] [])
          (with_fds (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) dup_model) [] := rfl

/-! ### The descriptor table stays unique across an install

`fd_table_unique_arm_dup` and `fd_table_unique_arm_dup3` rest on
`fd_table_unique_fd_insert`: `fd_insert` drops the descriptor's old
binding before it conses the new one, Linux's one slot per descriptor
(`do_dup2`'s store over `fdt->fd[fd]`, fs/file.c:1304, Linux v6.18.46).
The pair below states it at the table `dup3(0, 1, 0)` leaves, and names
the mistake the filter prevents: consing the new binding over the old
one, which the invariant refuses. -/

/-- The table `dup3(0, 1, 0)` accepts binds each descriptor once.
model: `fd_table_unique_fd_insert` at `dup_model`; the invariant is the model's, its kernel reading is `do_dup2`'s one slot per fd -/
theorem dup3_post_table_is_unique :
    fd_table_unique (fd_insert (m_fds dup_model) 1 (.FdChannel 0)) := by
  show ((fd_insert (m_fds dup_model) 1 (.FdChannel 0) :
           List (word × FdEntry)).map Prod.fst).Nodup
  decide

/-- …and a table that consed the binding without dropping fd 1's old one
is not: the invariant is not vacuous at the shape an install produces.
model: negative twin of `dup3_post_table_is_unique`; a replacement leaving two bindings of fd 1 is refused by `fd_table_unique` -/
theorem consing_over_a_bound_fd_is_not_unique :
    ¬ fd_table_unique ((1, .FdChannel 0) :: m_fds dup_model) := by
  show ¬ (((1, .FdChannel 0) :: m_fds dup_model :
             List (word × FdEntry)).map Prod.fst).Nodup
  decide

end V_Fs_File

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.File
