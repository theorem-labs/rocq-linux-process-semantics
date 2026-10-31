import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-cases: a71fd38a08571d519b9cfc5f66308db5c26da570
covers: pselect_a_file_counts_once_per_set -- a_file_counts_once_per_set, a_descriptor_count_is_rejected
covers: pselect_exceptfds_comes_back_zeroed -- exceptfds_comes_back_zeroed, an_exceptional_file_is_rejected
covers: pselect_bits_at_or_above_n_are_invisible -- bits_at_or_above_n_are_invisible, a_bit_above_n_surviving_is_rejected
covers: pselect_a_closed_descriptor_below_n_is_ebadf -- a_closed_descriptor_below_n_is_ebadf, a_count_over_a_closed_descriptor_is_rejected
covers: pselect_a_channel_is_declined -- a_channel_is_declined, a_readable_channel_is_rejected
covers: pselect_n_above_nr_open_default_is_declined -- n_above_nr_open_default_is_declined, n_at_nr_open_default_is_answered
covers: pselect_a_real_sigmask_is_declined_but_a_bad_size_is_einval -- a_real_sigmask_is_declined, a_bad_sigsetsize_is_einval
covers: pselect_a_bad_sigsetsize_beats_an_unreadable_set -- a_bad_sigsetsize_beats_an_unreadable_set, efault_behind_a_bad_sigsetsize_is_rejected
covers: pselect_null_mask_ignores_the_size -- null_mask_ignores_the_size
covers: pselect_a_deadline_with_a_request_is_declined -- a_deadline_with_a_request_is_declined, the_same_request_without_a_deadline_is_answered
covers: pselect_an_empty_request_sleeps_and_writes_zeros -- an_empty_request_sleeps_and_writes_zeros, a_sleep_leaving_the_timespec_is_rejected
covers: pselect_an_exceptfds_only_request_still_sleeps -- an_exceptfds_only_request_still_sleeps
covers: pselect_a_null_timeout_with_nothing_requested_is_declined -- a_null_timeout_with_nothing_requested_is_declined, an_invented_zero_under_a_null_timeout_is_rejected
covers: pselect_where_an_errno_comes_from_decides_the_writeback -- einval_from_core_sys_select_without_a_deadline, einval_from_core_sys_select_under_a_deadline_is_declined, einval_from_set_user_sigmask_survives_the_deadline
covers: pselect_a_set_that_is_readable_but_not_writable_is_declined -- a_set_readable_but_not_writable_is_declined
covers: pselect_n_zero_never_dereferences_a_set_pointer -- n_zero_never_dereferences_a_set_pointer
covers: pselect_the_timespec_is_judged_raw -- tv_nsec_at_nsec_per_sec_is_einval, a_negative_tv_sec_is_not_rescued_by_a_carry, a_negative_tv_nsec_is_einval, the_normalized_deadline_is_rejected
covers: pselect_aliased_sets_are_modeled -- aliased_read_and_except_sets_name_both_writes, the_snapshot_ledger_is_rejected, aliased_read_and_write_sets_agree, aliased_sets_still_answer_ebadf
covers: ppoll_counts_descriptors_not_bits -- ppoll_counts_descriptors_not_bits, ppoll_a_bit_count_is_rejected
covers: ppoll_a_read_write_file_polls_as_any_other -- a17_ppoll_rdwr_polls_as_any_other
covers: ppoll_an_unopened_descriptor_is_pollnval_not_ebadf -- ppoll_an_unopened_descriptor_is_pollnval, ppoll_ebadf_for_an_unopened_descriptor_is_rejected
covers: ppoll_a_negative_fd_is_skipped_not_invalid -- ppoll_a_negative_fd_is_skipped, ppoll_pollnval_for_a_negative_fd_is_rejected
covers: ppoll_events_filters_the_default_pollmask -- ppoll_events_filters_the_default_pollmask, ppoll_an_echoed_events_is_rejected
covers: ppoll_a_channel_is_declined -- ppoll_a_channel_is_declined, ppoll_a_channel_with_no_events_is_still_declined
covers: ppoll_above_the_stack_bound_is_declined -- ppoll_above_the_stack_bound_is_declined, ppoll_at_the_stack_bound_is_answered, ppoll_at_the_stack_bound_the_array_is_read, ppoll_above_the_stack_bound_the_array_is_not_read
covers: ppoll_nfds_above_the_soft_limit_is_einval_before_the_copy -- ppoll_nfds_above_the_soft_limit_is_einval, ppoll_efault_ahead_of_the_limit_test_is_rejected
covers: ppoll_an_unreadable_array_is_efault -- ppoll_an_unreadable_array_is_efault
covers: ppoll_nfds_zero_never_dereferences_ufds -- ppoll_nfds_zero_never_dereferences_ufds
covers: ppoll_a_deadline_expires_to_zeros_but_an_early_return_is_declined -- ppoll_a_deadline_expires_to_zeros, ppoll_an_early_return_under_a_deadline_is_declined
covers: ppoll_a_null_timeout_with_nothing_ready_is_declined -- ppoll_a_null_timeout_with_nothing_ready_is_declined, ppoll_a_ready_descriptor_under_a_null_timeout_is_answered
covers: ppoll_an_unwritable_array_is_declined -- ppoll_an_unwritable_array_is_declined
covers: ppoll_the_timeout_is_judged_before_the_signal_mask -- ppoll_an_unreadable_timeout_beats_a_bad_sigsetsize, ppoll_einval_ahead_of_the_timeout_is_rejected, ppoll_a_bad_sigsetsize_beats_an_unreadable_array
covers: ppoll_an_unreadable_mask_is_efault -- ppoll_an_unreadable_mask_is_efault -/

/-! # Checks.Cases.Fs.Select — what `pselect6` and `ppoll` answer, read off against Linux

Worked examples over `Sys.Fs.Select.pselect6_spec` and `ppoll_spec`, the twin
of `theories/LinuxProcessSem/Checks/Cases/Fs/Select.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f),
read in a checkout at that commit.

HOW THESE ARE STATED.  Rocq states every example through `check_syscall` on
a `mkInput 72 …` or `mkInput 73 …`, so each one pins the dispatcher line —
which argument register is which, and the `int` narrowing of pselect6's `n`
and the `unsigned int` narrowing of ppoll's `nfds` — together with the arm.
This file does the same on `Specs.syscall_spec`, on inputs built by `ps_in`
and `pp_in`; a check is stated on the relation itself, as an `iff` over
EVERY outcome `o`, so one theorem fixes what is admitted and what is refused,
and beside it the concrete lie a kernel could tell is refuted on its own.  A
decline is stated as `↔ o = Unmodeled`, which refuses every answer at once;
where Rocq's second conjunct names one answer in particular, that answer is
refuted separately as well.  Every proof but the two `decide`d membership
examples is `sys_norm` or `sys_refute` (`Checks/Cases/Tactic.lean`): the spec is unfolded, the dispatcher's lookup
decided, the monad primitives read, and every closed subterm — the
`bytes_at` reads, the bitmap scans, the fixture — evaluated.

WHAT THE INPUT BUILDERS ARE FOR.  A decline stated here is a decline of one
ARGUMENT SHAPE, never of a syscall number: numbers 72 and 73 have arms.
`tools/check_decline_registers.py` reads a `syscall_spec (mkInput N …) m
Unmodeled` statement as the claim that N is declined, so the number lives in
`ps_in` and `pp_in` and no statement below spells `mkInput` — the reader then
sees no number to register, which is the truth.

THREE THINGS THE FIXTURES DO FOR THE EVALUATOR, none of them a claim about
the model.  A `bytes_at` lookup past the end of its list reduces to
`List.get?Internal [] (k+1)`, and that core-library function's last arm
(`| _, _ => none`, module `Init.GetElem` of the pinned Lean v4.34.0)
overlaps the two before it, so its equation lemma carries a side condition that the ground
evaluator `sys_norm` runs (`simp +ground`) applies no equation under: the
lookup never normalizes and the pin stays open.  So (1) `mem_join` takes
the HIGHER region first, and every pointer an example wants unreadable —
`hole` — sits below every region it lays out, where `bytes_at`'s lower
bound answers `none` outright; the readable regions are Rocq's, only their
order in `mem_join` differs.  (2) The writable views are range tests where
Rocq's are 128- and 512-byte `bytes_at` lists: evaluating a 512-element
list exhausts the default recursion depth, and a range test says the same
thing in one comparison.  (3) The two pins that lay out a 30- or 31-entry
array raise `maxRecDepth`, as `Checks/Cases/Sys/Uapi/Fs.lean` does, since a
248-byte list is past that default too.  Each is a limit of the tactic,
recorded here so the next file does not rediscover it.

ONE DECLINE IS THE LEAN TWIN'S ALONE.  `nfds = 0` with a kernel-space `ufds`
is declined by `Sys/Fs/Select.lean`'s `ppoll_core` where Rocq answers 0 and
Linux -EFAULT (its docstring has the lines); the two pins under "the
zero-length call" state the decline and refuse the 0.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Select

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

-- Sys/Fs/Select.lean: the two specs' unfoldings, at the priority every spec
-- has (`Checks/Cases/Tactic.lean`'s register says what a spec owes).
attribute [sys_simp low] pselect6_spec.eq_1 ppoll_spec.eq_1

/-! ## The pselect6 fixtures

Rocq's, address for address.  The three descriptor-set bitmaps are placed
CONTIGUOUSLY, so one `bytes_at` carrying up to three little-endian words
describes all of them: `readfds` at `ps_inp`, `writefds` eight bytes later,
`exceptfds` eight after that.  The timespec and the {`sigset_t *`, `size_t`}
pack each get their own 16 bytes. -/

def ps_inp  : word := 4096
def ps_outp : word := 4104
def ps_exp  : word := 4112
def ps_tsp  : word := 4128
def ps_sig  : word := 4160

/-- Everything the pselect6 examples name is writable — the 128 bytes from
`ps_inp` on — except where an example passes `fun _ => none` on purpose.
A range test rather than Rocq's 128-byte list; the header says why. -/
def ps_wmem : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4224 then some 0 else none

/-- An address below every region either syscall's examples lay out, so a
pointer to it is unreadable in every readable view an example builds. -/
def hole : word := 2048

/-- The left map where it answers, the right one otherwise.  Every use below
puts the HIGHER region on the left (the header says why). -/
def mem_join (m1 m2 : word → Option byte) : word → Option byte :=
  fun a => match m1 a with
           | some b => some b
           | none => m2 a

/-- stdin (a channel) at fd 0 and file `f` = "hi" open read-only at fd 3, so
both descriptor kinds the model has are present: a file, whose readiness
`vfs_poll` answers with the constant `DEFAULT_POLLMASK`, and a channel, whose
readiness is a schedule the model does not represent.  Rocq spells it
through `mkModel`; `fixture_of` fills the slots `mkModel` does not take with
the demo process's fields, none of which either spec reads. -/
def pselect_fds : List (word × FdEntry) := [(0, .FdChannel 0), (3, .FdFile [102] 0)]

def pselect_fs : Fs.Fs := [([102], [104, 105])]

def pselect_model : Model := fixture_of (fds := pselect_fds) (fs := pselect_fs)

/-- The same process under a soft `RLIMIT_NOFILE` of 4, for the ppoll pins
that test the limit: above it, at it, and above it together with the band. -/
def pselect_model_lim : Model := with_nofile 4 pselect_model

/-- The same process with every descriptor kind the model has, one per slot,
so each arm of `bits_all_pollable` and `ppoll_revents_of` is reached by a pin
of its own — no mutation operator rewrites a match arm, so only a pin can
hold one: fd 4 the file open write-only, fd 5 the directory, fd 6 a fresh
socket, fd 7 the read end of a pipe, fd 8 /dev/null open read-write, fd 9
/dev/urandom.  fd 9 is therefore OPEN here, where `pselect_model`'s -EBADF
pins name it as the closed one. -/
def pselect_kinds_fds : List (word × FdEntry) :=
  pselect_fds ++ [(4, .FdFileW [102] 0), (5, .FdDir), (6, .FdSocket .SkFresh),
                  (7, .FdPipe 0 false), (8, .FdDevNull true true), (9, .FdUrandom)]

def pselect_model_kinds : Model := fixture_of (fds := pselect_kinds_fds) (fs := pselect_fs)

/-- The top of user space, `TASK_SIZE` as a pointer: the last address
`__access_ok` accepts for a zero-length range (include/asm-generic/access_ok.h:40,
`addr <= limit - size` with `size` 0, Linux v6.18.46).  Named so a statement
can sit on the edge without spelling the constant. -/
def user_top : word := Z_to_bv 64 TASK_SIZE

/-- A pselect6 call: the six argument registers in `SYSCALL_DEFINE6(pselect6,
…)`'s order (fs/select.c:793-795, Linux v6.18.46) — `n`, `inp`, `outp`, `exp`, `tsp`, `sig` —
over the given readable and writable views of memory. -/
def ps_in (n inp outp exp tsp sig : word) (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 72 [n, inp, outp, exp, tsp, sig] mem wmem

-- The fixtures enter the normal form by their unfoldings, at low priority
-- like every other (`Checks/Cases/Tactic.lean`'s header on how a fixture
-- enters the set); every one of them is closed, so the second pass
-- evaluates both sides of a pin to the same tree.
attribute [sys_simp low] pselect_model.eq_1 pselect_model_lim.eq_1 pselect_model_kinds.eq_1 ps_in.eq_1

/-! ## The dispatcher line: 72, and `n` narrowed to `int` -/

/-- Syscall 72 is `pselect6`: `__NR_pselect6 72`
(include/uapi/asm-generic/unistd.h:192, Linux v6.18.46), and riscv64 has no
`select` or `_newselect` number at all.
kernel: include/uapi/asm-generic/unistd.h:__NR_pselect6@v6.18.46 -/
example : (72 : Int) ∈ modeled_sysnos := by decide

/-- `n` is an `int` (fs/select.c:793), so riscv64's `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88) narrows the register through
`__SC_CAST` (include/linux/syscalls.h:132) before `core_sys_select` sees it:
a register holding 2^32 + 4 is the `n = 4` of `a_file_counts_once_per_set`
below with `writefds` NULL, not a huge count.  The table line applies
`Syscall.nfds32` for exactly that reason.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:pselect6,core_sys_select@v6.18.46 -/
theorem n_is_narrowed_to_int (o : outcome SyscallEffect) :
    syscall_spec (ps_in (Z_to_bv 64 (2 ^ 32 + 4)) ps_inp 0 0 0 0
        (bytes_at ps_inp (word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-! ## `do_select`: a bit count, and `DEFAULT_POLLMASK` on every file

`do_select` (fs/select.c:483-611, Linux v6.18.46) has three independent
`retval++`, one per result mask (:540, :545, :550), and `select_poll_one`
(:465-481) hands every descriptor to `vfs_poll` (include/linux/poll.h:78-83,
Linux v6.18.46), which answers `DEFAULT_POLLMASK` (:24) for a file with no
`->poll` — a mask that meets `POLLIN_SET` and `POLLOUT_SET`
(fs/select.c:459-462, Linux v6.18.46) and misses `POLLEX_SET` (:463). -/

/-- The return value is a BIT count, not a descriptor count: fd 3 named in
both `readfds` and `writefds` contributes twice (fs/select.c:540, :545) and
the call returns 2.  Both sets come back with the bit still set, because
`DEFAULT_POLLMASK` meets `POLLIN_SET` and `POLLOUT_SET`.
kernel: fs/select.c:do_select,select_poll_one; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem a_file_counts_once_per_set (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 2 [(ps_inp, word_le8 8), (ps_outp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- A kernel answering 1 — the number of ready descriptors — is lying:
`do_select` counts masks, not descriptors.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem a_descriptor_count_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem) pselect_model
        (Ok (mkEffect 1 [(ps_inp, word_le8 8), (ps_outp, word_le8 8)] []) m' evs) := by
  sys_refute

/-- `exceptfds` is requested, so it IS copied back — as a zero word — and it
adds nothing to the count.  `DEFAULT_POLLMASK` misses `POLLEX_SET`
(fs/select.c:463) entirely, so no file is ever exceptional and the third
`retval++` (:550) never fires for one.
kernel: fs/select.c:do_select,select_poll_one; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem exceptfds_comes_back_zeroed (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 ps_exp 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 0 ++ word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8), (ps_exp, word_le8 0)] []) pselect_model [] := by
  sys_norm

/-- A kernel reporting the file exceptional — the `exceptfds` bit kept and
counted — has a `->poll` a regular file does not have.
kernel: fs/select.c:do_select; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem an_exceptional_file_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp 0 ps_exp 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 0 ++ word_le8 8)) ps_wmem) pselect_model
        (Ok (mkEffect 2 [(ps_inp, word_le8 8), (ps_exp, word_le8 8)] []) m' evs) := by
  sys_refute

/-! ## `max_select_fd`: the partial-word mask and -EBADF

`max_select_fd` (fs/select.c:417-457, Linux v6.18.46) masks the last word with
`~(~0UL << (n & (BITS_PER_LONG-1)))` (:425), tests `set & ~*open_fds`
(:433-435) and answers -EBADF before `do_select` polls anything (:494). -/

/-- A bit at or above `n` is INVISIBLE and comes back CLEARED.  The word here
names fd 3 and fd 9, and fd 9 is not open — but with `n = 4` the partial-word
mask (fs/select.c:425) hides bit 9 from the -EBADF test and `do_select`'s
inner loop stops at `i >= n` (:532-533); the result word starts zeroed
(:673) and is assigned wholesale (:566-567), so the write-back drops it.
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem bits_at_or_above_n_are_invisible (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- A kernel handing bit 9 back — echoing the request instead of the zeroed
result word — has skipped the zeroing of the result words in
`core_sys_select` (fs/select.c:673-675).
kernel: fs/select.c:max_select_fd,do_select,core_sys_select@v6.18.46 -/
theorem a_bit_above_n_surviving_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model (Ok (mkEffect 1 [(ps_inp, word_le8 520)] []) m' evs) := by
  sys_refute

/-- Raise `n` past that bit and the SAME word is -EBADF, with nothing copied
back at all: `max_select_fd`'s `set & ~*open_fds` test (fs/select.c:433-435)
runs over the union of the three requested sets before a single descriptor
is polled, so one closed descriptor decides the whole call.
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem a_closed_descriptor_below_n_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) pselect_model [] := by
  sys_norm

/-- A kernel polling the open descriptor and reporting it — 1, with the
closed one dropped — is lying: `max_select_fd` returns -EBADF (fs/select.c:435)
before `do_select` reaches its scan (:494-498).
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem a_count_over_a_closed_descriptor_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 10 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model (Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) m' evs) := by
  sys_refute

/-- The closed descriptor need not sit at the top bit.  With `n = 64` the
partial-word mask is the whole word (`n & 63` is 0, so `~(~0UL << 0)` is
all ones, fs/select.c:425) and `set & ~*open_fds` (:433-435) runs over every
set bit: fd 9 at bit 9 is closed and the call is -EBADF even though bit 63,
the top of the scanned range, is clear.  A walk that looked at the top bit
alone would answer 1 here.
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem a_closed_descriptor_below_the_top_bit_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (ps_in 64 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) pselect_model [] := by
  sys_norm

/-- A kernel that polled fd 3 and reported it — 1, with the closed fd 9
dropped — has skipped `max_select_fd`'s test on a bit below the top one.
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem a_count_that_skipped_a_closed_descriptor_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 64 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model (Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) m' evs) := by
  sys_refute

/-- The bit AT `n` is the first invisible one.  With `n = 9` the mask
`~(~0UL << (n & 63))` (fs/select.c:425) keeps bits 0..8, so bit 9 — the
closed fd 9 — is outside the -EBADF test (:433-435) and outside
`do_select`'s scan, which breaks at `i >= n` (:532-533): the call answers
the open fd 3 alone and writes the request back without bit 9.
kernel: fs/select.c:max_select_fd,do_select@v6.18.46 -/
theorem a_bit_at_exactly_n_is_invisible (o : outcome SyscallEffect) :
    syscall_spec (ps_in 9 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- A kernel testing bit `n` itself — -EBADF for the closed fd 9 at `n = 9`
— has an off-by-one in the mask the kernel does not have.
kernel: fs/select.c:max_select_fd@v6.18.46 -/
theorem a_bit_at_exactly_n_tested_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 9 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
        pselect_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE -EBADF TEST RUNS OVER THE UNION.  `BITS(fds, n)` is
`*in | *out | *ex` (fs/select.c:415), so a closed descriptor named in
`writefds` ALONE is -EBADF exactly as one in `readfds` is (:431-435).
kernel: fs/select.c:max_select_fd@v6.18.46 -/
theorem a_closed_descriptor_in_writefds_alone_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 0 ps_outp 0 0 0 (bytes_at ps_outp (word_le8 512)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) pselect_model [] := by
  sys_norm

/-- …and one named in `exceptfds` ALONE is too: the union does not care
which set the bit came from.
kernel: fs/select.c:max_select_fd@v6.18.46 -/
theorem a_closed_descriptor_in_exceptfds_alone_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 0 0 ps_exp 0 0 (bytes_at ps_exp (word_le8 512)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) pselect_model [] := by
  sys_norm

/-- A kernel that only tested `readfds` would poll nothing here, find no
exceptional descriptor and hand `exceptfds` back zeroed with 0; that is the
answer of a model whose union is `readfds` alone, and it is refused.
kernel: fs/select.c:max_select_fd@v6.18.46 -/
theorem a_zeroed_exceptfds_over_a_closed_descriptor_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 10 0 0 ps_exp 0 0 (bytes_at ps_exp (word_le8 512)) ps_wmem)
        pselect_model (Ok (mkEffect 0 [(ps_exp, word_le8 0)] []) m' evs) := by
  sys_refute

/-! ## The two declines of `core_sys_select`'s band -/

/-- A CHANNEL is declined.  The model's channels are pipes, whose
`pipeanon_fops` sets `.poll = pipe_poll` (fs/pipe.c:1261), and `pipe_poll`
(:660-706) reports EPOLLIN only on a non-empty ring (:690): readiness is a
function of what the peer has written so far — wall-clock arrival — and
`m_stdin` records which bytes will eventually arrive, not which have.
Either answer would be a claim the model cannot support, so it fails closed.
kernel: fs/pipe.c:pipe_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem a_channel_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 1 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 1)) ps_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and in particular the answer a SNAPSHOT of `m_stdin` would tempt a
model into — 1, bit 0 kept, the pipe readable — is refused.  Not because no
kernel gives it: Linux gives exactly that answer whenever the ring holds a
byte (`pipe_poll` sets EPOLLIN on a non-empty ring, fs/pipe.c:690).  It is
refused because the model cannot know whether this kernel does NOW, so this
is the decline of `a_channel_is_declined` restated on the one answer that
looks derivable, not the refutation of a lie.
kernel: fs/pipe.c:pipe_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem a_readable_channel_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 1 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 1)) ps_wmem)
        pselect_model (Ok (mkEffect 1 [(ps_inp, word_le8 1)] []) m' evs) := by
  sys_refute

/-- A channel BESIDE a file is declined too: `do_select` polls every set bit
below `n` (fs/select.c:531-536), so the file at bit 3 does not make the
channel at bit 0 go away, and one undecidable descriptor declines the whole
call.  A walk that judged the top bit alone would answer 1 here.
kernel: fs/select.c:do_select; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem a_channel_beside_a_file_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 9)) ps_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- Whichever set names the channel: `exceptfds` alone is polled through the
same union (`BITS`, fs/select.c:415) and the same `select_poll_one`, so it
declines like `readfds` does — `pipe_poll` can report EPOLLHUP or EPOLLERR
(fs/pipe.c:691-704) and the model cannot say whether it will.
kernel: fs/select.c:do_select,max_select_fd; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem a_channel_in_exceptfds_alone_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 1 0 0 ps_exp 0 0 (bytes_at ps_exp (word_le8 1)) ps_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- An `n` above `NR_OPEN_DEFAULT` = 64 is declined.  `core_sys_select`
clamps `n` to `fdt->max_fds` (fs/select.c:641-642), which is a property of
the fd table's ALLOCATION HISTORY and not of which descriptors are open; the
model tracks the latter only, so above the floor it cannot say how many
bytes are read and written back.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem n_above_nr_open_default_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 65 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and 64 itself is inside the band: at `n = 64` the clamp provably never
bites, since `max_fds` is at least `NR_OPEN_DEFAULT`
(include/linux/fdtable.h:24), and the whole word is scanned.
kernel: fs/select.c:core_sys_select,max_select_fd,do_select@v6.18.46 -/
theorem n_at_nr_open_default_is_answered (o : outcome SyscallEffect) :
    syscall_spec (ps_in 64 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-! ## Every descriptor kind, one pin per match arm of the pselect6 scan

`vfs_poll` (include/linux/poll.h:78-83, Linux v6.18.46) never reads `f_mode`:
a file with no `->poll` takes `DEFAULT_POLLMASK` (:24) whether it was opened
for reading or for writing, and no directory `file_operations` in the tree
defines `->poll`.  The arms these pins reach are `bits_all_pollable`'s.
Every other kind the model has carries a `->poll` whose answer depends on a
peer or on state the model does not hold, and each is declined by its own
arm.  These pins are stated on `pselect_model_kinds`, which holds one
descriptor of each kind. -/

/-- A write-only file and a directory are readable AND writable, like the
read-only file: fd 4 (`FdFileW`) and fd 5 (`FdDir`) in both sets, `n = 6`,
answer 4 — two bits kept in each set — because `vfs_poll` hands back
`DEFAULT_POLLMASK` for a file with no `->poll` regardless of its access mode.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_select,select_poll_one@v6.18.46 -/
theorem a_write_only_file_and_a_directory_are_readable_and_writable (o : outcome SyscallEffect) :
    syscall_spec (ps_in 6 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 48 ++ word_le8 48)) ps_wmem) pselect_model_kinds o
      ↔ o = Ok (mkEffect 4 [(ps_inp, word_le8 48), (ps_outp, word_le8 48)] []) pselect_model_kinds [] := by
  sys_norm

/-- A kernel reporting the write-only file unreadable — bit 4 dropped from
`readfds`, 3 in all — has consulted the access mode, which `vfs_poll` does
not; the answer is refused.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_select@v6.18.46 -/
theorem an_unreadable_write_only_file_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 6 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 48 ++ word_le8 48)) ps_wmem) pselect_model_kinds
        (Ok (mkEffect 3 [(ps_inp, word_le8 32), (ps_outp, word_le8 48)] []) m' evs) := by
  sys_refute

/-- A SOCKET is declined: `sock_poll` (net/socket.c:1426-1445) answers from
the protocol's own `->poll`, a function of what the peer has sent and of the
send queue, none of which the model represents.
kernel: net/socket.c:sock_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem a_socket_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 7 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 64)) ps_wmem)
        pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- A PIPE END is declined for the channel's reason: `pipe_poll`
(fs/pipe.c:660-706) reports EPOLLIN on a non-empty ring (:690) and EPOLLOUT
on one that is not full (:697), and a fresh read end is neither readable
nor — holding FMODE_READ alone — ever writable.
kernel: fs/pipe.c:pipe_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem a_pipe_end_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 8 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 128)) ps_wmem)
        pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- /dev/null is declined, and this decline is a GAP rather than a doubt:
`null_fops` (drivers/char/mem.c:644-652) has no `.poll`, so `vfs_poll` would
answer `DEFAULT_POLLMASK` and the kernel reports the descriptor readable and
writable.  The arm is not written yet; no refutation of that true answer is
stated here, because it is the answer.
kernel: include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem dev_null_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 9 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 256)) ps_wmem)
        pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- /dev/urandom is declined the same way: `urandom_fops`
(drivers/char/random.c:1572-1581) has no `.poll` — `random_poll` (:1414) is
installed on the blocking `random_fops` (:1563) only — so the kernel's
answer is again `DEFAULT_POLLMASK`, and again the arm is a gap.
kernel: drivers/char/random.c:random_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem dev_urandom_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 512)) ps_wmem)
        pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## `get_sigset_argpack` and `set_user_sigmask`: the sixth argument

`SYSCALL_DEFINE6(pselect6, …)` unpacks the {`sigset_t *`, `size_t`} pair
with `get_sigset_argpack` (fs/select.c:774-791, Linux v6.18.46, called at
:799-800) before `do_pselect` runs, and `do_pselect` calls `set_user_sigmask`
(kernel/signal.c:3281-3297, Linux v6.18.46) at :755-757, AFTER the timeout and
BEFORE
`core_sys_select` (:759). -/

/-- A real signal mask is declined
(`set_user_sigmask` saves `current->blocked` and installs the caller's,
kernel/signal.c:3292-3294).  The pack points at eight READABLE zero bytes
sixteen bytes past itself, so the kernel really would install the mask
here; the -EFAULT of an unreadable one is the next pin.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:get_sigset_argpack@v6.18.46 -/
theorem a_real_sigmask_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 (ps_sig + 16) ++ word_le8 8 ++ word_le8 0))
          (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- A mask pointer of 1 with the right size is -EFAULT in the kernel —
`set_user_sigmask`'s `copy_from_user` fails (kernel/signal.c:3289-3290)
after the size test passes (:3287-3288) — and the model declines it all the
same: `pselect_sigpack` never reads the mask, so a readable and an
unreadable real mask are one `PsSigReal` to it.  A gap the ppoll twin does
not have (`ppoll_an_unreadable_mask_is_efault`), recorded as one.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:get_sigset_argpack@v6.18.46 -/
theorem an_unreadable_real_mask_is_declined_too (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 8)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …while the SAME 16-byte pack with a wrong `sigsetsize` is -EINVAL
(kernel/signal.c:3287-3288).  The kernel's `sigset_t` is 8 bytes, so 8 is the
only size `set_user_sigmask` accepts; 4 is glibc's business, not the kernel's.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:get_sigset_argpack@v6.18.46 -/
theorem a_bad_sigsetsize_is_einval (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- THE ERRNO-ORDER PAIR.  `set_user_sigmask` runs in `do_pselect`
(fs/select.c:755-757) before `core_sys_select` (:759), so a call carrying
BOTH an unreadable descriptor set and a bad `sigsetsize` is -EINVAL: the set
is never copied in and its -EFAULT never happens.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem a_bad_sigsetsize_beats_an_unreadable_set (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- The other order — `get_fd_set`'s -EFAULT (fs/select.c:391) first — is
what a harness whose emulator copied the sets in first once answered, and
it is inadmissible for the kernel the model describes.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem efault_behind_a_bad_sigsetsize_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
        pselect_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- {NULL, 999} is NO MASK, not a bad size: `set_user_sigmask` returns 0 on a
NULL mask (kernel/signal.c:3285-3286) BEFORE it looks at `sigsetsize`
(:3287), so the second word is never judged.  That is what makes musl's plain
`select` — which always passes the constant pair {NULL, 8} rather than a
NULL sixth argument — an ordinary call rather than a declined one.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:get_sigset_argpack@v6.18.46 -/
theorem null_mask_ignores_the_size (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 0 ++ word_le8 999)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- …and {NULL, 8} — the pack musl's `select` actually passes — is no mask
either.  This is the shape the pin above cannot fix: a model that tested
the size BEFORE the pointer would still answer {NULL, 999} as no mask by
accident of the wrong size, and would take {NULL, 8} for a real mask and
decline it.  The kernel's order is pointer first (kernel/signal.c:3285-3286),
then size (:3287).
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:get_sigset_argpack@v6.18.46 -/
theorem null_mask_with_the_kernel_size_is_no_mask (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 0 ++ word_le8 8)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-! ## The three -EFAULTs, in the order the kernel raises them

`get_sigset_argpack` is read in the syscall entry (fs/select.c:799-800, Linux v6.18.46),
before `do_pselect` reads the timespec (:739-740) and before it calls
`set_user_sigmask` (:755-757); `core_sys_select` then copies all three sets
in (:669-672) before `max_select_fd` judges any of them (:494).  Rocq's
file pins none of the three -EFAULTs directly; these do, with the pointer
in question at `hole`. -/

/-- An unreadable {`sigset_t *`, `size_t`} pack is -EFAULT
(fs/select.c:781-782, :788-790, answered at :799-800).
kernel: fs/select.c:get_sigset_argpack,pselect6@v6.18.46 -/
theorem an_unreadable_argpack_is_efault (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 hole (bytes_at ps_inp (word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- …and it is raised BEFORE the timespec is judged: with the pack
unreadable and `tv_nsec` out of range, the answer is -EFAULT, because
`SYSCALL_DEFINE6(pselect6, …)` returns at :799-800 before `do_pselect`
reaches `poll_select_set_timeout` (:751-752).
kernel: fs/select.c:pselect6,get_sigset_argpack,do_pselect@v6.18.46 -/
theorem an_unreadable_argpack_beats_a_bad_timespec (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp hole
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- The -EINVAL of the timespec is the rejection there: it is two steps
further in.
kernel: fs/select.c:pselect6,get_sigset_argpack@v6.18.46 -/
theorem einval_ahead_of_an_unreadable_argpack_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 ps_tsp hole
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem) pselect_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- An unreadable timespec is -EFAULT (`get_timespec64`,
kernel/time/time.c:878-880, answered by `do_pselect` at fs/select.c:739-740).
kernel: fs/select.c:do_pselect; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem an_unreadable_timespec_is_efault (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 hole 0 (fun _ => none) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- …and it beats a wrong `sigsetsize`: `do_pselect` reads the timespec
(fs/select.c:739-740) before it calls `set_user_sigmask` (:755).
kernel: fs/select.c:do_pselect; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem an_unreadable_timespec_beats_a_bad_sigsetsize (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 hole ps_sig (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- The -EINVAL of `set_user_sigmask` is the rejection there.
kernel: fs/select.c:do_pselect@v6.18.46 -/
theorem einval_ahead_of_an_unreadable_timespec_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 hole ps_sig (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
        pselect_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- An unreadable descriptor set is -EFAULT (`get_fd_set`, fs/select.c:391,
through `core_sys_select`'s import at :669-672), with nothing written back.
kernel: fs/select.c:get_fd_set,core_sys_select@v6.18.46 -/
theorem an_unreadable_set_is_efault (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 hole 0 0 0 0 (fun _ => none) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- …and the import of all three sets (fs/select.c:669-672) precedes
`max_select_fd` (:494): an unreadable `writefds` beside a closed descriptor
in `readfds` is -EFAULT, not -EBADF.
kernel: fs/select.c:get_fd_set,core_sys_select,do_select@v6.18.46 -/
theorem an_unreadable_set_beats_a_closed_descriptor (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 ps_inp hole 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- The -EBADF is the rejection there: `max_select_fd` runs on kernel copies
that were never made.
kernel: fs/select.c:core_sys_select,do_select@v6.18.46 -/
theorem ebadf_ahead_of_an_unreadable_set_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 10 ps_inp hole 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem) pselect_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and `n < 0` is judged before any set is imported (fs/select.c:632-634
before :669-672): a negative `n` beside an unreadable `readfds` is -EINVAL,
not -EFAULT.
kernel: fs/select.c:core_sys_select,get_fd_set@v6.18.46 -/
theorem einval_for_a_negative_n_beats_an_unreadable_set (o : outcome SyscallEffect) :
    syscall_spec (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) hole 0 0 0 0 (fun _ => none) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-! ## `poll_select_finish`: the remaining-time write-back

Every return of `core_sys_select` passes through `poll_select_finish`
(fs/select.c:295-365, Linux v6.18.46, called at :760), which returns early for a NULL `tsp`
(:303-304) or a {0,0} end time (:310-311), and otherwise writes
`end_time - ktime_get_ts64()` back (:313-314, :342-344) after clamping a
negative remainder to {0,0} (:315-316). -/

/-- A real deadline plus a bit requested below `n` in `readfds` is declined:
the call returns early with 1, and the remaining time `poll_select_finish`
writes (fs/select.c:313-314) is a live clock reading the model cannot
produce.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem a_deadline_with_a_request_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- Drop the deadline and the same call answers: with `tsp` NULL the write
does not happen (fs/select.c:303-304), so the answer is forced.
kernel: fs/select.c:poll_select_finish,do_select@v6.18.46 -/
theorem the_same_request_without_a_deadline_is_answered (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- A real deadline with an EMPTY request runs to expiry and writes 16 ZERO
bytes.  `end_time` is in the past by then, so the clamp at fs/select.c:315-316
fires and `put_timespec64` (kernel/time/time.c:903-912) stores {0,0}: the
written value is forced rather than sampled.  This is
`select(0, NULL, NULL, NULL, &tv)`, the portable sleep.  It rests on the
personality premise `Sys/Fs/Select.lean`'s `pselect_finish` states: a
process whose personality carries `STICKY_TIMEOUTS` skips the write
(:306-307), and the Lean tree has no harness to rule that process out per
run, so this pin and its refutation below hold for the `PER_LINUX`-with-no-flag
word `execve` hands a program that never called `personality(2)`.
kernel: fs/select.c:poll_select_finish,do_select; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem an_empty_request_sleeps_and_writes_zeros (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0 (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model [] := by
  sys_norm

/-- A kernel returning 0 and leaving the timespec as the caller wrote it has
skipped the write-back at fs/select.c:342-344, which a non-NULL `tsp` with
a non-zero end time always reaches — unless the process carries
`STICKY_TIMEOUTS` (:306-307), the premise the pin above names.  Under that
flag this IS Linux's answer; the refutation holds for a process without it,
and says so rather than calling the answer a lie.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem a_sleep_leaving_the_timespec_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 ps_tsp 0 (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) ps_wmem)
        pselect_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The expiry write needs a WRITABLE timespec.  When `put_timespec64` fails,
`poll_select_finish` does not report -EFAULT: it falls through to `sticky:`
and returns `ret` — 0 — unchanged (fs/select.c:343-345, :361-364), with an
unspecified prefix of the sixteen bytes landed.  The model has no
representation for that prefix, so it declines the shape.
kernel: fs/select.c:poll_select_finish; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem an_unwritable_timespec_at_expiry_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0 (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) (fun _ => none))
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- A requested {0,0} with something READY polls once and answers the count
— and writes NO time back: `poll_select_set_timeout` stores {0,0} for it
(fs/select.c:279-280), `do_select` marks it timed out before the first pass
(:503-506), and `poll_select_finish` returns before the write for a zero
`end_time` (:310-311).
kernel: fs/select.c:poll_select_set_timeout,do_select,poll_select_finish@v6.18.46 -/
theorem a_zero_timeout_polls_once_and_writes_no_time (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- A kernel writing the {0,0} back after that poll has taken the early
return at fs/select.c:310-311 for the clamp at :315-316; refused.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem a_time_written_back_under_a_zero_timeout_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model
        (Ok (mkEffect 1 [(ps_inp, word_le8 8), (ps_tsp, word_le8 0 ++ word_le8 0)] []) m' evs) := by
  sys_refute

/-- AND THE EMPTY REQUEST IS NOT THE ONLY SHAPE THAT WAITS.  `DEFAULT_POLLMASK`
misses `POLLEX_SET` (fs/select.c:463), so an `exceptfds` bit can never fire
the third `retval++` (:550) and the set always comes back zeroed.  A request
naming an open file in `exceptfds` ALONE therefore still returns 0 and runs
to expiry — the same forced 16 zero bytes, plus the zeroed `exceptfds` word.
kernel: fs/select.c:poll_select_finish,do_select; include/linux/poll.h:vfs_poll; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem an_exceptfds_only_request_still_sleeps (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 0 0 ps_exp ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) (bytes_at ps_exp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 0 [(ps_exp, word_le8 0), (ps_tsp, word_le8 0 ++ word_le8 0)] [])
              pselect_model [] := by
  sys_norm

/-- The same empty request under a NULL timeout is DECLINED, and not
answered 0.  `schedule_hrtimeout_range_clock` treats a NULL expiry as
infinite (kernel/time/sleep_timeout.c:206-209), so `do_select`'s `timed_out`
flag is never set (fs/select.c:603-605) and the loop cannot exit with a zero
count (:575-576): the call never returns.
kernel: kernel/time/sleep_timeout.c:schedule_hrtimeout_range_clock; fs/select.c:do_select@v6.18.46 -/
theorem a_null_timeout_with_nothing_requested_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 0 0 (fun _ => none) ps_wmem) pselect_model o ↔ o = Unmodeled := by
  sys_norm

/-- `pselect6(0, NULL, NULL, NULL, NULL, NULL) == 0` is unreachable, and a
kernel reporting it is inventing a return.
kernel: kernel/time/sleep_timeout.c:schedule_hrtimeout_range_clock; fs/select.c:do_select@v6.18.46 -/
theorem an_invented_zero_under_a_null_timeout_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 0 0 (fun _ => none) ps_wmem) pselect_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## Where an errno comes from decides whether it survives the write-back

`n = -1` (the register holds 0xFFFFFFFF; `SYSCALL_DEFINE6` casts it to
`int`) is -EINVAL out of `core_sys_select` (fs/select.c:632-634, Linux v6.18.46), which
`do_pselect` hands to `poll_select_finish` (:760).  A wrong `sigsetsize` is
also -EINVAL, but out of `set_user_sigmask`, which `do_pselect` returns
DIRECTLY (:755-757) and never reaches the write-back. -/

/-- With no deadline, `core_sys_select`'s -EINVAL is the answer.
kernel: fs/select.c:core_sys_select,poll_select_finish@v6.18.46 -/
theorem einval_from_core_sys_select_without_a_deadline (o : outcome SyscallEffect) :
    syscall_spec (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- With a real deadline it is DECLINED — the error still passes through
`poll_select_finish`, which writes a live clock reading to `*tsp` on its way
out (fs/select.c:313-314, :342-344).
kernel: fs/select.c:core_sys_select,poll_select_finish@v6.18.46 -/
theorem einval_from_core_sys_select_under_a_deadline_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- The wrong `sigsetsize` is answered even with the deadline in place, and
even though `n` is also invalid: `set_user_sigmask`'s -EINVAL
(kernel/signal.c:3287-3288) returns from `do_pselect` (fs/select.c:755-757)
before `core_sys_select` and before the write-back.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem einval_from_set_user_sigmask_survives_the_deadline (o : outcome SyscallEffect) :
    syscall_spec (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 ps_tsp ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 4))
          (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0))
            (bytes_at ps_inp (word_le8 8))))
        ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-! ## The write-back gate and the zero-length copies -/

/-- The set is readable, so the import succeeds and the call has an answer —
but the bitmap is not WRITABLE, and `set_fd_set` (fs/select.c:397-403) is a
`__copy_to_user`, which lands an unspecified PREFIX and then faults, with
`core_sys_select` reporting -EFAULT for the whole call (:688-691).  The
model has no representation for "some number of bytes landed", so it
declines the shape rather than assert a byte count it cannot derive.
kernel: fs/select.c:set_fd_set,core_sys_select@v6.18.46 -/
theorem a_set_readable_but_not_writable_is_declined (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) (fun _ => none))
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- `n = 0` never DEREFERENCES a set pointer.  `FDS_BYTES(0)` (fs/select.c:381)
is 0, so `get_fd_set` (:386-395) and `set_fd_set` (:397-403) both copy zero
bytes and a wild pointer is never touched — no -EFAULT, and nothing written
back.  The timeout here is a requested {0,0} rather than NULL, because a
NULL timeout with nothing requested is the unreachable shape above; {0,0}
polls once and returns, and `poll_select_finish` writes nothing for it
either (:310-311).
kernel: fs/select.c:FDS_BYTES,get_fd_set,set_fd_set,poll_select_finish@v6.18.46 -/
theorem n_zero_never_dereferences_a_set_pointer (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 65536 65536 65536 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 0 [] []) pselect_model [] := by
  sys_norm

/-! ## The timespec is judged raw

`do_pselect` hands `poll_select_set_timeout` the fields exactly as the
program wrote them (fs/select.c:751, Linux v6.18.46), `get_timespec64`
(kernel/time/time.c:872-892, Linux v6.18.46) normalizes nothing, and
`timespec64_valid` (include/linux/time64.h:97-106, Linux v6.18.46) rejects
`tv_sec < 0` (:100-101) and a
`tv_nsec` at or above `NSEC_PER_SEC` read as `unsigned long` (:103).  The
carry that would make 1000000000 one second belongs to `kern_select`
(fs/select.c:712-714, Linux v6.18.46), which serves numbers riscv64 does not have. -/

/-- `tv_nsec` exactly at `NSEC_PER_SEC`: out of range, not one second.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem tv_nsec_at_nsec_per_sec_is_einval (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0 (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- …and no carry rescues a negative `tv_sec` (include/linux/time64.h:100-101).
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem a_negative_tv_sec_is_not_rescued_by_a_carry (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 (Z_to_bv 64 (-1)) ++ word_le8 2000000000)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- A negative `tv_sec` is -EINVAL ON ITS OWN (include/linux/time64.h:100-101),
with a `tv_nsec` the other test accepts: the pin above pairs it with a
`tv_nsec` of 2·10^9, which the `NSEC_PER_SEC` test (:103) refuses by itself,
so only this one shows the `tv_sec < 0` test firing.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem a_negative_tv_sec_alone_is_einval (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 (Z_to_bv 64 (-1)) ++ word_le8 0)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- A kernel taking {-1, 0} for a deadline already past — 0, sixteen zero
bytes written — has skipped `timespec64_valid`; refused.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem a_negative_tv_sec_taken_as_expired_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 (Z_to_bv 64 (-1)) ++ word_le8 0)) ps_wmem) pselect_model
        (Ok (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) m' evs) := by
  sys_refute

/-- A negative `tv_nsec` is enormous as an `unsigned long`
(include/linux/time64.h:103), so it is -EINVAL and not a borrow from `tv_sec`.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem a_negative_tv_nsec_is_einval (o : outcome SyscallEffect) :
    syscall_spec (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 2 ++ word_le8 (Z_to_bv 64 (-1000000000)))) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- The deadline a normalizing model would have answered instead — one
second's sleep, 16 zero bytes written — is the answer a real kernel refused
with -22 when the harness caught it.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem the_normalized_deadline_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 0 0 0 0 ps_tsp 0 (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
        pselect_model (Ok (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) m' evs) := by
  sys_refute

/-! ## Overlapping sets are modeled, and naming both writes is the point

`set_fd_set` runs three times in `inp`, `outp`, `exp` order
(fs/select.c:688-690, Linux v6.18.46) and the last write wins; the effect ledger names the
writes in that same order.  No memory snapshot can observe two writes to one
address, which is why these are pinned here and recorded in
bugs/pselect6-overlapping-sets.md. -/

/-- `readfds` aliased with `exceptfds`, the pair whose two words DIFFER: the
file is readable but never exceptional, so the address takes the imported
request first and zero second.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem aliased_read_and_except_sets_name_both_writes (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(ps_inp, word_le8 8), (ps_inp, word_le8 0)] []) pselect_model [] := by
  sys_norm

/-- The ledger a memory snapshot would produce — the surviving word reported
for both entries, losing the first write entirely — is not a trace the
kernel makes: `set_fd_set` stores the result of the `readfds` scan, not zero.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem the_snapshot_ledger_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (ps_in 4 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem) pselect_model
        (Ok (mkEffect 1 [(ps_inp, word_le8 0), (ps_inp, word_le8 0)] []) m' evs) := by
  sys_refute

/-- Aliasing `readfds` with `writefds`, the pair whose two words AGREE, since
both are the imported request.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem aliased_read_and_write_sets_agree (o : outcome SyscallEffect) :
    syscall_spec (ps_in 4 ps_inp ps_inp 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect 2 [(ps_inp, word_le8 8), (ps_inp, word_le8 8)] []) pselect_model [] := by
  sys_norm

/-- Only the WRITING path is affected: raise `n` past a closed descriptor and
the same aliased pointers answer the errno, naming no write.
kernel: fs/select.c:max_select_fd,core_sys_select@v6.18.46 -/
theorem aliased_sets_still_answer_ebadf (o : outcome SyscallEffect) :
    syscall_spec (ps_in 10 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) pselect_model [] := by
  sys_norm

/-! ## The ppoll fixtures

Rocq's: they sit well clear of the pselect6 ones so a bad address in one
cannot be answered by the other's bytes.  `pp_ufds` has room for the
30-entry band (`ppoll_nfds_max` * 8 = 240 bytes) and the timeout and mask
follow it. -/

def pp_ufds : word := 8192
def pp_tsp  : word := 8448
def pp_sig  : word := 8480

/-- Everything the ppoll examples name is writable — the 512 bytes from
`pp_ufds` on — except where one passes `fun _ => none` on purpose.  A range
test rather than Rocq's 512-byte list; the header says why. -/
def pp_wmem : word → Option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a 8704 then some 0 else none

/-- One `struct pollfd` (include/uapi/asm-generic/poll.h:36-40, Linux v6.18.46): `int fd`,
`short events`, `short revents`, little-endian, 8 bytes.  The `revents` the
caller supplies is always 0 here — the kernel overwrites it whatever it
held, and the write-back pins below are what say so. -/
def pp_entry (fd events : Int) : List byte :=
  word_le4 (Z_to_bv 64 fd) ++ word_le2 (Z_to_bv 64 events) ++ word_le2 (Z_to_bv 64 0)

def pp_entries (k : Nat) (e : List byte) : List byte := (List.replicate k e).flatten

/-- A 16-byte `struct __kernel_timespec`. -/
def pp_ts (sec nsec : Int) : List byte :=
  word_le8 (Z_to_bv 64 sec) ++ word_le8 (Z_to_bv 64 nsec)

/-- A ppoll call: the five argument registers in `SYSCALL_DEFINE5(ppoll, …)`'s
order (fs/select.c:1095-1097, Linux v6.18.46) — `ufds`, `nfds`, `tsp`, `sigmask`,
`sigsetsize` — over the given readable and writable views of memory. -/
def pp_in (ufds nfds tsp sig sigsetsize : word) (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 73 [ufds, nfds, tsp, sig, sigsetsize, 0] mem wmem

attribute [sys_simp low] pp_in.eq_1

/-! ## The dispatcher line: 73, and `nfds` narrowed to `unsigned int` -/

/-- Syscall 73 is `ppoll`: `__NR_ppoll 73` (include/uapi/asm-generic/unistd.h:194,
Linux v6.18.46), and riscv64 has no `poll` number at all.
kernel: include/uapi/asm-generic/unistd.h:__NR_ppoll@v6.18.46 -/
example : (73 : Int) ∈ modeled_sysnos := by decide

/-- `nfds` is an `unsigned int` (fs/select.c:1095), narrowed by riscv64's
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88) through
`__SC_CAST` (include/linux/syscalls.h:132) before `do_sys_poll` compares it
with the limit: a register holding 2^32 + 1 is the one-entry call of
`ppoll_counts_descriptors_not_bits` below, not a count above `RLIMIT_NOFILE`.
The table line applies `Syscall.unfds32` for exactly that reason.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:ppoll,do_sys_poll@v6.18.46 -/
theorem ppoll_nfds_is_narrowed_to_unsigned_int (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds (Z_to_bv 64 (2 ^ 32 + 1)) 0 0 0 (bytes_at pp_ufds (pp_entry 3 1)) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model [] := by
  sys_norm

/-! ## `do_poll` and `do_pollfd`: a descriptor count, an answer per entry

`do_poll` (fs/select.c:876-962, Linux v6.18.46) increments `count` once per entry whose
`do_pollfd` answered a non-zero mask (:913-916) and stores
`mangle_poll(mask)` in the entry's `revents` (:914); `do_pollfd` (:853-874)
returns 0 for a negative `fd` (:860-861), `EPOLLNVAL` for one that is not
open (:864-865) and `vfs_poll(...) & filter` otherwise (:868-873). -/

/-- POLL IS A DESCRIPTOR COUNT WHERE SELECT IS A BIT COUNT.  An entry asking
for POLLIN|POLLOUT on a file that is ready for both contributes 1
(fs/select.c:915-916) — where the same descriptor named in both `readfds`
and `writefds` contributes 2 to pselect6's return.  The `revents` written
back is `DEFAULT_POLLMASK & events` = 5, two bytes at offset 6 of the entry
(:1019-1020), and the `fd` and `events` fields in front of it are NOT
rewritten — which is why the ledger names a 2-byte write and not an 8-byte
one.
kernel: fs/select.c:do_poll,do_pollfd,do_sys_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_counts_descriptors_not_bits (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model [] := by
  sys_norm

/-- Importing select's rule would answer 2, and that is a lie: `count++`
runs once per entry (fs/select.c:915-916).
kernel: fs/select.c:do_poll@v6.18.46 -/
theorem ppoll_a_bit_count_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem) pselect_model
        (Ok (mkEffect 2 [(pp_ufds + 6, word_le2 5)] []) m' evs) := by
  sys_refute

/-- AN UNOPENED DESCRIPTOR IS AN ANSWER, NOT AN ERROR, and this is the one
place ppoll and pselect6 disagree about the same descriptor: `do_pollfd`
returns `EPOLLNVAL` when `fd_empty` holds (fs/select.c:864-865), so the entry
reports POLLNVAL (0x20, include/uapi/asm-generic/poll.h:11) and COUNTS
(:915-916).
kernel: fs/select.c:do_pollfd,do_poll; include/uapi/asm-generic/poll.h:POLLNVAL@v6.18.46 -/
theorem ppoll_an_unopened_descriptor_is_pollnval (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []) pselect_model [] := by
  sys_norm

/-- select's answer — -EBADF for the whole call — is the rejection it is:
nothing in `do_sys_poll` or `do_poll` returns -EBADF.
kernel: fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_ebadf_for_an_unopened_descriptor_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem) pselect_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A NEGATIVE `fd` IS NEITHER.  `do_pollfd` returns 0 (fs/select.c:860-861)
before `CLASS(fd, f)` (:863), so the entry is not looked up at all: its
`revents` is written as 0 and it does not count.  The timeout is a requested
{0,0} rather than NULL because a NULL one with a zero count never returns.
kernel: fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_negative_fd_is_skipped (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model [] := by
  sys_norm

/-- POLLNVAL — what a reader who took "not a valid descriptor" as the
condition would write — is the rejection: the `fd < 0` test precedes the
`fd_empty` one.
kernel: fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_pollnval_for_a_negative_fd_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
        pselect_model (Ok (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []) m' evs) := by
  sys_refute

/-- `events` IS A FILTER, and a bit outside `DEFAULT_POLLMASK` selects
nothing.  `do_pollfd` answers `vfs_poll(...) & (demangle_poll(events) |
EPOLLERR | EPOLLHUP)` (fs/select.c:868, :873), and neither EPOLLERR nor
EPOLLHUP is in `DEFAULT_POLLMASK` (include/linux/poll.h:24), so a
POLLPRI-only request on a regular file reports an empty `revents` and does
not count.
kernel: fs/select.c:do_pollfd,do_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_events_filters_the_default_pollmask (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 2))) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model [] := by
  sys_norm

/-- The answer a model that echoed `events` back would give is refused: the
file is never exceptional.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_an_echoed_events_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 2))) pp_wmem)
        pselect_model (Ok (mkEffect 1 [(pp_ufds + 6, word_le2 2)] []) m' evs) := by
  sys_refute

/-- A CHANNEL IS DECLINED, for the reason pselect6 declines it: `pipe_poll`
(fs/pipe.c:660-706) answers from what the peer has written so far.
kernel: fs/select.c:do_pollfd; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem ppoll_a_channel_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 0 1))) pp_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- Not even an `events` of 0 makes the answer derivable, since EPOLLERR and
EPOLLHUP are in the filter unconditionally (fs/select.c:868) and `pipe_poll`
can report both (fs/pipe.c:691-704).
kernel: fs/select.c:do_pollfd; fs/pipe.c:pipe_poll@v6.18.46 -/
theorem ppoll_a_channel_with_no_events_is_still_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 0 0))) pp_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## Every descriptor kind, one pin per match arm of the ppoll entry

The same kinds, one entry at a time, on `pselect_model_kinds`; the arms these
pins reach are `ppoll_revents_of`'s. -/

/-- A write-only file polls as any other: `vfs_poll` (include/linux/poll.h:78-83)
never reads `f_mode`, so fd 4 (`FdFileW`) asked for POLLIN|POLLOUT reports
`DEFAULT_POLLMASK & 5` = 5 and counts.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_write_only_file_polls_as_any_other (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 4 5)) pp_wmem) pselect_model_kinds o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model_kinds [] := by
  sys_norm

/-- A directory polls as any other too: no directory `file_operations`
defines `->poll`, so fd 5 (`FdDir`) asked for POLLIN reports 1 and counts.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_directory_polls_as_any_other (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 5 1)) pp_wmem) pselect_model_kinds o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model_kinds [] := by
  sys_norm

/-- A socket entry is declined: `sock_poll` (net/socket.c:1426-1445) defers
to the protocol, whose answer the model cannot derive.
kernel: net/socket.c:sock_poll; fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_a_socket_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 6 1)) pp_wmem) pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- A pipe end is declined, as the channel is: `pipe_poll` (fs/pipe.c:660-706)
answers from the ring.
kernel: fs/pipe.c:pipe_poll; fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_a_pipe_end_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 7 1)) pp_wmem) pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- /dev/null is declined as a GAP: `null_fops` (drivers/char/mem.c:644-652)
has no `.poll`, so the kernel answers `DEFAULT_POLLMASK & events` = 1 here;
the arm is not written, and no refutation of that true answer is stated.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_dev_null_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 8 1)) pp_wmem) pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- /dev/urandom the same way: `urandom_fops` (drivers/char/random.c:1572-1581)
has no `.poll`; `random_poll` (:1414) belongs to `random_fops` (:1563).
kernel: drivers/char/random.c:random_poll; fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_dev_urandom_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem) pselect_model_kinds o
      ↔ o = Unmodeled := by
  sys_norm

/-- ASK FOR EVERY BIT AND `DEFAULT_POLLMASK` COMES BACK WHOLE.  An `events`
of 0xffff selects all sixteen bits, and `vfs_poll`'s answer for a file with
no `->poll` is `EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM` (include/linux/poll.h:24)
= 0x1|0x4|0x40|0x100 = 325, no more: EPOLLERR and EPOLLHUP, though in the
filter (fs/select.c:868), are not in the mask.  The pins asking for 1, 2 and
5 cannot tell 325 from 5; this one holds the two high bits.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_every_event_requested_returns_the_default_pollmask (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 0xffff)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 325)] []) pselect_model [] := by
  sys_norm

/-- A kernel echoing the whole request — every bit set in `revents` — has
reported EPOLLPRI, EPOLLERR, EPOLLHUP and EPOLLNVAL on an open regular
file; refused.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd@v6.18.46 -/
theorem ppoll_an_echoed_full_events_word_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 0xffff)) pp_wmem) pselect_model
        (Ok (mkEffect 1 [(pp_ufds + 6, word_le2 0xffff)] []) m' evs) := by
  sys_refute

/-! ## `do_sys_poll`: the limit, the copy, the stack bound

`do_sys_poll` (fs/select.c:967-1039, Linux v6.18.46) tests `nfds > rlimit(RLIMIT_NOFILE)`
first (:981-982), copies the whole array in (:991-993), keeps at most
`N_STACK_PPS` = 30 entries on the stack (:964-965, :984) and chains
`kmalloc`ed blocks after that (:999-1005). -/

set_option maxRecDepth 8192 in
/-- THE STACK BOUND.  At 31 entries the chain is extended by a `kmalloc`
(fs/select.c:999-1001) that can answer -ENOMEM (:1002-1004), so the model
declines.  Every entry here names `fd = -1`, so nothing but the count can be
the reason.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_above_the_stack_bound_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 31 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 31 (pp_entry (-1) 0))))
        pp_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 8192 in
/-- At 30 the SAME array is inside the band: every entry is `fd = -1`, so the
call answers 0 with thirty zero `revents` — stated, as Rocq states it, as
"not declined" rather than by spelling out thirty 2-byte writes.
kernel: fs/select.c:do_sys_poll,do_poll@v6.18.46 -/
theorem ppoll_at_the_stack_bound_is_answered :
    ¬ syscall_spec (pp_in pp_ufds 30 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 30 (pp_entry (-1) 0))))
        pp_wmem) pselect_model Unmodeled := by
  sys_refute

/-- The same bound, placed against the copy: with the array unreadable, the
-EFAULT of the one copy in `do_sys_poll` (fs/select.c:991-993, Linux v6.18.46) is
answered at 30,
which proves the copy was attempted — the bound did not fire.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_at_the_stack_bound_the_array_is_read (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 30 0 0 0 (fun _ => none) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- …and one entry more, over the identical unreadable array, is declined
rather than -EFAULT: the count is the only thing that changed.  The kernel's
own answer here is deterministic — the first `copy_from_user` of 30 entries
(fs/select.c:991-993) fails before the `kmalloc` (:1000) is reached — but the
band is a bound on the count alone, taken before the copy, so the model
declines the shape instead of following the copy into it.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_above_the_stack_bound_the_array_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 31 0 0 0 (fun _ => none) pp_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- `nfds` ABOVE THE SOFT RLIMIT_NOFILE IS -EINVAL, AND IT IS DECIDED FIRST.
`do_sys_poll` tests `nfds > rlimit(RLIMIT_NOFILE)` (fs/select.c:981-982)
before it copies a byte, so the answer here is -EINVAL even though `ufds` is
unreadable: the -EFAULT that pointer would raise never happens.  The limit is
answered from state (`State.m_nofile`, the soft limit the run was launched
with).
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_nfds_above_the_soft_limit_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 5 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model_lim [] := by
  sys_norm

/-- A kernel answering -EFAULT for it has copied before testing the limit,
which `do_sys_poll` does not do.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_efault_ahead_of_the_limit_test_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 5 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- `nfds` EQUAL to the limit is inside it: the test is `nfds > rlimit(RLIMIT_NOFILE)`
(fs/select.c:981-982), strict, so four entries under a limit of 4 reach the
copy (:991-993), whose -EFAULT for the unreadable array is the answer — proof
that the limit test let the call through.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_nfds_at_the_soft_limit_is_answered (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 4 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model_lim [] := by
  sys_norm

/-- -EINVAL at `nfds == RLIMIT_NOFILE` is the off-by-one the kernel does
not have; refused.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_einval_at_the_soft_limit_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 4 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- THE LIMIT IS TESTED BEFORE THE BAND.  `nfds` = 31 is above `N_STACK_PPS`
and above the limit of 4; `do_sys_poll` answers the limit's -EINVAL first
(fs/select.c:981-982), before `N_STACK_PPS` matters (:984), so the model's
own decline of the band never gets a turn.  This is the order the
`ppoll_core` docstring claims; without a pin the two tests could be swapped
unnoticed.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_above_the_limit_and_the_band_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 31 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model_lim [] := by
  sys_norm

/-- A kernel copying the array before testing the limit — -EFAULT here —
does what `do_sys_poll` does not; refused.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_efault_above_the_limit_and_the_band_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 31 0 0 0 (fun _ => none) pp_wmem) pselect_model_lim
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A KERNEL-SPACE ARRAY WITH ENTRIES IS -EFAULT, not a decline: the one copy
in `do_sys_poll` (fs/select.c:991-993, Linux v6.18.46) is refused by
`_inline_copy_from_user`'s range test (include/linux/uaccess.h:168, Linux
v6.18.46) before a byte is read, and `do_ppoll` in QEMU 11.1.1
(linux-user/syscall.c:1559-1563) refuses the range the same way through
`lock_user` — both answers are -EFAULT, so it is inside the intersection.
Only the ZERO-length call, below, has two answers.
kernel: fs/select.c:do_sys_poll; include/linux/uaccess.h:_inline_copy_from_user@v6.18.46 -/
theorem ppoll_a_kernel_space_array_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pp_in (user_top + 1) 1 0 0 0 (fun _ => none) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- AN UNREADABLE ARRAY IS -EFAULT once the limit test is past.  One
`copy_from_user` takes the whole array (fs/select.c:991-993), so a single
unreadable byte fails all of it — `err` starts at -EFAULT (:971) and the jump
keeps it — and nothing is written back.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_an_unreadable_array_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (fun _ => none) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- `nfds = 0` NEVER DEREFERENCES `ufds`.  `len` is 0 (fs/select.c:984), the
loop breaks before the copy (:988-989), `do_poll` walks no entries and the
write-back loop writes none (:1019-1020), wherever in user space the pointer
points: `user_write_access_begin(ufds, 0)` (:1012-1013) still asks
`access_ok`, which a user-space address passes mapped or not.  With a
requested {0,0} the call polls once and returns 0, and `poll_select_finish`
writes nothing for it either (:310-311).
kernel: fs/select.c:do_sys_poll,poll_select_finish@v6.18.46 -/
theorem ppoll_nfds_zero_never_dereferences_ufds (o : outcome SyscallEffect) :
    syscall_spec (pp_in 65536 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 0 [] []) pselect_model [] := by
  sys_norm

/-! ### The zero-length call on a kernel-space pointer

`user_write_access_begin(ufds, nfds * sizeof(*ufds))` (fs/select.c:1012-1013,
Linux v6.18.46) runs at `nfds = 0` too; on riscv64 it is `user_access_begin`
(arch/riscv/include/asm/uaccess.h:456-462, Linux v6.18.46), which is
`access_ok`, and `__access_ok` (include/asm-generic/access_ok.h:31-41, Linux
v6.18.46) with a size of 0 is
`addr <= TASK_SIZE_MAX`.  A pointer above `TASK_SIZE` fails it and the call
is -EFAULT (`err`, :971).  Rocq's spec answers 0 there; the Lean twin
declines, for the reason its `ppoll_core` docstring gives. -/

/-- `nfds = 0` with `ufds` in the kernel half of the address space is
declined: Linux answers -EFAULT through `access_ok`, and Rocq's 0 is not an
answer this twin may keep.
kernel: fs/select.c:do_sys_poll; arch/riscv/include/asm/uaccess.h:user_access_begin; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_nfds_zero_with_a_kernel_space_ufds_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in (Z_to_bv 64 0xffff800000000000) 0 pp_tsp 0 0
        (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and in particular the 0 the Rocq spec answers is refused.
kernel: fs/select.c:do_sys_poll; arch/riscv/include/asm/uaccess.h:user_access_begin; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_zero_for_a_kernel_space_ufds_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in (Z_to_bv 64 0xffff800000000000) 0 pp_tsp 0 0
        (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- THE EDGE IS `TASK_SIZE` ITSELF.  `__access_ok` with a size of 0 accepts
`addr <= TASK_SIZE_MAX - 0` (include/asm-generic/access_ok.h:40), so a `ufds`
exactly at the top of user space passes and the zero-length call is
answered 0, as it is for any user-space pointer.
kernel: fs/select.c:do_sys_poll; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_nfds_zero_at_the_top_of_user_space_is_answered (o : outcome SyscallEffect) :
    syscall_spec (pp_in user_top 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 0 [] []) pselect_model [] := by
  sys_norm

/-- …and one byte above it is declined: Linux answers -EFAULT there, and
QEMU 11.1.1's `do_ppoll` (linux-user/syscall.c:1553-1563) never looks at the
pointer when `nfds` is 0 and answers 0, so no single answer is in the
intersection.
kernel: fs/select.c:do_sys_poll; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_nfds_zero_one_byte_above_user_space_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in (user_top + 1) 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- TWO ENTRIES, TWO WRITES, EACH AT ITS OWN OFFSET.  `do_sys_poll` writes
`revents` with `ufds++` between entries (fs/select.c:1019-1020), so the
second entry's two bytes land at offset 8 + 6 = 14, and `do_poll` counts
each non-zero mask (:915-916): an open file asked for POLLIN and an unopened
descriptor both count, 2 in all.
kernel: fs/select.c:do_sys_poll,do_poll,do_pollfd@v6.18.46 -/
theorem ppoll_writes_each_entry_at_its_own_offset (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 2 0 0 0 (bytes_at pp_ufds (pp_entry 3 1 ++ pp_entry 9 1)) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 2 [(pp_ufds + 6, word_le2 1), (pp_ufds + 14, word_le2 32)] [])
              pselect_model [] := by
  sys_norm

/-- A write-back that forgot to advance `ufds` — both `revents` at the first
entry's offset — is refused.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_a_second_entry_at_the_first_offset_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 2 0 0 0 (bytes_at pp_ufds (pp_entry 3 1 ++ pp_entry 9 1)) pp_wmem)
        pselect_model
        (Ok (mkEffect 2 [(pp_ufds + 6, word_le2 1), (pp_ufds + 6, word_le2 32)] []) m' evs) := by
  sys_refute

/-! ## `poll_select_finish`, reached from `do_sys_poll` with `PT_TIMESPEC`

The same function pselect6 reaches, with the same argument (fs/select.c:1116, Linux v6.18.46):
an expired deadline writes the clamped {0,0} (:315-316, :342-344), an early
return writes a live clock reading, and a NULL `tsp` writes nothing. -/

/-- An empty request under a real deadline runs to expiry, returns 0 and
writes 16 ZERO bytes over `*tsp`, because `end_time` is in the past by then
and the `rts.tv_sec < 0` clamp (fs/select.c:315-316) fires — under the same
`STICKY_TIMEOUTS` premise (:306-307) the pselect6 sleep pins carry.
kernel: fs/select.c:poll_select_finish,do_poll; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem ppoll_a_deadline_expires_to_zeros (o : outcome SyscallEffect) :
    syscall_spec (pp_in 0 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 0 [(pp_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model [] := by
  sys_norm

/-- A requested {0,0} with a READY entry polls once, answers 1 and writes
NO time back: `do_poll` marks the call timed out before its first pass
(fs/select.c:887-890) and `poll_select_finish` returns before the write for
a zero `end_time` (:310-311).  Rocq states this shape on a read-write file;
here it is the read-only one.
kernel: fs/select.c:do_poll,do_pollfd,poll_select_finish@v6.18.46 -/
theorem ppoll_a_zero_timeout_polls_once_and_writes_no_time (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 5))) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model [] := by
  sys_norm

/-- A kernel writing {0,0} back after that poll has taken the early return
at fs/select.c:310-311 for the clamp; refused.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem ppoll_a_time_written_back_under_a_zero_timeout_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 5))) pp_wmem)
        pselect_model
        (Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5), (pp_tsp, word_le8 0 ++ word_le8 0)] []) m' evs) := by
  sys_refute

/-- An errno out of `do_sys_poll` under a real deadline is declined, as
pselect6's is: the limit's -EINVAL (fs/select.c:981-982) still passes
through `poll_select_finish` (:1116), which writes a live remaining time
(:313-314) on its way out.
kernel: fs/select.c:do_sys_poll,poll_select_finish@v6.18.46 -/
theorem ppoll_an_errno_under_a_deadline_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 5 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000)) pp_wmem)
        pselect_model_lim o
      ↔ o = Unmodeled := by
  sys_norm

/-- Put something ready in the array instead and the return comes back
EARLY, so the remaining time is a live clock reading (fs/select.c:313-314):
declined, not an invented 0.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem ppoll_an_early_return_under_a_deadline_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 1000000)) (bytes_at pp_ufds (pp_entry 3 1))) pp_wmem)
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- A NULL TIMEOUT WITH NOTHING READY IS DECLINED, and not answered 0.
`schedule_hrtimeout_range_clock` treats a NULL expiry as infinite
(kernel/time/sleep_timeout.c:206-209), so `do_poll`'s `timed_out` flag is
never set (fs/select.c:958-959) and the loop cannot exit with a zero count
(:934-935): the call never returns.
kernel: kernel/time/sleep_timeout.c:schedule_hrtimeout_range_clock; fs/select.c:do_poll@v6.18.46 -/
theorem ppoll_a_null_timeout_with_nothing_ready_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry (-1) 0)) pp_wmem) pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- Give it a ready descriptor and the same NULL timeout is an ordinary
answer — the shape libraries actually issue.
kernel: fs/select.c:do_poll,do_pollfd,poll_select_finish@v6.18.46 -/
theorem ppoll_a_ready_descriptor_under_a_null_timeout_is_answered (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 1)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model [] := by
  sys_norm

/-- THE WRITE-BACK GATE.  The array is readable, so the import succeeds and
the call has an answer — but the entry is not WRITABLE, and the `revents`
write-back is a `user_write_access_begin` plus a run of `unsafe_put_user`s
(fs/select.c:1012-1022), which lands an unspecified PREFIX and then faults
(:1035-1038).  Linux answers -EFAULT for the whole call after some entries
may already have been updated; the model has no representation for that, so
it declines rather than assert which entries landed.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_an_unwritable_array_is_declined (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 1)) (fun _ => none))
        pselect_model o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## The errno order, and it is not pselect6's

pselect6 reads its {`sigset_t *`, `size_t`} pack in the syscall entry, BEFORE
the timeout (fs/select.c:799-800, Linux v6.18.46); ppoll has five arguments and needs no
pack, so `get_timespec64` runs first (:1103-1104) and `set_user_sigmask`
second (:1111-1113). -/

/-- An unreadable timeout beats a wrong `sigsetsize` here, where the
transplanted pselect6 order would answer -EINVAL.
kernel: fs/select.c:ppoll; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem ppoll_an_unreadable_timeout_beats_a_bad_sigsetsize (o : outcome SyscallEffect) :
    syscall_spec (pp_in 0 0 pp_tsp pp_sig 4 (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-- That -EINVAL is the rejection it is: `set_user_sigmask` is not reached
until `get_timespec64` has succeeded (fs/select.c:1103-1104, :1111).
kernel: fs/select.c:ppoll@v6.18.46 -/
theorem ppoll_einval_ahead_of_the_timeout_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in 0 0 pp_tsp pp_sig 4 (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
        pselect_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The other side of the same order: with the timeout fine, the wrong
`sigsetsize` is answered (kernel/signal.c:3287-3288), and it beats the
-EFAULT the unreadable array would otherwise raise — `ppoll`
(fs/select.c:1095-1117, Linux v6.18.46) calls `set_user_sigmask` at
:1111-1113 before it lets `do_sys_poll` copy anything at :1115.
kernel: fs/select.c:ppoll; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem ppoll_a_bad_sigsetsize_beats_an_unreadable_array (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 pp_tsp pp_sig 4
        (mem_join (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
        pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- The timespec is judged raw here as in pselect6: `tv_nsec` at
`NSEC_PER_SEC` is -EINVAL out of `poll_select_set_timeout` (fs/select.c:1107-1108,
`timespec64_valid` at include/linux/time64.h:103), not one second.
kernel: fs/select.c:ppoll,poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem ppoll_a_bad_timespec_is_einval (o : outcome SyscallEffect) :
    syscall_spec (pp_in 0 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000000)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- The one-second sleep a normalizing model would answer is refused.
kernel: fs/select.c:ppoll,poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem ppoll_the_normalized_deadline_is_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pp_in 0 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000000)) pp_wmem) pselect_model
        (Ok (mkEffect 0 [(pp_tsp, word_le8 0 ++ word_le8 0)] []) m' evs) := by
  sys_refute

/-- A wrong `sigsetsize` is answered even under a real deadline: the -EINVAL
returns from the syscall entry (fs/select.c:1111-1113) before `do_sys_poll`
and before `poll_select_finish`, so no remaining time is written.
kernel: fs/select.c:ppoll; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem ppoll_a_bad_sigsetsize_survives_the_deadline (o : outcome SyscallEffect) :
    syscall_spec (pp_in 0 0 pp_tsp pp_sig 4
        (mem_join (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) (bytes_at pp_tsp (pp_ts 0 1000000)))
        pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) pselect_model [] := by
  sys_norm

/-- A NULL mask with a wrong `sigsetsize` is NO MASK: `set_user_sigmask`
returns 0 on the NULL pointer (kernel/signal.c:3285-3286) before it reads the
size (:3287), so the call is answered as if the two arguments were absent.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:ppoll@v6.18.46 -/
theorem ppoll_null_mask_ignores_the_size (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 4 (bytes_at pp_ufds (pp_entry 3 1)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model [] := by
  sys_norm

/-- AN UNREADABLE MASK IS -EFAULT, and it is `set_user_sigmask`'s own
copy from user memory (kernel/signal.c:3289-3290, Linux v6.18.46) rather
than anything the syscall entry does — so it is raised only after the size test passes
(:3287-3288), which is the order the pin above depends on.  A mask that IS
readable would be INSTALLED, and that is declined.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:ppoll@v6.18.46 -/
theorem ppoll_an_unreadable_mask_is_efault (o : outcome SyscallEffect) :
    syscall_spec (pp_in 0 0 pp_tsp hole 8 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem) pselect_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) pselect_model [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

def a17_select_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_select_model.eq_1

/-- Rocq: `Select.bits_all_pollable`, Select.v:375 at 96c2debdb.
The assumed tmpfs description has no ->poll; fs/select.c, do_select,
Linux v6.18.46 uses the default readiness mask irrespective of access mode.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem a17_rdwr_bits_pollable :
    bits_all_pollable [(3, .FdFileRW [102] 0)] 8 4 = true := by
  decide

/-- Rocq: `Select.ppoll_revents_of`, Select.v:880-885 at 96c2debdb.
Only requested default bits survive: fs/select.c, do_pollfd, Linux
v6.18.46 filters vfs_poll's DEFAULT_POLLMASK on the assumed tmpfs file.
kernel: fs/select.c:do_pollfd@v6.18.46 -/
theorem a17_rdwr_revents_masked :
    ppoll_revents_of [(3, .FdFileRW [102] 0)] 3 13 = some 5 := by
  decide

/-- Rocq's `ppoll_a_read_write_file_polls_as_any_other`: fd 3, a
read-write file, asked for POLLIN|POLLOUT reports both and counts.
`do_pollfd` (fs/select.c, Linux v6.18.46) polls it through `vfs_poll`
(include/linux/poll.h), which answers `DEFAULT_POLLMASK` for a file
whose `f_op` has no `.poll` whatever its access mode, and the request
mask keeps POLLIN|POLLOUT.  That the modeled file has no `.poll` is a
premise about the image (a tmpfs cwd), not a fact about S_IFREG:
`Sys/Fs/Select.lean`'s header and
bugs/pselect6-unchecked-environment-obligations.md carry it.  The pinned
guest answers exactly this on `testing/syscall-check/tests/ppoll_spec.c`'s
`rdwr` case.  The `iff` refuses every other outcome, the idle 0 with
zeroed `revents` among them.
kernel: fs/select.c:do_pollfd@v6.18.46 -/
theorem a17_ppoll_rdwr_polls_as_any_other (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
        a17_select_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) a17_select_model [] := by
  sys_norm

def a17_select_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_select_append_model.eq_1

/-- Rocq: `Select.bits_all_pollable`, Select.v:380 at 96c2debdb.
The assumed tmpfs description has no ->poll in append mode either;
fs/select.c, do_select, Linux v6.18.46 uses the default readiness mask
irrespective of access mode.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem a17_append_bits_pollable :
    bits_all_pollable [(3, .FdFileA [102] 0)] 8 4 = true := by
  decide

/-- Rocq: `Select.ppoll_revents_of`, Select.v:886-893 at 96c2debdb.
Only requested default bits survive: fs/select.c, do_pollfd, Linux
v6.18.46 filters vfs_poll's DEFAULT_POLLMASK on the assumed tmpfs file,
opened for append as for anything else.
kernel: fs/select.c:do_pollfd@v6.18.46 -/
theorem a17_append_revents_masked :
    ppoll_revents_of [(3, .FdFileA [102] 0)] 3 13 = some 5 := by
  decide

/-- fd 3, an append-mode file, asked for POLLIN|POLLOUT reports both and
counts, as Rocq's `ppoll_a_read_write_file_polls_as_any_other` states for
the read-write kind.  `do_pollfd` (fs/select.c, Linux v6.18.46) polls it
through `vfs_poll` (include/linux/poll.h), which answers `DEFAULT_POLLMASK`
for a file whose `f_op` has no `.poll` whatever its access mode, and the
request mask keeps POLLIN|POLLOUT.  That the modeled file has no `.poll`
is a premise about the image (a tmpfs cwd), not a fact about S_IFREG:
`Sys/Fs/Select.lean`'s header and
bugs/pselect6-unchecked-environment-obligations.md carry it.  The `iff`
refuses every other outcome, the idle 0 with zeroed `revents` among them.
kernel: fs/select.c:do_pollfd@v6.18.46 -/
theorem a17_ppoll_append_polls_as_any_other (o : outcome SyscallEffect) :
    syscall_spec (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
        a17_select_append_model o
      ↔ o = Ok (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) a17_select_append_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Select
