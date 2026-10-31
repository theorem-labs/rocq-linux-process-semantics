-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Select.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! # Checks.Cases.Checks.Sys.Fs.Select — what the pselect6 and ppoll CHECKERS answer

Pins over `Checks.Sys.Fs.Select.check_pselect6` and `check_ppoll`, the
checker-level half of `theories/LinuxProcessSem/Checks/Cases/Fs/Select.v`.
Not part of the trusted specification: this file is QA on the checkers,
written to be READ.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f),
read in a checkout at that commit.

TWO LEAN FILES COVER ONE ROCQ FILE, and the split is by what is being
tested.  Rocq states every example of `Checks/Cases/Fs/Select.v` through
`check_syscall`, so each one fixes two things at once: what the SPEC admits,
and that the CHECKER's verdict on a concrete effect is `CheckOk`,
`CheckReject` or `CheckUnmodeled`.  `Checks/Cases/Fs/Select.lean` carries
the first half, as `iff`s over every outcome of `syscall_spec`, and was
written while the tree had no checker to state the second half on.  This
file carries the second half: the same calls, the same effects, and the
checker's verdict on each, so a checker that accepted everything, rejected
everything or declined everything fails here by name.  The KERNEL argument
for every answer is beside the spec-level pin of the same claim in that
file and in the Rocq example the mapping at the end of this header names;
each docstring here keeps only the reading its own verdict rests on.

HOW THESE ARE STATED.  Each pin above the V-Fs-Select sentinel applies
the checker the way the dispatcher does:
`check_pselect6_row` and `check_ppoll_row` below are the argument
narrowing of Rocq's `arm_pselect6` and `arm_ppoll`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and of the rows for 72
and 73 in `Sys/SyscallTable.lean`, spelled once.  The inputs are the
fixtures of `Checks/Cases/Fs/Select.lean`, imported rather than copied, so
the two files cannot drift apart on an address or a byte.  A Rocq
`<> CheckUnmodeled` is stated as the exact verdict the checker gives and
the disequality derived from it, so the stronger fact is what a reader
sees.  Every equality down to the V-Fs-Select sentinel is closed by
`rfl`: `Model` has no `DecidableEq`, so `decide` is unavailable,
and the checker on a closed input reduces to a constructor by evaluation
alone; the one disequality is derived from its equality by `rw`.  Below
the sentinel the Rocq `= CheckReject` conjuncts are restated through
`check_syscall` itself.

No pin here carries a `probe:`
line, although `testing/syscall-check/tests/pselect6_spec.c` and
`ppoll_spec.c` run many of these shapes against the kernel.  What stands
in the way is `tools/check_lean_pin_evidence.py`'s polarity reading, which
classes a statement by `¬`, `≠`, `False` and the word `Unmodeled`: a
`= CheckReject` or `= CheckUnmodeled` verdict reads as positive there, so
the `reject --mutate` or `fail-closed` case that matches it would be
refused as the wrong polarity.  Until that reader knows the checker's
verdicts, every evidence line below is a kernel reading.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  The Rocq file is registered
once, by the register block at the top of `Checks/Cases/Fs/Select.lean`,
and `tools/check_lean_cases_parity.py` refuses a second register at this
path:
it mirrors no Rocq file, so a block here would be a claim nothing could be
held to.  The mapping is therefore prose, read by no guard, kept so a
reader can find the Rocq `Example` a verdict pin restates.  Each line is
the Rocq `Example` followed by the theorems that restate its `check_syscall`
conjuncts; the pins under "The checker's own shape" and the `_is_rejected`
twins beside the positive pins have no Rocq conjunct and are this file's
own.  It stops being complete the day a theorem restating a Rocq conjunct
is added without a line.  A theorem after the V-Fs-Select sentinel whose
name is one listed here with `_over_the_real_table` appended restates the
same conjunct through `check_syscall` and has no line of its own.

- `pselect_a_file_counts_once_per_set`: `pselect_a_file_counts_once_per_set`, `pselect_a_descriptor_count_is_rejected`
- `pselect_exceptfds_comes_back_zeroed`: `pselect_exceptfds_comes_back_zeroed`
- `pselect_bits_at_or_above_n_are_invisible`: `pselect_bits_at_or_above_n_are_invisible`
- `pselect_a_closed_descriptor_below_n_is_ebadf`: `pselect_a_closed_descriptor_below_n_is_ebadf`
- `pselect_a_channel_is_declined`: `pselect_a_channel_is_declined`
- `pselect_n_above_nr_open_default_is_declined`: `pselect_n_above_nr_open_default_is_declined`
- `pselect_a_real_sigmask_is_declined_but_a_bad_size_is_einval`: `pselect_a_real_sigmask_is_declined`, `pselect_a_bad_sigsetsize_is_einval`
- `pselect_a_bad_sigsetsize_beats_an_unreadable_set`: `pselect_a_bad_sigsetsize_beats_an_unreadable_set`, `pselect_efault_behind_a_bad_sigsetsize_is_rejected`
- `pselect_null_mask_ignores_the_size`: `pselect_null_mask_ignores_the_size`
- `pselect_a_deadline_with_a_request_is_declined`: `pselect_a_deadline_with_a_request_is_declined`, `pselect_the_same_request_without_a_deadline_is_answered`
- `pselect_an_empty_request_sleeps_and_writes_zeros`: `pselect_an_empty_request_sleeps_and_writes_zeros`
- `pselect_an_exceptfds_only_request_still_sleeps`: `pselect_an_exceptfds_only_request_still_sleeps`
- `pselect_a_null_timeout_with_nothing_requested_is_declined`: `pselect_a_null_timeout_with_nothing_requested_is_declined`
- `pselect_where_an_errno_comes_from_decides_the_writeback`: `pselect_einval_from_core_sys_select_without_a_deadline`, `pselect_einval_from_core_sys_select_under_a_deadline_is_declined`, `pselect_einval_from_set_user_sigmask_survives_the_deadline`
- `pselect_a_set_that_is_readable_but_not_writable_is_declined`: `pselect_a_set_that_is_readable_but_not_writable_is_declined`
- `pselect_n_zero_never_dereferences_a_set_pointer`: `pselect_n_zero_never_dereferences_a_set_pointer`
- `pselect_the_timespec_is_judged_raw`: `pselect_tv_nsec_at_nsec_per_sec_is_einval`, `pselect_a_negative_tv_sec_is_not_rescued_by_a_carry`, `pselect_a_negative_tv_nsec_is_einval`, `pselect_the_normalized_deadline_is_rejected`
- `pselect_aliased_sets_are_modeled`: `pselect_aliased_read_and_except_sets_name_both_writes`, `pselect_the_snapshot_ledger_is_rejected`, `pselect_aliased_read_and_write_sets_agree`, `pselect_aliased_sets_still_answer_ebadf`
- `ppoll_counts_descriptors_not_bits`: `ppoll_counts_descriptors_not_bits`, `ppoll_a_bit_count_is_rejected`
- `ppoll_a_read_write_file_polls_as_any_other`: not restated through the
  checker; `Checks/Cases/Fs/Select.lean` pins it on the spec, on
  `FdFileRW` (`a17_ppoll_rdwr_polls_as_any_other`), and pins the same
  decision on `FdFileA` (`a17_ppoll_append_polls_as_any_other`).
  `ppoll_a_write_only_file_polls_as_any_other` and
  `ppoll_a_write_only_file_reported_idle_is_rejected` state the same
  decision on `FdFileW`, because the kernel's answer does not depend on
  the mode: `do_pollfd` (fs/select.c:868-870, Linux v6.18.46) polls a regular
  file through `vfs_poll` (include/linux/poll.h:78-83, same version), which
  answers `DEFAULT_POLLMASK` for a file with no `->poll` (:80-81), so the
  idle answer is the
  lie for a read-write file exactly as for a write-only one.
- `ppoll_an_unopened_descriptor_is_pollnval_not_ebadf`: `ppoll_an_unopened_descriptor_is_pollnval`, `ppoll_ebadf_for_an_unopened_descriptor_is_rejected`
- `ppoll_a_negative_fd_is_skipped_not_invalid`: `ppoll_a_negative_fd_is_skipped`, `ppoll_pollnval_for_a_negative_fd_is_rejected`
- `ppoll_events_filters_the_default_pollmask`: `ppoll_events_filters_the_default_pollmask`, `ppoll_an_echoed_events_is_rejected`
- `ppoll_a_channel_is_declined`: `ppoll_a_channel_is_declined`, `ppoll_a_channel_with_no_events_is_still_declined`
- `ppoll_above_the_stack_bound_is_declined`: `ppoll_above_the_stack_bound_is_declined`, `ppoll_at_the_stack_bound_is_judged`, `ppoll_at_the_stack_bound_is_answered`
- `ppoll_nfds_above_the_soft_limit_is_einval_before_the_copy`: `ppoll_nfds_above_the_soft_limit_is_einval`, `ppoll_efault_ahead_of_the_limit_test_is_rejected`
- `ppoll_an_unreadable_array_is_efault`: `ppoll_an_unreadable_array_is_efault`
- `ppoll_nfds_zero_never_dereferences_ufds`: `ppoll_nfds_zero_never_dereferences_ufds`
- `ppoll_a_deadline_expires_to_zeros_but_an_early_return_is_declined`: `ppoll_a_deadline_expires_to_zeros`, `ppoll_an_early_return_under_a_deadline_is_declined`
- `ppoll_a_null_timeout_with_nothing_ready_is_declined`: `ppoll_a_null_timeout_with_nothing_ready_is_declined`, `ppoll_a_ready_descriptor_under_a_null_timeout_is_answered`
- `ppoll_an_unwritable_array_is_declined`: `ppoll_an_unwritable_array_is_declined`
- `ppoll_the_timeout_is_judged_before_the_signal_mask`: `ppoll_an_unreadable_timeout_beats_a_bad_sigsetsize`, `ppoll_einval_ahead_of_the_timeout_is_rejected`, `ppoll_a_bad_sigsetsize_beats_an_unreadable_array`
- `ppoll_an_unreadable_mask_is_efault`: `ppoll_an_unreadable_mask_is_efault` -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Select

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (bytes_at)
-- Selective, because this file redeclares the spec-level file's ppoll pin names
-- with the checker's verdict: a wholesale `open` of both would make each of
-- them ambiguous for any file that opens the two together.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Select
  (mem_join pp_entries pp_entry pp_in pp_sig pp_ts pp_tsp pp_ufds pp_wmem
   ps_exp ps_in ps_inp ps_outp ps_sig ps_tsp ps_wmem
   pselect_model pselect_model_kinds pselect_model_lim user_top)

/-! ## The dispatcher's application of each checker -/

/-- `check_pselect6` as the dispatcher applies it: `n` narrowed to `int` by
`nfds32`, the other five registers as they arrive — Rocq's `arm_pselect6`
and the row for 72 in `Sys/SyscallTable.lean`; `ca_check_arm_pselect6`
rewrites `arm_pselect6`'s `ca_check` to this application. -/
def check_pselect6_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
    (in_arg i 5) eff m

/-- `check_ppoll` as the dispatcher applies it: `nfds` narrowed to
`unsigned int` by `unfds32`, the other four registers as they arrive —
Rocq's `arm_ppoll` and the row for 73 in `Sys/SyscallTable.lean`. -/
def check_ppoll_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m

/-! ## The checker's own shape: the outcome first, then the effect's ledgers -/

/-- An effect that zero-fills a range is one `pselect6_outcome` never
describes — the call writes its sets and its timespec and nothing else — so
the checker's wildcard arm rejects it although the return value and the
writes are the kernel's: each empty ledger in the accepting arm is
load-bearing.
kernel: fs/select.c:core_sys_select,set_fd_set,poll_select_finish@v6.18.46 -/
theorem pselect_an_effect_with_a_zero_fill_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (SyscallEffect.mkEffectU 1 [(ps_inp, word_le8 8)] [(0, 0)] [] [] []) pselect_model
      = CheckReject := by
  rfl

/-- …and the same odd-shaped effect against a declined call is
`CheckUnmodeled`, not `CheckReject`: the outcome is computed before the
effect is looked at.
kernel: fs/select.c:do_select; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_a_declined_call_is_declined_whatever_the_effect_shape :
    check_pselect6_row (ps_in 1 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 1)) ps_wmem)
      (SyscallEffect.mkEffectU 1 [(ps_inp, word_le8 1)] [(0, 0)] [] [] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- The same two facts for `check_ppoll`: a zero-fill beside the kernel's
return value and `revents` write is rejected…
kernel: fs/select.c:do_sys_poll,do_pollfd,poll_select_finish@v6.18.46 -/
theorem ppoll_an_effect_with_a_zero_fill_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
      (SyscallEffect.mkEffectU 0 [(pp_ufds + 6, word_le2 0)] [(0, 0)] [] [] []) pselect_model
      = CheckReject := by
  rfl

/-- …and against a channel entry the same shape is declined, not rejected.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_a_declined_call_is_declined_whatever_the_effect_shape :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 0 1))) pp_wmem)
      (SyscallEffect.mkEffectU 1 [(pp_ufds + 6, word_le2 1)] [(0, 0)] [] [] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- `n` is an `int` (fs/select.c:793): riscv64's `__SYSCALL_DEFINEx` narrows
the register through `__SC_CAST` before `core_sys_select` sees it, and the
row applies `nfds32` for exactly that reason.  A register holding 2^32 is
`n = 0`, the call that dereferences no set pointer — not a count above
`NR_OPEN_DEFAULT`, which the row would decline.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:pselect6,core_sys_select@v6.18.46 -/
theorem pselect_the_row_narrows_n_to_int :
    check_pselect6_row (ps_in (Z_to_bv 64 (2 ^ 32)) 65536 65536 65536 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- `nfds` is an `unsigned int` (fs/select.c:1095), narrowed the same way;
the row applies `unfds32`.  A register holding 2^32 is `nfds = 0`, answered
0 — not a count above `RLIMIT_NOFILE`, whose -EINVAL (:981-982) would make
this answer a rejected one.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:ppoll,do_sys_poll@v6.18.46 -/
theorem ppoll_the_row_narrows_nfds_to_unsigned_int :
    check_ppoll_row (pp_in 65536 (Z_to_bv 64 (2 ^ 32)) pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-! ## pselect6: `do_select` counts masks, and every file is ready -/

/-- fd 3 named in `readfds` and `writefds` counts twice: `do_select` has one
`retval++` per result mask (fs/select.c:540, :545), and the checker accepts
2 with both sets echoed.
kernel: fs/select.c:do_select,select_poll_one; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_a_file_counts_once_per_set :
    check_pselect6_row (ps_in 4 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem)
      (mkEffect 2 [(ps_inp, word_le8 8), (ps_outp, word_le8 8)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The descriptor count, 1, is the lie `do_select` never tells, and the
checker rejects it with the same sets echoed.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem pselect_a_descriptor_count_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8), (ps_outp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rfl

/-- `exceptfds` is copied back as a zero word and adds nothing to the count:
`DEFAULT_POLLMASK` misses `POLLEX_SET` (fs/select.c:463), so the third
`retval++` (:550) never fires for a file.
kernel: fs/select.c:do_select,select_poll_one; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_exceptfds_comes_back_zeroed :
    check_pselect6_row (ps_in 4 ps_inp 0 ps_exp 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 0 ++ word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8), (ps_exp, word_le8 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A kernel reporting the file exceptional — the `exceptfds` bit kept and
counted, 2 — is rejected: `vfs_poll` answers `DEFAULT_POLLMASK` for a file
with no `->poll` (include/linux/poll.h:78-83), and `POLLEX_SET`
(fs/select.c:463) shares no bit with it, so :548-550 never fires.
kernel: fs/select.c:do_select; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_an_exceptional_file_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 ps_exp 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 0 ++ word_le8 8)) ps_wmem)
      (mkEffect 2 [(ps_inp, word_le8 8), (ps_exp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rfl

/-- Bit 9 set with `n = 4` is invisible twice over.  `max_select_fd` masks
the partial word to the bits below `n` (fs/select.c:425) before its
`set & ~*open_fds` test (:431-435), so the closed fd 9 is not -EBADF; and
`do_select` stops at `i >= n` (:532-533) while `core_sys_select` has zeroed
the result words (:673-675), so the word `set_fd_set` writes back does not
carry the bit.
kernel: fs/select.c:max_select_fd,do_select,core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_bits_at_or_above_n_are_invisible :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A kernel handing bit 9 back — echoing the request instead of the zeroed
result word — is rejected: `core_sys_select` zeroes the result words
(fs/select.c:673-675) and `do_select` never reaches bit 9 to set one
(:532-533).
kernel: fs/select.c:core_sys_select,do_select,set_fd_set@v6.18.46 -/
theorem pselect_a_bit_above_n_surviving_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 520)] []) pselect_model
      = CheckReject := by
  rfl

/-- The same bit under `n = 10` names closed fd 9, and `max_select_fd`
answers -EBADF (fs/select.c:433-435) before any set is scanned or written.
kernel: fs/select.c:core_sys_select,max_select_fd@v6.18.46 -/
theorem pselect_a_closed_descriptor_below_n_is_ebadf :
    check_pselect6_row (ps_in 10 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
      (mkEffect (errno_ret EBADF) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A kernel polling the open descriptor and reporting it — 1, with the
closed one dropped — is rejected: `max_select_fd` returns -EBADF
(fs/select.c:433-435) before `do_select` scans anything (:494-498).
kernel: fs/select.c:core_sys_select,max_select_fd,do_select@v6.18.46 -/
theorem pselect_a_count_over_a_closed_descriptor_is_rejected :
    check_pselect6_row (ps_in 10 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rfl

/-- A channel in a set is declined: its readiness is a schedule the model
does not represent, so the checker answers `CheckUnmodeled` whatever it is
shown — here the readable answer a kernel might well give.
kernel: fs/select.c:do_select; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_a_channel_is_declined :
    check_pselect6_row (ps_in 1 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 1)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 1)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- `n = 65` reaches the `fdt->max_fds` clamp (fs/select.c:639-642), whose
value the model does not carry, so the call is declined whatever the
answer.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem pselect_n_above_nr_open_default_is_declined :
    check_pselect6_row (ps_in 65 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-! ## The signal mask: installed masks are declined, bad sizes are -EINVAL -/

/-- A non-NULL mask of the kernel's size is declined before it is read.  A
readable one `set_user_sigmask` would INSTALL (kernel/signal.c:3292-3294)
for the call's duration, which the model does not represent; this one —
the pointer is 1, outside the readable view — Linux would -EFAULT at the
copy (:3289-3290).  Neither is an answer the model gives, so the verdict
does not rest on the mask's readability.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_a_real_sigmask_is_declined :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 8)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- The same mask with `sigsetsize` 4 is -EINVAL at kernel/signal.c:3287-3288,
before the set is read.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_a_bad_sigsetsize_is_einval :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A count under a bad `sigsetsize` is rejected: `set_user_sigmask` fails
the size test (kernel/signal.c:3287-3288) and `do_pselect` returns that
(fs/select.c:755-757) without reaching `core_sys_select`.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_a_count_under_a_bad_sigsetsize_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rfl

/-- The errno-order pair: `set_user_sigmask` runs in `do_pselect`
(fs/select.c:755-757) before `core_sys_select` (:759), so a bad size beside
an unreadable set is -EINVAL.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_a_bad_sigsetsize_beats_an_unreadable_set :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The -EFAULT of the set's copy-in is the other order, and the checker
rejects it: `do_pselect` does not reach `core_sys_select` once
`set_user_sigmask` has failed.  That is Linux's order.  QEMU 11.1.1's
user-mode `do_pselect6` (linux-user/syscall.c:1456-1466) copies the three
sets in before it opens the sigset pack (:1491-1500) and answers -EFAULT
here, so the refusal is the kernel's answer and not the intersection's; the
residual is the spec's — `Sys/Fs/Select.lean` proves -EINVAL certain, as
Rocq's does — and not this pin's, which restates the spec.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_efault_behind_a_bad_sigsetsize_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckReject := by
  rfl

/-- {NULL, 999} is no mask, not a bad size: `set_user_sigmask` returns 0 on a
NULL mask (kernel/signal.c:3285-3286) before it reads the size.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:pselect6@v6.18.46 -/
theorem pselect_null_mask_ignores_the_size :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 0 ++ word_le8 999)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EINVAL for the NULL mask's odd size is rejected: `set_user_sigmask`
returns 0 for a NULL pointer (kernel/signal.c:3285-3286) before the size
test at :3287.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:do_pselect@v6.18.46 -/
theorem pselect_einval_for_a_null_mask_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 ps_sig
        (mem_join (bytes_at ps_sig (word_le8 0 ++ word_le8 999)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rfl

/-! ## The timeout: a deadline with a request is declined, a sleep is not -/

/-- A five-second deadline beside a ready descriptor: the kernel returns at
once and `poll_select_finish` writes the remaining time back
(fs/select.c:313-314, :342-344), a value the model cannot compute, so the
call is declined even for the count it would give.
kernel: fs/select.c:do_pselect,poll_select_finish@v6.18.46 -/
theorem pselect_a_deadline_with_a_request_is_declined :
    check_pselect6_row (ps_in 4 ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- The same request with a NULL `tsp` is answered: nothing is written back
(fs/select.c:303-304).
kernel: fs/select.c:do_select,poll_select_finish@v6.18.46 -/
theorem pselect_the_same_request_without_a_deadline_is_answered :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- Nothing requested and a one-millisecond deadline: the call sleeps it
out, returns 0, and `poll_select_finish` writes {0, 0} back once the
`rts.tv_sec < 0` clamp fires (fs/select.c:315-316).
kernel: fs/select.c:do_select,poll_select_finish; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem pselect_an_empty_request_sleeps_and_writes_zeros :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) ps_wmem)
      (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A kernel returning 0 and leaving the timespec as the caller wrote it is
rejected: a non-NULL `tsp` with a non-zero end time always reaches the
write-back (fs/select.c:342-344) — unless the process carries
`STICKY_TIMEOUTS` (:306-307), under which this IS Linux's answer.  The
refusal holds for a process without that personality flag, the premise the
spec-level pin `a_sleep_leaving_the_timespec_is_rejected` records.
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem pselect_a_sleep_leaving_the_timespec_is_rejected :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) ps_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckReject := by
  rfl

/-- An `exceptfds`-only request on a file is a request nothing satisfies, so
it sleeps like the empty one, and its set comes back zeroed.
kernel: fs/select.c:do_select,set_fd_set,poll_select_finish@v6.18.46 -/
theorem pselect_an_exceptfds_only_request_still_sleeps :
    check_pselect6_row (ps_in 4 0 0 ps_exp ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) (bytes_at ps_exp (word_le8 8)))
        ps_wmem)
      (mkEffect 0 [(ps_exp, word_le8 0), (ps_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The same sleep with the set zeroed but the timespec left alone is
rejected on the same premise: the write-back at fs/select.c:342-344 comes
with the set's write, not instead of it.
kernel: fs/select.c:set_fd_set,poll_select_finish@v6.18.46 -/
theorem pselect_an_exceptfds_only_sleep_leaving_the_timespec_is_rejected :
    check_pselect6_row (ps_in 4 0 0 ps_exp ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000)) (bytes_at ps_exp (word_le8 8)))
        ps_wmem)
      (mkEffect 0 [(ps_exp, word_le8 0)] []) pselect_model
      = CheckReject := by
  rfl

/-- Nothing requested and no deadline blocks forever (fs/select.c:603-605),
which is no answer at all: declined, and the invented 0 is not accepted.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem pselect_a_null_timeout_with_nothing_requested_is_declined :
    check_pselect6_row (ps_in 0 0 0 0 0 0 (fun _ => none) ps_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-! ## Where an errno comes from decides the write-back -/

/-- `n` = 2^32 - 1 arrives as `int` -1 and `core_sys_select` answers -EINVAL
(fs/select.c:632-634): without a deadline that is the whole answer.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem pselect_einval_from_core_sys_select_without_a_deadline :
    check_pselect6_row (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 0 0
        (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A count for a negative `n` is rejected: `core_sys_select` answers
-EINVAL at fs/select.c:632-634 before any set is imported or scanned.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem pselect_a_count_for_a_negative_n_is_rejected :
    check_pselect6_row (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 0 0
        (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rfl

/-- The same -EINVAL under a deadline is returned through
`poll_select_finish`, whose write-back for a nonzero `end_time`
(fs/select.c:313-345) the model cannot compute: declined.  The return
path is the last line of `do_pselect` (fs/select.c:760).
kernel: fs/select.c:core_sys_select,poll_select_finish@v6.18.46 -/
theorem pselect_einval_from_core_sys_select_under_a_deadline_is_declined :
    check_pselect6_row (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 ps_tsp 0
        (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8)))
        ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- `set_user_sigmask`'s -EINVAL returns from `do_pselect` directly
(fs/select.c:755-757), never reaching `poll_select_finish`, so under the
same deadline it is answered.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_einval_from_set_user_sigmask_survives_the_deadline :
    check_pselect6_row (ps_in (Z_to_bv 64 (2 ^ 32 - 1)) ps_inp 0 0 ps_tsp ps_sig
        (mem_join (bytes_at ps_sig (word_le8 1 ++ word_le8 4))
          (mem_join (bytes_at ps_tsp (word_le8 5 ++ word_le8 0)) (bytes_at ps_inp (word_le8 8))))
        ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-! ## The set pointers -/

/-- A set that is readable but not writable: `set_fd_set` would fail on the
write-back (fs/select.c:688-691) after the scan, an -EFAULT the model does
not compute the partial writes of, so the call is declined.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_a_set_that_is_readable_but_not_writable_is_declined :
    check_pselect6_row (ps_in 4 ps_inp 0 0 0 0 (bytes_at ps_inp (word_le8 8)) (fun _ => none))
      (mkEffect 1 [(ps_inp, word_le8 8)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- `n = 0` never dereferences a set pointer: `FDS_BYTES(0)` is 0, so
`get_fd_set` copies nothing (fs/select.c:387-391) wherever the pointers
point, and a {0, 0} deadline returns 0 with no write-back.
kernel: fs/select.c:core_sys_select,get_fd_set,poll_select_finish@v6.18.46 -/
theorem pselect_n_zero_never_dereferences_a_set_pointer :
    check_pselect6_row (ps_in 0 65536 65536 65536 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EFAULT for `n = 0` is rejected: `get_fd_set` copies `FDS_BYTES(0)`,
which is 0 bytes (fs/select.c:387-391), so no pointer is dereferenced and
none can fault.
kernel: fs/select.c:core_sys_select,get_fd_set@v6.18.46 -/
theorem pselect_efault_for_n_zero_is_rejected :
    check_pselect6_row (ps_in 0 65536 65536 65536 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckReject := by
  rfl

/-! ## The timespec is judged raw -/

/-- `tv_nsec` exactly at `NSEC_PER_SEC` is out of range
(include/linux/time64.h:103), -EINVAL from `poll_select_set_timeout`, not
one second.
kernel: fs/select.c:do_pselect,poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem pselect_tv_nsec_at_nsec_per_sec_is_einval :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- No carry rescues a negative `tv_sec` (include/linux/time64.h:100-101).
kernel: fs/select.c:do_pselect,poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem pselect_a_negative_tv_sec_is_not_rescued_by_a_carry :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 (Z_to_bv 64 (-1)) ++ word_le8 2000000000)) ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A negative `tv_nsec` is enormous as an `unsigned long`
(include/linux/time64.h:103).
kernel: fs/select.c:do_pselect,poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem pselect_a_negative_tv_nsec_is_einval :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 2 ++ word_le8 (Z_to_bv 64 (-1000000000)))) ps_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The deadline a normalizing model would have answered — one second's
sleep, sixteen zero bytes — is the answer a real kernel refused with -22,
and the checker rejects it.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem pselect_the_normalized_deadline_is_rejected :
    check_pselect6_row (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
      (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model
      = CheckReject := by
  rfl

/-! ## Overlapping sets: the ledger names both writes, in `set_fd_set` order -/

/-- `readfds` aliased with `exceptfds`: `set_fd_set` runs in `inp`, `outp`,
`exp` order (fs/select.c:688-690), so the address takes the request first
and zero second, and the ledger says so.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_aliased_read_and_except_sets_name_both_writes :
    check_pselect6_row (ps_in 4 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8), (ps_inp, word_le8 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The ledger a memory snapshot would produce — the surviving word for both
entries — loses the first write, and the checker rejects it.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_the_snapshot_ledger_is_rejected :
    check_pselect6_row (ps_in 4 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 0), (ps_inp, word_le8 0)] []) pselect_model
      = CheckReject := by
  rfl

/-- `readfds` aliased with `writefds`: both words are the imported request,
and the count is 2.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_aliased_read_and_write_sets_agree :
    check_pselect6_row (ps_in 4 ps_inp ps_inp 0 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 2 [(ps_inp, word_le8 8), (ps_inp, word_le8 8)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- Aliasing changes nothing about -EBADF: `max_select_fd` (fs/select.c:433-435)
still fires for closed fd 9 under `n = 10`.
kernel: fs/select.c:core_sys_select,max_select_fd@v6.18.46 -/
theorem pselect_aliased_sets_still_answer_ebadf :
    check_pselect6_row (ps_in 10 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 520)) ps_wmem)
      (mkEffect (errno_ret EBADF) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-! ## ppoll: `do_poll` counts entries, and `revents` is written per entry -/

/-- One entry asking POLLIN|POLLOUT on a file: `count++` runs once per entry
(fs/select.c:915-916), so the answer is 1 with `revents` 5 at offset 6.
kernel: fs/select.c:do_poll,do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_counts_descriptors_not_bits :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- select's bit count, 2, is the lie `do_poll` never tells.
kernel: fs/select.c:do_poll@v6.18.46 -/
theorem ppoll_a_bit_count_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
      (mkEffect 2 [(pp_ufds + 6, word_le2 5)] []) pselect_model
      = CheckReject := by
  rfl

/-- A write-only file polls as any other: `vfs_poll` (include/linux/poll.h:78-83)
never reads `f_mode`.  Rocq states this on `FdFileRW`; here it is fd 4 of
`pselect_model_kinds`, an `FdFileW` (the header's mapping says why).
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_write_only_file_polls_as_any_other :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 4 5))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model_kinds
      = CheckOk pselect_model_kinds [] := by
  rfl

/-- Reporting that file idle — 0 with `revents` 0 — is rejected: the
`DEFAULT_POLLMASK` answer is not a schedule.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_write_only_file_reported_idle_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 4 5))) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model_kinds
      = CheckReject := by
  rfl

/-- An unopened descriptor is an ANSWER: `do_pollfd` reports `EPOLLNVAL`
when `fd_empty` holds (fs/select.c:864-865), 32 in `revents`, and it
counts.
kernel: fs/select.c:do_pollfd,do_poll; include/uapi/asm-generic/poll.h:POLLNVAL@v6.18.46 -/
theorem ppoll_an_unopened_descriptor_is_pollnval :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EBADF is select's answer to the same descriptor — `max_select_fd`'s
(fs/select.c:433-435) — and no path of `do_pollfd` raises it: rejected.
kernel: fs/select.c:do_pollfd,max_select_fd@v6.18.46 -/
theorem ppoll_ebadf_for_an_unopened_descriptor_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem)
      (mkEffect (errno_ret EBADF) [] []) pselect_model
      = CheckReject := by
  rfl

/-- A negative `fd` is skipped, not invalid: `do_pollfd` returns 0 for it
(fs/select.c:860-861) before `fd_empty` is asked, so `revents` is 0 and the
entry does not count.
kernel: fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_negative_fd_is_skipped :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- `POLLNVAL` for a negative `fd` is rejected: that answer is for an
UNOPENED non-negative one.
kernel: fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_pollnval_for_a_negative_fd_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []) pselect_model
      = CheckReject := by
  rfl

/-- `events` filters the mask: POLLPRI alone (2) on a file meets nothing in
`DEFAULT_POLLMASK`, so `revents` is 0 and the entry does not count
(fs/select.c:868-873).
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_events_filters_the_default_pollmask :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 2))) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- Echoing `events` into `revents` is rejected: the mask is `& filter`ed,
not copied.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_an_echoed_events_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 2))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 2)] []) pselect_model
      = CheckReject := by
  rfl

/-- A channel entry is declined whatever it is shown: its readiness is a
schedule the model does not represent, so no single answer is provable.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_a_channel_is_declined :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 0 1))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- Even with no `events` requested: the filter takes EPOLLERR|EPOLLHUP
unconditionally and `do_pollfd` polls the file regardless
(fs/select.c:868-870), through `vfs_poll` (include/linux/poll.h:78-83);
the channel's `->poll` is a schedule.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_a_channel_with_no_events_is_still_declined :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 0 0))) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-! ## The stack bound -/

set_option maxRecDepth 8192 in
/-- At 31 entries `do_sys_poll` extends the chain by a `kmalloc`
(fs/select.c:999-1001) that can answer -ENOMEM (:1002-1004): declined,
whatever the kernel returned.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_above_the_stack_bound_is_declined :
    check_ppoll_row (pp_in pp_ufds 31 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 31 (pp_entry (-1) 0))))
        pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckUnmodeled := by
  rfl

set_option maxRecDepth 8192 in
/-- At 30 the same array is inside the band and the call is JUDGED: thirty
`fd = -1` entries answer 0 with thirty zero `revents`, so a ledger with no
writes is rejected rather than declined.
kernel: fs/select.c:do_sys_poll,do_poll@v6.18.46 -/
theorem ppoll_at_the_stack_bound_is_judged :
    check_ppoll_row (pp_in pp_ufds 30 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 30 (pp_entry (-1) 0))))
        pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckReject := by
  rfl

/-- Rocq's statement of the same fact, derived: at 30 the checker does not
decline.
kernel: fs/select.c:do_sys_poll,do_poll@v6.18.46 -/
theorem ppoll_at_the_stack_bound_is_answered :
    check_ppoll_row (pp_in pp_ufds 30 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 30 (pp_entry (-1) 0))))
        pp_wmem)
      (mkEffect 0 [] []) pselect_model
      ≠ CheckUnmodeled := by
  rw [ppoll_at_the_stack_bound_is_judged]
  exact fun h => nomatch h

/-- Entry `k`'s `revents` sits at offset `8k + 6`; `do_sys_poll` writes each
entry's in order, `ufds++` between them (fs/select.c:1015-1020, Linux
v6.18.46).  Spelled
once so the accepted ledger at the bound can be stated. -/
def pp_zero_revents (n : Nat) : List (word × List byte) :=
  (List.range n).map fun k => (pp_ufds + BitVec.ofNat 64 (8 * k + 6), word_le2 0)

set_option maxRecDepth 8192 in
/-- …and the ledger the checker ACCEPTS at the bound is the thirty zero
`revents`, one per `fd = -1` entry (fs/select.c:860-861), with the return
value 0: "judged" above is "judged against this".
kernel: fs/select.c:do_sys_poll,do_poll,do_pollfd@v6.18.46 -/
theorem ppoll_at_the_stack_bound_accepts_thirty_zero_revents :
    check_ppoll_row (pp_in pp_ufds 30 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entries 30 (pp_entry (-1) 0))))
        pp_wmem)
      (mkEffect 0 (pp_zero_revents 30) []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-! ## The soft limit and the array -/

/-- `nfds` above `RLIMIT_NOFILE` is -EINVAL (fs/select.c:981-982) before the
copy, so an unreadable array does not matter.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_nfds_above_the_soft_limit_is_einval :
    check_ppoll_row (pp_in pp_ufds 5 0 0 0 (fun _ => none) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model_lim
      = CheckOk pselect_model_lim [] := by
  rfl

/-- The copy's -EFAULT ahead of the limit test is the order `do_sys_poll`
does not have: rejected.  QEMU 11.1.1's user-mode `do_ppoll`
(linux-user/syscall.c:1559-1563) locks the array for writing before it
reads the timeout or the mask and answers -EFAULT here, so as for pselect6
the refusal is the kernel's answer and the residual is the spec's.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_efault_ahead_of_the_limit_test_is_rejected :
    check_ppoll_row (pp_in pp_ufds 5 0 0 0 (fun _ => none) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model_lim
      = CheckReject := by
  rfl

/-- An unreadable array under the limit is -EFAULT from the copy
(fs/select.c:991-993).
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_an_unreadable_array_is_efault :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (fun _ => none) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EINVAL for the unreadable array under the limit is rejected: the limit
test at fs/select.c:981-982 passes for one entry, and the copy's failure is
-EFAULT (:991-993), not -EINVAL.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_einval_for_an_unreadable_array_under_the_limit_is_rejected :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (fun _ => none) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rfl

/-- `nfds = 0` never dereferences `ufds`: `len` is 0 (fs/select.c:984) and
the loop breaks before the copy (:988-989); with a {0, 0} deadline the call
returns 0 and writes nothing.
kernel: fs/select.c:do_sys_poll,poll_select_finish@v6.18.46 -/
theorem ppoll_nfds_zero_never_dereferences_ufds :
    check_ppoll_row (pp_in 65536 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EFAULT for `nfds = 0` is rejected: `len` is 0 (fs/select.c:984), the
loop breaks before the copy (:988-989), and the zero-length
`user_write_access_begin` on a user-space pointer passes (:1012).
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_efault_for_nfds_zero_is_rejected :
    check_ppoll_row (pp_in 65536 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckReject := by
  rfl

/-- With `nfds = 0` the write-back's access check at fs/select.c:1012 is
zero-length, and `__access_ok` (include/asm-generic/access_ok.h:40) accepts
`addr <= TASK_SIZE_MAX` for a size of 0, so a `ufds` exactly at the top of
user space is answered 0…
kernel: fs/select.c:do_sys_poll; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_checker_answers_nfds_zero_at_the_top_of_user_space :
    check_ppoll_row (pp_in user_top 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- …and so is one byte above it, where Linux answers -EFAULT: the
zero-length call answers 0 for any pointer, which is the recorded
difference the spec-level pin
`ppoll_nfds_zero_one_byte_above_user_space_is_zero` in
`Checks/Cases/Fs/Select.lean` carries; this is the checker saying the
same.  QEMU 11.1.1's user-mode `do_ppoll` (linux-user/syscall.c:1553-1563)
never looks at the pointer when `nfds` is 0 and answers 0 too.
kernel: fs/select.c:do_sys_poll; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_checker_answers_nfds_zero_above_user_space :
    check_ppoll_row (pp_in (user_top + 1) 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-! ## The deadline -/

/-- No entries and a one-millisecond deadline: the sleep expires, and
`poll_select_finish` writes {0, 0} back (fs/select.c:315-316).
kernel: fs/select.c:poll_select_finish,do_poll; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem ppoll_a_deadline_expires_to_zeros :
    check_ppoll_row (pp_in 0 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000)) pp_wmem)
      (mkEffect 0 [(pp_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- A kernel returning 0 and leaving the timespec alone is rejected, on the
pselect6 pin's premise: the write-back at fs/select.c:342-344 is reached
unless the process carries `STICKY_TIMEOUTS` (:306-307).
kernel: fs/select.c:poll_select_finish@v6.18.46 -/
theorem ppoll_a_sleep_leaving_the_timespec_is_rejected :
    check_ppoll_row (pp_in 0 0 pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 1000000)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckReject := by
  rfl

/-- A ready entry under the same deadline returns early, and the remaining
time written back (fs/select.c:313-314) is a value the model cannot
compute: declined.
kernel: fs/select.c:do_poll,poll_select_finish@v6.18.46 -/
theorem ppoll_an_early_return_under_a_deadline_is_declined :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 1000000)) (bytes_at pp_ufds (pp_entry 3 1))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- Nothing ready and no deadline blocks forever (fs/select.c:958-959):
declined, and the invented 0 is not accepted.
kernel: fs/select.c:do_poll,do_pollfd@v6.18.46 -/
theorem ppoll_a_null_timeout_with_nothing_ready_is_declined :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry (-1) 0)) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-- A ready descriptor under a NULL timeout is counted on the first pass
(fs/select.c:915-916) and the loop exits on the count (:934-935), so the
call is answered.
kernel: fs/select.c:do_poll,do_pollfd@v6.18.46 -/
theorem ppoll_a_ready_descriptor_under_a_null_timeout_is_answered :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 1)) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- An array that is readable but not writable: the `revents` write-back
(fs/select.c:1012-1020) fails partway, with no representation for which
entries landed, so the call is declined.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_an_unwritable_array_is_declined :
    check_ppoll_row (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 1)) (fun _ => none))
      (mkEffect 1 [(pp_ufds + 6, word_le2 1)] []) pselect_model
      = CheckUnmodeled := by
  rfl

/-! ## The errno order: the timeout before the mask, as in `do_pselect` -/

/-- `ppoll` reads the timeout first (fs/select.c:1103-1104) and the mask
second (:1111-1113): an unreadable timeout beside a bad `sigsetsize` is
-EFAULT.
kernel: fs/select.c:ppoll; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem ppoll_an_unreadable_timeout_beats_a_bad_sigsetsize :
    check_ppoll_row (pp_in 0 0 pp_tsp pp_sig 4 (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The mask's -EINVAL ahead of the timeout's -EFAULT is rejected: the mask
is handed to `set_user_sigmask` (kernel/signal.c:3281-3297) only at
fs/select.c:1111, after `get_timespec64` (:1103-1104) has succeeded.  That
is `do_pselect`'s order too (:739-740
before :755), not a departure from it: the one step pselect6 has ahead of
the timeout is the pack read (:799-800), whose failure is -EFAULT.
kernel: fs/select.c:ppoll,do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem ppoll_einval_ahead_of_the_timeout_is_rejected :
    check_ppoll_row (pp_in 0 0 pp_tsp pp_sig 4 (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rfl

/-- With the timeout readable, the bad `sigsetsize` is answered
(kernel/signal.c:3287-3288) before `do_sys_poll` copies anything
(fs/select.c:1115).
kernel: fs/select.c:ppoll; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem ppoll_a_bad_sigsetsize_beats_an_unreadable_array :
    check_ppoll_row (pp_in pp_ufds 1 pp_tsp pp_sig 4
        (mem_join (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) (bytes_at pp_tsp (pp_ts 0 0))) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- An unreadable mask of the right size is -EFAULT from `set_user_sigmask`'s
own copy (kernel/signal.c:3289-3290), after the size test passes.
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:ppoll@v6.18.46 -/
theorem ppoll_an_unreadable_mask_is_efault :
    check_ppoll_row (pp_in 0 0 pp_tsp pp_sig 8 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- -EINVAL for the unreadable mask of the right size is rejected: the size
test (kernel/signal.c:3287-3288) passes at 8, and the copy's failure is
-EFAULT (:3289-3290).
kernel: kernel/signal.c:set_user_sigmask; fs/select.c:ppoll@v6.18.46 -/
theorem ppoll_einval_for_an_unreadable_mask_is_rejected :
    check_ppoll_row (pp_in 0 0 pp_tsp pp_sig 8 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Select

-- lean-port sentinel: ticket V-Fs-Select appends below this line

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Select

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (bytes_at)
-- Selective, because this file redeclares the spec-level file's ppoll pin names
-- with the checker's verdict: a wholesale `open` of both would make each of
-- them ambiguous for any file that opens the two together.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Select
  (mem_join pp_entries pp_entry pp_in pp_sig pp_ts pp_tsp pp_ufds pp_wmem
   ps_exp ps_in ps_inp ps_outp ps_sig ps_tsp ps_wmem
   pselect_model pselect_model_kinds pselect_model_lim user_top)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

section V_Fs_Select

/-! ## V-Fs-Select — `pselect6` and `ppoll` over the real table

The pins above apply `check_pselect6_row` / `check_ppoll_row`; here each
of the eleven `= CheckReject` conjuncts in
`theories/LinuxProcessSem/Checks/Cases/Fs/Select.v` is restated through
the Lean `check_syscall`, over `checked_table`, under the name of its
checker-level twin with `_over_the_real_table` appended, and proved by
computing the dispatch once and handing over that pin.

What a pin here adds is the ARM's claim: the lookup at 72 / 73 finds
`arm_pselect6` / `arm_ppoll`, not the dispatcher's decline, and which
registers it narrows. -/

/-- The lookup on `ps_in` finds `arm_pselect6` at 72 for every argument.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_ps_in (n inp outp exp tsp sig : word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (ps_in n inp outp exp tsp sig mem wmem).in_sysno)
      = some arm_pselect6 :=
  lookup_ca_checked_table_pselect6

/-- The table applies `check_pselect6_row` to `ps_in`, narrowing `a0` to `int`.
model: `check_syscall` through the arm, unfolded; the table's own contents, not a kernel claim. -/
theorem check_syscall_ps_in (n inp outp exp tsp sig : word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (ps_in n inp outp exp tsp sig mem wmem) eff m
      = check_pselect6_row (ps_in n inp outp exp tsp sig mem wmem) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_ps_in n inp outp exp tsp sig mem wmem)

/-- The lookup on `pp_in` finds `arm_ppoll` at 73 for every argument.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim. -/
theorem lookup_pp_in (ufds nfds tsp sig sigsetsize : word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (pp_in ufds nfds tsp sig sigsetsize mem wmem).in_sysno)
      = some arm_ppoll :=
  lookup_ca_checked_table_ppoll

/-- The table applies `check_ppoll_row` to `pp_in`, narrowing `a1` to `unsigned int`.
model: `check_syscall` through the arm, unfolded; the table's own contents, not a kernel claim. -/
theorem check_syscall_pp_in (ufds nfds tsp sig sigsetsize : word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (pp_in ufds nfds tsp sig sigsetsize mem wmem) eff m
      = check_ppoll_row (pp_in ufds nfds tsp sig sigsetsize mem wmem) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_pp_in ufds nfds tsp sig sigsetsize mem wmem)

/-- The `= CheckReject` conjunct of Rocq's
`pselect_a_file_counts_once_per_set`, through the table:
The descriptor count, 1, is the lie `do_select` never tells, and the
checker rejects it with the same sets echoed.
kernel: fs/select.c:do_select@v6.18.46 -/
theorem pselect_a_descriptor_count_is_rejected_over_the_real_table :
    check_syscall (ps_in 4 ps_inp ps_outp 0 0 0
        (bytes_at ps_inp (word_le8 8 ++ word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 8), (ps_outp, word_le8 8)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_ps_in]
  exact pselect_a_descriptor_count_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`pselect_a_bad_sigsetsize_beats_an_unreadable_set`, through the table:
The -EFAULT of the set's copy-in is the other order, and the checker
rejects it: `do_pselect` does not reach `core_sys_select` once
`set_user_sigmask` has failed.  That is Linux's order; QEMU 11.1.1's
user-mode answer here is -EFAULT, and
`pselect_efault_behind_a_bad_sigsetsize_is_rejected` says why that
residual is the spec's.
kernel: fs/select.c:do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem pselect_efault_behind_a_bad_sigsetsize_is_rejected_over_the_real_table :
    check_syscall (ps_in 4 ps_inp 0 0 0 ps_sig
        (bytes_at ps_sig (word_le8 1 ++ word_le8 4)) ps_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model
      = CheckReject := by
  rw [check_syscall_ps_in]
  exact pselect_efault_behind_a_bad_sigsetsize_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`pselect_the_timespec_is_judged_raw`, through the table:
The deadline a normalizing model would have answered — one second's
sleep, sixteen zero bytes — is the answer a real kernel refused with -22,
and the checker rejects it.
kernel: fs/select.c:poll_select_set_timeout; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem pselect_the_normalized_deadline_is_rejected_over_the_real_table :
    check_syscall (ps_in 0 0 0 0 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 1000000000)) ps_wmem)
      (mkEffect 0 [(ps_tsp, word_le8 0 ++ word_le8 0)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_ps_in]
  exact pselect_the_normalized_deadline_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`pselect_aliased_sets_are_modeled`, through the table:
The ledger a memory snapshot would produce — the surviving word for both
entries — loses the first write, and the checker rejects it.
kernel: fs/select.c:core_sys_select,set_fd_set@v6.18.46 -/
theorem pselect_the_snapshot_ledger_is_rejected_over_the_real_table :
    check_syscall (ps_in 4 ps_inp 0 ps_inp 0 0 (bytes_at ps_inp (word_le8 8)) ps_wmem)
      (mkEffect 1 [(ps_inp, word_le8 0), (ps_inp, word_le8 0)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_ps_in]
  exact pselect_the_snapshot_ledger_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_counts_descriptors_not_bits`, through the table:
select's bit count, 2, is the lie `do_poll` never tells.
kernel: fs/select.c:do_poll@v6.18.46 -/
theorem ppoll_a_bit_count_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
      (mkEffect 2 [(pp_ufds + 6, word_le2 5)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_a_bit_count_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_a_read_write_file_polls_as_any_other`, through the table:
Reporting that file idle — 0 with `revents` 0 — is rejected: the
`DEFAULT_POLLMASK` answer is not a schedule.  This stands on `FdFileW`
for the Rocq `FdFileRW` fixture, as the header's mapping explains.
kernel: include/linux/poll.h:vfs_poll; fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_a_write_only_file_reported_idle_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 4 5))) pp_wmem)
      (mkEffect 0 [(pp_ufds + 6, word_le2 0)] []) pselect_model_kinds
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_a_write_only_file_reported_idle_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_an_unopened_descriptor_is_pollnval_not_ebadf`, through the table:
-EBADF is select's answer to the same descriptor — `max_select_fd`'s
(fs/select.c:433-435) — and no path of `do_pollfd` raises it: rejected.
kernel: fs/select.c:do_pollfd,max_select_fd@v6.18.46 -/
theorem ppoll_ebadf_for_an_unopened_descriptor_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 9 1)) pp_wmem)
      (mkEffect (errno_ret EBADF) [] []) pselect_model
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_ebadf_for_an_unopened_descriptor_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_a_negative_fd_is_skipped_not_invalid`, through the table:
`POLLNVAL` for a negative `fd` is rejected: that answer is for an
UNOPENED non-negative one.
kernel: fs/select.c:do_pollfd,do_poll@v6.18.46 -/
theorem ppoll_pollnval_for_a_negative_fd_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry (-1) 1))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 32)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_pollnval_for_a_negative_fd_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_events_filters_the_default_pollmask`, through the table:
Echoing `events` into `revents` is rejected: the mask is `& filter`ed,
not copied.
kernel: fs/select.c:do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_an_echoed_events_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 pp_tsp 0 0
        (mem_join (bytes_at pp_tsp (pp_ts 0 0)) (bytes_at pp_ufds (pp_entry 3 2))) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 2)] []) pselect_model
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_an_echoed_events_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_nfds_above_the_soft_limit_is_einval_before_the_copy`, through the table:
The copy's -EFAULT ahead of the limit test is the order `do_sys_poll`
does not have: rejected.  QEMU 11.1.1's user-mode answer here is
-EFAULT, and `ppoll_efault_ahead_of_the_limit_test_is_rejected` says why
that residual is the spec's.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem ppoll_efault_ahead_of_the_limit_test_is_rejected_over_the_real_table :
    check_syscall (pp_in pp_ufds 5 0 0 0 (fun _ => none) pp_wmem)
      (mkEffect (errno_ret EFAULT) [] []) pselect_model_lim
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_efault_ahead_of_the_limit_test_is_rejected

/-- The `= CheckReject` conjunct of Rocq's
`ppoll_the_timeout_is_judged_before_the_signal_mask`, through the table:
The mask's -EINVAL ahead of the timeout's -EFAULT is rejected: the mask
is handed to `set_user_sigmask` (kernel/signal.c:3281-3297) only at
fs/select.c:1111, after `get_timespec64` (:1103-1104) has succeeded.  That
is `do_pselect`'s order too (:739-740 before :755).
kernel: fs/select.c:ppoll,do_pselect; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem ppoll_einval_ahead_of_the_timeout_is_rejected_over_the_real_table :
    check_syscall (pp_in 0 0 pp_tsp pp_sig 4 (bytes_at pp_sig (word_le8 0 ++ word_le8 0)) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rw [check_syscall_pp_in]
  exact ppoll_einval_ahead_of_the_timeout_is_rejected

/-! ### Which registers the arms narrow -/

/-- `n` arrives in `a0` narrowed to `int`: a register holding `2^33` is
`n = 0` to Linux, the call that dereferences no set pointer, and the table
answers it.  An arm reading the whole register would see `2^32`, above
`pselect_nfds_max`, and decline.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:pselect6,core_sys_select@v6.18.46 -/
theorem pselect_n_is_a0_narrowed_to_int_over_the_real_table :
    check_syscall (ps_in (Z_to_bv 64 (2 ^ 33)) 65536 65536 65536 ps_tsp 0
        (bytes_at ps_tsp (word_le8 0 ++ word_le8 0)) ps_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- `nfds` arrives in `a1` narrowed to `unsigned int`: a register holding
`2^32` is `nfds = 0`, answered 0 under the zero timeout.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:ppoll,do_sys_poll@v6.18.46 -/
theorem ppoll_nfds_is_a1_narrowed_to_unsigned_int_over_the_real_table :
    check_syscall (pp_in 65536 (Z_to_bv 64 (2 ^ 32)) pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect 0 [] []) pselect_model
      = CheckOk pselect_model [] := by
  rfl

/-- The -EINVAL a count above the soft descriptor limit earns
(fs/select.c:981-982) is rejected on the call above: an arm reading the
whole register would see a count of `2^32` and accept it.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/select.c:ppoll,do_sys_poll@v6.18.46 -/
theorem ppoll_einval_for_a_narrowed_zero_count_is_rejected_over_the_real_table :
    check_syscall (pp_in 65536 (Z_to_bv 64 (2 ^ 32)) pp_tsp 0 0 (bytes_at pp_tsp (pp_ts 0 0)) pp_wmem)
      (mkEffect (errno_ret EINVAL) [] []) pselect_model
      = CheckReject := by
  rfl

/-- This pins `ufds` to `a0` and `nfds` to `a1` through the table: read the
other way round, `nfds` would be the array's address and the count of 1
would not be accepted.
kernel: fs/select.c:do_poll,do_pollfd; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem ppoll_counts_descriptors_not_bits_over_the_real_table :
    check_syscall (pp_in pp_ufds 1 0 0 0 (bytes_at pp_ufds (pp_entry 3 5)) pp_wmem)
      (mkEffect 1 [(pp_ufds + 6, word_le2 5)] []) pselect_model
      = CheckOk pselect_model [] := by
  rw [check_syscall_pp_in]
  exact ppoll_counts_descriptors_not_bits

end V_Fs_Select

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Select
