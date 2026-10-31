import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

/-! # Checks.Cases.Checks.Witness.Uaccess — the range witness, read off against Linux

Pins over `Checks.Witness.Uaccess`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Uaccess.v`.  The Rocq tree pins
the SPEC side of this boundary in `Checks/Cases/Uaccess.v`, the Lean tree
in that file's twin `Checks/Cases/Uaccess.lean`; the witness side has no
Rocq check file, so this one mirrors nothing and holds the Lean tree's
tests for the witness.  Not part of the trusted specification.

`access_ok_zero_witness buf count m k` is the outcome an arm exhibits once
the kernel has decided to move NO bytes: the arm's own zero answer `k`
where the range passes `__access_ok` (include/asm-generic/access_ok.h,
Linux v6.18.46), -EFAULT where it does not.  The pins walk the predicate's
two conjuncts at their bounds — `size <= TASK_SIZE_MAX` and
`addr <= TASK_SIZE_MAX - size`, both inclusive, each from its passing and
its failing side — with `TASK_SIZE_MAX` the `TASK_SIZE` fallback riscv64
gets in that header, 2^47 under Sv48; and one pin takes the count at
2^64 - 1, since `size` is `unsigned long` and a signed reading of the
register would pass a range the kernel refuses.  Each proof decides the
predicate on the pin's own values from the goal, rather than by restating
the condition it expects to find there, so that a changed range test fails
exactly the pins whose values it moves and no other.  The
limit is written as that numeral rather than as `State.TASK_SIZE`, so that
each pin is stated in the terms of the kernel function it cites, which
names the limit through the macro and never by value; the first pin below
ties the numeral to the model's constant, so a limit that moved would fail
here.  The kernel reading of the constant itself, with its derivation
from the page-table geometry, is `task_size_is_the_sv48_top` in
`Checks/Cases/Uaccess.lean` and its Rocq twin; the pin below restates
the value because this file does not import that one. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Witness.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

variable (m : Model) (k : outcome SyscallEffect)

/-- The numeral the pins below use for the limit is the model's `TASK_SIZE`:
2^47, the Sv48 half-space.
model: the model's own constant at a numeral; the kernel reading is
`task_size_is_the_sv48_top` in `Checks/Cases/Uaccess.lean` -/
theorem the_limit_is_task_size : TASK_SIZE = 2 ^ 47 := by decide

section InRange

/-! ## Ranges the kernel accepts: the arm's answer stands -/

/-- A page at 0x1000 passes both conjuncts, so the arm's own zero answer
stands: the kernel moved no bytes and found no fault to report.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem in_range_keeps_the_arms_answer :
    access_ok_zero_witness (Z_to_bv 64 0x1000) (Z_to_bv 64 4096) m k = k := by
  unfold access_ok_zero_witness
  exact ite_eq_left (by decide)

/-- The last window below the limit passes: `addr <= TASK_SIZE_MAX - size`
is inclusive, and 2^47 - 4096 with 4096 bytes ends exactly at 2^47.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem the_last_window_keeps_the_arms_answer :
    access_ok_zero_witness (Z_to_bv 64 (2 ^ 47 - 4096)) (Z_to_bv 64 4096) m k = k := by
  unfold access_ok_zero_witness
  exact ite_eq_left (by decide)

/-- A zero-length transfer is checked like any other, and at 2^47 itself
both conjuncts hold — `0 <= limit` and `addr <= limit - 0` — so the arm's
answer stands.  `import_ubuf` tests the range whatever `len` is, 0
included, before a zero-length `getrandom`, `sendto` or `recvfrom`
transfer; of those, the socket witnesses consume this definition, and
`getrandom`'s tests `access_okb` in place (`Checks/Witness/Uaccess.lean`
says why).  The tracer's record of the answer is
`testing/syscall-check/tests/zero_len_fault.c`, CASE `chan0-top` and
`rand0-top`.
kernel: include/asm-generic/access_ok.h:__access_ok; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem zero_length_at_the_limit_keeps_the_arms_answer :
    access_ok_zero_witness (Z_to_bv 64 (2 ^ 47)) (Z_to_bv 64 0) m k = k := by
  unfold access_ok_zero_witness
  exact ite_eq_left (by decide)

/-- The whole space from address 0: `size <= TASK_SIZE_MAX` is inclusive,
so a count of exactly 2^47 at 0 passes both conjuncts — `2^47 <= 2^47` and
`0 <= 0` — and the arm's answer stands.  This is the passing side of the
first conjunct, which `a_length_over_the_limit_is_efault` walks from the
other: a `read` of 2^47 bytes at address 0 passes the range test and goes
on to the `MAX_RW_COUNT` clamp.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_read@v6.18.46 -/
theorem the_whole_space_keeps_the_arms_answer :
    access_ok_zero_witness (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 47)) m k = k := by
  unfold access_ok_zero_witness
  exact ite_eq_left (by decide)

end InRange

section Refused

/-! ## Ranges the kernel refuses: -EFAULT, whatever the arm would have said

The answer is the one `vfs_read` and `vfs_write` in fs/read_write.c (Linux
v6.18.46) give after the `FMODE` gates and before `rw_verify_area`, and
the one `import_ubuf` in lib/iov_iter.c (v6.18.46) gives before a socket
or getrandom transfer — for a count `MAX_RW_COUNT` leaves alone:
`import_ubuf` clamps first, so at a count above the limit it tests the
clamped range and passes, and the over-limit pins below are the `vfs_*`
verdict alone, as their evidence lines say.  It is the range verdict and
not a copy fault: no byte moved. -/

/-- One byte higher than the last window fails: the window would end past
the limit.  The arm's answer `k` is gone and -EFAULT stands in its place.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_read@v6.18.46 -/
theorem past_the_limit_is_efault :
    access_ok_zero_witness (Z_to_bv 64 (2 ^ 47 - 4095)) (Z_to_bv 64 4096) m k
      = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  unfold access_ok_zero_witness ret_outcome
  exact ite_eq_right (by decide)

/-- A zero-length transfer one past the limit is -EFAULT even though no
byte would have moved: the first conjunct passes and the second fails.
The tracer's record is `testing/syscall-check/tests/zero_len_fault.c`,
CASE `chan0-past` and `rand0-past`.
kernel: include/asm-generic/access_ok.h:__access_ok; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem zero_length_past_the_limit_is_efault :
    access_ok_zero_witness (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) m k
      = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  unfold access_ok_zero_witness ret_outcome
  exact ite_eq_right (by decide)

/-- A length above the limit fails the FIRST conjunct, at address 0 where
the second would pass for any admissible length.  In the kernel's unsigned
arithmetic the first conjunct refuses alone — `limit - size` would wrap,
and `&&` never evaluates it — while in the model's `Int` arithmetic
`TASK_SIZE - len` is -1 and the second conjunct fails too: the size
conjunct is implied by the address conjunct in `Int` and is there to
mirror the unsigned subtraction, so no pin can fail it alone.  That
argument is `Checks/Cases/Uaccess.lean`'s and its Rocq twin's.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_write@v6.18.46 -/
theorem a_length_over_the_limit_is_efault :
    access_ok_zero_witness (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 47 + 1)) m k
      = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  unfold access_ok_zero_witness ret_outcome
  exact ite_eq_right (by decide)

/-- THE RANGE VERDICT, NOT THE WALK'S.  A range starting 4 bytes below 2^64
with 8 bytes wraps: `State.read_bytes_map` walks it in word arithmetic and
would read it whole, while `__access_ok`'s subtraction refuses it.  The
witness answers -EFAULT; delete the range test and let a mapping walk
decide, and this pin fails.  Why no probe can reach a wrapping range —
the tracer's writable view stops at 2^47 — is on
`Checks/Cases/Uaccess.lean` and its Rocq twin.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_read@v6.18.46 -/
theorem a_wrapping_range_is_efault :
    access_ok_zero_witness (Z_to_bv 64 (2 ^ 64 - 4)) (Z_to_bv 64 8) m k
      = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  unfold access_ok_zero_witness ret_outcome
  exact ite_eq_right (by decide)

/-- THE COUNT IS UNSIGNED.  A count of 2^64 - 1 — the `(size_t)-1` a C
caller writes as -1 — fails the FIRST conjunct on the size alone, whatever
the base: `size` is `unsigned long` in `__access_ok`, so no signed reading
of the register is the kernel's, and a witness that read the count as
`bv_signed` would pass this range as a -1 and answer `k`.  Every other
pin's count is below 2^63, where the two readings agree; this one is where
they part.  The spec side has the same corner with a probe behind it,
`access_ok_zero_negative_count_is_efault` in `Checks/Cases/Uaccess.lean`
(`testing/syscall-check/tests/read_window.c`, CASE `negc`).
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_read@v6.18.46 -/
theorem a_negative_count_is_efault :
    access_ok_zero_witness (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 64 - 1)) m k
      = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  unfold access_ok_zero_witness ret_outcome
  exact ite_eq_right (by decide)

end Refused

section TwoAnswers

/-- Two answers and no third: the witness never declines, on any range,
when the arm's own answer is not itself a decline.  `__access_ok` decides
every range, so there is nothing here for the model to fail closed on;
the pass-through of a `k` a consumer declines on purpose is
`in_range_keeps_the_arms_answer`'s, at a generic `k`, and not this pin's.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem never_declines (buf count : word) (hk : k ≠ Unmodeled) :
    access_ok_zero_witness buf count m k ≠ Unmodeled := by
  unfold access_ok_zero_witness
  split
  · exact hk
  · unfold ret_outcome
    exact nofun

end TwoAnswers

section Tactic

/-! ## `srw`, with only the witnesses' definition in scope

This file imports `Checks/Witness/Uaccess.lean` and through it
`Checks/Witness/Prelude.lean`, and nothing of `Checks/Sys/`, so the `srw`
here is the witnesses' alone: the two examples pin its expansion — a
rewrite, then the reduction of the redex the rewrite exposed — which the
examples in `Checks/Cases/Checks/Witness/Prelude.lean` cannot, since there
the checkers' `srw` is in scope too and Lean elaborates only one of the
two.  Drop the `dsimp only` from the macro and the first example fails
here. -/

/-- `srw`: rewrite, then re-reduce the redex the rewrite exposed.
model: the tactic's own expansion; no kernel behaviour is claimed -/
example (x y z : Nat) (h : x = z) (hy : z + 1 = y) : (fun n => n + 1) x = y := by
  srw h
  rw [hy]

/-- `srw … at h`: the same on a hypothesis.
model: the tactic's own expansion; no kernel behaviour is claimed -/
example (x y : Nat) (h : x = 3) (hx : (fun n => n + 1) x = y) : 3 + 1 = y := by
  srw h at hx
  exact hx

end Tactic

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Witness.Uaccess
