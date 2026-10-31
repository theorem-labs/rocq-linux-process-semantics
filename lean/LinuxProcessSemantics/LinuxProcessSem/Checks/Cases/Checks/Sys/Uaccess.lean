import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess

/-! # Checks.Cases.Checks.Sys.Uaccess — the checkers' user-access gates, read off against Linux

Pins over `Checks.Sys.Uaccess`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Uaccess.v`.  The Rocq tree has no
check file for it — its lemmas are stated in the file itself — so this
file mirrors nothing: these are the Lean tree's tests for what the twin
ports, placed where every pin in this tree lives
(`Checks/Cases/<mirror path>`) so that `tools/check_lean_pins.py` reads
them and the twin holds only definitions, their Rocq-twin lemmas, the
tactic macros and the Lean-only `check_access_ok_zero_split`, the split
those macros perform.  Not part of the trusted specification:
this file is QA on the definitions, written to be READ.

The two acceptors under test decide what a checker ADMITS from a
zero-byte trace: whether the range verdict `access_ok` hands down before
any transfer is the arm's own question or the bare -EFAULT, and whether
an arm the model cannot decide returned the -EFAULT or its one fallback.
Each pin places the checker on a concrete address — a real buffer, the
limit `zero_len_fault.c` probes, one byte past it — and refutes the
concrete lie a kernel cannot tell there.  The last section exercises the
tactic macros and claims nothing about Linux; it says so.

The probe cases cited are about the Rocq checker: the harness runs the
EXTRACTED ROCQ model (`check.sh` extracts it), so no Lean definition is
ever evaluated against a trace.  A `probe:` line here names the case
whose recorded answer is the fact the Lean pin states, and the kernel
lines in the section headers are the evidence for both. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess

section ZeroTransferGate

/-! ## `check_access_ok_zero`: the range verdict, executable

`vfs_read` and `vfs_write` ask `access_ok(buf, count)` before they
dispatch and return -EFAULT when it refuses (fs/read_write.c, v6.18.46),
and on riscv64 `access_ok` is `__access_ok` on the untagged address
(arch/riscv/include/asm/uaccess.h, v6.18.46; the untagging is the
identity at the pointer-masking length 0 every `execve` sets, the premise
`Sys/Uaccess.lean`'s header and Rocq `State.access_okb` carry): `size <=
limit && addr <=
limit - size` with `limit = TASK_SIZE_MAX` (include/asm-generic/access_ok.h,
v6.18.46).  A transfer that moves NO bytes still faces it, so the gate's
verdict is the whole of what a zero-count trace can show, and the pins
here place the checker on both sides of the limit `zero_len_fault.c`
probes: a real buffer, the limit itself, and one byte past it. -/

variable (m m' : Model) (k : check_result) (eff : SyscallEffect) (evs : List event)

/-- In range, the gate is the arm's own checker: `read(0, buf, 0)` at a
real buffer is the arm's zero, whatever the arm's checker `k` decides.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0 -/
theorem check_access_ok_zero_in_range_is_the_arms_checker :
    check_access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) eff m k = k := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 0)) = true := by decide
  simp only [check_access_ok_zero, h, ↓reduceIte]

/-- The limit itself is in range with a zero count: `0 <= limit` and
`2^47 <= limit - 0`, so `read(0, 2^47, 0)` is the arm's answer.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-top -/
theorem check_access_ok_zero_at_the_limit_is_the_arms_checker :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47)) (Z_to_bv 64 0) eff m k = k := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47)) (bv_unsigned (Z_to_bv 64 0)) = true := by decide
  simp only [check_access_ok_zero, h, ↓reduceIte]

/-- One byte past it, the gate is the bare -EFAULT acceptor and the arm's
checker is never consulted: `read(0, 2^47 + 1, 0)` is -EFAULT.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-past -/
theorem check_access_ok_zero_past_the_limit_is_the_efault_acceptor :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) eff m k
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47 + 1)) (bv_unsigned (Z_to_bv 64 0)) = false := by decide
  simp only [check_access_ok_zero, h, Bool.false_eq_true, ↓reduceIte]

/-- ... so a kernel answering 0 there is refused, whatever checker the
arm brought: chan0-past is never 0.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan0-past -/
theorem check_access_ok_zero_past_the_limit_refuses_a_zero :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) (mkEffect (Z_to_bv 64 0) [] []) m k
      ≠ CheckOk m' evs := by
  rw [check_access_ok_zero_past_the_limit_is_the_efault_acceptor]
  simp only [check_ret_only, show bv_eqb (Z_to_bv 64 0) (errno_ret EFAULT) = false by decide,
    Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- In range, the gate turns no fault into acceptance: with the arm's
checker demanding 0, a -EFAULT at a real buffer is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0 -/
theorem check_access_ok_zero_in_range_refuses_a_fault :
    check_access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) (mkEffect (errno_ret EFAULT) [] []) m
      (check_ret_only (mkEffect (errno_ret EFAULT) [] []) (Z_to_bv 64 0) m []) ≠ CheckOk m' evs := by
  rw [check_access_ok_zero_in_range_is_the_arms_checker]
  simp only [check_ret_only, show bv_eqb (errno_ret EFAULT) (Z_to_bv 64 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- And at the limit itself: a harness whose reservation ended below
`TASK_SIZE` and faulted `read(0, 2^47, 0)` is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0-top -/
theorem check_access_ok_zero_at_the_limit_refuses_a_fault :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47)) (Z_to_bv 64 0) (mkEffect (errno_ret EFAULT) [] []) m
      (check_ret_only (mkEffect (errno_ret EFAULT) [] []) (Z_to_bv 64 0) m []) ≠ CheckOk m' evs := by
  rw [check_access_ok_zero_at_the_limit_is_the_arms_checker]
  simp only [check_ret_only, show bv_eqb (errno_ret EFAULT) (Z_to_bv 64 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The gate is the same function on the write side: `write(1, 2^47 + 1, 0)`
is -EFAULT and a 0 there is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate write:ret=0 -- write0-past -/
theorem check_access_ok_zero_past_the_limit_refuses_a_zero_write :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) (mkEffect (Z_to_bv 64 0) [] []) m
      (check_ret_only (mkEffect (Z_to_bv 64 0) [] []) (Z_to_bv 64 0) m []) ≠ CheckOk m' evs :=
  check_access_ok_zero_past_the_limit_refuses_a_zero m m' _ evs

/-- ... and past the limit the bare -EFAULT itself is admitted, whatever
`k` would have said: the acceptor the gate falls back to is
`check_ret_only` on `errno_ret EFAULT`, not a refusal.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-past -/
theorem check_access_ok_zero_past_the_limit_admits_the_bare_efault :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) (mkEffect (errno_ret EFAULT) [] []) m k
      = CheckOk m [] := by
  rw [check_access_ok_zero_past_the_limit_is_the_efault_acceptor]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The COUNT moves the end: one byte at 2^47 - 1 ends exactly at the
limit (`addr <= limit - size` with equality) and is the arm's answer.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan-top-1 -/
theorem check_access_ok_zero_count_to_the_limit_is_the_arms_checker :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 - 1)) (Z_to_bv 64 1) eff m k = k := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47 - 1)) (bv_unsigned (Z_to_bv 64 1)) = true := by decide
  simp only [check_access_ok_zero, h, ↓reduceIte]

/-- ... and one more byte of count, at the same address, is the -EFAULT
acceptor: the end, not the base, is what crossed the limit.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan-top-2 -/
theorem check_access_ok_zero_count_past_the_limit_is_the_efault_acceptor :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 - 1)) (Z_to_bv 64 2) eff m k
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47 - 1)) (bv_unsigned (Z_to_bv 64 2)) = false := by decide
  simp only [check_access_ok_zero, h, Bool.false_eq_true, ↓reduceIte]

/-- ... so a 0 there is refused: chan-top-2 is never 0.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan-top-2 -/
theorem check_access_ok_zero_count_past_the_limit_refuses_a_zero :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 - 1)) (Z_to_bv 64 2) (mkEffect (Z_to_bv 64 0) [] []) m k
      ≠ CheckOk m' evs := by
  rw [check_access_ok_zero_count_past_the_limit_is_the_efault_acceptor]
  simp only [check_ret_only, show bv_eqb (Z_to_bv 64 0) (errno_ret EFAULT) = false by decide,
    Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- A count with the top bit set fails `size <= limit` before the address
is looked at, so `vfs_read` returns -EFAULT at a real buffer; the signed
reading of the count would have admitted it.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_access_ok_zero_huge_count_is_the_efault_acceptor :
    check_access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 63)) eff m k
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 (2 ^ 63))) = false := by decide
  simp only [check_access_ok_zero, h, Bool.false_eq_true, ↓reduceIte]

/-- A range that wraps 2^64 is refused although its END, 4, is in range:
`__access_ok` asks `addr <= limit - size` of the base, never of the sum.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_access_ok_zero_wrapping_range_is_the_efault_acceptor :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 64 - 4)) (Z_to_bv 64 8) eff m k
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 64 - 4)) (bv_unsigned (Z_to_bv 64 8)) = false := by decide
  simp only [check_access_ok_zero, h, Bool.false_eq_true, ↓reduceIte]

/-- The gate never declines on its own: out of range it is `check_ret_only`,
which has no declining arm, and in range it is whatever `k` is.
model: the range verdict is a Boolean and the -EFAULT arm is `check_ret_only`; only the continuation `k` can decline -/
theorem check_access_ok_zero_declines_only_through_k (buf count : word)
    (hk : k ≠ CheckUnmodeled) : check_access_ok_zero buf count eff m k ≠ CheckUnmodeled := by
  unfold check_access_ok_zero
  cases access_okb buf (bv_unsigned count) with
  | true => simp only [↓reduceIte]; exact hk
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact check_ret_only_no_unmodeled eff _ m []

/-- The split, both sides at once on the in-range witness: the checker
is `k` and the spec is its continuation.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0 -/
theorem check_access_ok_zero_split_in_range (ks : Sys SyscallEffect) :
    check_access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) eff m k = k
      ∧ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) ks = ks := by
  rcases check_access_ok_zero_split (Z_to_bv 64 0x10000) (Z_to_bv 64 0) eff m k ks with
    ⟨_, hc, hs⟩ | ⟨hok, _, _⟩
  · exact ⟨hc, hs⟩
  · exact absurd hok (by decide)

/-- ... and on the out-of-range witness: the checker is the bare -EFAULT
acceptor and the spec is `err_ret EFAULT`.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-past -/
theorem check_access_ok_zero_split_past_the_limit (ks : Sys SyscallEffect) :
    check_access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) eff m k
        = check_ret_only eff (errno_ret EFAULT) m []
      ∧ access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) ks = err_ret EFAULT := by
  rcases check_access_ok_zero_split (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) eff m k ks with
    ⟨hok, _, _⟩ | ⟨_, hc, hs⟩
  · exact absurd hok (by decide)
  · exact ⟨hc, hs⟩

end ZeroTransferGate

section EfaultOr

/-! ## `check_efault_or`: -EFAULT or the one fallback

The acceptor for an arm the model cannot decide: a destination whose
writability it does not track, where the kernel's `copy_to_user` either
fails — the arm returns -EFAULT — or succeeds and the arm returns its
one other answer.  Both arms are bare returns; anything else is refused,
and the acceptor never declines. -/

variable (m m' : Model) (evs : List event) (fallback : word) (a : word) (b : byte)

/-- The bare -EFAULT is admitted whatever the fallback is.
model: the first arm is `eff_is_errno EFAULT`, a closed computation on the acceptor; `fallback` is free -/
theorem check_efault_or_admits_the_bare_efault :
    check_efault_or fallback (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] := by
  simp only [check_efault_or, eff_is_errno, bv_eqb_refl, ↓reduceIte]

/-- So is the bare fallback — 0, for an arm whose success is a zero return.
model: the acceptor's second arm is `check_ret_only` on the fallback; which return that is belongs to the calling arm -/
theorem check_efault_or_admits_the_fallback :
    check_efault_or (Z_to_bv 64 0) (mkEffect (Z_to_bv 64 0) [] []) m = CheckOk m [] := by
  simp only [check_efault_or,
    show eff_is_errno EFAULT (mkEffect (Z_to_bv 64 0) [] []) = false by decide,
    Bool.false_eq_true, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The second arm is the fallback the CALLER names, not a fixed 0: with
fallback 7, a bare 7 is admitted and a bare 0 is refused.
model: the second arm is `check_ret_only` on `fallback`; nothing in the acceptor fixes which return that is -/
theorem check_efault_or_admits_the_named_fallback_only :
    check_efault_or (Z_to_bv 64 7) (mkEffect (Z_to_bv 64 7) [] []) m = CheckOk m []
      ∧ check_efault_or (Z_to_bv 64 7) (mkEffect (Z_to_bv 64 0) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩
  · simp only [check_efault_or,
      show eff_is_errno EFAULT (mkEffect (Z_to_bv 64 7) [] []) = false by decide,
      Bool.false_eq_true, ↓reduceIte]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [check_efault_or,
      show eff_is_errno EFAULT (mkEffect (Z_to_bv 64 0) [] []) = false by decide,
      Bool.false_eq_true, ↓reduceIte, check_ret_only,
      show bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 7) = false by decide]

/-- A fallback that is itself -EFAULT is admitted by the first arm, so the
acceptor is total on its two answers even when they coincide.
model: the bare-EFAULT pin at `fallback := errno_ret EFAULT`; nothing here reads the kernel -/
theorem check_efault_or_admits_an_efault_fallback :
    check_efault_or (errno_ret EFAULT) (mkEffect (errno_ret EFAULT) [] []) m = CheckOk m [] :=
  check_efault_or_admits_the_bare_efault m _

/-- Another errno is refused: -EINVAL is neither arm when the fallback is 0.
kernel: include/uapi/asm-generic/errno-base.h:EFAULT,EINVAL@v6.18.46 -/
theorem check_efault_or_refuses_another_errno :
    check_efault_or (Z_to_bv 64 0) (mkEffect (errno_ret EINVAL) [] []) m ≠ CheckOk m' evs :=
  fun h => check_efault_or_not_einval _ _ _ _ (by decide) h

/-- Another success is refused too: a 1 where the fallback is 0.
model: the acceptor's second arm is `check_ret_only` on the fallback, which refuses every other return -/
theorem check_efault_or_refuses_another_return :
    check_efault_or (Z_to_bv 64 0) (mkEffect (Z_to_bv 64 1) [] []) m = CheckReject := by
  simp only [check_efault_or,
    show eff_is_errno EFAULT (mkEffect (Z_to_bv 64 1) [] []) = false by decide,
    Bool.false_eq_true, ↓reduceIte, check_ret_only,
    show bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0) = false by decide]

/-- A -EFAULT beside a write is refused: the first arm is `eff_is_errno`,
the shape that moved no bytes, and a fault that wrote is not it.  That is
a premise on the CALLER, not a claim about Linux — `copy_to_user` can
store a prefix and then fault (the `eff_is_errno` section note in
`Checks/Cases/Checks/Sys/Prelude.lean`) — so an arm may hand this
acceptor its answer only where its one user write is all-or-nothing.
model: the first arm is `eff_is_errno EFAULT`, which `eff_is_errno_refuses_a_write` pins on the same shape -/
theorem check_efault_or_refuses_a_write_beside_efault :
    check_efault_or fallback (mkEffect (errno_ret EFAULT) [(a, [b])] []) m = CheckReject := rfl

/-- And the fallback beside a copy-in ledger is refused: both arms are
bare returns, and a ledgered shape has `check_ret_only_copyins`.
model: both arms of the acceptor are return-only shapes; a ledger belongs to `check_ret_only_copyins` -/
theorem check_efault_or_refuses_a_ledger_beside_the_fallback :
    check_efault_or (Z_to_bv 64 0) (with_copyins [(a, 1)] (mkEffect (Z_to_bv 64 0) [] [])) m
      = CheckReject := rfl

/-- The acceptor never declines: even the -EINVAL both arms refuse is a
`CheckReject`, not a `CheckUnmodeled`.
model: an acceptor over two Boolean tests has no declining arm; the modeled surface is the calling arm's question -/
theorem check_efault_or_never_declines :
    check_efault_or (Z_to_bv 64 0) (mkEffect (errno_ret EINVAL) [] []) m ≠ CheckUnmodeled :=
  check_efault_or_no_unmodeled _ _ m

/-- Neither does the combinator it decides, on the same fallback.
model: `alt` of two `pure`s has no `Unmodeled` outcome -/
theorem efault_or_alt_never_declines (i : SyscallInput) :
    ¬ alt (err_ret EFAULT) (ret_only (Z_to_bv 64 0)) i m Unmodeled :=
  efault_or_no_unmodeled _ i m

/-- Soundness and completeness at once, on the fallback 0: the acceptor
answers `CheckOk` exactly on the outcomes the combinator admits.
model: the acceptor is the executable form of `alt (err_ret EFAULT) (ret_only fallback)`; its two directions are the twin's soundness and completeness lemmas -/
theorem check_efault_or_ok_iff_alt (i : SyscallInput) (eff : SyscallEffect) :
    check_efault_or (Z_to_bv 64 0) eff m = CheckOk m' evs
      ↔ alt (err_ret EFAULT) (ret_only (Z_to_bv 64 0)) i m (Ok eff m' evs) :=
  ⟨check_efault_or_sound_ok _ i eff m m' evs, check_efault_or_complete_ok _ i eff m m' evs⟩

end EfaultOr

section Tactics

/-! ## The tactic macros, exercised

No kernel claim here.  Each example is the goal shape a checker proof
hands the macro — the `sendto`/`recvfrom` shapes of Rocq's
`Checks/Sys/Net/Socket.v`, whose soundness proofs open with
`ok_zero_cases H buf count` and whose completeness proofs with
`ok_zero_split buf count` — so a macro whose Lean arms stopped matching
the Rocq ones would fail to build here rather than in the first checker
port that reaches for it. -/

/-- `ok_zero_cases`: the soundness shape.  The out-of-range arm comes
FIRST (Lean's `Bool` lists `false` before `true`); on it `H` is the bare
-EFAULT acceptor, and on the in-range arm `H` is the arm's own checker.
The verdict is exposed as `Hok`, which the first arm reads.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (buf count r : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : check_access_ok_zero buf count eff m (check_ret_only eff r m []) = CheckOk m' evs) :
    access_ok_zero buf count (ret_only r) i m (Ok eff m' evs) := by
  ok_zero_cases h buf count
  · have _hok : access_okb buf (bv_unsigned count) = false := Hok
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- `ok_zero_split`: the completeness shape.  The out-of-range arm comes
FIRST (Lean's `Bool` lists `false` before `true`) and the verdict stays
in context as `Hok`, which each arm reads — Rocq's `check_sendto_complete_ok`
selects its arm by index (`ok_zero_split buf count. 2: { … }`), so a
port of it depends on exactly this order; both arms are then taken down
to the checker's own equation and closed by `check_ret_only_ok_iff`,
since the in-range arm's `bv_eqb r r` is symbolic and not `rfl`'s to
close.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (buf count r : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : access_ok_zero buf count (ret_only r) i m (Ok eff m' evs)) :
    check_access_ok_zero buf count eff m (check_ret_only eff r m []) = CheckOk m' evs := by
  ok_zero_split buf count
  · have _hok : access_okb buf (bv_unsigned count) = false := Hok
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · have _hok : access_okb buf (bv_unsigned count) = true := Hok
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- `ok_zero_complete`: the completeness shape whose two arms both close
by computation — here both answers are the concrete -EFAULT.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (buf count : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : access_ok_zero buf count (ret_only (errno_ret EFAULT)) i m (Ok eff m' evs)) :
    check_access_ok_zero buf count eff m (check_ret_only eff (errno_ret EFAULT) m [])
      = CheckOk m' evs := by
  ok_zero_complete buf count

end Tactics

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Uaccess
