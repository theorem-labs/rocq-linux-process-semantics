import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # Checks.Cases.Uaccess — worked examples over the user-buffer boundary

Mirrors `theories/LinuxProcessSem/Checks/Cases/Uaccess.v`, which answers to
the kernel uaccess headers — the range test it transcribes is
`__access_ok` (include/asm-generic/access_ok.h at v6.18.46), not anything
include/linux/uaccess.h defines.  Not part of the trusted specification:
this file holds the worked examples for the range guard
`Sys.Uaccess.access_ok_zero` and the gates beside it, and no syscall's own
arms.

The theorems marked `rocq-twin:` are the Rocq file's examples, name for
name, in the Rocq file's own sections; the sections after them pin the
decisions
`Sys/Uaccess.lean` ports that the Rocq file leaves to the syscall arms —
the value of `rw_bytes_max`, the two gates on it, the zero-transfer guard
on the outcomes it admits and refuses, and the zero-byte effect shape —
against the kernel where they are kernel claims and as `model:` facts
where they are the model's own.  The zero-transfer pins are stated on the
guard's OUTCOMES, as `Checks/Cases/Mm/Mmap.lean` states an arm's: an `iff`
over every outcome fixes what is admitted and what is refused in one
statement, and the refutation beside it names the lie the probe's
`--mutate` case tells.

The harness cannot reach the wrapping and high ranges below;
`Checks/Cases/Uaccess.v` says why (the tracer maps nothing at or above
`TASK_SIZE`), and `bugs/wrapping-walks-unbounded-segments.md` is why the
definition can.  It CAN reach the boundary itself, from both sides, and
`testing/syscall-check/tests/zero_len_fault.c` does: those pins cite the
probe's `CASE` lines instead of the header. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess

/-! ## The range check and the byte walk, where they disagree

`State.access_okb` tests a range as `__access_ok` does, by a SUBTRACTION
in `Int`; `State.read_bytes_map` walks `buf`, `buf + 1`, ... in WORD
arithmetic and so WRAPS at 2^64.  A range that starts just under the top
of the address space therefore walks off the end, comes back at 0, and
reads in full — while its exact end is past `State.TASK_SIZE`.  These
examples pin that the guard every zero-delivery arm asks,
`Sys.Uaccess.access_ok_zero`, answers -EFAULT there and does not let the
walk speak for it.

`wrap_buf` is 2^64 - 4 and the count is 8, so the walk covers the four
bytes below 2^64 and the four at 0.  `wrap_mem` maps exactly those eight
and nothing else. -/

def wrap_buf : word := Z_to_bv 64 (2 ^ 64 - 4)

def wrap_mem : word → Option byte :=
  fun a => if (decide (bv_unsigned a < 4) || decide (2 ^ 64 - 4 ≤ bv_unsigned a))
           then some (Z_to_bv 8 0) else none

/-- The walk really does wrap: all eight bytes read, so a guard that
trusted the walk would call the range mapped end to end.
rocq-twin: wrap_range_reads_across_the_top
model: the bare walk on the wrapping witness, kept so the refusal below is not vacuous -/
theorem wrap_range_reads_across_the_top :
    read_bytes_map wrap_mem wrap_buf (Z_to_bv 64 8) ≠ none := by decide

/-- And the kernel's predicate refuses it: `size` is 8, comfortably under
`TASK_SIZE`, so the first half passes, and it is `addr <= TASK_SIZE - 8`
that 2^64 - 4 violates (include/asm-generic/access_ok.h, `__access_ok`,
v6.18.46).
rocq-twin: wrap_range_is_refused
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrap_range_is_refused :
    access_okb wrap_buf 8 = false := by decide

/-- THE ONE THAT MATTERS: the arm's verdict is the range's, whatever the
walk says.  Delete the range test from `access_ok_zero` and let a mapping
walk decide, and this theorem fails — which is the whole of the guard's
mutation test.  The -EFAULT is `vfs_read`'s and `vfs_write`'s
(fs/read_write.c, v6.18.46: `if (unlikely(!access_ok(buf, count))) return
-EFAULT;` before any dispatch), on the range `__access_ok` refuses.
rocq-twin: access_ok_zero_faults_on_the_wrap
kernel: fs/read_write.c:vfs_read,vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_faults_on_the_wrap (k : Sys SyscallEffect) :
    access_ok_zero wrap_buf (Z_to_bv 64 8) k = err_ret EFAULT := by
  have h : access_okb wrap_buf (bv_unsigned (Z_to_bv 64 8)) = false := by decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- THE MUTATION TEST, MADE PERMANENT rather than performed once: the
mapping walk alone, evaluated on the same witness, says the range is
fine, which is the wrong answer.  Pinning it here is what stops the pin
above from going vacuous — it would also pass if `wrap_mem` quietly
stopped mapping the range, or if `wrap_buf` stopped wrapping, and
then it would be testing nothing.
rocq-twin: wrap_would_pass_a_bare_walk
model: the bare walk on the wrapping witness at eight bytes and at one, both mapped -/
theorem wrap_would_pass_a_bare_walk :
    ((match read_bytes_map wrap_mem wrap_buf (Z_to_bv 64 8) with
      | some _ => true | none => false)
     && (match read_bytes_map wrap_mem wrap_buf (Z_to_bv 64 1) with
         | some _ => true | none => false)) = true := by decide

/-! ## Past `TASK_SIZE`, where a range does NOT wrap and is still refused

The wrap is not the only way a walk-based argument fails, and a guard that
only closed the wrap would still be wrong.  `buf = 2^63` with `count = 8`
does NOT wrap — its `Int` sum is 2^63 + 8, comfortably under 2^64, so the
walk visits exactly the bytes the sum names — and `access_ok` refuses it
anyway, because `__access_ok` tests `addr <= TASK_SIZE - size`.

THIS IS THE CASE THAT DISCRIMINATES THE GUARD.  A plain no-wrap test at
2^64 passes here and would answer the arm's 0; only asking
`State.access_okb`, the kernel's own predicate, answers -EFAULT.  Same
reason as the wrap for belonging here: the harness cannot map 2^63
either. -/

def high_mem : word → Option byte :=
  fun a => if (decide (2 ^ 63 ≤ bv_unsigned a) && decide (bv_unsigned a < 2 ^ 63 + 8))
           then some (Z_to_bv 8 0) else none

/-- The range is mapped end to end, exactly as the wrapping one was.
rocq-twin: high_range_reads
model: the bare walk on the high witness, kept so the refusal below is not vacuous -/
theorem high_range_reads :
    read_bytes_map high_mem (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 8) ≠ none := by decide

/-- And it does NOT wrap — so a no-wrap conjunct would have admitted it.
This is the mutation test for `access_okb` itself, in the same permanent
form as `wrap_would_pass_a_bare_walk` above.
rocq-twin: high_range_would_pass_a_no_wrap_test
model: the sum of the high witness stays under 2^64, so a no-wrap test says nothing about it -/
theorem high_range_would_pass_a_no_wrap_test :
    ¬ two_pow_64 ≤ bv_unsigned (Z_to_bv 64 (2 ^ 63)) + bv_unsigned (Z_to_bv 64 8) := by
  decide

/-- `__access_ok` refuses `[2^63, 2^63 + 8)` on `addr <= limit - size`
alone (include/asm-generic/access_ok.h, v6.18.46).
rocq-twin: high_range_is_refused
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem high_range_is_refused :
    access_okb (Z_to_bv 64 (2 ^ 63)) 8 = false := by decide

/-! ## The boundary itself, from both sides

`State.TASK_SIZE` is 2^47 — the Sv48 `TASK_SIZE_64` the harness asserts at
boot — and `__access_ok` admits a range whose exact end is AT the limit
and refuses one that ends one byte past it.  The edge is reached three
ways: through the count with `buf = 0`, through the base with `count = 0`,
and with the last eight bytes of the space.  (`access_okb`'s size conjunct
is implied by its address conjunct in `Int`; it is there to mirror the
kernel's unsigned subtraction, not as a separately pinnable half.)  The
probes in `testing/syscall-check/tests/zero_len_fault.c` make the same
three shapes of claim at the limit and one past it; under qemu-user the
kernel half of the at-the-limit cases is a `reject` that only the VM
harness checks against Linux.  The guard-level pins in the section after
the next cite those probes. -/

/-- The Sv48 top: `TASK_SIZE_64` is `PGDIR_SIZE * PTRS_PER_PGD / 2`
(arch/riscv/include/asm/pgtable.h, v6.18.46), which at four levels is
`PGDIR_SIZE` = 2^39 bytes (`PGDIR_SHIFT_L4` = 39,
arch/riscv/include/asm/pgtable-64.h, v6.18.46) times `PTRS_PER_PGD` = 512
entries, halved: 2^47, the `0x800000000000 (128TB) for RV64 using SV48
mmu` of pgtable.h's own comment above `TASK_SIZE_64`.  A derived macro
this tool cannot evaluate, so the reading is pinned through the Rocq twin.
rocq-twin: task_size_is_the_sv48_top -/
theorem task_size_is_the_sv48_top : TASK_SIZE = 2 ^ 47 := by decide

/-- A zero-length range AT the limit passes: `addr <= limit - 0`.
rocq-twin: access_ok_at_the_top
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_at_the_top :
    access_okb (Z_to_bv 64 (2 ^ 47)) 0 = true := by decide

/-- ... and one byte past it fails on the same comparison.
rocq-twin: access_ok_one_past_the_top
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_one_past_the_top :
    access_okb (Z_to_bv 64 (2 ^ 47 + 1)) 0 = false := by decide

/-- The last eight bytes of the space end exactly at the limit.
rocq-twin: access_ok_last_eight_bytes
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_last_eight_bytes :
    access_okb (Z_to_bv 64 (2 ^ 47 - 8)) 8 = true := by decide

/-- Shifted up by one, the same eight bytes end one past it.
rocq-twin: access_ok_last_eight_bytes_shifted_by_one
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_last_eight_bytes_shifted_by_one :
    access_okb (Z_to_bv 64 (2 ^ 47 - 7)) 8 = false := by decide

/-- The whole space from 0: `size <= limit` with equality, then
`0 <= limit - limit`.
rocq-twin: access_ok_whole_space
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_whole_space :
    access_okb (Z_to_bv 64 0) (2 ^ 47) = true := by decide

/-- ... and one byte more fails the size conjunct itself.
rocq-twin: access_ok_whole_space_plus_one
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_whole_space_plus_one :
    access_okb (Z_to_bv 64 0) (2 ^ 47 + 1) = false := by decide

/-! ## The constant this replaced, pinned as wrong

Before the v6.18.46 pin the model compared against `LONG_MAX` — riscv64's
`TASK_SIZE_MAX` from v6.10-rc1 (commit ad5643cf2f69, `#define TASK_SIZE_MAX
LONG_MAX` in arch/riscv/include/asm/pgtable.h) through v6.16-rc3; the
revert 890ba5be6335 is first released in v6.16-rc4, and `State.v`'s note
on `TASK_SIZE` lists its stable backports — and so ACCEPTED every range
ending under 2^63.  At the pinned kernel the limit is `TASK_SIZE`, and a
range at 2^60 is refused.  The two examples together are what separates
the constants: move `TASK_SIZE` back to `LONG_MAX` — in the spec and, once
`Checks/ExecutableSpecs.lean` lands, in the checker at once, so that every
biconditional proof stays green — and `task_size_refuses_the_band` fails.

STABLE KERNELS INSIDE THAT WINDOW ANSWER 0 where the `¬ … Ok 0` pins of
the zero-transfer section refuse it: a v6.12.y before .36 or a v6.15.y
before .5 passes `read(0, 2^60, 0)`.  CLAUDE.md admits every real
behaviour of a supported implementation and excludes a bug the
implementation would itself call one; the revert's own message says
addresses between `TASK_SIZE` and `LONG_MAX` are not valid user addresses
and that `access_ok` let them pass, and reverts "correctness first" —
which is why that 0 is refused rather than admitted beside -EFAULT. -/

def long_max_access_okb (base : word) (len : Int) : Bool :=
  decide (len ≤ 2 ^ 63 - 1) && decide (bv_unsigned base ≤ 2 ^ 63 - 1 - len)

/-- The retired limit admits the band.
rocq-twin: long_max_would_admit_the_band
model: the retired `LONG_MAX` limit of v6.10-rc1 through v6.16-rc3 (reverted in v6.16-rc4), kept only to separate the constants -/
theorem long_max_would_admit_the_band :
    long_max_access_okb (Z_to_bv 64 (2 ^ 60)) 8 = true := by decide

/-- The pinned limit refuses it.
rocq-twin: task_size_refuses_the_band
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem task_size_refuses_the_band :
    access_okb (Z_to_bv 64 (2 ^ 60)) 8 = false := by decide

/-! ## The bound, and the two gates written on it

`Sys.Uaccess.rw_bytes_max` is a modeling bound and not a kernel one; its
docstring carries the argument for the value.  What is pinned here is the
VALUE and the two gates at and past it.  The value pin is a tripwire
against an edit of that one line between runs of
`tools/check_rw_bytes_max_mirrors.py`, which holds the line, and every
harness copy of the bound, to the Rocq constant; the spec docstring says
what that tool does not compare. -/

/-- 2^17, on the nose: the value bugs/rw-bytes-max-ceiling.md measures and
every `RW_MAX` under testing/syscall-check/ repeats, all of them held to
the Rocq constant by `tools/check_rw_bytes_max_mirrors.py`.
model: the modeling bound's value, a rewrite for proofs holding a concrete count -/
theorem rw_bytes_max_is_2_17 : rw_bytes_max = 131072 := by decide

/-- The write-side bound sits far inside the `MAX_RW_COUNT` clamp `vfs_write`
applies after `rw_verify_area` (fs/read_write.c, v6.18.46): `INT_MAX &
PAGE_MASK` with `INT_MAX` = 0x7fffffff (include/vdso/limits.h, v6.18.46)
and `PAGE_MASK` at riscv's 4 KiB page (include/vdso/page.h over
`CONFIG_PAGE_SHIFT` = 12, which arch/riscv/Kconfig's `select
HAVE_PAGE_SIZE_4KB` fixes through arch/Kconfig's `PAGE_SHIFT`, v6.18.46)
is 0x7ffff000.
The constant is defined in include/linux/fs.h (`MAX_RW_COUNT`, v6.18.46)
and applied in `vfs_write`; the evidence line names the function, because
the macro's value is spelled through `INT_MAX` and `PAGE_MASK`, which
`check_lean_pin_evidence.py` declines to evaluate and would report.  This
is the numeral half of `rw_count_clamp_of_rw` (`Sys/Uaccess.lean`), which
is stated on the clamp; its proof discharges `rw_bytes_max ≤ MAX_RW_COUNT`
against the Lean constant, so the numeral is still checked by nobody
mechanical against the kernel macro — a pin at `INT_MAX` itself would pass
this evidence line identically — and is re-derived above and by the review.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem rw_bytes_max_inside_max_rw_count : rw_bytes_max ≤ 0x7ffff000 := by decide

/-- The count gate admits the bound itself: the hole guards are written in
this gate's shape, and `ftruncate_spec.c`'s `bound-at` records a grow of
exactly `rw_bytes_max` judged by the model and answered 0 by Linux.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-at -/
theorem modeled_rw_count_at_the_bound :
    modeled_rw_count (Z_to_bv 64 131072) = true := by decide

/-- ... and refuses one byte more.  A transfer of that count is still
judged, through the range disjunct of `modeled_rw_range`: the `over` case
of `pread_pwrite_spec.c` records `RW_MAX + 1` readable bytes really moving,
so the gate being off here is not a decline of the transfer.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- over -/
theorem modeled_rw_count_one_past_the_bound :
    modeled_rw_count (Z_to_bv 64 131073) = false := by decide

/-- Above the bound the range gate asks Linux's question and admits ANY
count at an in-range buffer — here 2^31, past even the kernel's own
`MAX_RW_COUNT` clamp: `__access_ok` admits the range, and the clamp is what
bounds the transfer, not an errno (include/asm-generic/access_ok.h,
`__access_ok`, v6.18.46).
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_admits_any_count_in_range :
    modeled_rw_range (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 31)) = true := by decide

/-- Above the bound, a range leaving the address space is what the gate
declines: `__access_ok` refuses `[2^47 - 4096, 2^47 - 4096 + 2^20)`, and
Linux answers -EFAULT where an arm asking this gate first says `unmodeled`
(the argument on `modeled_rw_range`).
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_declines_a_large_range_past_the_top :
    modeled_rw_range (Z_to_bv 64 (2 ^ 47 - 4096)) (Z_to_bv 64 (2 ^ 20)) = false := by decide

/-- Below the bound the gate is the old constant and asks nothing about
the range: the wrapping witness passes it although `wrap_range_is_refused`
holds.  That is the gap bugs/write-out-of-range-short-write.md owns — the
model has no -EFAULT arm for an out-of-range scalar write — pinned so a
change to the disjunction is seen, beside the kernel's own answer for the
range (`wrap_range_is_refused` above): `__access_ok` refuses it, and this
pin records that the model's first disjunct does not ask.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_keeps_the_old_gate_off_range :
    modeled_rw_range wrap_buf (Z_to_bv 64 8) = true := by decide

/-- One past the bound the count gate is off and only the range speaks: the
wrapping witness is refused, which is the tight edge of the decline.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_one_past_the_bound_off_range :
    modeled_rw_range wrap_buf (Z_to_bv 64 131073) = false := by decide

/-- ... and the same count at an in-range buffer is admitted by the range
disjunct alone — the first count the old gate refuses, carried by
`__access_ok`.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_one_past_the_bound_in_range :
    modeled_rw_range (Z_to_bv 64 0x10000) (Z_to_bv 64 131073) = true := by decide

/-- Above the bound the range gate is exact at the top: a 2^20-byte range
ending AT `TASK_SIZE` is admitted ...
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_admits_a_range_ending_at_the_top :
    modeled_rw_range (Z_to_bv 64 (2 ^ 47 - 2 ^ 20)) (Z_to_bv 64 (2 ^ 20)) = true := by decide

/-- ... and the same range one byte up is declined: `addr <= limit - size`
fails by one, so the gate's second disjunct is `__access_ok` to the byte.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_declines_a_range_one_past_the_top :
    modeled_rw_range (Z_to_bv 64 (2 ^ 47 - 2 ^ 20 + 1)) (Z_to_bv 64 (2 ^ 20)) = false := by decide

/-- A count of 2^64 - 1 — negative as `ssize_t`, above the bound as the
unsigned word the gate reads — is declined at any buffer: `size <= limit`
fails, and Linux answers -EFAULT where an arm asking this gate first says
`unmodeled` (the argument on `modeled_rw_range`).
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem modeled_rw_range_declines_a_negative_count :
    modeled_rw_range (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 64 - 1)) = false := by decide

/-- The count gate reads the word unsigned too: 2^64 - 1 is past the bound,
not -1 under it — the `negc` case's count, which Linux answers -EFAULT.
probe: testing/syscall-check/tests/read_window.c#conform -- negc -/
theorem modeled_rw_count_negative_count_is_past_the_bound :
    modeled_rw_count (Z_to_bv 64 (2 ^ 64 - 1)) = false := by decide

/-! ## The zero-transfer guard, on its outcomes

`access_ok_zero buf count k` is `k` when `__access_ok` admits the range
and -EFAULT when it does not, and it reads no memory at all.  The pins
below state that on the OUTCOMES the guard admits: `k`'s own, or exactly
the -EFAULT effect — and the refutation beside each is the lie the probe's
`--mutate` case tells, a fault where the kernel answered 0 and a 0 where it
answered -EFAULT.  Every one of them is a shape
`testing/syscall-check/tests/zero_len_fault.c` runs against the pinned
kernel under the VM harness, so the evidence is the probe's `CASE` line
rather than the header.

WHICH CASES ARE CITED.  The probe reaches the same `access_ok` through
`read`, `write` and `getrandom`, and in Rocq every ZERO-DELIVERY path asks
this guard — a read with a zero count or nothing left to deliver on a
channel, pipe or socket, a zero-count write, the null device's write, and
`sendto`/`recvfrom` (`ReadWrite.read_spec`, `ReadWrite.write_spec`,
`Socket.sendto_spec`, `Socket.recvfrom_spec`) — while the DELIVERING read
paths inline `access_okb` and `getrandom` spells the test out so that
-EINTR survives into its -EFAULT arm (`Random.getrandom_spec`).  The pins
cite the probe's zero-length `read` cases, which are that path; a replay of
them exercises this guard once `read` is ported the same way.

THE BUFFER IS A STAND-IN, THE END IS NOT.  The probe's `buf` is a static
array whose address the linker chooses (0x12000 in the recorded traces);
the pins name 0x10000 instead and keep the range's END exact, which is all
`__access_ok` compares once `size <= limit` holds.  The three pins
quantified over EVERY in-range base close that gap: they hold at the
recorded address, at NULL and at the limit alike, and cite the header
rather than a probe.

`file0-null` and `chan0-unmapped` have no `reject` case in the probe, so
the refutation at NULL is stated against the kernel's predicate directly
(`kernel:` evidence) rather than against a recorded lie; a
`testing: syscall-check:` follow-up adding `reject --mutate read:ret=-EFAULT`
to both modes, re-recorded under the pinned VM, would let that pin cite the
probe like its neighbours. -/

/-- `Z_to_bv` round-trips a value inside the word: `BitVec.toNat_ofInt`
reduces modulo 2^64, which changes nothing in `[0, 2^64)`.  What the
base-quantified pins below need to read a computed count back.
model: a fact about `Z_to_bv`, the word encoding, not about the kernel -/
theorem bv_unsigned_Z_to_bv_of_range (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt]
  omega

/-- In range, the guard is the arm's own answer, whatever it is.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0 -/
theorem access_ok_zero_in_range_is_the_arms_answer (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) k i m o ↔ k i m o := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 0)) = true := by decide
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- ... so a kernel reporting -EFAULT there, on an arm whose zero answer
is 0, is lying.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0 -/
theorem access_ok_zero_in_range_is_never_efault (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 0) (ret_only 0) i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  rw [access_ok_zero_in_range_is_the_arms_answer]
  simp only [ret_only, pure_iff, outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq,
    and_true]
  decide

/-- NULL is unmapped and in range: the guard is a range verdict, not a
copy, and answers the arm's 0 at address 0.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- file0-null -/
theorem access_ok_zero_null_is_in_range (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 0) (Z_to_bv 64 0) k i m o ↔ k i m o := by
  have h : access_okb (Z_to_bv 64 0) (bv_unsigned (Z_to_bv 64 0)) = true := by decide
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- ... so a kernel reporting -EFAULT at NULL with nothing to copy is lying:
`__access_ok` admits `[0, 0)` — `0 <= limit` and `0 <= limit - 0` — and the
range verdict is the whole of what `vfs_read` asks before it dispatches.
The probe records the 0 (`file0-null`) and has no `reject` case for it, so
the lie is refused against the predicate itself.
kernel: fs/read_write.c:vfs_read,vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_null_is_never_efault (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0) (Z_to_bv 64 0) (ret_only 0) i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  rw [access_ok_zero_null_is_in_range]
  simp only [ret_only, pure_iff, outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq,
    and_true]
  decide

/-- EVERY in-range base with a zero count is the arm's answer — NULL, the
probe's static array wherever the linker put it, an unmapped page, the
limit itself: `__access_ok` asks `0 <= limit` and `addr <= limit - 0`.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_zero_count_in_range_is_the_arms_answer (base : word)
    (hb : bv_unsigned base ≤ 2 ^ 47) (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero base (Z_to_bv 64 0) k i m o ↔ k i m o := by
  have h : access_okb base (bv_unsigned (Z_to_bv 64 0)) = true := by
    apply access_okb_intro
    have hz : bv_unsigned (Z_to_bv 64 0) = 0 := by decide
    rw [hz]
    unfold TASK_SIZE
    omega
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- EVERY in-range base with the count that runs exactly to the limit is the
arm's answer: `addr <= limit - (limit - addr)` with equality.  This is the
`count-top` shape at the probe's real address and at every other.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_count_to_the_top_for_every_base (base : word)
    (hb : bv_unsigned base ≤ 2 ^ 47) (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero base (Z_to_bv 64 (2 ^ 47 - bv_unsigned base)) k i m o ↔ k i m o := by
  have hz : bv_unsigned (Z_to_bv 64 (2 ^ 47 - bv_unsigned base)) = 2 ^ 47 - bv_unsigned base := by
    apply bv_unsigned_Z_to_bv_of_range <;> unfold bv_unsigned at * <;> omega
  have h : access_okb base (bv_unsigned (Z_to_bv 64 (2 ^ 47 - bv_unsigned base))) = true := by
    apply access_okb_intro
    rw [hz]
    unfold TASK_SIZE
    omega
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- ... and one byte more is -EFAULT from every in-range base, the
`count-past` shape wherever the buffer sits: `addr <= limit - size` fails by
exactly one.
kernel: fs/read_write.c:vfs_read,vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_count_past_the_top_for_every_base (base : word)
    (hb : bv_unsigned base ≤ 2 ^ 47) (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero base (Z_to_bv 64 (2 ^ 47 - bv_unsigned base + 1)) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have hz : bv_unsigned (Z_to_bv 64 (2 ^ 47 - bv_unsigned base + 1))
      = 2 ^ 47 - bv_unsigned base + 1 := by
    apply bv_unsigned_Z_to_bv_of_range <;> unfold bv_unsigned at * <;> omega
  have h : access_okb base (bv_unsigned (Z_to_bv 64 (2 ^ 47 - bv_unsigned base + 1))) = false := by
    cases hc : access_okb base (bv_unsigned (Z_to_bv 64 (2 ^ 47 - bv_unsigned base + 1)))
    · rfl
    · exfalso
      have hle := access_okb_le _ _ hc
      rw [hz] at hle
      unfold TASK_SIZE at hle
      omega
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- At the limit itself, `buf = 2^47` with `count = 0`: `__access_ok`
admits the limit (`addr <= limit - 0`), and the guard is the arm's answer.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-top -/
theorem access_ok_zero_at_the_top_is_the_arms_answer (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 (2 ^ 47)) (Z_to_bv 64 0) k i m o ↔ k i m o := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47)) (bv_unsigned (Z_to_bv 64 0)) = true := by decide
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- ... and a harness whose reservation ended below `TASK_SIZE` would
report -EFAULT there; the model refuses it.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- chan0-top -/
theorem access_ok_zero_at_the_top_is_never_efault (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 (2 ^ 47)) (Z_to_bv 64 0) (ret_only 0) i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  rw [access_ok_zero_at_the_top_is_the_arms_answer]
  simp only [ret_only, pure_iff, outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq,
    and_true]
  decide

/-- One byte past the limit, `buf = 2^47 + 1` with `count = 0`: the guard
admits exactly the -EFAULT effect and nothing else — not `k`'s answer, not
`Unmodeled`.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-past -/
theorem access_ok_zero_one_past_the_top_is_efault (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 47 + 1)) (bv_unsigned (Z_to_bv 64 0)) = false := by
    decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- ... so the 0 an arm would have answered without the guard is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan0-past -/
theorem access_ok_zero_one_past_the_top_is_never_zero (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 (2 ^ 47 + 1)) (Z_to_bv 64 0) k i m
        (Ok (mkEffect 0 [] []) m []) := by
  rw [access_ok_zero_one_past_the_top_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-- The edge reached through the COUNT: a buffer at 0x10000 with a count
running exactly to 2^47 ends at the limit and is the arm's answer ...
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- count-top -/
theorem access_ok_zero_count_to_the_top_is_the_arms_answer (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 47 - 0x10000)) k i m o ↔ k i m o := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 (2 ^ 47 - 0x10000))) = true := by
    decide
  unfold access_ok_zero
  simp only [h, ↓reduceIte]

/-- ... so the -EFAULT a harness whose reservation ended below `TASK_SIZE`
would report there is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=-EFAULT -- count-top -/
theorem access_ok_zero_count_to_the_top_is_never_efault (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 47 - 0x10000)) (ret_only 0) i m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  rw [access_ok_zero_count_to_the_top_is_the_arms_answer]
  simp only [ret_only, pure_iff, outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq,
    and_true]
  decide

/-- ... and the same count plus one is -EFAULT.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- count-past -/
theorem access_ok_zero_count_past_the_top_is_efault (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 47 - 0x10000 + 1)) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 (2 ^ 47 - 0x10000 + 1)))
      = false := by decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- ... so the 0 that count would have answered without the guard is
refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- count-past -/
theorem access_ok_zero_count_past_the_top_is_never_zero (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 47 - 0x10000 + 1)) k i m
        (Ok (mkEffect 0 [] []) m []) := by
  rw [access_ok_zero_count_past_the_top_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-- The band the retired `LONG_MAX` limit admitted, 2^60, on the guard:
-EFAULT at the pinned kernel.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-band -/
theorem access_ok_zero_in_the_band_is_efault (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 0) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 60)) (bv_unsigned (Z_to_bv 64 0)) = false := by decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- ... and the 0 an in-window kernel would answer there is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan0-band -/
theorem access_ok_zero_in_the_band_is_never_zero (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 0) k i m
        (Ok (mkEffect 0 [] []) m []) := by
  rw [access_ok_zero_in_the_band_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-- 2^63, the high witness, on the guard: -EFAULT with nothing mapped or
unmapped consulted.
probe: testing/syscall-check/tests/zero_len_fault.c#conform -- chan0-hi -/
theorem access_ok_zero_high_is_efault (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 0) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have h : access_okb (Z_to_bv 64 (2 ^ 63)) (bv_unsigned (Z_to_bv 64 0)) = false := by decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- ... and the 0 an arm would answer at 2^63 without the guard is refused.
probe: testing/syscall-check/tests/zero_len_fault.c#reject --mutate read:ret=0 -- chan0-hi -/
theorem access_ok_zero_high_is_never_zero (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 0) k i m
        (Ok (mkEffect 0 [] []) m []) := by
  rw [access_ok_zero_high_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-! ## A count negative as `ssize_t`

`count` is a 64-bit word and `access_ok_zero` reads it UNSIGNED, as
`__access_ok` reads `size`: a count of 2^64 - 1 fails `size <= limit`
before anything else is asked.  That is the order the `rw_bytes_max`
docstring argues — `vfs_read` asks `access_ok` before `rw_verify_area`'s
`(ssize_t) count < 0` test, so the -EINVAL there is unreachable on an MMU
kernel and -EFAULT is the answer — and the probe records it:
`testing/syscall-check/tests/read_window.c`'s `negc` case reads with
`count = -1` and asserts -EFAULT.  Read the count SIGNED and the guard
would let `[buf, buf - 1)` through as a range of length -1; these pins
refuse that reading. -/

/-- A count of 2^64 - 1 is -EFAULT at an in-range buffer: `size <= limit`
fails on the size alone, whatever the base.
probe: testing/syscall-check/tests/read_window.c#conform -- negc -/
theorem access_ok_zero_negative_count_is_efault (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 64 - 1)) k i m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  have h : access_okb (Z_to_bv 64 0x10000) (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 1))) = false := by
    decide
  unfold access_ok_zero
  simp only [h, Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff]

/-- ... so the 0 a signed reading of the count would answer is refused ...
probe: testing/syscall-check/tests/read_window.c#reject --mutate read#1:ret=0,drop-writes -- negc -/
theorem access_ok_zero_negative_count_is_never_zero (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 64 - 1)) k i m
        (Ok (mkEffect 0 [] []) m []) := by
  rw [access_ok_zero_negative_count_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-- ... and so is the -EINVAL of `rw_verify_area`'s sign test, which
`vfs_read` and `vfs_write` reach only after `access_ok` has passed
(fs/read_write.c, v6.18.46): order is behaviour, and the errno is the
range test's.
kernel: fs/read_write.c:vfs_read,vfs_write,rw_verify_area; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem access_ok_zero_negative_count_is_never_einval (k : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ access_ok_zero (Z_to_bv 64 0x10000) (Z_to_bv 64 (2 ^ 64 - 1)) k i m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  rw [access_ok_zero_negative_count_is_efault]
  simp only [outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, and_true]
  decide

/-! ## The zero-byte effect shape

`delivered_writes` is the one place the effect write list for a delivery
is built, so that a read delivering nothing has the same effect on every
fd kind.  Model facts: what the kernel does with zero bytes is pinned on
the guard above, and this is the shape the model records it in. -/

/-- No byte moved, no entry ...
model: `delivered_writes` on the empty delivery -/
theorem delivered_writes_nothing_is_no_entry (buf : word) :
    delivered_writes buf [] = [] := by rfl

/-- ... and in particular not a vacuous `(buf, [])` one.
model: `delivered_writes` on the empty delivery, refusing the vacuous entry -/
theorem delivered_writes_nothing_is_not_a_vacuous_entry (buf : word) :
    delivered_writes buf [] ≠ [(buf, [])] := by
  intro h
  cases h

/-- Bytes moved, one entry at the buffer with exactly those bytes.
model: `delivered_writes` on a two-byte delivery -/
theorem delivered_writes_bytes_is_one_entry (buf : word) (x y : byte) :
    delivered_writes buf [x, y] = [(buf, [x, y])] := by rfl

/-- One byte moved, one entry with that byte: the singleton is not the
empty case.
model: `delivered_writes` on a one-byte delivery -/
theorem delivered_writes_one_byte_is_one_entry (buf : word) (x : byte) :
    delivered_writes buf [x] = [(buf, [x])] := by rfl

/-! ## The write source: the readable prefix of the clamped count

`Sys.Uaccess.write_source` is what every scalar write arm reads out of
the user buffer: `State.readable_bytes` at the `State.rw_count_clamp`ed
count.  Two decisions are pinned here, each beside its refusal: the
bytes are the readable PREFIX — the walk stops at the first unreadable
byte and invents nothing past it — and the count walked is the CLAMPED
one, at the kernel's value and not a page to either side of it.

Three memories.  `source_mem` has bytes at 4096 and 4097, a hole at 4098,
and a third byte at 4099 the walk must never reach: Prelude's `mem_ab`
with the byte past the hole added, restated because this file imports
`Sys.Uaccess` alone.  A one-byte hole inside a page is not a shape Linux
can present — protection is per page — but it is the shape the harness's
`--mutate mem-hide` presents to the model (`write_spec.c`'s `w-hole`), so
those pins are about the walk's RULE.  `page_source_mem` is the shape
Linux can present: two bytes below a page boundary and nothing on the page
after it.  And the constant map `fun _ => some b`, every byte readable,
is where the COUNT is the only limit: it is the memory on which the clamp
decision can be told from its absence at all, since a hole stops the walk
before any clamp is reached; `readable_bytes_aux_const` is the rewrite
that lets those pins state a count in the billions without walking it. -/

def source_mem : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else if bv_eqb a 4097 then some 98
           else if bv_eqb a 4099 then some 99 else none

/-- Five asked, two readable: the prefix, and only the prefix — what
`generic_perform_write` lands before the byte that will not fault in.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_source_is_the_readable_prefix :
    write_source source_mem 4096 5 = [97, 98] := by decide

/-- ... not the count zero-filled, and not the byte past the hole: the
copy stops at the first unreadable byte and reads nothing beyond it.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_source_invents_nothing_past_the_hole :
    write_source source_mem 4096 5 ≠ [97, 98, 0, 0, 0]
    ∧ write_source source_mem 4096 5 ≠ [97, 98, 99] := by decide

/-- Not one byte readable at the start: the empty prefix.  On it every
arm that answers at all answers -EFAULT — `generic_perform_write`'s
`status = -EFAULT` with nothing written for a file, and the channel arm
alike — and the pipe arm declines, as it declines every source it cannot
read whole.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_source_empty_where_the_first_byte_is_unreadable :
    write_source source_mem 4098 2 = [] := by decide

/-- A count under the clamp is walked as named: two bytes readable, one
asked, one read.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_stops_at_the_count :
    write_source source_mem 4096 1 = [97] := by decide

/-- The count is CLAMPED before the walk: `vfs_write` caps it at
`MAX_RW_COUNT` after `rw_verify_area` and ahead of the write operation
(fs/read_write.c, v6.18.46), so at 2^40 the prefix is bounded by the clamp
for every memory and every buffer.  An upper bound only — a walk clamped
tighter satisfies it too; `write_source_stops_at_max_rw_count` below is
the pin that fixes the value.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_is_bounded_by_the_clamp (mp : word → Option byte) (buf : word) :
    ((write_source mp buf (Z_to_bv 64 (2 ^ 40))).length : Int) ≤ 0x7ffff000 := by
  have h := write_source_length_le mp buf (Z_to_bv 64 (2 ^ 40))
  have hc : rw_count_clamp (Z_to_bv 64 (2 ^ 40)) = 0x7ffff000 := by decide
  rw [hc] at h
  exact h

/-- ... and over the clamp the walk is the same readable prefix: the
clamp caps the count, it does not fault the range or empty the source.
The hole at 4098 stops this walk long before any clamp is reached, so this
pin says nothing about the clamp's value; the constant-map pins below do.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_over_the_clamp_is_still_the_prefix :
    write_source source_mem 4096 (Z_to_bv 64 (2 ^ 40)) = [97, 98] := by decide

/-- The shape Linux can present: two readable bytes below a page boundary,
nothing on the page at 4096, and a byte at 8192 the walk must never
reach. -/
def page_source_mem : word → Option byte :=
  fun a => if bv_eqb a 4094 then some 97 else if bv_eqb a 4095 then some 98
           else if bv_eqb a 8192 then some 99 else none

/-- A source that straddles into an unmapped page reads up to the page
edge and no further: the prefix `generic_perform_write` lands before
`fault_in_iov_iter_readable` fails on the page at 4096, and the loop
answers -EFAULT for nothing more.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_source_stops_at_the_page_edge :
    write_source page_source_mem 4094 5000 = [97, 98] := by decide

/-- ... neither empty nor reaching the byte beyond the hole.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_source_at_the_page_edge_is_not_empty_and_not_beyond :
    write_source page_source_mem 4094 5000 ≠ []
    ∧ write_source page_source_mem 4094 5000 ≠ [97, 98, 99] := by decide

/-- On a memory with every byte readable the walk is the count itself:
`readable_bytes_aux` over `k` bytes of a constant map is `k` copies of the
byte.  The rewrite the constant-map pins below go through, so that a
count in the billions is stated, never walked.
model: a closed fact about the walk on a constant map; the rewrite behind the clamp pins -/
theorem readable_bytes_aux_const (b : byte) (k : Nat) (a : word) :
    readable_bytes_aux (fun _ => some b) a k = List.replicate k b := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [readable_bytes_aux, List.replicate, ih]

/-- Five asked, everything readable, five read: the count binds above one
byte.  This is the pin that tells the walk at the named count from a walk
capped at a smaller bound — the retired `rw_bytes_max` ceiling on the
count was such a cap, and `pread_pwrite_spec.c`'s `over` case records
`RW_MAX + 1` bytes really moving.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_walks_the_named_count_when_all_is_readable (buf : word) :
    write_source (fun _ => some 7) buf 5 = [7, 7, 7, 7, 7] := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const]
  decide

/-- ... and not two or three of them.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_is_not_capped_below_the_count (buf : word) :
    write_source (fun _ => some 7) buf 5 ≠ [7, 7]
    ∧ write_source (fun _ => some 7) buf 5 ≠ [7, 7, 7] := by
  rw [write_source_walks_the_named_count_when_all_is_readable]; decide

/-- The retired ceiling, one past: 131073 asked of a wholly readable memory
is 131073 read.  `rw_bytes_max` no longer bounds the count (issue #460),
and the `over` case records that many bytes moving.
probe: testing/syscall-check/tests/pread_pwrite_spec.c#conform -- over -/
theorem write_source_walks_one_past_rw_bytes_max (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 131073)).length = 131073 := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const, List.length_replicate]
  decide

/-- Everything readable and 2^40 asked: the walk stops at `MAX_RW_COUNT`,
0x7ffff000 bytes, the value `vfs_write` clamps `count` to after
`rw_verify_area` (fs/read_write.c, v6.18.46).  The clamp told from its
absence: an unclamped walk of the same memory has length 2^40.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_stops_at_max_rw_count (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 (2 ^ 40))).length = 0x7ffff000 := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const, List.length_replicate]
  decide

/-- ... not the count named, and not `INT_MAX`: the clamp is `INT_MAX &
PAGE_MASK` (include/linux/fs.h, `MAX_RW_COUNT`, v6.18.46), a page below
`INT_MAX`, so "the clamp is a no-op under 2^31" is false by one page.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_at_2_40_is_neither_the_count_nor_int_max (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 (2 ^ 40))).length ≠ 2 ^ 40
    ∧ (write_source (fun _ => some 0) buf (Z_to_bv 64 (2 ^ 40))).length ≠ 0x7fffffff := by
  rw [write_source_stops_at_max_rw_count]; decide

/-- The edge from below: one byte short of `MAX_RW_COUNT` is walked as
named.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_one_short_of_max_rw_count_is_walked_as_named (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 0x7fffefff)).length = 0x7fffefff := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const, List.length_replicate]
  decide

/-- At the edge: `MAX_RW_COUNT` itself is walked in full — the test is
`count > MAX_RW_COUNT`, not `>=` (fs/read_write.c, `vfs_write`, v6.18.46).
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_walks_max_rw_count_in_full (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 0x7ffff000)).length = 0x7ffff000 := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const, List.length_replicate]
  decide

/-- And one past it is cut back to it, which is where a clamp at `INT_MAX`
would first differ.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_one_past_max_rw_count_is_cut (buf : word) :
    (write_source (fun _ => some 0) buf (Z_to_bv 64 0x7ffff001)).length = 0x7ffff000 := by
  unfold write_source
  rw [readable_bytes_eq, readable_bytes_aux_const, List.length_replicate]
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Uaccess
