import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Kernel.Sched.Syscalls — what `sched_getaffinity`, `sched_setscheduler` and `sched_yield` answer, read off against Linux

Worked examples over `Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec`,
`Sys.Kernel.Sched.Syscalls.sched_setscheduler_spec` and
`Sys.Kernel.Sched.Syscalls.sched_yield_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sched/Syscalls.v`.  Not part
of the trusted specification: this file is QA on the definitions, written
to be READ, and every claim in it is a claim about what the kernel does,
with the citation beside it.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  Every concrete call goes through the dispatcher —
`syscall_spec` on a `SyscallInput` numbered 119, 123 or 124 — so that the
table's argument wiring is under test with the arm, as Rocq's
`check_syscall (mkInput …)` cases have it; the pins that quantify over an
argument, an input or a model are stated on the spec itself, which is
where "any memory" and "any model" can be said.  A decision is pinned twice: an
`iff` over EVERY outcome `o`, which fixes the admitted answer and refuses
every other one, `Unmodeled` included; and a refutation of the concrete
answer a wrong model or a lying kernel would give.  Both close by
`sys_norm` / `sys_refute` (`Checks/Cases/Tactic.lean`).

The declines separate missing state from implementation differences.
The model lacks CPU counts, scheduling credentials, other tasks, and some configuration choices.
Partial user-memory copies also leave the copy-in ledger uncertain.
The spec docstrings explain these limits and cite their implementation sources.
The negative-argument band adds a temporary limit until PR #1929 changes Rocq and Lean follows it.
Linux and QEMU disagree on the effect in that band.
The pins therefore require `Unmodeled` instead of one implementation's effect.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

/- The `kernel:` tag grammar requires bare symbols.
Its resolver includes the syscall definition under `sched_setscheduler`.
The adjacent prose identifies that entry point with `SYSCALL_DEFINE3(sched_setscheduler)` and its line numbers. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sched.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register lines the specs owe `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation in the set, and `record_copyins` — the copy-in wrapper of
`Sys/Syscall.lean`, which `Checks/Cases/Sys/Syscall.lean` pins but no Cases
file of a spec had yet to unfold — for its own; they are registered here,
beside the pins that read them, because a port PR creates its own files and
edits no shared one (docs/merge-commutativity.md).  The wrapper's line
belongs in `Tactic.lean`'s Sys/Syscall group beside `ret_only.eq_1`, a
one-line move for the R1 fold; until then a second copy-in port registers
the same equation from its own Cases file, which Lean accepts. -/

attribute [sys_simp low] sched_getaffinity_spec.eq_1 sched_setscheduler_spec.eq_1 record_copyins.eq_1

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- `SCHED_NORMAL` is 0.
kernel: include/uapi/linux/sched.h:SCHED_NORMAL@v6.18.46 -/
example : SCHED_NORMAL = 0 := by decide
/-- `SCHED_FIFO` is 1.
kernel: include/uapi/linux/sched.h:SCHED_FIFO@v6.18.46 -/
example : SCHED_FIFO = 1 := by decide
/-- `SCHED_RR` is 2.
kernel: include/uapi/linux/sched.h:SCHED_RR@v6.18.46 -/
example : SCHED_RR = 2 := by decide
/-- `SCHED_BATCH` is 3.
kernel: include/uapi/linux/sched.h:SCHED_BATCH@v6.18.46 -/
example : SCHED_BATCH = 3 := by decide
/-- `SCHED_IDLE` is 5; 4 is the header's reserved SCHED_ISO.
kernel: include/uapi/linux/sched.h:SCHED_IDLE@v6.18.46 -/
example : SCHED_IDLE = 5 := by decide
/-- `SCHED_DEADLINE` is 6.
kernel: include/uapi/linux/sched.h:SCHED_DEADLINE@v6.18.46 -/
example : SCHED_DEADLINE = 6 := by decide
/-- `SCHED_EXT` is 7.
kernel: include/uapi/linux/sched.h:SCHED_EXT@v6.18.46 -/
example : SCHED_EXT = 7 := by decide
/-- `SCHED_RESET_ON_FORK` is bit 30.
kernel: include/uapi/linux/sched.h:SCHED_RESET_ON_FORK@v6.18.46 -/
example : SCHED_RESET_ON_FORK = 1073741824 := by decide
/-- `MAX_RT_PRIO` is 100, so 99 is the last priority the range gate admits.
kernel: include/linux/sched/prio.h:MAX_RT_PRIO@v6.18.46 -/
example : MAX_RT_PRIO = 100 := by decide
/-- `EINVAL` is 22.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
example : EINVAL = 22 := by decide
/-- `EFAULT` is 14.
kernel: include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
example : EFAULT = 14 := by decide
/-- `ESRCH` is 3.
kernel: include/uapi/asm-generic/errno-base.h:ESRCH@v6.18.46 -/
example : ESRCH = 3 := by decide
/-- `EPERM` is 1.
kernel: include/uapi/asm-generic/errno-base.h:EPERM@v6.18.46 -/
example : EPERM = 1 := by decide

/-! ## sched_getaffinity (123)

`SYSCALL_DEFINE3(sched_getaffinity, pid_t, pid, unsigned int, len,
unsigned long __user *, user_mask_ptr)` (kernel/sched/syscalls.c:1329-1355,
Linux v6.18.46) computes `(len * BITS_PER_BYTE) < nr_cpu_ids` on an
`unsigned int len` (:1335-1336), then `len & (sizeof(unsigned long)-1)`
(:1337-1338), and touches neither the pid nor the pointer before either
gate: `find_process_by_pid` runs inside the helper at :1306 and the
pointer's only use is the `copy_to_user` at :1347.  Every example below
is here because a `CheckReject`-shaped claim needs a kernel answering
something no kernel answers, and a decline on a length Linux ANSWERS is a
claim about the model alone.  `testing/syscall-check/tests/sched_getaffinity_len.c`'s
`einval` run asserts 0, 2^29, 2^31 and 7 * 2^29 alongside the unaligned
lengths on a live kernel; the rest of the wrapping set and the
compat-aligned lengths are walked here rather than one probe call each. -/

/-- `sched_getaffinity(pid, len, user_mask_ptr)` as the dispatcher sees it:
syscall 123, the three arguments in a0..a2, nothing readable or writable. -/
def sched_getaffinity_in (pid len user_mask_ptr : word) : SyscallInput :=
  SyscallInput.mkInput 123 [pid, len, user_mask_ptr, 0, 0, 0] (fun _ => none) (fun _ => none)

attribute [sys_simp low] sched_getaffinity_in.eq_1

/-- THE WRAPPING LENGTHS.  `len` is an `unsigned int` and `BITS_PER_BYTE`
is the plain `8` (include/linux/bits.h:12), so `len * BITS_PER_BYTE` is
computed in 32 bits.  The product is zero exactly on the multiples of
2^29, and `nr_cpu_ids` is at least 1, so every one of them is -EINVAL at
:1335-1336 — the large ones included, which read as obviously-big-enough
to a model that did the multiplication over the integers.  The pid and
the mask pointer are garbage throughout: both gates run before either is
looked at.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46
rocq-twin: sched_getaffinity_wrapping_lengths_are_einval -/
theorem sched_getaffinity_wrapping_lengths_are_einval (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 0 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 1073741824 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 1610612736 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 2147483648 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 2684354560 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 3221225472 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 3758096384 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- THE LENGTHS CONGRUENT TO 4 MOD 8 are what tell the native gate's `& 7`
(`sizeof(unsigned long)-1`, kernel/sched/syscalls.c:1337) from the compat
gate's `& 3` (`sizeof(compat_ulong_t)-1`, kernel/compat.c:144-153), and
they are the sharpest available mistake: a spec written from
`COMPAT_SYSCALL_DEFINE3(sched_getaffinity)` instead of the native
definition would decline these and still answer -EINVAL for every other
length in this file.  They are -EINVAL for an LP64 caller, which is the
only kind this model loads.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46
rocq-twin: sched_getaffinity_compat_aligned_lengths_are_einval -/
theorem sched_getaffinity_compat_aligned_lengths_are_einval (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 4 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 12 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 4294967292 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- …and every other unaligned length is refused by the same `& 7`: 1, 7,
9 and the all-ones `unsigned int`.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_unaligned_lengths_are_einval (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 1 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 7 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 9 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 4294967295 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and the boundary is exactly where the wrap puts it.  The two
neighbours of 2^29 are eight-aligned like it, differ from it by one
machine word, and are NOT refused by the size gate: 2^29 - 8 has 2^32 - 64
bits, above every `NR_CPUS` (arch/riscv/Kconfig, `config NR_CPUS`, every
`range` ends at 512 or below), and 2^29 + 8 has 64 bits, below
`nr_cpu_ids` only on a machine with more than 64 CPUs.  Past both gates
the answer is the success path's `min(len, cpumask_size())` byte count and
mask bytes (:1345-1350), or the -EFAULT of its `copy_to_user` at :1347 on
the garbage pointer here; the model carries neither `cpumask_size()` nor
the task's mask and declines every length both gates let through.  2^29 itself,
between them, is still answered: pinning it here is what makes this lemma
fail when the boundary moves rather than merely say where it is.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46
rocq-twin: sched_getaffinity_wrap_neighbours_are_unmodeled -/
theorem sched_getaffinity_wrap_neighbours_are_unmodeled (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 536870904 3735928559) demo_model o ↔ o = Unmodeled)
    ∧ (syscall_spec (sched_getaffinity_in 0 536870920 3735928559) demo_model o ↔ o = Unmodeled)
    ∧ (syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- THE NEGATIVE DIRECTION, on the wrapping length the probe's `einval` run
issues and whose byte-count lie its `reject --mutate sched_getaffinity#11:ret=8`
refuses on the live kernel; the other lies are refused here: a kernel that
answered a wrapping length with a plausible byte count, with the -EFAULT
its untouched pointer cannot produce (the `copy_to_user` is at :1347,
behind both gates), or with the -ESRCH its unreached task lookup cannot
produce (:1305-1308, inside the helper called at :1343), is refused.  So is
one that answered -EINVAL and wrote to the mask anyway: nothing is stored
before either gate.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46
rocq-twin: sched_getaffinity_wrapping_length_lies_rejected -/
theorem sched_getaffinity_wrapping_length_lies_rejected :
    ¬ syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model
        (Ok (mkEffect 8 [] []) demo_model [])
    ∧ ¬ syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [])
    ∧ ¬ syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model
        (Ok (mkEffect (errno_ret ESRCH) [] []) demo_model [])
    ∧ ¬ syscall_spec (sched_getaffinity_in 0 536870912 3735928559) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [(3735928559, [Z_to_bv 8 0])] []) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- THE MODELED-OUT BAND.  8, 16 and 128 pass both gates on any machine
with at most 64, 128 and 1024 CPUs and are then answered with
`min(len, cpumask_size())` (kernel/sched/syscalls.c:1345-1350, Linux
v6.18.46) — a byte
count that depends on `NR_CPUS` and `nr_cpu_ids` — while a larger machine
refuses the same length at :1335-1336.  No single answer holds across the
supported machines, so the model declines rather than pick one; 8 is the
smallest length that can succeed and the one the probe's `modeled-out`
case issues, and 128 is the `sizeof(cpu_set_t)` a `CPU_COUNT` query
through musl's `sched_getaffinity` passes unchanged (its `cpu_set_t` is
`unsigned long __bits[128/sizeof(long)]`).
probe: testing/syscall-check/tests/sched_getaffinity_len.c#fail-closed --expect-unmodeled sched_getaffinity -- modeled-out -/
theorem sched_getaffinity_modeled_lengths_decline (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 8 4096) demo_model o ↔ o = Unmodeled)
    ∧ (syscall_spec (sched_getaffinity_in 0 16 4096) demo_model o ↔ o = Unmodeled)
    ∧ (syscall_spec (sched_getaffinity_in 0 128 4096) demo_model o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- …and neither the byte count a 64-CPU machine returns for 8 nor the
-EINVAL a 65-CPU machine returns is admitted on its own: the decline is
the whole answer.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_modeled_length_answers_rejected :
    ¬ syscall_spec (sched_getaffinity_in 0 8 4096) demo_model
        (Ok (mkEffect 8 [(4096, [1, 0, 0, 0, 0, 0, 0, 0])] []) demo_model [])
    ∧ ¬ syscall_spec (sched_getaffinity_in 0 8 4096) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- `len` IS AN `unsigned int`: `__SC_CAST` (include/linux/syscalls.h:132)
narrows the a1 register to 32 bits before `SYSCALL_DEFINE3(sched_getaffinity)`
sees it, so 2^32 + 4 is the unaligned 4 and refused, and 2^32 + 8 is the 8
that leaves the modeled surface.  The predicate cannot observe the
narrowing (both tests are unchanged by adding a multiple of 2^32, as the
Rocq definition `Syscalls.affinity_len_einval_b` says); what this pins is
that no arm compares the length against a BOUND, which the narrowing would
change.
kernel: kernel/sched/syscalls.c:sched_getaffinity; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sched_getaffinity_len_is_unsigned_int (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 0 (Z_to_bv 64 (2 ^ 32 + 4)) 4096) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 (Z_to_bv 64 (2 ^ 32 + 8)) 4096) demo_model o ↔
      o = Unmodeled) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- THE PID AND THE POINTER ARE DEAD before either gate, so the spec takes
neither: for every input and every model, a length of 4 is -EINVAL and
the model is untouched.  Stated on the spec itself because the dispatcher's
`in_arg` does not reduce over a symbolic argument list; the wiring is
pinned on `sysno_123_reads_the_length_from_a1`.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_ignores_pid_and_pointer (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    sched_getaffinity_spec 4 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- EVERY length the predicate refuses is -EINVAL, whatever the pid, the
pointer or the model: the gate is the whole of the modeled surface.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_refused_length_is_einval (len : word) (h : affinity_len_einval_b len = true)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    sched_getaffinity_spec len i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exact absurd h hc

/-- …and every length it admits declines, on the spec itself.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_admitted_length_declines (len : word) (h : affinity_len_einval_b len = false)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    sched_getaffinity_spec len i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · rename_i hc
    exact absurd (h.symm.trans hc) Bool.false_ne_true
  · sys_norm

/-- THE TABLE READS a1.  The same three registers with the length moved to
a0 and a2 name a pid and a pointer of 8 and a length of 0, which is
refused; with the 8 in a1 the call declines.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sysno_123_reads_the_length_from_a1 (o : outcome SyscallEffect) :
    (syscall_spec (sched_getaffinity_in 8 0 8) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_getaffinity_in 0 8 0) demo_model o ↔ o = Unmodeled) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-! ## sched_setscheduler (119)

These are here because the kernel answers -EINVAL by four different routes
and by the same number, so `testing/syscall-check/tests/sched_setscheduler_policy.c`
cannot say WHICH route a model took; the discriminations that need saying
are made here, against the spec, and the refutations are of answers only
a lying kernel produces. -/

/-- `sched_setscheduler(pid, policy, param)` as the dispatcher sees it:
syscall 119, the three arguments in a0..a2, `mem` readable, nothing
writable. -/
def sched_setscheduler_in (pid policy param : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 119 [pid, policy, param, 0, 0, 0] mem (fun _ => none)

attribute [sys_simp low] sched_setscheduler_in.eq_1

/-- Where the `struct sched_param` lives in every readable fixture below. -/
def sched_param_ptr : word := Z_to_bv 64 4096

/-- Four readable bytes at 4096 holding a little-endian `int`, which is the
whole of a `struct sched_param` (include/linux/sched.h:410-412, Linux
v6.18.46).  Nothing
else in the address space is readable, which is what makes the -EFAULT and
decline cases below reachable at all. -/
def sched_param_mem (v : Int) : word → Option byte :=
  bytes_at sched_param_ptr (Z_to_le_bytes 4 v)

/-- Three readable bytes at 4096 and nothing at 4099: a `struct sched_param`
whose last byte no memory backs, for the read-width pins. -/
def sched_param_mem_3 : word → Option byte :=
  bytes_at sched_param_ptr (Z_to_le_bytes 3 0)

/-- The demo process with its tid pinned at 4096, for the pid pins. -/
def sched_tid_model : Model := with_tid (Z_to_bv 64 4096) demo_model

attribute [sys_simp low] sched_tid_model.eq_1

/-! ### The rewrites that read the fixtures

`sys_norm` decides closed gates in its first pass and evaluates closed
terms in its second, and two shapes here defeat the second: a
`read_bytes_map` over a map built from `bytes_at` and `Z_to_le_bytes`
unfolds past Lean's recursion limit, and the dispatcher's `in_arg` over the
literal register list is evaluated only by that pass, after the match on
the read is already stuck.  Both are supplied as rewrites in the form the
FIRST pass produces, the way `Checks/Cases/Fs/Sync.lean`'s "The fixtures'
readings" supply its closed `fd_lookup`s: the wiring lemmas turn `in_arg (mkInput …) k` into
the k-th register, and the read lemmas turn each fixture read into its
bytes, so the match reduces before any evaluation is attempted.  Every
read lemma is closed by `decide`, the kernel's own evaluation of the map. -/

/-- The dispatcher's wiring on a literal six-register input: a0.
model: the table's `in_arg` on a literal register list, a rewrite for `sys_norm`. -/
theorem in_arg_0 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- …a1.
model: the table's `in_arg` on a literal register list, a rewrite for `sys_norm`. -/
theorem in_arg_1 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- …a2.
model: the table's `in_arg` on a literal register list, a rewrite for `sys_norm`. -/
theorem in_arg_2 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 2 = a2 := rfl

/-- The four bytes of a `sched_param` holding 0.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_0 :
    read_bytes_map (sched_param_mem 0) sched_param_ptr (Z_to_bv 64 4) = some [0, 0, 0, 0] := by decide
/-- …holding 1.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_1 :
    read_bytes_map (sched_param_mem 1) sched_param_ptr (Z_to_bv 64 4) = some [1, 0, 0, 0] := by decide
/-- …holding 99.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_99 :
    read_bytes_map (sched_param_mem 99) sched_param_ptr (Z_to_bv 64 4) = some [99, 0, 0, 0] := by decide
/-- …holding 100.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_100 :
    read_bytes_map (sched_param_mem 100) sched_param_ptr (Z_to_bv 64 4) = some [100, 0, 0, 0] := by decide
/-- …holding the `int` -1, whose four bytes are all ones.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_minus_1 :
    read_bytes_map (sched_param_mem 4294967295) sched_param_ptr (Z_to_bv 64 4)
      = some [255, 255, 255, 255] := by decide
/-- …holding 256, whose low byte is 0.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_256 :
    read_bytes_map (sched_param_mem 256) sched_param_ptr (Z_to_bv 64 4) = some [0, 1, 0, 0] := by decide
/-- …holding 65536, whose low half is 0.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_65536 :
    read_bytes_map (sched_param_mem 65536) sched_param_ptr (Z_to_bv 64 4) = some [0, 0, 1, 0] := by decide

/-- The same `struct sched_param` holding 0, laid out from 4097: an odd
address, for the pin that says the copy has no alignment requirement. -/
def sched_param_odd_ptr : word := Z_to_bv 64 4097

def sched_param_odd_mem : word → Option byte :=
  bytes_at sched_param_odd_ptr (Z_to_le_bytes 4 0)

/-- The four bytes at the odd address.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_odd :
    read_bytes_map sched_param_odd_mem sched_param_odd_ptr (Z_to_bv 64 4) = some [0, 0, 0, 0] := by decide
/-- …and the three-byte map, whose four-byte read finds no fourth byte.
model: a closed read of the fixture bytes, a rewrite for `sys_norm`. -/
theorem read_sched_param_3_bytes :
    read_bytes_map sched_param_mem_3 sched_param_ptr (Z_to_bv 64 4) = none := by decide

attribute [sys_simp]
  in_arg_0 in_arg_1 in_arg_2
  read_sched_param_0 read_sched_param_1 read_sched_param_99 read_sched_param_100
  read_sched_param_minus_1 read_sched_param_256 read_sched_param_65536 read_sched_param_odd
  read_sched_param_3_bytes

/-- THE PRIORITY IS A `__u32` AT THE RANGE GATE.  `struct sched_param`
holds an `int` (include/linux/sched.h:411), and `_sched_setscheduler`
copies it into `struct sched_attr`'s `__u32 sched_priority`
(kernel/sched/syscalls.c:771; include/uapi/linux/sched/types.h:108), so -1
meets `attr->sched_priority > MAX_RT_PRIO-1` (:567-568) as 4294967295 and
is refused THERE — by the same gate that refuses 100, and before the
`rt_policy(policy) != (sched_priority != 0)` comparison (:570) ever runs.
Both answers are -EINVAL, so no probe can separate them; what CAN be
separated is 99, which the range gate admits, from -1, which it does not.
A model that read the field signed would put -1 on the far side of the
range gate, where `rt_policy(SCHED_FIFO)` and `sched_priority != 0` agree
and nothing below refuses it, so SCHED_FIFO at -1 would come out as the
decline a genuine RT request gets — which is the case that fails here.
SCHED_IDLE at -1 cannot make that discrimination: a signed read reaches the
same -EINVAL through the agreement test at :570, which is why this pin is
written on policy 1.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler@v6.18.46
rocq-twin: sched_setscheduler_negative_priority_is_out_of_range -/
theorem sched_setscheduler_negative_priority_is_out_of_range (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 4294967295)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    -- ...and 99 is admitted by that gate, so SCHED_FIFO at 99 is not an -EINVAL at all: it is
    -- the RT request the model declines
    ∧ (syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 99)) demo_model o ↔
      o = Unmodeled)
    -- ...while 100 is refused, one past MAX_RT_PRIO-1
    ∧ (syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 100)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
Both implementations return -EINVAL without copying when `param` is NULL, even with negative policy and pid.
The `int policy` argument reads 2^32 + 5 as SCHED_IDLE in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:962, Linux v6.18.46).
Linux returns zero for this caller request with priority zero through `__sched_setscheduler` (kernel/sched/syscalls.c:555-571, :757, Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_policy_wins (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0
        (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63))
        (fun _ => none)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 32 + 5)) sched_param_ptr
        (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_policy_is_unmodeled (pid policy param : word)
    (hn : w_is0 param = false) (h : sint32 policy < 0) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    sched_setscheduler_spec pid policy param i m o ↔
      o = Unmodeled := by
  simp only [sched_setscheduler_spec, hn, Bool.false_eq_true, ↓reduceIte, h, decide_true, Bool.true_or, unmodeled]

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
The `pid_t` argument reads 2^32 as pid zero in `do_sched_setscheduler` (kernel/sched/syscalls.c:880-881, Linux v6.18.46).
`find_process_by_pid` maps that zero to `current` (kernel/sched/syscalls.c:253-256, Linux v6.18.46).
The caller therefore reaches the SCHED_IDLE success at priority zero through `__sched_setscheduler` (kernel/sched/syscalls.c:555-571, :757, Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_is_an_int (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 31)) 5 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32)) 5 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- The temporary decline prevents a certain effect for this non-NULL negative argument.
Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_int_min_pid_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 31)) 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret ESRCH) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 31)) 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- `int policy` IS 32 BITS TOO.  `SYSCALL_DEFINE3(sched_setscheduler)`
(kernel/sched/syscalls.c:962-965) reads the low half of a1, so a register
with its sign bit set and 5 in its low half is SCHED_IDLE, not a negative
policy: the 2^32 + 5 case of `sched_setscheduler_negative_policy_wins` with
the highest bit instead of bit 32.
kernel: kernel/sched/syscalls.c:sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_policy_sign_bit_is_not_read (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 63 + 5)) sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [] := by
  sys_norm

/-- …and the -EINVAL a 64-bit sign test would give it is refused.
kernel: kernel/sched/syscalls.c:sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_policy_sign_bit_einval_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 63 + 5)) sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_pid_declines_before_the_copy (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) demo_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The temporary decline prevents a certain effect for this non-NULL negative argument.
Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_pid_efault_rejected :
    ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_null_param_and_negative_pid_are_distinct (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 0 0 (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- These conjuncts prevent two effects from becoming certain answers.
The first conjunct rejects -EFAULT for NULL `param`.
Linux returns -EINVAL for NULL in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-886, Linux v6.18.46).
QEMU v11.1.1 returns -EINVAL for NULL in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12096).
The second conjunct declines a real QEMU answer until #1929.
Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
QEMU can thus return -EINVAL with the four-byte ledger for the readable non-NULL parameter and negative pid.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pre_copy_einval_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 0 0 (fun _ => none)) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
          (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- The temporary decline prevents a certain effect for this non-NULL negative argument.
Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pre_copy_einval_is_linux_order :
    ¬ syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63))
          (fun _ => none)) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- -EFAULT IS THE RANGE VERDICT AND NOTHING ELSE.  The copy of
`do_sched_setscheduler` (kernel/sched/syscalls.c:887-888, Linux v6.18.46)
is `access_ok` and then the copy (include/linux/uaccess.h,
`_inline_copy_from_user`, Linux v6.18.46): `__access_ok`
(include/asm-generic/access_ok.h, Linux v6.18.46) refuses four bytes whose
last one is at
`TASK_SIZE`, and refuses them before a load; a range it ADMITS that memory
does not back is declined instead, because Linux answers -EFAULT there too
and the ledger cannot say which bytes it read first.  The two addresses
below are one byte apart and land on opposite sides of that line.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: sched_setscheduler_fault_is_the_range_verdict -/
theorem sched_setscheduler_fault_is_the_range_verdict (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 5 (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [])
    -- the last four bytes wholly under TASK_SIZE: the range passes, and the model declines
    -- rather than reporting the fault
    ∧ (syscall_spec (sched_setscheduler_in 0 5 (Z_to_bv 64 (TASK_SIZE - 4)) (fun _ => none)) demo_model o ↔
      o = Unmodeled) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- The Sv48 `TASK_SIZE` is 0x800000000000 (`State.TASK_SIZE`), so the
refused address above is 0x7ffffffffffd: the numeral the positive pin
below passes, so that its -EFAULT is judged against the cited function
without the model's own constant in the way.
model: the model's own constant at a numeral; the kernel reading is on the pins beside it. -/
example : Z_to_bv 64 (TASK_SIZE - 3) = 0x7ffffffffffd := by decide

/-- The same -EFAULT at the numeral: the copy of `do_sched_setscheduler`
(kernel/sched/syscalls.c:887-888, Linux v6.18.46) is the only -EFAULT in
the chain, and the last byte of this range is the first address
`__access_ok` refuses.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_range_past_task_size_is_efault (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 5 0x7ffffffffffd (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [] := by
  sys_norm

/-- …and it records no copy-in: `access_ok` fails before a load, so a
ledger on the -EFAULT is a lie.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46
rocq-twin: sched_setscheduler_fault_is_the_range_verdict -/
theorem sched_setscheduler_fault_records_no_copyin :
    ¬ syscall_spec (sched_setscheduler_in 0 5 (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => none)) demo_model
        (Ok (with_copyins [(Z_to_bv 64 (TASK_SIZE - 3), 4)] (mkEffect (errno_ret EFAULT) [] [])) demo_model []) := by
  sys_refute

/-- THE COPY READS ALL FOUR BYTES, SO A PARAM THREE BYTES WIDE DECLINES.
`copy_from_user(&lparam, param, sizeof(struct sched_param))`
(kernel/sched/syscalls.c:887) is one copy of the whole `int`
(include/linux/sched.h:410-412); `sched_setscheduler_priority_is_four_bytes_wide`
pins the value it reads.  This pins the range: a `param` whose fourth byte
no memory backs is a copy the kernel cannot complete — -EFAULT on Linux and
under qemu-user alike — and is declined here rather than answered, because
the ledger cannot say which bytes were read before the fault (Rocq's
`Kernel.Sys.prlimit64_spec` gives the reason), exactly as the wholly
unbacked range of `sched_setscheduler_fault_is_the_range_verdict` is; a
model reading three bytes would see 0 and answer SCHED_IDLE's 0 instead.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_partly_backed_param_declines (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr sched_param_mem_3) demo_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …refusing both the 0 a three-byte read would answer and the -EFAULT a
model that reported the fault instead of declining would give.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_partly_backed_param_answers_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr sched_param_mem_3) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr sched_param_mem_3) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_is_read_at_32_bits (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 - 1)) 5 sched_param_ptr
        (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled := by
  sys_norm

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
The `pid_t` argument reads 2^32 as pid zero in `do_sched_setscheduler` (kernel/sched/syscalls.c:880-881, Linux v6.18.46).
`find_process_by_pid` maps that zero to `current` (kernel/sched/syscalls.c:253-256, Linux v6.18.46).
The -ESRCH effect for that caller request is false.
QEMU can return the first conjunct's -EINVAL with a four-byte copy-in ledger.
The twin declines that real answer until #1929.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_width_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 - 1)) 5 sched_param_ptr
          (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32)) 5 sched_param_ptr
          (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret ESRCH) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- THE COPY COMES BEFORE THE TASK LOOKUP.  The copy of
`do_sched_setscheduler` (kernel/sched/syscalls.c:887-888, Linux v6.18.46)
precedes the task lookup at :890-892, so a
pid naming another task beside a `param` past TASK_SIZE is -EFAULT — not
the -ESRCH of a missing task, and not the decline a foreign pid otherwise
earns here: the range verdict is decided before the task is.  On the model
with the tid pinned, so that 4097 is unambiguously not this task; the
probe's `einval` run makes the same call with a pid no run has.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_copy_precedes_task_lookup (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) sched_tid_model o ↔
      o = Ok (mkEffect (errno_ret EFAULT) [] []) sched_tid_model [] := by
  sys_norm

/-- …refusing the -ESRCH a lookup-first kernel would give, and a ledger on a
copy that faulted before it read anything.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_copy_precedes_task_lookup_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) sched_tid_model
        (Ok (mkEffect (errno_ret ESRCH) [] []) sched_tid_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) sched_tid_model
        (Ok (with_copyins [(Z_to_bv 64 (2 ^ 63), 4)] (mkEffect (errno_ret EFAULT) [] [])) sched_tid_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- THE DECLINES, each on the exact argument that makes it one.  Every
call here is one Linux ANSWERS — SCHED_FIFO at priority 1 and SCHED_NORMAL
at 0 are ordinary requests, and SCHED_IDLE with SCHED_RESET_ON_FORK is a
0 — so each is a claim about the model alone: `RLIMIT_RTPRIO` and
`CAP_SYS_NICE` decide the first (`user_check_sched_setscheduler`,
kernel/sched/syscalls.c:483-493); whether the task is ALREADY SCHED_IDLE
decides the next two (:509-512); `CONFIG_SCHED_CLASS_EXT` decides whether
7 is a policy at all (`normal_policy`, kernel/sched/sched.h:192-198); the
reset-on-fork bit `_sched_setscheduler` strips (:779-783) is a state change
nothing records; and a positive pid with no tid pinned is a task the model
cannot say is this one.
kernel: kernel/sched/syscalls.c:user_check_sched_setscheduler,_sched_setscheduler; kernel/sched/sched.h:normal_policy@v6.18.46
rocq-twin: sched_setscheduler_declines -/
theorem sched_setscheduler_declines (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 1)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 0 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 3 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
        (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and the 0 each of those really returns on a permitted machine is not
admitted on its own: a decline is the whole answer, so that no later arm
turns the gap into a guess.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_declined_success_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 1)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 0 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
          (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

/-- SCHED_RR is declined with SCHED_FIFO, at every priority the range gate
admits (`rt_policy`, kernel/sched/sched.h:206-209; the rlimit gate at
kernel/sched/syscalls.c:483-493 decides both), and SCHED_EXT is declined
WHATEVER the priority: a priority the range gate refuses happens to be
-EINVAL under both configs, but the whole number is declined rather than
half of it, because `valid_policy` (:555-556) is consulted before the
range gate and is the config question.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,user_check_sched_setscheduler; kernel/sched/sched.h:rt_policy,normal_policy@v6.18.46 -/
theorem sched_setscheduler_rr_and_ext_decline (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 2 sched_param_ptr (sched_param_mem 1)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 2 sched_param_ptr (sched_param_mem 99)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 100)) demo_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 1)) demo_model o ↔
      o = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and NEITHER answer a real kernel gives for SCHED_EXT at priority 0 is
admitted on its own, which is what makes that decline a fail-closed answer
rather than a gap.  The two configs disagree and both are supported: with
`CONFIG_SCHED_CLASS_EXT` off, `normal_policy` (kernel/sched/sched.h:192-198)
is false for 7, so `valid_policy` is too and `__sched_setscheduler` answers
-EINVAL at kernel/sched/syscalls.c:555-556; with it on, 7 is a fair policy,
that -EINVAL never happens, and the answer turns on the same task state
SCHED_NORMAL's does — `_sched_setscheduler` copies `PRIO_TO_NICE(p->static_prio)`
into `attr.sched_nice` (:772), which is `task_nice(p)` itself
(include/linux/sched.h:1899-1902), so the fair-policy nice gate at :478-479
cannot fire and the task decides: 0 when it is not SCHED_IDLE and no loaded
ext scheduler has set `p->scx.disallow` (`scx_check_setscheduler`,
kernel/sched/ext.c:3085-3094, else -EACCES), -EPERM when it is SCHED_IDLE
without the `RLIMIT_NICE` room `is_nice_reduction` asks for (:509-512,
:115-121).  Every other decline here is refuted by the answer a permitted
machine gives; this one is refuted by both sides of a config choice.
kernel: kernel/sched/sched.h:normal_policy; kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_ext_answers_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- THE RT-AGREEMENT GATE, `rt_policy(policy) != (attr->sched_priority != 0)`
(kernel/sched/syscalls.c:569-571): an RT policy at priority 0 and a
non-RT policy at a nonzero priority are both -EINVAL, from the arguments
alone, so both are answered — SCHED_FIFO and SCHED_RR at 0, SCHED_NORMAL
and SCHED_IDLE at 1.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_rt_disagreement_is_einval (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 2 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 0 sched_param_ptr (sched_param_mem 1)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 1)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- A POLICY NUMBER THE HEADER DOES NOT DEFINE: 4 is the reserved SCHED_ISO
and `valid_policy` (kernel/sched/sched.h:216-220) is false for it under
every config, so `__sched_setscheduler` answers -EINVAL at :555-556 —
after the copy, so the ledger is carried.
kernel: kernel/sched/syscalls.c:__sched_setscheduler; kernel/sched/sched.h:valid_policy@v6.18.46 -/
theorem sched_setscheduler_undefined_policy_is_einval (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 4 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 8 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- …and that -EINVAL without its ledger is refused: the copy at :887 ran
before the policy was looked at.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_post_copy_einval_needs_its_ledger :
    ¬ syscall_spec (sched_setscheduler_in 0 4 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- …and the ledger it carries is four bytes wide, on the success as well as
on the -EINVAL.  `struct sched_param` is the single `int sched_priority`
(include/linux/sched.h:410-412), so the `copy_from_user` at
kernel/sched/syscalls.c:887 names `sizeof(struct sched_param)` = 4 and a
kernel reporting eight read bytes claims to have touched four bytes of the
address space the call never looked at.  The width is not an argument of the
call, so no probe can vary it; and it is the one part of the ledger a model
written from `sched_setattr`'s `struct sched_attr`, whose `size` field really
is a parameter, would get wrong.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_copyin_is_four_bytes :
    ¬ syscall_spec (sched_setscheduler_in 0 4 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 8)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 8)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- SCHED_DEADLINE IS -EINVAL AND NEVER ANYTHING ELSE from this entry
point: `_sched_setscheduler` builds an `attr` whose `sched_deadline` is 0
(kernel/sched/syscalls.c:769-773), `__checkparam_dl` refuses
`attr->sched_deadline == 0` (kernel/sched/deadline.c:3541-3543), so
`dl_policy(policy) && !__checkparam_dl(attr)` (:569) fires for every
`param` a caller can pass — and it fires before `user_check_sched_setscheduler`'s
-EPERM for DEADLINE (:502-503) is reached.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler; kernel/sched/deadline.c:__checkparam_dl@v6.18.46 -/
theorem sched_setscheduler_deadline_is_einval (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [] := by
  sys_norm

/-- …so neither the -EPERM an unprivileged DEADLINE request would otherwise
get nor a success is admitted.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_deadline_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EPERM) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- THE ONE ANSWER PAST THE TASK LOOKUP.  SCHED_IDLE at priority 0 on the
calling task passes every gate of `__sched_setscheduler` (kernel/sched/syscalls.c:555-571),
skips every `goto req_priv` of `user_check_sched_setscheduler` (:477-522:
`fair_policy(5)`, `rt_policy(5)` and `dl_policy(5)` are false,
`!idle_policy(5)` is false, `check_same_owner(current)` holds, and
`p->sched_reset_on_fork` is 0 after `sched_fork`, kernel/sched/core.c:4704-4722),
and returns 0 from either exit (:640-642 or :757); between :574 and those
exits nothing else fires — the SUGOV flag test (:578-579; the legacy entry
point sets no flag but RESET_ON_FORK), `security_task_setscheduler` (:581,
0 with no LSM), `p == rq->stop` (:615, a kthread), `scx_check_setscheduler`
(:620, 0 for every policy but SCHED_EXT) and the DEADLINE bandwidth gate
(:691, guarded by `dl_policy(policy) || dl_task(p)`).  The four bytes it
read are recorded.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,user_check_sched_setscheduler@v6.18.46
rocq-twin: sched_setscheduler_idle_is_zero -/
theorem sched_setscheduler_idle_is_zero (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [] := by
  sys_norm

/-- …and the lies a kernel would have to tell to make it something else.
-EPERM is the sharpest of them: it is what the call really returns when
`p->sched_reset_on_fork` is set (kernel/sched/syscalls.c:519-526) or when
a capability is missing, so a model that had made the SCHED_IDLE answer
depend on a credential it does not carry would ACCEPT it here and agree
with this file everywhere else.  -EINVAL is refused (priority 0 is the one
SCHED_IDLE accepts), a write-back is refused (the call has no output
parameter), and a success without its ledger is refused (the copy at :887
ran).
kernel: kernel/sched/syscalls.c:user_check_sched_setscheduler,do_sched_setscheduler@v6.18.46
rocq-twin: sched_setscheduler_idle_is_zero -/
theorem sched_setscheduler_idle_lies_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EPERM) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)]
              (mkEffect (Z_to_bv 64 0) [(sched_param_ptr, [Z_to_bv 8 0])] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- …nor does the success change the model: the policy the call writes is
state the model does not carry, and every arm that would read it is
declined, so the post-state is the pre-state and any other is refused.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_idle_leaves_the_model_alone :
    ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model []) := by
  sys_refute

/-- THE TASK IS LOOKED UP BEFORE THE POLICY IS JUDGED.  `do_sched_setscheduler`
looks the task up (kernel/sched/syscalls.c:890-892, `CLASS(find_get_task, p)(pid)`
and its -ESRCH) before `__sched_setscheduler`'s `valid_policy` (:555-556)
is reached, so pid 4097 — a task the model has no
representation of — with the undefined policy 4 declines: Linux answers
-ESRCH if no such task exists and -EINVAL if one does, and the model cannot
tell which.  A model that judged the policy before the task would answer
-EINVAL here.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler,__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_task_lookup_precedes_policy (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 4097 4 sched_param_ptr (sched_param_mem 0)) sched_tid_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and that -EINVAL is refused on it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_other_pid_bad_policy_einval_rejected :
    ¬ syscall_spec (sched_setscheduler_in 4097 4 sched_param_ptr (sched_param_mem 0)) sched_tid_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) sched_tid_model []) := by
  sys_refute

/-- THE PRIORITY IS READ AT ITS FULL WIDTH.  `sched_priority` is a
four-byte `int` (include/linux/sched.h:410-412) and the range gate
(kernel/sched/syscalls.c:567-568) and the RT-agreement gate (:570) compare
the whole `__u32`, so 256 and 65536 — whose low byte and low half are 0 —
are nonzero priorities, and SCHED_IDLE at either is the agreement gate's
-EINVAL.  A model reading one or two bytes of the field would answer 0.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_priority_is_four_bytes_wide (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 256)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 65536)) demo_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- …and the 0 a short read would give is refused for both.
kernel: kernel/sched/syscalls.c:__sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_short_priority_read_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 256)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 65536)) demo_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- `param` NEED NOT BE ALIGNED.  `copy_from_user` is `access_ok` and a
byte copy — `__access_ok` (include/asm-generic/access_ok.h:31-41) tests the
range and nothing else — so a `struct sched_param` at 4097 is read like one
at 4096, and the SCHED_IDLE request through it is 0 with the ledger naming
the odd address.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sched_setscheduler_param_need_not_be_aligned (o : outcome SyscallEffect) :
    syscall_spec (sched_setscheduler_in 0 5 sched_param_odd_ptr sched_param_odd_mem) demo_model o ↔
      o = Ok (with_copyins [(sched_param_odd_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [] := by
  sys_norm

/-- …and an -EFAULT for the odd address is refused.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_odd_param_fault_rejected :
    ¬ syscall_spec (sched_setscheduler_in 0 5 sched_param_odd_ptr sched_param_odd_mem) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- THE PID THE PINNED TID NAMES, against one it does not, on the SAME
model.  `find_process_by_pid` (kernel/sched/syscalls.c:253-256) is
`pid ? find_task_by_vpid(pid) : current`, and `pid_t` is an `int`, so the
pinned tid names the caller, the same register with its high half set
names the caller too, the neighbouring pid is a different task and
declined, and pid 0 is `current` whatever the tid is.  This is the shape
musl's `pthread_setschedparam` issues — it passes `t->tid`, never 0 — so
the pair matters: an arm that answered only pid 0 leaves every real caller
outside the modeled surface, and one that answered any positive pid would
claim to know about a task it has no representation of.
kernel: kernel/sched/syscalls.c:find_process_by_pid,do_sched_setscheduler@v6.18.46
rocq-twin: sched_setscheduler_pid_is_the_pinned_tid -/
theorem sched_setscheduler_pid_is_the_pinned_tid (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model [])
    ∧ (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 + 4096)) 5 sched_param_ptr
        (sched_param_mem 0)) sched_tid_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model [])
    ∧ (syscall_spec (sched_setscheduler_in 4097 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model o ↔
      o = Unmodeled)
    ∧ (syscall_spec (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model o ↔
      o = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and the -ESRCH a kernel with no task 4097 would answer is not admitted
either: whether one exists is what the model cannot say, so the decline
admits neither the -ESRCH nor the 0.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_other_pid_answers_rejected :
    ¬ syscall_spec (sched_setscheduler_in 4097 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret ESRCH) [] [])) sched_tid_model [])
    ∧ ¬ syscall_spec (sched_setscheduler_in 4097 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model
        (Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model []) := by
  refine ⟨?_, ?_⟩ <;> sys_refute

/-- Linux rejects negative policy in `SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:964-965, Linux v6.18.46).
It rejects negative pid before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c:885-888, Linux v6.18.46).
QEMU v11.1.1 tests NULL `param` in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c:12095-12103).
It then copies four bytes before the host checks the signed arguments.
An unreadable pointer can change the errno.
A readable pointer changes the copy-in ledger.
The intersection therefore supplies no single effect for non-NULL negative arguments.
The twin declines that band until PR #1929 changes Rocq and Lean follows it.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_pid_is_unmodeled (pid policy param : word)
    (hn : w_is0 param = false) (h : sint32 pid < 0) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    sched_setscheduler_spec pid policy param i m o ↔ o = Unmodeled := by
  simp only [sched_setscheduler_spec, hn, Bool.false_eq_true, ↓reduceIte, h, decide_true, Bool.or_true, unmodeled]

/-- Linux v6.18.46 rejects NULL before copying in `do_sched_setscheduler` (kernel/sched/syscalls.c).
QEMU v11.1.1 does the same in `do_syscall1`, case `TARGET_NR_sched_setscheduler` (linux-user/syscall.c).
Negative arguments cannot change that common effect.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_null_param_negative_arguments (o : outcome SyscallEffect) :
    (syscall_spec (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model [])
    ∧ (syscall_spec (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none)) demo_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-! ## sched_yield (124)

WHERE THESE WERE READ.  At the pin, and the line numbers are its: every
function and constant the `kernel:` annotations below name —
`do_sched_yield` and `SYSCALL_DEFINE0(sched_yield)` in
kernel/sched/syscalls.c, riscv64's `SYSCALL_DEFINE0` in
arch/riscv/include/asm/syscall_wrapper.h, `EPERM`, `EINTR` and `EINVAL` in
include/uapi/asm-generic/errno-base.h, `__NR_sched_yield` in
include/uapi/asm-generic/unistd.h — was re-read in Linux v6.18.46,
commit 1f99e9ab748f, the tree AGENTS.md makes the citation baseline,
before those annotations were written.  Saying so is worth a paragraph
because the first version of these pins named v6.12.1 — the tree the port
was drafted against — and `tools/check_lean_pin_evidence.py` retraces a
citation in the pinned clone only, so a reading at any other version is
one it reports rather than checks.  The two trees do NOT read the same:
`do_sched_yield` calls `current->sched_class->yield_task(rq)` at v6.12.1
and `rq->donor->sched_class->yield_task(rq)` at the pin
(kernel/sched/syscalls.c:1365, Linux v6.18.46), the proxy-execution donor
split; the riscv `SYSCALL_DEFINE0` and the two errno lines are identical
at both.  Nothing a pin here rests on moves with that line — the function
is still per-run-queue bookkeeping that returns nothing — and that, not
"reads the same", is what the annotations claim.

HOW THE PINS THAT NAME AN ERRNO ARE CITED.  `tools/check_lean_pin_evidence.py`
holds a positive pin — one whose statement carries no `¬`, `≠`, `False`
or `Unmodeled` — to KMENTION: every uppercase constant it names and this
tree defines must occur in the text of the cited symbols.  The syscall
spells no errno, so a pin naming one beside it cites two groups in the one
annotation, `<file>:<symbol>; <file>:<symbol>`, the shape the tool's
header gives for a set of outcomes decided in several places: the syscall
or the wrapper for why the word is answered or ignored, and
include/uapi/asm-generic/errno-base.h for which word the errno is.  The
first version of these pins cited the function alone and drew the finding;
the second spelled the errnos as words, which lost the tie to `errno_ret`
that Rocq's spelling carries for free.  The statements below are Rocq's,
spelling included.

No probe under `testing/syscall-check/tests/` calls 124 and no recorded
trace carries it; the Rocq Cases header says why the accepting half waits
on a recording made under the pinned guest.  Until one lands, the pins
below are the whole of what tests this arm. -/

def sched_yield_in (a0 a1 a2 a3 a4 a5 : word) : SyscallInput :=
  SyscallInput.mkInput 124 [a0, a1, a2, a3, a4, a5] (fun _ => none) (fun _ => none)

attribute [sys_simp low] sched_yield_in.eq_1

def sched_yield_zeros : SyscallInput := sched_yield_in 0 0 0 0 0 0

attribute [sys_simp low] sched_yield_zeros.eq_1

/-- 124 IS DISPATCHED AT ALL: `__NR_sched_yield` is 124 and the Lean table
has an arm for it — `sysno_124` in the generated
`Checks/Cases/SyscallTable.lean` says which.  Rocq states this on
`modeled_sysnos`, and so does this.
kernel: include/uapi/asm-generic/unistd.h:__NR_sched_yield@v6.18.46
rocq-twin: sched_yield_is_modeled -/
theorem sched_yield_is_modeled : (124 : Int) ∈ modeled_sysnos := by decide

/-- THE ANSWER IS 0 AND NOTHING ELSE MOVES.  `SYSCALL_DEFINE0(sched_yield)`
is `do_sched_yield(); return 0;` and its kernel-doc says "Return: 0";
everything `do_sched_yield` touches is per-run-queue scheduler bookkeeping
this model has no representation of — the wrapper is cited for the 0,
the helper for what does not move.  Stated as an `iff` over every
outcome, so the 0 is fixed and every other answer refused, `Unmodeled`
included.
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46
rocq-twin: sched_yield_answers_zero -/
theorem sched_yield_answers_zero (o : outcome SyscallEffect) :
    syscall_spec sched_yield_zeros demo_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model [] := by
  sys_norm

/-- EVERY ARGUMENT WORD IS IGNORED, and that is the declaration's shape
rather than this spec's convenience: riscv64 overrides `SYSCALL_DEFINE0`
with one taking `const struct pt_regs *__unused`, expanding without
`SC_RISCV_REGS_TO_ARGS`, so no argument register reaches the body.  A spec
that refused some argument shape would decline a call Linux answers 0.
Three shapes a probe would not think to pass: all bits set, a mix of
addresses and errno-looking words, and the all-ones word in the last
register alone.  Register 1 of the second is `errno_ret EINVAL`, as Rocq
spells it — an ARGUMENT the wrapper discards, not an answer, so the
declaration bears on the word only by ignoring it; the header that
defines `EINVAL` is cited beside it for the reason the section header
gives.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SYSCALL_DEFINE0; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46
rocq-twin: sched_yield_ignores_every_argument_word -/
theorem sched_yield_ignores_every_argument_word (o : outcome SyscallEffect) :
    (syscall_spec (sched_yield_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
        (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
        (Z_to_bv 64 (2 ^ 64 - 1))) demo_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model [])
    ∧ (syscall_spec (sched_yield_in 4096 (errno_ret EINVAL) (Z_to_bv 64 0x7fff80000000)
        (Z_to_bv 64 (2 ^ 32)) 1 0) demo_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model [])
    ∧ (syscall_spec (sched_yield_in 0 0 0 0 0 (Z_to_bv 64 (2 ^ 64 - 1))) demo_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- …AND FOR EVERY INPUT AND EVERY MODEL, on the spec itself: the three
vectors above are the Rocq example's, and this is the claim they sample.
`sched_yield_spec` takes no argument and reads no register, so the
statement quantifies the whole `SyscallInput` and the model, and the
answer is 0 with the model handed back unchanged; `Unmodeled` and every
other outcome are refused by the `iff`.  Stated on the spec because the
dispatcher's `in_arg` does not reduce over a symbolic argument list; that
124 reaches this spec is pinned where the table is generated —
`sysno_124` in the generated `Checks/Cases/SyscallTable.lean`,
`lookup_arm spec_table 124 = some sched_yield_arm` — and by the three
pins above, which go through `syscall_spec` at 124.  The 0 itself is
`SYSCALL_DEFINE0(sched_yield)`'s `return 0;` (kernel/sched/syscalls.c:1385,
Linux v6.18.46); the annotation names the declaration because
argument-independence is what this pin adds over
`sched_yield_answers_zero`.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SYSCALL_DEFINE0@v6.18.46 -/
theorem sched_yield_ignores_input_and_model (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    sched_yield_spec i m o ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- WHICH WORDS THE ERRNO-SHAPED REFUSALS BELOW ARE, pinned rather than
said: `EPERM` is 1 and `EINTR` is 4
(include/uapi/asm-generic/errno-base.h:5 and :8), and `errno_ret e` is
`Z_to_bv 64 (-e)`, so `-EPERM` is the all-ones word — the "nearest integer
below 0" the next pin refuses in its second conjunct and again, as
`errno_ret EPERM`, in its fourth — and `-EINTR` is `2 ^ 64 - 4`.  The last
two conjuncts are the negative half: the four answers the next pin refuses
are THREE distinct words, neither two nor four, which its docstring says
and this pins.  `EPERM` and `EINTR` themselves are pinned to the header
once for the tree, in `Checks/Cases/State.lean`'s `errno_base_values`, and
the `EPERM` wrap is pinned there too, as
`bv_unsigned (errno_ret EPERM) = 2 ^ 64 - 1` in
`errno_ret_encodes_the_block`; `Checks/Cases/Sys/Syscall.lean`'s
`errno_ret_EBADF_in_a0` and `errno_ret_EINVAL_in_a0` state two other
errnos in this pin's shape.  What is new here is the `EINTR` half and the
distinctness.
kernel: include/uapi/asm-generic/errno-base.h:EPERM,EINTR@v6.18.46 -/
theorem sched_yield_refused_errnos_are_these_words :
    errno_ret EPERM = Z_to_bv 64 (2 ^ 64 - 1)
    ∧ errno_ret EINTR = Z_to_bv 64 (2 ^ 64 - 4)
    ∧ Z_to_bv 64 1 ≠ errno_ret EPERM
    ∧ errno_ret EPERM ≠ errno_ret EINTR := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- THE REFUSALS.  No kernel answers this call anything but 0, so each of
these is an answer the model must refuse: the two nearest integers, an
errno, and the -EPERM the Rocq example names as the word
`ALLOW_ERROR_INJECTION` would make reachable on a kernel running a
`bpf_override_return` program — a residual under which every word here is
reachable, not that one alone (`Sys.Kernel.Sched.Syscalls.sched_yield_spec`
has the source), and which this model does not describe.  FOUR CONJUNCTS, THREE
WORDS: `errno_ret EPERM` is `Z_to_bv 64 (-1)` (`EPERM` is 1), so the
second conjunct and the fourth are the same proposition.  Both are kept,
because this pin restates the Rocq `Example` conjunct for conjunct and a
reader comparing the two should find them the same shape; the redundancy
is Rocq's and is named here rather than silently collapsed, here and in
the checker-level restatement in
`Checks/Cases/Checks/Sys/Kernel/Sched/Syscalls.lean` alike.  Cited to
`SYSCALL_DEFINE0(sched_yield)`, whose `return 0;` is why every one of
these is refused, and to `do_sched_yield`.
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46
rocq-twin: sched_yield_nonzero_answers_rejected -/
theorem sched_yield_nonzero_answers_rejected :
    ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (mkEffect (Z_to_bv 64 1) [] []) demo_model [])
    ∧ ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) demo_model [])
    ∧ ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (mkEffect (errno_ret EINTR) [] []) demo_model [])
    ∧ ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (mkEffect (errno_ret EPERM) [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- …and a 0 that claims to have written user memory, read it, or freed a
mapping is refused too: the call has no output parameter, no argument to
fetch and nothing to unmap.  The empty copy-in ledger is the half
`tools/check_copyin_parity.py` compares against the harness.
kernel: kernel/sched/syscalls.c:do_sched_yield@v6.18.46
rocq-twin: sched_yield_effect_shape_is_bare -/
theorem sched_yield_effect_shape_is_bare :
    ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) demo_model [])
    ∧ ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (with_copyins [(Z_to_bv 64 4096, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [])
    ∧ ¬ syscall_spec sched_yield_zeros demo_model
        (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] []
              [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] []) demo_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sched.Syscalls
