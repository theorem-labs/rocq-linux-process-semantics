import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Kernel.Futex.Syscalls — what `futex` answers, read off against Linux

Worked examples over `Sys.Kernel.Futex.Syscalls.futex_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Futex/Syscalls.v`.  Not part
of the trusted specification: this file is QA on the definition, written
to be READ, and every claim in it is a claim about what the kernel does,
with the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f).

HOW THESE ARE STATED.  A check is stated on the relation itself, as an
`iff` over EVERY outcome `o`, so one theorem fixes what is admitted and
what is refused; beside it, the concrete lie a kernel could tell is refuted
on its own.  The model is SYMBOLIC in every pin: `futex_spec` reads the
syscall input's memory and nothing of the model, so each answer is stated
for every `m` at once and the post-state is that same `m`.  The proofs are
`sys_norm` and `sys_refute` (`Checks/Cases/Tactic.lean`) wherever the call
is concrete; the universally quantified statements at the end — the two
clone-gate twins and the refusals they imply, then the two futex twins, the
ledger tie and the reading they rest on — close by `decide` on a gate's one
admitted word or case-split the symbolic gates by hand, and say so where
they occur.

THE WAITER SET OF A PRIVATE FUTEX KEY IS EMPTY IN THIS MODEL, and every
answer below rests on it.  A waiter is a `struct futex_q` on the plist of
a hash bucket, put there by `futex_queue` (kernel/futex/futex.h:363-369, v6.18.46,
over `__futex_queue`, kernel/futex/core.c:891) and matched by
`futex_match` (kernel/futex/futex.h:255, v6.18.46) on the `union futex_key` the
queueing task computed.  For
an op carrying `FUTEX_PRIVATE_FLAG`, `get_futex_key`
(kernel/futex/core.c:624-630, v6.18.46) builds that key from the caller's own mm
(`key->private.mm = mm; key->private.address = address; return 0;`), so
only a task whose `current->mm` is the SAME POINTER can produce a key that
`futex_match` accepts.  The bucket a private key hashes into is the
global table's until the mm owns a private hash (`__futex_hash_private`,
kernel/futex/core.c:181-198 (v6.18.46), returns NULL without one, and
`need_futex_hash_allocate_default`, kernel/fork.c:1917-1924 (v6.18.46), allocates
one only on a `CLONE_VM` clone), so it can hold other processes' waiters;
the key is what excludes them.

WHAT CAN PUT A WAITER ON THIS MM'S KEYS, and why nothing in this model
can.  Linux has two routes.  A second task sharing the mm: `clone` (220)
or `clone3` (435) with `CLONE_VM`, or io_uring's kernel workers
(`create_io_thread`, kernel/fork.c:2547-2560 (v6.18.46), clones with `CLONE_VM`).
And a waiter with NO task at all: io_uring's `IORING_OP_FUTEX_WAIT` queues
a `futex_q` on the submitter's behalf through `futex_wait_setup`
(kernel/futex/waitwake.c:591-664, v6.18.46) with a NULL task — `io_futex_wait`
(io_uring/futex.c:269-312, v6.18.46) calls it at :295-296 with `NULL, NULL`, and
"@task may be NULL, for async usage of futexes" (kernel/futex/futex.h:361, v6.18.46)
— so a single task can queue a private waiter, keep running, and then see
its own `FUTEX_WAKE` count 1.  The first route is closed the way Rocq
closes it: the Lean `clone` (220) and `clone3` (435) arms
(`Sys/Kernel/Fork.lean`, ticket S-Kernel-Fork-clone) accept one flag word
each — `clone_fork_flags_b` the register `SIGCHLD`, `clone3_fork_args_b`
the image whose `flags` field is 0 — and neither word carries `CLONE_VM`,
so every task either arm creates has an mm of its own (`copy_mm`, kernel/fork.c:1520,
v6.18.46, shares `current->mm` only under `CLONE_VM`, :1543-1544, and
otherwise `dup_mm`s it, :1547) and can never hold a key
`futex_match` accepts against this task's.  That premise is a compile-time
fact at the end of this file, as Rocq's `clone_fork_gate_grants_no_shared_mm`
and `clone3_fork_gate_grants_no_shared_mm` name for name: widening either
gate to a word with `CLONE_VM` breaks the build there, beside this
paragraph.  Rocq's header names no io_uring route and owes that
correction.  The second route is closed by the table: `Sys/SyscallTable.lean`
carries neither `io_uring_setup` (425) nor `io_uring_enter` (426), so no
ring exists to queue through and no io-wq thread sharing the mm is ever
created; `io_uring_setup_has_no_arm` and its siblings pin that, and the
day a `lean: port io_uring …` PR lands one of those arms, the pins for
that number break the build beside this paragraph and that PR owes the
premise's next shape.  `Sys/Uapi/Sched.lean`'s `CLONE_VM` docstring says
this file pins the premise "over both clone gates", which is what the two
twins below do.

So the count `futex_wake` returns is 0 by construction rather than by
luck, and a FUTEX_WAIT whose value still matches would park forever.  THE
SECOND HALF IS WHY THE SPEC IS NARROW: an operation whose answer depends
on a waiter EXISTING is unanswerable here, and declines.

WHAT THE ROCQ FILE PINS AND WHAT IT PROBES.  Rocq keeps two universally
quantified answers, `futex_wake_private_answers` and
`futex_wait_private_answers`, and sends every concrete decision to two
probes against a real kernel: `testing/syscall-check/tests/futex_private.c`
for the answered calls and their `--mutate` lies, and
`testing/syscall-check/tests/unmodeled_futex.c` for the declines.  The
Lean tree has no replay harness, so this file pins every decision the two
probes reach, on Rocq's own addresses where the probe's choice matters,
and cites the probe case beside each pin as its evidence.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Futex.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The fixtures

The futex word lives one page up, at 4096, and holds the value 7 in the
hart's byte order; nothing else is readable.  Every other address a pin
names is chosen for one gate: 8192 is aligned, in range and UNMAPPED (the
address `futex_private.c`'s `wake_unmapped` case probes), 4097 is
misaligned, 2^47 is the first ALIGNED address `access_ok` refuses on Sv48
(`futex_private.c`'s `past_task_size`; 2^47 - 3 is the first of any
alignment, and the alignment test would answer for it first), 2^47 - 4 is
the last aligned word inside the range, and 2^47 + 1 fails both gates at
once, which is what tells their order apart.  The boundary addresses are
spelled from `State.TASK_SIZE`, so the pins over them follow the declared
address-space size and not a literal.  A second word, all ones, tells a
u32 compare from a sign-extending or a two-byte one, which the word 7
cannot. -/

/-- The address of the futex word. -/
def futex_addr : word := 4096

/-- The word holds 7: four bytes at `futex_addr`, least significant first,
and `none` everywhere else (`Prelude.bytes_at`). -/
def futex_mem : word → Option byte := bytes_at futex_addr [7, 0, 0, 0]

/-- The syscall input every pin reads: number 98, the given registers,
`futex_mem` as the readable memory and nothing writable. -/
def futex_input (args : List word) : SyscallInput :=
  SyscallInput.mkInput 98 args futex_mem (fun _ => none)

/-- Aligned, in range, and nothing mapped there. -/
def unmapped_addr : word := 8192

/-- One past the word: `4097 % 4 = 1`. -/
def misaligned_addr : word := 4097

/-- The first address past the user range on Sv48: `access_ok(2^47, 4)` is
`2^47 <= 2^47 - 4`, which is false.  Aligned, so only the range gate can
refuse it. -/
def past_task_size : word := Z_to_bv 64 TASK_SIZE

/-- Misaligned AND past the range: the one address on which the two
`get_futex_key` refusals disagree, so the answer is whichever fires first. -/
def misaligned_past : word := Z_to_bv 64 (TASK_SIZE + 1)

/-- The last aligned word inside the range: `access_ok(2^47 - 4, 4)` is
`2^47 - 4 <= 2^47 - 4`, which holds with equality. -/
def last_in_range : word := Z_to_bv 64 (TASK_SIZE - 4)

/-- The all-ones word: four bytes `0xff` at `futex_addr`, and `none`
everywhere else. -/
def futex_mem_ff : word → Option byte := bytes_at futex_addr [0xff, 0xff, 0xff, 0xff]

/-- The syscall input over the all-ones word. -/
def futex_input_ff (args : List word) : SyscallInput :=
  SyscallInput.mkInput 98 args futex_mem_ff (fun _ => none)

/-! ### The fixtures' readings

The input's memory is read off by projection, and the two reads a pin can
reach are closed facts.  Registered in `sys_simp` at the default priority,
ahead of the low-priority unfoldings, so the fixture stays a name in the
normal form (`Checks/Cases/Tactic.lean`'s header says why a fixture enters
the set by its projections or by its unfolding, never both). -/

/-- The readable memory of every input here is `futex_mem`.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem in_mem_futex_input (args : List word) : (futex_input args).in_mem = futex_mem := rfl

/-- The four bytes at the word, as `read_bytes_map` reads them: 7 in the
low byte, address order.
model: a closed read off the fixture memory, a rewrite for `sys_norm`. -/
theorem read_futex_word :
    read_bytes_map futex_mem futex_addr (Z_to_bv 64 FUTEX_WORD_SIZE) = some [7, 0, 0, 0] := by
  decide

/-- Nothing is mapped at 8192, so the read of a word there is `none`.
model: a closed read off the fixture memory, a rewrite for `sys_norm`. -/
theorem read_unmapped_word :
    read_bytes_map futex_mem unmapped_addr (Z_to_bv 64 FUTEX_WORD_SIZE) = none := by
  decide

/-- The readable memory of every all-ones input is `futex_mem_ff`.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem in_mem_futex_input_ff (args : List word) : (futex_input_ff args).in_mem = futex_mem_ff := rfl

/-- The four bytes of the all-ones word, as `read_bytes_map` reads them.
model: a closed read off the fixture memory, a rewrite for `sys_norm`. -/
theorem read_futex_word_ff :
    read_bytes_map futex_mem_ff futex_addr (Z_to_bv 64 FUTEX_WORD_SIZE) = some [0xff, 0xff, 0xff, 0xff] := by
  decide

attribute [sys_simp] in_mem_futex_input read_futex_word read_unmapped_word
  in_mem_futex_input_ff read_futex_word_ff

-- Sys/Kernel/Futex/Syscalls.lean: the spec, its two commands and the
-- shared key check, at the priority every spec has.  The gate predicates
-- (`futex_aligned_b`, `access_okb`) stay out: a gate is decided, never
-- unfolded.
attribute [sys_simp low]
  futex_spec.eq_1 futex_wake_private_spec.eq_1 futex_wait_private_spec.eq_1 futex_key_check.eq_1

-- Sys/Syscall.lean: the copy-in wrapper is `bind spec (fun eff => pure …)`,
-- read by `bind_pure_iff` once its unfolding is in the set.  No earlier
-- port carried a copy-in, so `Checks/Cases/Tactic.lean`'s register does
-- not hold this line yet; it belongs in that file's `Sys/Syscall.lean`
-- group beside `ret_only.eq_1`, and moves there with the next
-- `lean: checks:` change to the register.
attribute [sys_simp low] record_copyins.eq_1

/-! ## `get_futex_key`: alignment first, then the range, in that order

`get_futex_key` (kernel/futex/core.c:548-770, v6.18.46) is the first thing both
commands reach.  Its first decision is `if (unlikely((address % size) !=
0)) return -EINVAL;` (:569-570) with `size` 4 for every call this spec can
see (`Uapi.FUTEX_WORD_SIZE`); its second is `if (unlikely(!access_ok(uaddr,
size))) return -EFAULT;` (:573-574).  Both are on the address the caller
passed, before any page is resolved. -/

/-- A misaligned address is -EINVAL, whatever the memory holds: the test
at kernel/futex/core.c:569-570 (v6.18.46) reads the address and nothing else.
probe: testing/syscall-check/tests/futex_private.c#conform -- misaligned -/
theorem misaligned_wake_is_einval (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec misaligned_addr (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A kernel that lets a misaligned address through to the count is
refused: `get_futex_key` returns before `futex_wake` reaches its bucket.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- misaligned -/
theorem misaligned_wake_is_not_zero (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec misaligned_addr (futex_input []) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-- The same refusal on a wait: the alignment test is `get_futex_key`'s,
which `futex_wait_setup` calls first (kernel/futex/waitwake.c:617-619),
before the word is read, so no copy-in is recorded.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem misaligned_wait_is_einval (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec misaligned_addr (Z_to_bv 64 7) (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and it is -EINVAL with an EMPTY ledger: a kernel claiming to have
read the word before refusing its address has the two lines of
`futex_wait_setup` in the wrong order.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem misaligned_wait_reads_nothing (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec misaligned_addr (Z_to_bv 64 7) (futex_input []) m
        (Ok (with_copyins [(misaligned_addr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  sys_refute

/-- An address past the user range is -EFAULT: `access_ok(2^47, 4)` fails
on Sv48, and it is the RANGE that failed, not a page lookup.
probe: testing/syscall-check/tests/futex_private.c#conform -- past_task_size -/
theorem past_range_wake_is_efault (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec past_task_size (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- A kernel whose user range ran past `TASK_SIZE` is refused.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- past_task_size -/
theorem past_range_wake_is_not_zero (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec past_task_size (futex_input []) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-- ORDER IS BEHAVIOUR: an address that is misaligned AND past the range is
-EINVAL, because kernel/futex/core.c:569-570 runs before :573-574.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem misaligned_past_range_is_einval (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec misaligned_past (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A spec with the two tests the other way round would answer -EFAULT
here; that answer is refused.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem misaligned_past_range_is_not_efault (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec misaligned_past (futex_input []) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- THE ALIGNMENT IS FOUR BYTES, not two and not eight: an address ≡ 2 mod 4
is -EINVAL like the ≡ 1 one, because `size` is `futex_size(flags)` = 4
(`futex_size`, kernel/futex/futex.h:77-80, on `FLAGS_SIZE_32`) and the
test is `address % size` (kernel/futex/core.c:569).
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/futex.h:futex_size@v6.18.46 -/
theorem half_aligned_wake_is_einval (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec (Z_to_bv 64 4098) (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and an address ≡ 4 mod 8 passes it: 4100 is word-aligned and in range,
and a wake resolves no page, so it is 0 although nothing is readable there.
A spec testing `% 8` would answer -EINVAL.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/futex.h:futex_size@v6.18.46 -/
theorem word_aligned_wake_is_zero (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec (Z_to_bv 64 4100) (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- THE RANGE TEST IS INCLUSIVE AT THE TOP: `__access_ok` is `addr <= limit
- size` (include/asm-generic/access_ok.h:40), so the last aligned word
below `TASK_SIZE` passes and a private wake there is 0; a spec testing `<`
would answer -EFAULT.  That is the pinned kernel's answer and the booted
guest's; qemu-user's `do_futex` hands the host kernel the translated
address unchecked, so the host's own limit decides the last guest page
there — a question about `State.access_okb` as a whole, not about this
arm.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem last_in_range_wake_is_zero (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec last_in_range (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- A range wrapping 2^64 is -EFAULT: `__access_ok` compares the address
against `limit - size`, never `addr + size` against `limit`, so the sum's
wrap rescues nothing (include/asm-generic/access_ok.h:40).
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem wrapped_wake_is_efault (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec (Z_to_bv 64 0xfffffffffffffffc) (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- The range refusal on a wait, with an EMPTY ledger: `get_futex_key` runs
before the word is read (kernel/futex/waitwake.c:617-619), so a wait at
`TASK_SIZE` is -EFAULT and no copy-in is recorded.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem past_range_wait_is_efault (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec past_task_size (Z_to_bv 64 7) (futex_input []) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- …and a kernel claiming to have read the word before refusing its range
is refused, as for the misaligned address.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem past_range_wait_reads_nothing (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec past_task_size (Z_to_bv 64 7) (futex_input []) m
        (Ok (with_copyins [(past_task_size, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-! ## `futex_wake`: the count is 0, and nothing is read or changed

Past the key check, `futex_wake` (kernel/futex/waitwake.c:155-200, v6.18.46)
answers 0 on every mapped or unmapped address in range: `if
(!futex_hb_waiters_pending(hb)) return ret;` (:175-176) with `ret` still
the 0 the key check returned (:165-167) when the hash bucket is empty,
and otherwise the loop at :180-195, in which `futex_match` (:181) accepts
no key because the waiter set of a private key is empty here (the file
header).  `nr_wake` bounds the matches, and there are none. -/

/-- A private wake on a mapped, aligned word is 0: no waiters woken, the
model untouched, no event, nothing read.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake -/
theorem wake_is_zero (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec futex_addr (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- A kernel that claims it woke a waiter is lying: there is no task with
this mm to have queued one.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=1 -- wake -/
theorem wake_woke_nobody (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec futex_addr (futex_input []) m
        (Ok (mkEffect (Z_to_bv 64 1) [] []) m' evs) := by
  sys_refute

/-- A private wake resolves NO page: an aligned address in range with
nothing mapped at it is 0, not -EFAULT, because the private path of
`get_futex_key` returns at kernel/futex/core.c:624-630 (v6.18.46) before any
`get_user_pages_fast`.  This is the shape on which "resolve the buffer and
answer -EFAULT when it is not there" would be the wrong spec.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_unmapped -/
theorem wake_unmapped_is_zero (m : Model) (o : outcome SyscallEffect) :
    futex_wake_private_spec unmapped_addr (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- The -EFAULT the natural wrong spec would answer on an unmapped word is
refused.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=-EFAULT -- wake_unmapped -/
theorem wake_unmapped_is_not_efault (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec unmapped_addr (futex_input []) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A wake reads no user memory: a kernel whose ledger carries a copy-in
on a wake has read something `futex_wake` never fetches.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:smuggle-copyin:0x10000:8 -- wake -/
theorem wake_reads_nothing (m m' : Model) (evs : List event) :
    ¬ futex_wake_private_spec futex_addr (futex_input []) m
        (Ok (with_copyins [(Z_to_bv 64 0x10000, 8)] (mkEffect (Z_to_bv 64 0) [] [])) m' evs) := by
  sys_refute

/-- A wake emits no event: nothing observable leaves the process.
kernel: kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem wake_emits_nothing (m m' : Model) :
    ¬ futex_wake_private_spec futex_addr (futex_input []) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' [event.WriteEv 1 0]) := by
  sys_refute

/-! ## The count and the timeout are not read on a wake

`nr_wake` bounds a loop that runs zero times (kernel/futex/waitwake.c:
180-195), and `SYSCALL_DEFINE6(futex)` fetches `utime` only under
`futex_cmd_has_timeout(cmd)` (kernel/futex/syscalls.c:196, v6.18.46), whose list
(:161-172) has no `FUTEX_WAKE`.  So a private wake answers 0 for EVERY
`val` and EVERY `utime` — `INT_MAX`, 0 and -1 for the count, junk for the
timeout — and the statements say so with those two arguments symbolic. -/

/-- A private wake through `futex_spec` answers 0 whatever `val` and
`utime` hold: the two registers are dead on this command.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_counts -/
theorem wake_ignores_count_and_timeout (val utime : word) (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAKE_PRIVATE) val utime (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- A spec that declined a wake for a junk timeout, as the wait arm does
for its own, would refuse the three-argument `__syscall` musl's `__wake`
issues; the decline is refused on a wake.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_junk -/
theorem wake_with_junk_timeout_is_zero (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAKE_PRIVATE) (Z_to_bv 64 0x7fffffff)
        (Z_to_bv 64 0xdeadbeef) (futex_input []) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-! ## `futex_wait_setup`: -EAGAIN when the word differs, a decline when it matches

`futex_wait_setup` (kernel/futex/waitwake.c:591-664, v6.18.46) reads the word after
the key check — `ret = futex_get_value_locked(&uval, uaddr);` (:627), a
`get_user`-class fetch defined in kernel/futex/futex.h:332-341 (v6.18.46) — and
returns `-EWOULDBLOCK` when `uval != val` (:642-645).  -EWOULDBLOCK is
-EAGAIN (include/uapi/asm-generic/errno.h:22, v6.18.46).  When the word matches, the
caller is queued (:660) and blocks in `futex_do_wait` (:687); nothing in
this model wakes it, so the spec declines rather than invent a return. -/

/-- The word holds 7 and the caller expected 8: -EAGAIN, and the four-byte
read is on the ledger.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem wait_mismatch_is_eagain (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec futex_addr (Z_to_bv 64 8) (futex_input []) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- A kernel that claims the wait slept and was woken — a 0 return — is
refused: `__futex_wait` reaches its `return 0` (kernel/futex/waitwake.c:
690-691) only after `futex_unqueue` finds the entry gone, i.e. after some
task really did wake it, and here none can.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- wait_eagain -/
theorem wait_mismatch_is_not_zero (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec futex_addr (Z_to_bv 64 8) (futex_input []) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-- The -EAGAIN carries the read: a kernel whose ledger is empty on this
answer claims it decided `uval != val` without fetching `uval`.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:drop-copyins -- wait_eagain -/
theorem wait_mismatch_reads_the_word (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec futex_addr (Z_to_bv 64 8) (futex_input []) m
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The word holds 7 and the caller expected 7: the caller would block,
and the spec declines rather than answer.
kernel: kernel/futex/waitwake.c:futex_wait_setup,futex_do_wait,__futex_wait@v6.18.46 -/
theorem wait_match_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec futex_addr (Z_to_bv 64 7) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and in particular the matching wait is NOT -EAGAIN: the value test
at kernel/futex/waitwake.c:642 is an inequality, and a spec answering
-EAGAIN on a match would let a caller spin where Linux sleeps.
kernel: kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem wait_match_is_not_eagain (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec futex_addr (Z_to_bv 64 7) (futex_input []) m
        (Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EAGAIN) [] [])) m' evs) := by
  sys_refute

/-- THE WORD IS READ LITTLE-ENDIAN: the bytes `7, 0, 0, 0` are the value 7
and not 0x07000000, so a caller expecting the byte-swapped value gets
-EAGAIN.  riscv is little-endian (arch/riscv/include/uapi/asm/byteorder.h
includes linux/byteorder/little_endian.h) and `get_user` fetches the u32
in that order.
kernel: kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem wait_reads_little_endian (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec futex_addr (Z_to_bv 64 0x07000000) (futex_input []) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- THE COMPARE IS ON A u32, UNSIGNED: the all-ones word is 0xffffffff, a
`val` of 0xffffffff matches it, and the call declines as a blocking wait.
A spec reading the word sign-extended (the 64-bit -1) would find a
mismatch against the zero-extended `val` and answer -EAGAIN.
kernel: kernel/futex/syscalls.c:futex; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem wait_all_ones_match_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 0xffffffff) (Z_to_bv 64 0)
        (futex_input_ff []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- A register of all ones — what a C caller's `(int) -1` arrives as — is
the u32 0xffffffff after `SYSCALL_DEFINE6`'s `u32 val`, so it matches the
all-ones word too, and declines.
kernel: kernel/futex/syscalls.c:futex; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem wait_all_ones_register_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 0)
        (futex_input_ff []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and `val` 0xffff against the all-ones word is a mismatch, -EAGAIN with
the four-byte read: a spec reading two bytes would see 0xffff, match, and
decline instead.
kernel: kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem wait_all_ones_low_half_is_eagain (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec futex_addr (Z_to_bv 64 0xffff) (futex_input_ff []) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- A wait on a word the model cannot read declines: the private wait DOES
resolve the page (`futex_get_value_locked`, then `get_user` on a fault,
kernel/futex/waitwake.c:627-634, v6.18.46), and an absent byte is an absent fact in
a partial memory, not a fault.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_unmapped -/
theorem wait_unmapped_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_wait_private_spec unmapped_addr (Z_to_bv 64 0) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The unreadable word is not answered -EFAULT either, although Linux
would (`futex_wait_setup`, kernel/futex/waitwake.c:629-634 (v6.18.46), returns the
fault of its `get_user` retry): the model does not know the page is
absent, only that it has no byte for it, and guessing the kernel's answer
is what fail-closed forbids.  The probe case records both the kernel's
-EFAULT and the model's decline.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_unmapped -/
theorem wait_unmapped_is_not_efault (m m' : Model) (evs : List event) :
    ¬ futex_wait_private_spec unmapped_addr (Z_to_bv 64 0) (futex_input []) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## `futex_spec`: the op word, the value's width, and the timeout

`SYSCALL_DEFINE6(futex, u32 __user *, uaddr, int, op, u32, val, …)`
(kernel/futex/syscalls.c:188-208, v6.18.46) narrows `val` to 32 bits before
`do_futex` sees it, and the spec follows (`abi_low32`); the op is tested
WHOLE, which is stricter than the kernel's `int op` and is the fail-closed
direction.  `do_futex` (:112-159) sends the two private words to
`futex_wait` and `futex_wake` and every other word elsewhere. -/

/-- Syscall 98 with `FUTEX_WAIT_PRIVATE`, `val = 8` and no timeout reaches
the wait arm: -EAGAIN with the read on the ledger.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem wait_through_futex_spec (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 8) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- `val` IS 32 BITS: a register of 2^32 + 7 is the u32 value 7, which
matches the word, so the call declines as a blocking wait rather than
answering -EAGAIN for a mismatch on the full register.
kernel: kernel/futex/syscalls.c:futex; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem wait_val_is_32_bits (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 (2 ^ 32 + 7))
        (Z_to_bv 64 0) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- A spec comparing the whole register would answer -EAGAIN here; that
answer is refused.
kernel: kernel/futex/syscalls.c:futex; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem wait_val_high_half_is_dropped (m m' : Model) (evs : List event) :
    ¬ futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 (2 ^ 32 + 7))
        (Z_to_bv 64 0) (futex_input []) m
        (Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EAGAIN) [] [])) m' evs) := by
  sys_refute

/-- A wait with a non-NULL timeout declines before the word is read:
`get_timespec64` (kernel/time/time.c, v6.18.46) and `futex_init_timeout`
(kernel/futex/syscalls.c:174-186, called at :199-203, v6.18.46) have an -EFAULT and an -EINVAL of their own ahead of everything,
and the timer they arm has an -ETIMEDOUT this model has no clock for.
The probe's value MATCHES the word, so its guest really sleeps and times
out; the pin's value differs from the word on purpose, so that the
decline is visibly the timeout gate's and not the read's — without the
timeout the same call is -EAGAIN (`wait_through_futex_spec`).
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_timeout -/
theorem wait_with_timeout_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 8) (Z_to_bv 64 0x10000)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the decline is BEFORE the read: a spec that answered the
mismatch's -EAGAIN under a timeout would be right about the value and
wrong about the order, since the timeout is fetched at :196-206, before
`do_futex` (:207) is entered.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem wait_with_timeout_is_not_eagain (m m' : Model) (evs : List event) :
    ¬ futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 8) (Z_to_bv 64 0x10000)
        (futex_input []) m
        (Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EAGAIN) [] [])) m' evs) := by
  sys_refute

/-- THE TIMEOUT IS TESTED ON THE WHOLE REGISTER: a pointer whose low 32
bits are zero and whose high half is not is not NULL to `if (utime && …)`
(kernel/futex/syscalls.c:196, a test on the 64-bit pointer), so the wait
declines exactly as for any other non-NULL `utime` — Linux would fetch
through it and fault at `get_timespec64` (:199-200).  A spec testing
`abi_low32 utime` would answer the mismatch's -EAGAIN here.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem wait_with_high_timeout_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 8) (Z_to_bv 64 (2 ^ 32))
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- THE OP IS TESTED WHOLE: a register whose low half is a private wake and
whose high half is not zero declines, although `int op` makes it a private
wake to Linux.  Fail closed: the model refuses a call it could have
answered rather than answer one it should not.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_high -/
theorem op_high_half_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (2 ^ 32 + FUTEX_WAKE_PRIVATE)) (Z_to_bv 64 0x7fffffff)
        (Z_to_bv 64 0) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The shared spelling, `FUTEX_WAKE` with the private bit clear, declines:
`futex_to_flags` (kernel/futex/futex.h:49-50, v6.18.46) then sets `FLAGS_SHARED` and
`get_futex_key` resolves the page (kernel/futex/core.c:633-769, v6.18.46), whose
key another process may hold — neither the empty waiter set nor the
range-only -EFAULT survives.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_shared -/
theorem shared_wake_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAKE) (Z_to_bv 64 1) (Z_to_bv 64 0) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- `FUTEX_CLOCK_REALTIME` on a private wake declines: `do_futex` tests
`FLAGS_CLOCKRT` before its switch (kernel/futex/syscalls.c:118-123, v6.18.46) and
permits it on three other commands only, so Linux answers -ENOSYS.  A spec
masking the op with `FUTEX_CMD_MASK` would answer 0.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- clockrt -/
theorem clockrt_wake_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (FUTEX_WAKE_PRIVATE + 256)) (Z_to_bv 64 1) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The shared spelling of the wait, `FUTEX_WAIT` with the private bit
clear, declines for the shared wake's reason: `futex_to_flags`
(kernel/futex/futex.h:49-50) sets `FLAGS_SHARED` and the key is the
page's.  Linux would answer this call's -EAGAIN; the model does not know
who else may hold the key.
kernel: kernel/futex/futex.h:futex_to_flags; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem shared_wait_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 FUTEX_WAIT) (Z_to_bv 64 8) (Z_to_bv 64 0) (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- `FUTEX_CLOCK_REALTIME` on a private WAIT declines as on a wake:
`do_futex` permits the bit on `FUTEX_WAIT_BITSET` and not on `FUTEX_WAIT`
(kernel/futex/syscalls.c:118-123), so Linux answers -ENOSYS before the
word is looked at.
kernel: kernel/futex/syscalls.c:do_futex@v6.18.46 -/
theorem clockrt_wait_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (FUTEX_WAIT_PRIVATE + 256)) (Z_to_bv 64 8) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- `FUTEX_WAKE_BITSET` with the private bit is a DIFFERENT op word and
declines: it takes the caller's `val3` as the bitset
(kernel/futex/syscalls.c:133-135, v6.18.46) and has an -EINVAL for an empty one
(kernel/futex/waitwake.c:162-163, v6.18.46) this spec does not model.  The probe
issues it on the MISALIGNED address, where the bitset's -EINVAL and
`get_futex_key`'s coincide, and so does this pin.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- bitset_zero -/
theorem wake_bitset_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec misaligned_addr (Z_to_bv 64 (10 + FUTEX_PRIVATE_FLAG)) (Z_to_bv 64 1) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and on the ALIGNED word too, where only the bitset's own -EINVAL
(kernel/futex/waitwake.c:162-163, ahead of the `get_futex_key` at :165)
is left in Linux: the decline is the op word's, which `futex_spec` reads
before any address, and not the address's.
kernel: kernel/futex/syscalls.c:do_futex; kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem wake_bitset_aligned_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (10 + FUTEX_PRIVATE_FLAG)) (Z_to_bv 64 1) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- `FUTEX_WAKE_OP` declines: it writes to `uaddr2` through
`futex_atomic_op_inuser` (kernel/futex/waitwake.c:202-245, v6.18.46) before it looks
at a waiter.  The probe's registers: `nr_wake` 1 and, in the slot a wait
reads as `utime`, `nr_wake2` 1 — a word this command reads as a count.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_op -/
theorem wake_op_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (5 + FUTEX_PRIVATE_FLAG)) (Z_to_bv 64 1) (Z_to_bv 64 1)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- An op word outside `do_futex`'s switch — the probe's 0x40 with the
private bit — declines, and is NOT answered the -ENOSYS Linux gives it
(kernel/futex/syscalls.c:158, v6.18.46): the number is in the kernel's table and the
decline is this model's.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- badop -/
theorem bad_op_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    futex_spec futex_addr (Z_to_bv 64 (0x40 + FUTEX_PRIVATE_FLAG)) (Z_to_bv 64 1) (Z_to_bv 64 0)
        (futex_input []) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- EVERY op word but the two private ones declines, on every address,
value and timeout: every other command of `do_futex`'s switch
(kernel/futex/syscalls.c:125-158) is either unanswerable here or -ENOSYS
in Linux, and both are declines.  Symbolic in the op, so the case split
is by hand.
kernel: kernel/futex/syscalls.c:do_futex@v6.18.46 -/
theorem other_ops_are_unmodeled (uaddr op val utime : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect)
    (hwake : op ≠ Z_to_bv 64 FUTEX_WAKE_PRIVATE) (hwait : op ≠ Z_to_bv 64 FUTEX_WAIT_PRIVATE) :
    futex_spec uaddr op val utime i m o ↔ o = Unmodeled := by
  have h1 : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) = false := by
    simp only [bv_eqb, beq_eq_false_iff_ne, ne_eq]
    exact hwake
  have h2 : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) = false := by
    simp only [bv_eqb, beq_eq_false_iff_ne, ne_eq]
    exact hwait
  unfold futex_spec
  rw [h1, h2]
  simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-! ## The dispatcher: number 98, four registers read, two not

`__NR_futex` is 98 (include/uapi/asm-generic/unistd.h:270-271, v6.18.46).  The table
hands `futex_spec` a0..a3 and never a4, a5: `do_futex` passes `uaddr2`
only to commands outside the two words and overwrites `val3` on both
(kernel/futex/syscalls.c:127, :132, v6.18.46). -/

/-- Syscall 98 with a private wake reaches the wake arm and answers 0.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake -/
theorem sysno_98_is_futex (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (futex_input [futex_addr, Z_to_bv 64 FUTEX_WAKE_PRIVATE, 1, 0, 0, 0]) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- Junk in `uaddr2` and `val3` beside the junk timeout changes nothing on
a wake: neither register reaches the arm.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_junk -/
theorem sysno_98_ignores_uaddr2_and_val3 (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (futex_input [futex_addr, Z_to_bv 64 FUTEX_WAKE_PRIVATE, 1,
                               Z_to_bv 64 0xdeadbeef, Z_to_bv 64 0xbadc0de, Z_to_bv 64 0xffffffff]) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_norm

/-- Syscall 98 with a private wait on a mismatched word is -EAGAIN with the
read on the ledger, through the table.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem sysno_98_wait_is_eagain (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (futex_input [futex_addr, Z_to_bv 64 FUTEX_WAIT_PRIVATE, 8, 0, 0, 0]) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- …and through the table a forged 0 on that wait is refused, as
`wait_mismatch_is_not_zero` refuses it on the arm.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- wait_eagain -/
theorem sysno_98_wait_is_not_zero (m m' : Model) (evs : List event) :
    ¬ syscall_spec (futex_input [futex_addr, Z_to_bv 64 FUTEX_WAIT_PRIVATE, 8, 0, 0, 0]) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-- Junk in `uaddr2` and `val3` changes nothing on a wait either: `do_futex`
overwrites `val3` on the `FUTEX_WAIT` arm (kernel/futex/syscalls.c:127)
and hands `futex_wait` no `uaddr2` (:130).  The op is spelled as its
value, 128, so that the statement names only constants the cited text
spells; it is `FUTEX_WAIT | FUTEX_PRIVATE_FLAG`
(include/uapi/linux/futex.h:30).
kernel: kernel/futex/syscalls.c:do_futex; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem sysno_98_wait_ignores_uaddr2_and_val3 (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (futex_input [futex_addr, 128, 8, 0, Z_to_bv 64 0x902, 2306]) m o
      ↔ o = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)]
                 (mkEffect (errno_ret EAGAIN) [] [])) m [] := by
  sys_norm

/-- The table does NOT narrow the op the way it narrows an fd: a register
of 2^32 + 129 is refused the 0 a `fd32`-style cast would have produced.
The pin is stated as the refusal of that answer, because the decline
itself is `op_high_half_is_unmodeled` above and a decline stated through
the table takes the register shape `tools/check_decline_registers.py`
reads, which is reserved for numbers with no arm.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_high -/
theorem sysno_98_op_is_not_narrowed (m m' : Model) (evs : List event) :
    ¬ syscall_spec (futex_input [futex_addr, Z_to_bv 64 (2 ^ 32 + FUTEX_WAKE_PRIVATE), 1, 0, 0, 0]) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) m' evs) := by
  sys_refute

/-! ## The premise: the clone gates grant no shared mm, and no io_uring arm

The empty waiter set (file header) rests on nothing being able to queue a
waiter on this mm's private keys: no second task sharing the mm, and no
io_uring request waiting on the task's behalf.  The first half is pinned
the way Rocq pins it, on the two clone gates of `Sys/Kernel/Fork.lean`:
the one word `clone_fork_flags_b` accepts and the `flags` field of the one
image `clone3_fork_args_b` accepts both have `CLONE_VM` clear, so the child
either arm admits gets its own mm.  The two pins are Rocq's twins, name for
name; a later change widening either gate to a mask, or admitting a second
word, breaks the build here rather than nowhere — under a whole `lake
build`, or this module's own: `tools/lean_mutate.py --spec Kernel/Fork`
builds only `Sys/Kernel/Fork.lean` and `Checks/Cases/Kernel/Fork.lean`, so
its score never reaches these twins, and the widened gates that fail them
(a mask that clears the bit before the test, `SIGCHLD | CLONE_VM` as the
admitted word, the `flags` conjunct dropped from the image gate) were
built by hand in review.  Beside each twin stands
the refusal it implies, stated on the arm for `clone` and on the image gate
for `clone3`: a word or image carrying `CLONE_VM` is declined, for every
input, model and outcome.  The second half is the table's: it has no arm
for `io_uring_setup` (425) or `io_uring_enter` (426), and the four io_uring
pins that follow say so in the two shapes
`tools/check_decline_registers.py` reads — the table lookup, and the
universal decline through the dispatcher that `Dispatch.dispatch_unmodeled`
derives from it — so that a `lean: port io_uring …` PR fails this file's
build and that tool both, beside the paragraph that says why it matters.
Those declines are the MODEL's, not Linux's: each dispatcher pin's
evidence is the syscall number's definition, the one kernel fact its
statement carries. -/

/-- The `clone` gate admits one flag word, `SIGCHLD`, and that word has
`CLONE_VM` clear: a child the arm admits does not share the caller's mm
(`copy_mm`, kernel/fork.c:1520, v6.18.46, shares `current->mm` only
under `CLONE_VM` at :1543-1544 and `dup_mm`s otherwise, :1547), so it can
hold no private key of this task's.  Rocq states the test as
`Z.land (bv_unsigned flags) CLONE_VM = 0`; here it is the `bv_and` on the
word, the spelling every mask test of this tree uses (`Sys/Mm/Mmap.lean`'s
header says why the two agree below `2^64`).
rocq-twin: clone_fork_gate_grants_no_shared_mm -/
theorem clone_fork_gate_grants_no_shared_mm (flags : word)
    (h : Sys.Kernel.Fork.clone_fork_flags_b flags = true) :
    bv_unsigned (bv_and flags (Z_to_bv 64 CLONE_VM)) = 0 := by
  unfold Sys.Kernel.Fork.clone_fork_flags_b at h
  rw [(bv_eqb_eq _ _).1 h]
  decide

/-- The `clone3` gate admits one image, whose `flags` field is 0, and 0 has
`CLONE_VM` clear: the same fact for the other entry point, in the same
`bv_and` spelling of Rocq's `Z.land` test.
rocq-twin: clone3_fork_gate_grants_no_shared_mm -/
theorem clone3_fork_gate_grants_no_shared_mm (bs : List byte)
    (h : Sys.Kernel.Fork.clone3_fork_args_b bs = true) :
    bv_unsigned (bv_and (Sys.Kernel.Fork.clone_args_field bs 0) (Z_to_bv 64 CLONE_VM)) = 0 := by
  unfold Sys.Kernel.Fork.clone3_fork_args_b at h
  simp only [Bool.and_eq_true] at h
  have h0 : w_is0 (Sys.Kernel.Fork.clone_args_field bs 0) = true := h.1.1.1.1.1.1.1.1.1.1
  unfold w_is0 at h0
  rw [(bv_eqb_eq _ _).1 h0]
  decide

/-- The refusal the twin above implies, stated on the arm: a `clone` word
carrying `CLONE_VM` is not the one word the gate accepts, so the arm
declines it whatever the input and model.  For such a word Linux accepts,
it shares the mm (`copy_mm`, kernel/fork.c:1543-1545, v6.18.46; the words
`copy_process` refuses first with -EINVAL, :1951-1998, never reach it);
this model answers none of them, which is what keeps the waiter set empty.
A widening of the gate to a mask that admits the bit fails here beside the
twin.  `clone_vm_declines` in `Checks/Cases/Kernel/Fork.lean` is the same
refusal at the one word a probe drives, `SIGCHLD | CLONE_VM`.
kernel: kernel/fork.c:copy_mm@v6.18.46 -/
theorem clone_vm_word_declines (flags : word)
    (hvm : bv_unsigned (bv_and flags (Z_to_bv 64 CLONE_VM)) ≠ 0)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    Sys.Kernel.Fork.clone_spec flags i m o ↔ o = Unmodeled := by
  have hg : Sys.Kernel.Fork.clone_fork_flags_b flags = false := by
    cases hb : Sys.Kernel.Fork.clone_fork_flags_b flags with
    | false => rfl
    | true => exact absurd (clone_fork_gate_grants_no_shared_mm flags hb) hvm
  simp only [Sys.Kernel.Fork.clone_spec.eq_1, hg, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-- The same refusal at the other entry point, stated on the image gate: a
`struct clone_args` whose `flags` field carries `CLONE_VM` is not the one
image `clone3_fork_args_b` accepts, so `clone3_spec` declines it after the
read.  `clone3_flags_vm_declines` in `Checks/Cases/Kernel/Fork.lean` is
that decline at the one image a probe drives, `flags = CLONE_VM`; this pin
is the gate's own refusal, for every image carrying the bit.
kernel: kernel/fork.c:copy_mm@v6.18.46 -/
theorem clone3_vm_image_is_refused (bs : List byte)
    (hvm : bv_unsigned (bv_and (Sys.Kernel.Fork.clone_args_field bs 0) (Z_to_bv 64 CLONE_VM)) ≠ 0) :
    Sys.Kernel.Fork.clone3_fork_args_b bs = false := by
  cases hb : Sys.Kernel.Fork.clone3_fork_args_b bs with
  | false => rfl
  | true => exact absurd (clone3_fork_gate_grants_no_shared_mm bs hb) hvm

/-- `io_uring_setup` (425) has no arm in the Lean table: no ring can exist,
so no `IORING_OP_FUTEX_WAIT` can queue a task-less waiter and no SQPOLL or
io-wq thread sharing the mm is ever created.
model: the Lean table's own contents; the reason it matters is the file header. -/
theorem io_uring_setup_has_no_arm : lookup_arm spec_table 425 = none := rfl

/-- `io_uring_enter` (426) has no arm in the Lean table: nothing can be
submitted to a ring.
model: the Lean table's own contents; the reason it matters is the file header. -/
theorem io_uring_enter_has_no_arm : lookup_arm spec_table 426 = none := rfl

/-- Every `io_uring_setup` call declines through the dispatcher: no arm for
`__NR_io_uring_setup`, 425.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_uring_setup@v6.18.46 -/
theorem io_uring_setup_is_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 425 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; exact io_uring_setup_has_no_arm)

/-- Every `io_uring_enter` call declines through the dispatcher: no arm for
`__NR_io_uring_enter`, 426.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_uring_enter@v6.18.46 -/
theorem io_uring_enter_is_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 426 → syscall_spec i m Unmodeled :=
  fun h => dispatch_unmodeled spec_table i m (by rw [h]; exact io_uring_enter_has_no_arm)

/-! ## The Rocq twins, and the ledger tie

Three statements over a symbolic address, input and model.  Their gates
are open Bools that `sys_norm` cannot decide, so each is read by hand:
`futex_key_check_reading` fixes what the shared key check admits for any
continuation, and the wait arm's own continuation — the read, the value
test and the copy-in — is read inline where it is needed. -/

/-- `futex_key_check`'s three outcomes on a symbolic address: -EINVAL when
misaligned, -EFAULT when aligned and out of range, and the continuation's
own answer otherwise: `get_futex_key`'s two refusals in its own order
(kernel/futex/core.c:569-570 then :573-574, v6.18.46), the reading the
three statements below share, with the order pinned on a concrete address
by `misaligned_past_range_is_einval` above.  The range's width is spelled
through the twin's `FUTEX_WORD_SIZE_nat`, one value with `FUTEX_WORD_SIZE`
by `futex_word_size_nat_ok`, which the proof rewrites first.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem futex_key_check_reading (uaddr : word) (k : Sys SyscallEffect) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) :
    futex_key_check uaddr k i m o ↔
      (futex_aligned_b uaddr = false ∧ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
      ∨ (futex_aligned_b uaddr = true ∧ access_okb uaddr (FUTEX_WORD_SIZE_nat : Int) = false
          ∧ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [])
      ∨ (futex_aligned_b uaddr = true ∧ access_okb uaddr (FUTEX_WORD_SIZE_nat : Int) = true
          ∧ k i m o) := by
  rw [futex_word_size_nat_ok]
  unfold futex_key_check
  cases futex_aligned_b uaddr <;> cases access_okb uaddr FUTEX_WORD_SIZE <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, err_ret, ret_only, pure_iff,
      true_and, false_and, and_false, or_false, false_or, iff_self]

/-- THREE ANSWERS AND NO FOURTH, for every address at once.  Rocq's
`futex_wake_private_answers`: a private wake is -EINVAL, -EFAULT or 0, the
model comes back unchanged and the event list is empty.  That the count is
0 rather than the errno of an unresolvable page is the content: no arm
depends on what is mapped.
rocq-twin: futex_wake_private_answers -/
theorem futex_wake_private_answers (uaddr : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    futex_wake_private_spec uaddr i m (Ok eff m' evs) →
    m' = m ∧ evs = [] ∧
      (eff = mkEffect (errno_ret EINVAL) [] [] ∨ eff = mkEffect (errno_ret EFAULT) [] []
        ∨ eff = mkEffect (Z_to_bv 64 0) [] []) := by
  intro h
  unfold futex_wake_private_spec at h
  rw [futex_key_check_reading] at h
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · simp only [outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · simp only [outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
  · simp only [ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩

/-- A WAIT NEVER SUCCEEDS, for every address and every expected value at
once.  Rocq's `futex_wait_private_answers`: a private wait this model
answers has exactly one non-gate answer, -EAGAIN carrying the four-byte
copy-in, so a run in which the wait slept and was woken is not an outcome
this spec admits on any input.  Past the key check the continuation is
read inline: an unreadable word admits no `Ok`, a readable one is
`record_copyins` over the value test, and only the mismatch branch
answers.
rocq-twin: futex_wait_private_answers -/
theorem futex_wait_private_answers (uaddr val : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    futex_wait_private_spec uaddr val i m (Ok eff m' evs) →
    m' = m ∧ evs = [] ∧
      (eff = mkEffect (errno_ret EINVAL) [] [] ∨ eff = mkEffect (errno_ret EFAULT) [] []
        ∨ eff = with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] [])) := by
  intro h
  unfold futex_wait_private_spec at h
  rw [futex_key_check_reading] at h
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · simp only [outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · simp only [outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
  · rw [bind_input_iff] at h
    generalize hr : read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h
    cases r with
    | none =>
      simp only [unmodeled_iff, reduceCtorEq] at h
    | some uval =>
      dsimp only at h
      unfold record_copyins at h
      cases hv : bv_eqb (le_bytes_to_word uval) val
      · rw [hv] at h
        simp only [Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, bind_pure_iff, pure_iff,
          outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩
      · rw [hv] at h
        simp only [↓reduceIte, bind_unmodeled_iff, reduceCtorEq] at h

/-- THE LEDGER IS EXACTLY WHAT `futex_wait_reads_b` SAYS, on every answered
call: the four bytes at `uaddr` when the call is an answered private wait
past both gates, and nothing otherwise.  Rocq proves this as
`Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact` for its OCaml
tester; here it is the only consumer of the predicate, and what makes the
predicate a theorem about the ledger rather than a second opinion on it.
The wake half is `futex_wake_private_answers` and `futex_wake_not_wait`;
the wait half reads the key check and then the continuation inline, as
`futex_wait_private_answers` does, because the ledger of each arm is
decided by which gate refused it.
kernel: kernel/futex/futex.h:futex_get_value_locked; kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem futex_copyins_exact (uaddr op val utime : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    futex_spec uaddr op val utime i m (Ok eff m' evs) →
    eff.eff_copyins = (if futex_wait_reads_b uaddr op utime then [(uaddr, FUTEX_WORD_SIZE_nat)] else []) := by
  intro h
  unfold futex_spec at h
  unfold futex_wait_reads_b
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · rw [hwake] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · rw [hwait] at h
      simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    · rw [hwait] at h
      simp only [↓reduceIte, Bool.true_and] at h ⊢
      cases hu : w_is0 utime
      · rw [hu] at h
        simp only [Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      · rw [hu] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and] at h ⊢
        unfold futex_wait_private_spec at h
        rw [futex_key_check_reading] at h
        rcases h with ⟨ha, h⟩ | ⟨ha, hk, h⟩ | ⟨ha, hk, h⟩
        · simp only [outcome.Ok.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        · rw [futex_word_size_nat_ok] at hk
          simp only [outcome.Ok.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          simp only [ha, hk, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        · rw [futex_word_size_nat_ok] at hk
          simp only [ha, hk, Bool.and_true, ↓reduceIte]
          rw [bind_input_iff] at h
          generalize hr : read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h
          cases r with
          | none =>
            simp only [unmodeled_iff, reduceCtorEq] at h
          | some uval =>
            dsimp only at h
            unfold record_copyins at h
            cases hv : bv_eqb (le_bytes_to_word uval) (abi_low32 val)
            · rw [hv] at h
              simp only [Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, bind_pure_iff, pure_iff,
                outcome.Ok.injEq] at h
              obtain ⟨rfl, -, -⟩ := h
              rfl
            · rw [hv] at h
              simp only [↓reduceIte, bind_unmodeled_iff, reduceCtorEq] at h
  · rw [hwake] at h
    simp only [↓reduceIte] at h
    rw [futex_wake_not_wait op hwake]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨_, _, hc⟩ := futex_wake_private_answers uaddr i m eff m' evs h
    rcases hc with rfl | rfl | rfl <;> rfl

/-- THE LEDGER PREDICATE CLAIMS NOTHING FOR A TIMED WAIT: its `w_is0 utime`
conjunct makes `futex_wait_reads_b` false wherever `futex_spec` declines a
`FUTEX_WAIT_PRIVATE` for its timeout (`wait_with_timeout_is_unmodeled`),
so the predicate's read set is exactly the answered calls' and not the
kernel's — Linux does read the word of a timed wait, after the timeout is
fetched (`SYSCALL_DEFINE6(futex)`, kernel/futex/syscalls.c:196-207, v6.18.46).  Stated on the predicate itself, since
the spec has no answered outcome there for `futex_copyins_exact` to
compare, and that is why no mutation of this conjunct is observable through
the spec.
The op word is written as its numeral, 128 = FUTEX_WAIT | FUTEX_PRIVATE_FLAG
(include/uapi/linux/futex.h:11,26,30, v6.18.46).
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem futex_wait_reads_b_needs_null_timeout :
    futex_wait_reads_b futex_addr (Z_to_bv 64 128) (Z_to_bv 64 0x10000) = false := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Futex.Syscalls
