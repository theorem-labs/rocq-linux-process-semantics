import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Drivers.Char.Random — what `getrandom` admits, read off against Linux

Worked examples over `Sys.Drivers.Char.Random.getrandom_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Drivers/Char/Random.v`.  Not part of
the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f) throughout.

HOW THESE ARE STATED.  As in `Checks/Cases/Mm/Mprotect.lean`: the Lean tree
has no executable checker, so a check is stated on the relation itself, as
an `iff` over EVERY outcome `o`.  Where the admitted set is finite the
right-hand side lists it; where the environment chooses the bytes it is an
existential over the delivered list with the guard the kernel imposes on
its length, so one theorem still fixes both what is admitted and what is
refused.  Each decision gets that `iff`, closed by `sys_norm`, and a
refutation of the answer a lying kernel would give, closed by `sys_refute`;
the `iff` already excludes the lie, and the refutation is kept because it
is the shape a reader asks for and the shape the probe's `--mutate` cases
take.  `getrandom_spec` reads no model, so every pin quantifies over `m`;
the three twins of the Rocq examples name Rocq's `getrandom_model` because
Rocq does.

WHAT THE ROCQ FILE PINS AND WHAT IT PROBES.  Rocq keeps three examples —
the small request delivered in full and only in full, the inclusive edge
of the bound, and the large request's short count and -EINTR — and sends
the flag words, the zero-byte request, the unwritable destination and the
delivery shapes to `testing/syscall-check/tests/getrandom_spec.c` and
`getrandom_flags.c`.  The Lean tree has no replay harness yet, so this
file pins every arm, in the order the kernel decides them, and cites the
probe's `CASE` line where one records the same claim.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Drivers.Char.Random

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding and its errno list's, at low priority.  The gates — the flag
test, `modeled_rw_count`, `w_is0`, the bound test and `access_okb` — are
decided, never unfolded, so they are not registered.  The call fixture
`getrandom_call` and the byte walks over its zone are registered below,
beside their definitions.  The lines live here rather than in
`Tactic.lean`'s register on purpose: a port PR creates its own files and
edits no shared one, so that ports merge in any order. -/

attribute [sys_simp low] getrandom_spec.eq_1 getrandom_errnos.eq_1

/-! ## The constants these checks spell out -/

/-- The one flag the arm accepts beside 0.
kernel: include/uapi/linux/random.h:GRND_NONBLOCK@v6.18.46 -/
example : GRND_NONBLOCK = 1 := by decide
/-- The flag that selected the blocking pool, declined.
kernel: include/uapi/linux/random.h:GRND_RANDOM@v6.18.46 -/
example : GRND_RANDOM = 2 := by decide
/-- The one injectable errno.
kernel: include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
example : getrandom_errnos = [EINTR] := by decide
/-- The two errnos the refutations below offer and the arm never admits.
kernel: include/uapi/asm-generic/errno-base.h:EAGAIN,EFAULT@v6.18.46 -/
example : EAGAIN = 11 ∧ EFAULT = 14 := by decide

/-- 256, the getrandom(2) contract's figure and, through v5.17, the
kernel's own threshold — the `large_request = (nbytes > 256)` that
`extract_crng_user` carried at v4.17 and v5.17; at v6.18.46 the kernel's edge
is a page (`get_random_bytes_user`'s `ret % PAGE_SIZE == 0` test,
drivers/char/random.c:471, v6.18.46), and the `Sys/Drivers/Char/Random.lean`
docstring says why the spec keeps the intersection's 256.
model: the model's own bound at its numeral; the kernel reading is on `getrandom_small_max` -/
theorem getrandom_small_max_is_256 : getrandom_small_max = 256 := by decide

/-! ## Fixtures

Rocq's, name for name.  `getrandom_dest` is a writable landing zone at
4096, wide enough (512 bytes) for a request above the bound;
`getrandom_model` is the demo process, which the spec never reads;
`getrandom_call buflen` is one `getrandom(4096, buflen, 0)` whose readable
and writable views are both that zone; `some_bytes n` is `n` environment
bytes, all 7. -/

/-- A writable landing zone at 4096, wide enough for a request above
`getrandom_small_max`. -/
def getrandom_dest : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4608 then some 0 else none

/-- Rocq's `init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)`,
which is the Prelude's `demo_model`. -/
def getrandom_model : Model := demo_model

/-- One getrandom(4096, buflen, 0) over that zone. -/
def getrandom_call (buflen : Int) : SyscallInput :=
  SyscallInput.mkInput 278 [4096, Z_to_bv 64 buflen, 0, 0, 0, 0] getrandom_dest getrandom_dest

/-- `n` environment bytes, all the same.  IRREDUCIBLE on purpose:
`sys_norm`'s first pass decides every closed proposition it meets before
it rewrites inside it (`Simp.preDefault` runs `simpUsingDecide` ahead of
the children, Lean v4.34.0), and a closed equation about a 256-byte list
is decided by walking the list, one nested reduction per byte, past the
elaborator's recursion budget — a runtime error no `try` in `simp`
catches.  Irreducible, the list is opaque to that evaluation, the decide
gives up quietly, and what the pins need to know about the list is the
two rewrites `some_bytes_length` and `len_word_some_bytes` below. -/
@[irreducible] def some_bytes (n : Nat) : List byte := List.replicate n (Z_to_bv 8 7)

attribute [sys_simp low] getrandom_call.eq_1

/-! ### The zone, walked

The spec's one `match` is on `State.read_bytes_map i.in_wmem buf buflen`,
a closed TERM once the call is concrete — not a proposition `sys_norm`'s
first pass can decide, and a term its second pass would evaluate only
after evaluating the closed `errno_from` beneath it, which is the order
the `Tactic.lean` header says leaves an errno refutation open.  So the
walk's value at each request the pins name is pinned here by `decide` and
registered at the default priority: the `match` then reduces in the first
pass, and every pin below is plain `sys_norm` or `sys_refute`.  The values
are the zone's CURRENT bytes (zeroes), not the delivery; the spec ignores
them and only asks that they exist.

The walks are `decide +kernel`: a walk of a few hundred bytes is a few
hundred nested reductions, which exceeds the elaborator's default
recursion budget (`maxRecDepth`) while the kernel's reducer, which checks
the proof term either way, has no such budget.  The proof term is the
same `of_decide_eq_true rfl`; only which reducer runs it first differs.
Beside them, the two facts about `some_bytes` the pins need — its
length, and its `len_word` — as rewrites, because the list itself is
irreducible (its docstring says why) and nothing else may look inside
it. -/

/-- The zone answers a 16-byte request at 4096.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_16 :
    read_bytes_map getrandom_dest 4096 16 = some (List.replicate 16 0) := by decide +kernel
/-- ... a 256-byte request ...
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_256 :
    read_bytes_map getrandom_dest 4096 256 = some (List.replicate 256 0) := by decide +kernel
/-- ... a 257-byte request ...
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_257 :
    read_bytes_map getrandom_dest 4096 257 = some (List.replicate 257 0) := by decide +kernel
/-- ... and a 300-byte request, all inside its 512 bytes.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_300 :
    read_bytes_map getrandom_dest 4096 300 = some (List.replicate 300 0) := by decide +kernel
/-- A 16-byte request at 4600 runs off the zone's end at 4608: the walk
fails, and the spec declines.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_4600_16 :
    read_bytes_map getrandom_dest 4600 16 = none := by decide +kernel
/-- A 16-byte request at 8192 is wholly outside the zone.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_8192_16 :
    read_bytes_map getrandom_dest 8192 16 = none := by decide +kernel

/-- `some_bytes n` is `n` bytes long: read off `List.replicate`'s length
lemma, never by walking the list (the `some_bytes` docstring says why).
model: the length of the fixture's byte list, a rewrite for the first pass -/
@[sys_simp] theorem some_bytes_length (n : Nat) : (some_bytes n).length = n := by
  unfold some_bytes
  simp only [List.length_replicate]

/-- ... and its `len_word` is that length as a word.
model: the fixture's delivered count as a word, a rewrite for the first pass -/
@[sys_simp] theorem len_word_some_bytes (n : Nat) : len_word (some_bytes n) = Z_to_bv 64 (n : Int) := by
  unfold len_word some_bytes
  simp only [List.length_replicate]

/-- A zero-byte walk reads nothing and succeeds over EVERY memory, at
every address: the two loops are handed no fuel.  General, so the
zero-length pins below quantify over the input.
model: `State.read_bytes_map` at length 0, by unfolding -/
@[sys_simp] theorem read_bytes_map_zero (mp : word → Option byte) (a : word) :
    read_bytes_map mp a 0 = some [] := rfl

/-! ## Gate 1: the flag word

`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
(drivers/char/random.c:1385-1412, v6.18.46) reads `flags` before anything else: a
bit outside GRND_NONBLOCK, GRND_RANDOM and GRND_INSECURE is -EINVAL
(:1390-1391), GRND_INSECURE with GRND_RANDOM is -EINVAL (:1397-1398),
and GRND_NONBLOCK is read only under `!crng_ready()` (:1400-1402).  The
spec answers two flag words, 0 and GRND_NONBLOCK, identically, and
declines every other, so the pins here are of two kinds: that
GRND_NONBLOCK changes nothing, and that each other word is `Unmodeled`
whatever the kernel would answer — a decline the docstrings justify one
word at a time. -/

/-- GRND_NONBLOCK (1) admits exactly what 0 admits: the only reader of the
flag is the -EAGAIN return under `!crng_ready()` (:1400-1402), and the
pool is treated as ready before user code runs, so the flag never reaches
a branch that could answer differently.
probe: testing/syscall-check/tests/getrandom_flags.c#conform -- 1 ok -/
theorem nonblock_is_plain (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 1 (getrandom_call 16) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m [] ∧ (bs.length : Int) = 16 := by
  sys_norm

/-- The -EAGAIN GRND_NONBLOCK exists for (:1401-1402) is refused: it needs
`!crng_ready()` (:1400; the macro at :90), the pool not yet initialised,
which the model assumes never holds once user code runs.
kernel: drivers/char/random.c:getrandom,crng_ready@v6.18.46 -/
theorem nonblock_eagain_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 1 (getrandom_call 16) m
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- GRND_RANDOM (2) is declined.  At v6.18.46 the flag has no effect: past
the mask test (:1390-1391) and the conflict test (:1397-1398) nothing
reads it, and the uapi header's own comment says so
(include/uapi/linux/random.h:51), so Linux answers the plain read here.
The decline is Rocq's, made for the blocking /dev/random pool the flag
once selected in kernels this file has not read; declining what Linux
answers costs coverage and never soundness, and the probe records the
fail-closed verdict.
probe: testing/syscall-check/tests/getrandom_flags.c#fail-closed -- 2 -/
theorem grnd_random_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 2 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Offering the plain read Linux gives under GRND_RANDOM yields
`Unmodeled`, not an admission.
probe: testing/syscall-check/tests/getrandom_flags.c#fail-closed -- 2 -/
theorem grnd_random_delivery_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 2 i m (Ok (mkEffect 16 [(4096, some_bytes 16)] []) m' evs) := by
  sys_refute

/-- GRND_NONBLOCK|GRND_RANDOM (3) is declined too — the word a bit-test
acceptor of GRND_NONBLOCK would wave through.  Linux takes it: both bits
are inside the mask (:1390), the pair is not the -EINVAL pair (:1397),
and the plain read follows.
probe: testing/syscall-check/tests/getrandom_flags.c#fail-closed -- 3 -/
theorem nonblock_random_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 3 i m o ↔ o = Unmodeled := by
  sys_norm

/-- GRND_INSECURE (4) is declined: Linux accepts it (:1390) and skips the
readiness gate for it (:1400), answering the plain read; the model
declines the flag rather than modelling a pool that may not be ready.
probe: testing/syscall-check/tests/getrandom_flags.c#fail-closed -- 4 -/
theorem grnd_insecure_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 4 i m o ↔ o = Unmodeled := by
  sys_norm

/-- An unknown bit (256) is declined where Linux answers -EINVAL
(:1390-1391).  The decline precedes the errno alternative — this is the
word the probe's comment names as the one a spec with the gate behind the
errno would silently let through.
probe: testing/syscall-check/tests/getrandom_flags.c#fail-closed -- 256 -/
theorem unknown_flag_bit_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 256 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Offering the -EINVAL Linux gives for the unknown bit yields
`Unmodeled`: the model does not answer it, it declines.
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem unknown_flag_bit_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 256 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A set high half, `2^32`, is declined.  `flags` is `unsigned int` at
the boundary (:1385), so Linux sees 0 and answers the plain read; the
spec compares the whole 64-bit word.  A narrowing, not a disagreement.
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem high_half_flags_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 (Z_to_bv 64 (2 ^ 32)) i m o ↔ o = Unmodeled := by
  sys_norm

/-- The plain read Linux gives for the truncated word is refused.
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem high_half_flags_delivery_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 (Z_to_bv 64 (2 ^ 32)) i m
        (Ok (mkEffect 16 [(4096, some_bytes 16)] []) m' evs) := by
  sys_refute

/-! ### The flag gate precedes the length

Linux tests the flags (:1390-1398) before it imports the buffer (:1408)
or counts it (`get_random_bytes_user`, :440-441), so a zero-length call
with a bad flag word is -EINVAL, and a zero-length call under GRND_RANDOM
is 0.  The spec decides the flags first too, and declines both. -/

/-- GRND_RANDOM at zero length: Linux answers 0 (:1390 admits the bit,
:440-441 returns 0 for the empty iterator); the model declines the flag
before it looks at the length.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem grnd_random_zero_length_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    getrandom_spec 4096 0 2 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The 0 Linux answers there is refused.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem grnd_random_zero_length_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 0 2 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- An unknown bit at zero length: Linux answers -EINVAL (:1390-1391)
before the length is read; the model declines, and the -EINVAL is refused.
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem unknown_flag_bit_zero_length_einval_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getrandom_spec 4096 0 256 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## Gate 2: the transfer bound

`Uaccess.rw_bytes_max` is a modelling bound, not a kernel one: Linux
clamps a getrandom request at MAX_RW_COUNT in `import_ubuf`
(lib/iov_iter.c:1435-1436, v6.18.46) and delivers.  Above 128 KiB the spec declines
before it looks at memory; at 128 KiB it judges.  The gate itself is
pinned at its own edges in `Checks/Cases/Uaccess.lean`; here it is
pinned on the arm. -/

/-- One byte over the bound is declined for every input and every model:
the gate fires before the walk, so no memory rescues it.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem over_the_bound_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 131073 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A short delivery there is refused whatever the memory.  Linux clamps
and delivers (`import_ubuf`, :1435-1436); a count of five could only be a
copy that faulted after five bytes (`copy_to_iter`, :465-468), since the
signal break (:471-473) leaves a page multiple.  Both are declined here.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem over_the_bound_delivery_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 131073 0 i m (Ok (mkEffect 5 [(4096, some_bytes 5)] []) m' evs) := by
  sys_refute

/-- THE BOUND IS INCLUSIVE ON THE ARM: at exactly 128 KiB, over any input
whose buffer the walk finds writable, the call is judged as a large
request — the -EINTR alternative and a delivery of one byte up to the
whole request.  Stated on a hypothesis about the walk because the
128 KiB zone is not a fixture worth evaluating; the witness below shows
the hypothesis is satisfiable.  The walk is handed to `simp` by the
hypothesis before `sys_norm` reads the arm, for the reason the zone
section gives.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem at_the_bound_is_judged (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (bs : List byte) (hw : read_bytes_map i.in_wmem 4096 131072 = some bs) :
    getrandom_spec 4096 131072 0 i m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m []
       ∨ ∃ bs' : List byte, o = Ok (mkEffect (len_word bs') [(4096, bs')] []) m []
           ∧ 1 ≤ (bs'.length : Int) ∧ (bs'.length : Int) ≤ 131072) := by
  simp +decide only [getrandom_spec.eq_1, ↓reduceIte, bind_input_iff, hw]
  sys_norm

/-- The walk of an everywhere-writable memory succeeds at any length: the
witness that `at_the_bound_is_judged`'s hypothesis is satisfiable, by
induction rather than by evaluating a 128 KiB list.
model: `State.read_bytes_aux` over an everywhere-writable map, by induction on the fuel -/
theorem read_bytes_aux_all_writable (a : word) (k : Nat) :
    read_bytes_aux (fun _ => some (Z_to_bv 8 0)) a k = some (List.replicate k (Z_to_bv 8 0)) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [read_bytes_aux, ih, List.replicate_succ]

/-- ... and so does the chunked walk the spec runs, at the bound.
model: `State.read_bytes_map` over an everywhere-writable map at 131072 bytes, through `read_bytes_map_eq` -/
theorem all_writable_walks_the_bound :
    read_bytes_map (fun _ => some (Z_to_bv 8 0)) 4096 131072
      = some (List.replicate 131072 (Z_to_bv 8 0)) := by
  rw [read_bytes_map_eq]
  exact read_bytes_aux_all_writable 4096 (word_to_nat 131072)

/-! ## The destination walk

`import_ubuf` tests the range (lib/iov_iter.c:1437-1438, v6.18.46) and
`get_random_bytes_user` copies into it, returning what landed or -EFAULT
when nothing did (drivers/char/random.c:481, v6.18.46).  The spec asks instead
whether the WHOLE buffer is writable, and declines when it is not: a
destination that faults part-way is a program bug, and Linux's short
count or -EFAULT there is declined rather than contradicted.  The probe
records both shapes as fail-closed. -/

/-- A buffer half inside the zone (4600, 16 bytes; the zone ends at 4608)
is declined.  Linux would copy what lands before the fault and return that
count (`copy_to_iter` stops at the fault, :456; :481 returns what landed) —
how many bytes that is depends on where the fault falls, which the fixture's
edge at 4608, inside a page, does not model.
probe: testing/syscall-check/tests/getrandom_spec.c#fail-closed --mutate getrandom:wmem-hide:a0+8:8,ret=1,trunc-writes:1 -- 16 -/
theorem half_writable_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4600 16 0 (getrandom_call 16) m o ↔ o = Unmodeled := by
  sys_norm

/-- The short count Linux answers over a half-writable buffer — the probe's
mutation spells it as one byte landed — is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#fail-closed --mutate getrandom:wmem-hide:a0+8:8,ret=1,trunc-writes:1 -- 16 -/
theorem half_writable_short_count_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4600 16 0 (getrandom_call 16) m
        (Ok (mkEffect 1 [(4600, some_bytes 1)] []) m' evs) := by
  sys_refute

/-- A buffer wholly outside the zone (8192) is declined.  Linux copies
nothing and answers -EFAULT (:481).
probe: testing/syscall-check/tests/getrandom_spec.c#fail-closed --mutate getrandom:wmem-none,ret=0,drop-writes -- 16 -/
theorem unwritable_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 8192 16 0 (getrandom_call 16) m o ↔ o = Unmodeled := by
  sys_norm

/-- The -EFAULT Linux answers there (:481, a copy that moved nothing) is
refused: the model declines the call rather than answering it.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem unwritable_efault_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 8192 16 0 (getrandom_call 16) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## The zero-byte request

`import_ubuf` range-tests the zero-length buffer (lib/iov_iter.c:1437-1438,
v6.18.46) and `get_random_bytes_user` returns 0 for the empty iterator
(drivers/char/random.c:440-441, v6.18.46), so the answer is 0 in range and -EFAULT
past `State.TASK_SIZE` — and -EINTR beside either, because the readiness
wait (:1403) comes before the import (:1408).  `wait_for_random_bytes`
(:136-147) sleeps interruptibly (:142) and its -ERESTARTSYS becomes the
-EINTR the program sees in `arch_do_signal_or_restart`
(arch/riscv/kernel/signal.c:438-443, v6.18.46) when the handler lacks
SA_RESTART.
The walk of zero bytes succeeds over every memory (`read_bytes_map_zero`),
so these pins quantify over the input.

The range half is a v6.18.46 reading and the pins below say so: the
`access_ok` on a zero-length request arrived at v5.19 with
`import_single_range`, and through v5.18 the kernel answered 0 at any
address: the `while (nbytes)` loop of `extract_crng_user` at v4.17 and
v5.17, and the `if (!nbytes) return 0;` opening `get_random_bytes_user`
at v5.18, run no range test.  The arm is Rocq's, and
`bugs/getrandom-zero-length-refuses-the-pre-v5-19-zero.md` records what
it refuses. -/

/-- In range, exactly 0 or -EINTR, with no write entry either way.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; lib/iov_iter.c:import_ubuf; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem zero_length_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 0 0 i m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m [] ∨ o = Ok (mkEffect 0 [] []) m []) := by
  sys_norm

/-- The 0 is admitted ...
probe: testing/syscall-check/tests/getrandom_spec.c#conform -- 0 -/
theorem zero_length_zero_admitted (i : SyscallInput) (m : Model) :
    getrandom_spec 4096 0 0 i m (Ok (mkEffect 0 [] []) m []) := by
  sys_norm

/-- ... and so is the interrupt before the import.
probe: testing/syscall-check/tests/getrandom_spec.c#conform --mutate getrandom:ret=-EINTR -- 0 -/
theorem zero_length_eintr_admitted (i : SyscallInput) (m : Model) :
    getrandom_spec 4096 0 0 i m (Ok (mkEffect (errno_ret EINTR) [] []) m []) := by
  sys_norm

/-- The canonical zero-byte shape carries no write entry: an empty entry
at the buffer is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:smuggle-write:a0:0 -- 0 -/
theorem zero_length_empty_write_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 0 0 i m (Ok (mkEffect 0 [(4096, [])] []) m' evs) := by
  sys_refute

/-- A byte delivered against a zero-byte request is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=1,smuggle-write:a0:1 -- 0 -/
theorem zero_length_delivered_byte_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 0 0 i m (Ok (mkEffect 1 [(4096, some_bytes 1)] []) m' evs) := by
  sys_refute

/-- A bare nonzero non-errno return is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=1 -- 0 -/
theorem zero_length_bare_one_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 0 0 i m (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- AT the top of the address space, `buf = 2^47` with no bytes:
`__access_ok` admits the range (`addr <= limit - 0`), so it is 0 or
-EINTR as in range.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok; drivers/char/random.c:get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem zero_length_at_the_top_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec (Z_to_bv 64 (2 ^ 47)) 0 0 i m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m [] ∨ o = Ok (mkEffect 0 [] []) m []) := by
  sys_norm

/-- One byte past it, `__access_ok` refuses the range and `import_ubuf`
answers -EFAULT (lib/iov_iter.c:1437-1438), beside the -EINTR of the wait
that precedes the import.  At v6.18.46; kernels through v5.18 answer 0
here (the section header), which this iff excludes.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem zero_length_past_the_top_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 i m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m []
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  sys_norm

/-- The 0 an arm without the range test answers past the top is refused.
Stable kernels through v5.18 ARE that arm, so this pin fixes the model's
v6.18.46 answer and not the supported set's:
`bugs/getrandom-zero-length-refuses-the-pre-v5-19-zero.md`.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem zero_length_past_the_top_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- ... and -EFAULT in range is refused: the range verdict is the only
source of it at zero length, and the range is fine.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem zero_length_in_range_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 0 0 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## The small request: full delivery, and only full delivery

A request of at most `getrandom_small_max` bytes.  `get_random_bytes_user`
copies a request of at most CHACHA_KEY_SIZE (32) bytes straight out of the
key material (drivers/char/random.c:455-458, v6.18.46) and a larger one through the
block loop (:460-476), whose only early exit is `signal_pending` after a
whole page has landed (:471-473); so no request of at most a page is ever
short, and none is -EINTR (the wait at :1403 is behind the readiness
gate).  The environment chooses the BYTES; the pins fix their number. -/

/-- Sixteen bytes: any sixteen, and nothing else.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem small_request_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 0 (getrandom_call 16) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m [] ∧ (bs.length : Int) = 16 := by
  sys_norm

/-- The full delivery is admitted.
probe: testing/syscall-check/tests/getrandom_spec.c#conform -- 16 -/
theorem small_request_full_delivery_admitted (m : Model) :
    getrandom_spec 4096 16 0 (getrandom_call 16) m
      (Ok (mkEffect 16 [(4096, some_bytes 16)] []) m []) := by
  sys_norm

/-- The short count Linux cannot produce below the bound is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=5,trunc-writes:5 -- 16 -/
theorem small_request_short_count_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 5 [(4096, some_bytes 5)] []) m' evs) := by
  sys_refute

/-- ... and so is the interrupt: a small request never reaches a
`signal_pending` test.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=-EINTR,drop-writes -- 16 -/
theorem small_request_eintr_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- Over-delivery stays out: the loop stops when the iterator is empty
(:467) and the direct copy is capped by the iterator (:456).
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=17,grow-writes:1 -- 16 -/
theorem small_request_over_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 17 [(4096, some_bytes 17)] []) m' evs) := by
  sys_refute

/-- A nonzero request never "succeeds" with nothing delivered: the bare 0
(`ret ? ret : -EFAULT`, :481, never returns 0 for a nonempty iterator).
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=0,drop-writes -- 16 -/
theorem small_request_bare_zero_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- ... nor with an empty write entry.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=0,trunc-writes:0 -- 16 -/
theorem small_request_empty_write_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m (Ok (mkEffect 0 [(4096, [])] []) m' evs) := by
  sys_refute

/-- The return IS the delivered length: 2 with one byte written is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=2,trunc-writes:1 -- 16 -/
theorem small_request_ret_disagrees_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 2 [(4096, some_bytes 1)] []) m' evs) := by
  sys_refute

/-- The bytes land AT the buffer: a delivery one byte up is refused.
`import_ubuf(ITER_DEST, ubuf, len, &iter)` (:1408) makes `ubuf` itself the
destination.  (The probe's `shift-writes:1` case bundles this with a short
count; the pin isolates the address.)
kernel: drivers/char/random.c:getrandom; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem small_request_wrong_address_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 16 [(4097, some_bytes 16)] []) m' evs) := by
  sys_refute

/-- ... in ONE entry: a delivery split across two is refused — one
`copy_to_iter` into one contiguous `ubuf` (:456, :464).  (The probe's
`split-writes` case bundles this with a short count; the pin isolates the
split.)
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem small_request_split_writes_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 16 [(4096, some_bytes 8), (4104, some_bytes 8)] []) m' evs) := by
  sys_refute

/-- No memory ledger rides along: a zero-fill range beside the delivery
is refused ...
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:smuggle-zeros:a0:1 -- 16 -/
theorem small_request_smuggled_zeros_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 16 [(4096, some_bytes 16)] [(4096, 1)]) m' evs) := by
  sys_refute

/-- ... and so is an unmap range.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:smuggle-unmap:a0:1 -- 16 -/
theorem small_request_smuggled_unmap_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (SyscallEffect.mkEffectU 16 [(4096, some_bytes 16)] [] [(4096, 1)] [] []) m' evs) := by
  sys_refute

/-- The call reads no model and writes none: a success reporting another
model is refused on the model alone.  Stated in hypothesis form, as
`Checks/Cases/Mm/Mprotect.lean`'s ledger refutations are.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem small_request_model_change_rejected (m m' : Model) (hne : m' ≠ m) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call 16) m
        (Ok (mkEffect 16 [(4096, some_bytes 16)] []) m' evs) := by
  intro h
  sys_norm at h
  exact hne h.1

/-! ## The bound is inclusive

A request of exactly `getrandom_small_max` bytes is small; one byte more
is large, and its short count is admitted again.  The kernel delivers
both in full (the loop argument above: both are under a page), so only a
mutated claim separates the two sides of the edge. -/

/-- 256 bytes: the small shape.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem at_256_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 256 0 (getrandom_call 256) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m [] ∧ (bs.length : Int) = 256 := by
  sys_norm

/-- 256 of 256 is admitted ...
probe: testing/syscall-check/tests/getrandom_spec.c#conform -- 256 -/
theorem at_256_full_delivery_admitted (m : Model) :
    getrandom_spec 4096 256 0 (getrandom_call 256) m
      (Ok (mkEffect 256 [(4096, some_bytes 256)] []) m []) := by
  sys_norm

/-- ... and 255 of 256 is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=255,trunc-writes:255 -- 256 -/
theorem at_256_short_count_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 256 0 (getrandom_call 256) m
        (Ok (mkEffect 255 [(4096, some_bytes 255)] []) m' evs) := by
  sys_refute

/-- 257 bytes: the large shape, with the interrupt and any count from one
byte up.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem at_257_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 257 0 (getrandom_call 257) m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m []
       ∨ ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m []
           ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 257) := by
  sys_norm

/-- 255 of 257 is admitted: one byte past the bound the short count is
back.
probe: testing/syscall-check/tests/getrandom_spec.c#conform --mutate getrandom:ret=255,trunc-writes:255 -- 257 -/
theorem at_257_short_count_admitted (m : Model) :
    getrandom_spec 4096 257 0 (getrandom_call 257) m
      (Ok (mkEffect 255 [(4096, some_bytes 255)] []) m []) := by
  sys_norm

/-! ## The large request

Above the bound the environment chooses the count as well as the bytes:
a signal after a whole page yields the count so far
(`get_random_bytes_user`, :471-473 and :481), never 0 and never more than
asked (:467-468), and -EINTR stays admissible from the wait before the
import (:1403; `arch_do_signal_or_restart`).  The spec admits `[1, buflen]`,
wider than any one kernel's short counts — a page multiple at v6.18.46, a
64-byte multiple through v5.17, the block `extract_crng_user` copied at
v4.17 and v5.17 — because Rocq's
`getrandom_large_request_still_admits_the_short_count` claims of the
kernel only what getrandom(2) documents: a count that is positive and no
larger than the request.  The width costs priority 2, not 1. -/

/-- 300 bytes: -EINTR, or one to three hundred bytes at the buffer.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem large_request_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 300 0 (getrandom_call 300) m o ↔
      (o = Ok (mkEffect (errno_ret EINTR) [] []) m []
       ∨ ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m []
           ∧ 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ 300) := by
  sys_norm

/-- The full delivery is admitted ...
probe: testing/syscall-check/tests/getrandom_spec.c#conform -- 300 -/
theorem large_request_full_delivery_admitted (m : Model) :
    getrandom_spec 4096 300 0 (getrandom_call 300) m
      (Ok (mkEffect 300 [(4096, some_bytes 300)] []) m []) := by
  sys_norm

/-- ... and so is a partial one ...
probe: testing/syscall-check/tests/getrandom_spec.c#conform --mutate getrandom:ret=5,trunc-writes:5 -- 300 -/
theorem large_request_short_count_admitted (m : Model) :
    getrandom_spec 4096 300 0 (getrandom_call 300) m
      (Ok (mkEffect 5 [(4096, some_bytes 5)] []) m []) := by
  sys_norm

/-- ... down to one byte, of any value: the bytes are the environment's.
probe: testing/syscall-check/tests/getrandom_spec.c#conform --mutate getrandom:ret=1,trunc-writes:1,poison-writes:255 -- 300 -/
theorem large_request_one_byte_admitted (m : Model) :
    getrandom_spec 4096 300 0 (getrandom_call 300) m
      (Ok (mkEffect 1 [(4096, [Z_to_bv 8 255])] []) m []) := by
  sys_norm

/-- The interrupt carrying no data is admitted.
probe: testing/syscall-check/tests/getrandom_spec.c#conform --mutate getrandom:ret=-EINTR,drop-writes -- 300 -/
theorem large_request_eintr_admitted (m : Model) :
    getrandom_spec 4096 300 0 (getrandom_call 300) m
      (Ok (mkEffect (errno_ret EINTR) [] []) m []) := by
  sys_norm

/-- A nonzero request never "succeeds" with nothing delivered:
`ret ? ret : -EFAULT` (:481) never returns 0 for a nonempty iterator.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem large_request_bare_zero_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- ... nor with an empty write entry: the shape a lower bound of zero
would allow.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem large_request_empty_write_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m (Ok (mkEffect 0 [(4096, [])] []) m' evs) := by
  sys_refute

/-- An errno carries no data: -EINTR with a delivered byte is refused.
probe: testing/syscall-check/tests/getrandom_spec.c#reject --mutate getrandom:ret=-EINTR,trunc-writes:1 -- 300 -/
theorem large_request_eintr_with_data_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m
        (Ok (mkEffect (errno_ret EINTR) [(4096, some_bytes 1)] []) m' evs) := by
  sys_refute

/-- Over-delivery is refused: the loop stops on an empty iterator (:467).
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem large_request_over_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m
        (Ok (mkEffect 301 [(4096, some_bytes 301)] []) m' evs) := by
  sys_refute

/-- An errno outside `getrandom_errnos` is refused: -EAGAIN needs a pool
that is not ready under GRND_NONBLOCK (:1400-1402), and this call passes
neither.
kernel: drivers/char/random.c:getrandom,crng_ready@v6.18.46 -/
theorem large_request_eagain_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- ... and -EFAULT is refused over a writable buffer: of its two sources
on a nonzero request, the range test (`import_ubuf`, lib/iov_iter.c:1437-1438)
passes 4096 + 300 and the copy that moved nothing (:481) is what the walk
has excluded.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem large_request_efault_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 300 0 (getrandom_call 300) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## The Rocq examples, name for name

Each is the conjunction Rocq states, on Rocq's fixture, with the
refutations quantified over the post-state and the events a lying kernel
might report.  Rocq's admission reasons are on the Rocq examples. -/

/-- A SMALL REQUEST IS DELIVERED IN FULL, AND ONLY IN FULL: the full
delivery is admitted, and the short count, the interrupt and the
over-delivery are refused on the same call.
rocq-twin: getrandom_small_request_is_delivered_in_full -/
theorem getrandom_small_request_is_delivered_in_full :
    getrandom_spec 4096 16 0 (getrandom_call 16) getrandom_model
      (Ok (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model [])
    ∧ (∀ (m' : Model) (evs : List event),
        ¬ getrandom_spec 4096 16 0 (getrandom_call 16) getrandom_model
            (Ok (mkEffect 5 [(4096, some_bytes 5)] []) m' evs))
    ∧ (∀ (m' : Model) (evs : List event),
        ¬ getrandom_spec 4096 16 0 (getrandom_call 16) getrandom_model
            (Ok (mkEffect (errno_ret EINTR) [] []) m' evs))
    ∧ (∀ (m' : Model) (evs : List event),
        ¬ getrandom_spec 4096 16 0 (getrandom_call 16) getrandom_model
            (Ok (mkEffect 17 [(4096, some_bytes 17)] []) m' evs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · sys_norm
  · intro m' evs; sys_refute
  · intro m' evs; sys_refute
  · intro m' evs; sys_refute

/-- THE BOUND IS INCLUSIVE: 255 of 256 is refused, 256 of 256 is
admitted, and 255 of 257 is admitted again.
rocq-twin: getrandom_small_bound_is_inclusive -/
theorem getrandom_small_bound_is_inclusive :
    (∀ (m' : Model) (evs : List event),
        ¬ getrandom_spec 4096 256 0 (getrandom_call 256) getrandom_model
            (Ok (mkEffect 255 [(4096, some_bytes 255)] []) m' evs))
    ∧ getrandom_spec 4096 256 0 (getrandom_call 256) getrandom_model
        (Ok (mkEffect 256 [(4096, some_bytes 256)] []) getrandom_model [])
    ∧ getrandom_spec 4096 257 0 (getrandom_call 257) getrandom_model
        (Ok (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m' evs; sys_refute
  · sys_norm
  · sys_norm

/-- A LARGE REQUEST STILL ADMITS THE SHORT COUNT AND -EINTR, and still
refuses the bare 0.
rocq-twin: getrandom_large_request_still_admits_the_short_count -/
theorem getrandom_large_request_still_admits_the_short_count :
    getrandom_spec 4096 300 0 (getrandom_call 300) getrandom_model
      (Ok (mkEffect 300 [(4096, some_bytes 300)] []) getrandom_model [])
    ∧ getrandom_spec 4096 300 0 (getrandom_call 300) getrandom_model
        (Ok (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model [])
    ∧ getrandom_spec 4096 300 0 (getrandom_call 300) getrandom_model
        (Ok (mkEffect (errno_ret EINTR) [] []) getrandom_model [])
    ∧ (∀ (m' : Model) (evs : List event),
        ¬ getrandom_spec 4096 300 0 (getrandom_call 300) getrandom_model
            (Ok (mkEffect 0 [] []) m' evs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · sys_norm
  · sys_norm
  · sys_norm
  · intro m' evs; sys_refute

/-! ## The dispatcher -/

/-- Syscall 278 reaches `getrandom_spec` with a0..a2 as its three
arguments — the buffer, the length and the flag word, the last compared
whole — and its writable view as the walk's memory.  The input is
`getrandom_call 16` spelled out, so the small-request `iff` is this one
by definitional unfolding of the table.
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem sysno_278_is_getrandom (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4096, Z_to_bv 64 16, 0, 0, 0, 0] getrandom_dest getrandom_dest) m o
      ↔ ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m [] ∧ (bs.length : Int) = 16 :=
  small_request_iff m o


/-! ## Which view the walk reads

`import_ubuf(ITER_DEST, ubuf, len, &iter)` (drivers/char/random.c:1408,
v6.18.46) makes `ubuf` a destination, and `get_random_bytes_user` only ever
copies INTO it (`copy_to_iter`, :456 and :464): the syscall writes the
buffer and never reads it.  So the walk is of the input's WRITABLE view and
the readable view is not consulted.  Every fixture above passes the same
zone as both views, which no pin could tell apart; these two pass the zone
as one view only. -/

/-- The zone as the readable view alone: nothing is writable. -/
def getrandom_call_ro (buflen : Int) : SyscallInput :=
  SyscallInput.mkInput 278 [4096, Z_to_bv 64 buflen, 0, 0, 0, 0] getrandom_dest (fun _ => none)

/-- The zone as the writable view alone: nothing is readable. -/
def getrandom_call_wo (buflen : Int) : SyscallInput :=
  SyscallInput.mkInput 278 [4096, Z_to_bv 64 buflen, 0, 0, 0, 0] (fun _ => none) getrandom_dest

attribute [sys_simp low] getrandom_call_ro.eq_1 getrandom_call_wo.eq_1

/-- A sixteen-byte walk of a memory with no bytes fails at its first byte.
model: the byte walk over the empty map, evaluated -/
@[sys_simp] theorem empty_walk_16 :
    read_bytes_map (fun _ => none) 4096 16 = none := by decide +kernel

/-- A readable but unwritable destination is declined: Linux faults in
`copy_to_iter` and answers -EFAULT (:481), the model declines.  This is the
pin that fixes which view the walk reads.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem readable_unwritable_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 0 (getrandom_call_ro 16) m o ↔ o = Unmodeled := by
  sys_norm

/-- ... and the delivery a walk of the readable view would allow is refused.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem readable_unwritable_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ getrandom_spec 4096 16 0 (getrandom_call_ro 16) m
        (Ok (mkEffect 16 [(4096, some_bytes 16)] []) m' evs) := by
  sys_refute

/-- A writable but unreadable destination is the small request, exactly as
over the zone: the readable view is never read.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem unreadable_writable_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4096 16 0 (getrandom_call_wo 16) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4096, bs)] []) m [] ∧ (bs.length : Int) = 16 := by
  sys_norm


/-! ### The zone's edge

The walk is of exactly `buflen` bytes from exactly `buf`: the last sixteen
bytes of the zone are admitted and one byte further declines.  The pins
above sit eight bytes inside or eight bytes over the edge, which a walk
from `buf + 1` or of `buflen - 1` bytes would answer the same way. -/

/-- The zone's last sixteen bytes, 4592..4607.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_4592_16 :
    read_bytes_map getrandom_dest 4592 16 = some (List.replicate 16 0) := by decide +kernel
/-- One byte further, the sixteenth byte is 4608, outside the zone.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_4593_16 :
    read_bytes_map getrandom_dest 4593 16 = none := by decide +kernel

/-- A request filling the zone to its last byte is the small shape.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem at_the_zone_edge_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4592 16 0 (getrandom_call 16) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4592, bs)] []) m [] ∧ (bs.length : Int) = 16 := by
  sys_norm

/-- One byte over the zone's edge declines: Linux would fault on the last
byte and answer 15 (`copy_to_iter` stops at the fault, :481 returns the
count), the model declines.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem past_the_zone_edge_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4593 16 0 (getrandom_call 16) m o ↔ o = Unmodeled := by
  sys_norm

/-! ### The registers, through the table

`SYSCALL_DEFINE3(getrandom, ...)` takes three arguments (drivers/char/random.c:1385,
v6.18.46) and riscv hands them the first three argument registers:
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24,
v6.18.46) maps `orig_a0`, `a1`, `a2` onto them in order.  The pins here
vary one register at a time so that a table reading the wrong one, or a
constant in place of one, answers differently. -/

/-- a2 is the flag word: 278 with a2 = GRND_RANDOM declines through the
table, as `grnd_random_is_unmodeled` says of the arm.  (A table wired to a3
would answer the small shape here.)
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS@v6.18.46 -/
theorem sysno_278_a2_is_the_flag_word (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4096, Z_to_bv 64 16, 2, 0, 0, 0] getrandom_dest getrandom_dest) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- a1 is the length and a3..a5 are not read: a1 = 0 beside a3 = 16 is the
zero-byte request, not a sixteen-byte one, and the GRND_RANDOM in a4 and
the unknown bit in a5 decline nothing.  The -EINTR beside the 0 is the
zero-byte arm's, from the wait before the import (`arch_do_signal_or_restart`).
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem sysno_278_a1_is_the_length (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4096, 0, 0, Z_to_bv 64 16, 2, 256] getrandom_dest getrandom_dest) m o
      ↔ (o = Ok (mkEffect (errno_ret EINTR) [] []) m [] ∨ o = Ok (mkEffect 0 [] []) m []) := by
  sys_norm

/-- The zone's last 256 bytes, 4352..4607.
model: the byte walk over `getrandom_dest`, evaluated -/
@[sys_simp] theorem zone_walk_4352_256 :
    read_bytes_map getrandom_dest 4352 256 = some (List.replicate 256 0) := by decide +kernel

/-- The six registers as the table hands them: a0 = 4352, a1 = 256,
a2 = GRND_NONBLOCK, and in a3..a5 GRND_RANDOM, an unknown bit and a set
high half, each a decline were it read as the flag word.  Named so the
arm-level iff below can be reused through `syscall_spec` by unfolding:
`sys_norm` through the table does not close a 256-byte walk (it exhausts
the recursion depth), where the arm-level one does.
model: the table's `SyscallInput`, a0..a5 in Rocq's order -/
def getrandom_regs_call : SyscallInput :=
  SyscallInput.mkInput 278 [4352, Z_to_bv 64 256, 1, 2, 256, Z_to_bv 64 (2 ^ 32)] getrandom_dest getrandom_dest
attribute [sys_simp low] getrandom_regs_call.eq_1

/-- The arm on that input with a0/a1/a2 already in place: a 256-byte
delivery at 4352 under GRND_NONBLOCK, answered as 0 would be, since the
-EAGAIN branch (:1401) is not taken with the pool ready and
`get_random_bytes_user` copies every byte the walk admits.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem regs_call_arm_iff (m : Model) (o : outcome SyscallEffect) :
    getrandom_spec 4352 256 1 getrandom_regs_call m o ↔
      ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4352, bs)] []) m [] ∧ (bs.length : Int) = 256 := by
  sys_norm

/-- a0 is the buffer and a1 the length, from the registers and not from a
constant the other pins happen to share: the delivery lands at 4352, not
at the 4096 every other fixture uses, and is 256 bytes, the small bound.
a2 = GRND_NONBLOCK is answered as 0 would be; a3..a5 hold GRND_RANDOM, an
unknown bit and a set high half, each declined were it read as the flag
word, and none is.  The input is `getrandom_regs_call` spelled out, so
the arm-level `regs_call_arm_iff` is this one by definitional unfolding of
the table, as `sysno_278_is_getrandom` is `small_request_iff`.
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS@v6.18.46 -/
theorem sysno_278_a0_a1_are_the_buffer_and_length (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4352, Z_to_bv 64 256, 1, 2, 256, Z_to_bv 64 (2 ^ 32)]
                    getrandom_dest getrandom_dest) m o
      ↔ ∃ bs : List byte, o = Ok (mkEffect (len_word bs) [(4352, bs)] []) m [] ∧ (bs.length : Int) = 256 :=
  regs_call_arm_iff m o


/-- Both words arrive whole.  `len` is `size_t` and `flags` is `unsigned
int` (:1385), and the arm hands each register through untruncated, as
Rocq's table does: a length of 2^32 + 16 is over the bound, not sixteen
bytes, so a table narrowing it to 32 bits would answer the small shape
where Linux delivers 128 KiB (`import_ubuf`'s clamp, lib/iov_iter.c:1435-1436).
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem sysno_278_length_arrives_whole (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4096, Z_to_bv 64 (2 ^ 32 + 16), 0, 0, 0, 0] getrandom_dest getrandom_dest) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- ... and the flag word too: the set high half declines through the table
exactly as `high_half_flags_is_unmodeled` says of the arm, so a table
narrowing `flags` to the `unsigned int` Linux reads would be caught here.
kernel: include/uapi/asm-generic/unistd.h:__NR_getrandom; drivers/char/random.c:getrandom@v6.18.46 -/
theorem sysno_278_flags_arrive_whole (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 278 [4096, Z_to_bv 64 16, Z_to_bv 64 (2 ^ 32), 0, 0, 0] getrandom_dest getrandom_dest) m o
      ↔ o = Unmodeled := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Drivers.Char.Random
