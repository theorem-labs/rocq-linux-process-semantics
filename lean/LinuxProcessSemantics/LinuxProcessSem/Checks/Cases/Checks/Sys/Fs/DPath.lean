import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.DPath
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.DPath — what the getcwd checker answers, read off against Linux

Pins over `Checks.Sys.Fs.DPath`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/DPath.v` and
`theories/LinuxProcessSem/Checks/Witness/Fs/DPath.v`.  Rocq keeps no
worked-cases file for this checker — its checks are the probe
`testing/syscall-check/tests/getcwd_spec.c`, which runs the EXTRACTED
ROCQ checker and never a Lean definition — so this file mirrors no Rocq
source and `tools/check_lean_cases_parity.py` lists it `unmirrored`.
Not part of the trusted specification: this file is QA on the checker,
written to be READ.

WHY THE CHECKER AND NOT `check_syscall`.  Every pin above the
`V_Fs_DPath` section applies `check_getcwd` to the `size` word directly,
in the position `SYSCALL_DEFINE2(getcwd, buf, size)` gives it, and none
goes through the dispatcher: they were written before `checked_table`
carried a row for 17.  What those pins cannot see is a transposed
register in the arm — an arm that took a0 for the size would put
`getcwd(NULL, 4096)` in the band and accept `-ERANGE` for a buffer every
path fits — and the `V_Fs_DPath` section at the end of this file pins it
through `check_syscall`, beside the registration it is about
(`Checks/Arms/Fs/DPath.lean`).

WHAT THIS FILE ADDS TO `Checks/Cases/Fs/DPath.lean`.  That file fixes what
the SPEC admits, outcome by outcome; the four lemmas beside the checker
prove the checker answers exactly that.  Both hold when the checker and
the spec are wrong together — the proofs compare the two definitions with
each other and never with Linux — so each pin below names a concrete
answer from OUTSIDE both: an effect a trace could carry and the verdict
the kernel's own body forces on it, closed by `rfl` on the checker's
computation.  Every line of `SYSCALL_DEFINE2(getcwd)` cited here is
fs/d_path.c at Linux v6.18.46 (commit 1f99e9ab748f), by the line numbers
`Checks/Cases/Fs/DPath.lean`'s header tabulates: 419 `-ENOMEM`, 426
`-ENOENT`, 438 `-ENAMETOOLONG`, 439-440 `len > size` and `-ERANGE`,
441-442 `copy_to_user` and `-EFAULT`, 444 the success return.

WHAT MEASURES THESE PINS.  Nothing in the tree yet: `tools/lean_mutate.py
--spec` builds a spec mutant against `Checks/Cases/Fs/DPath.lean` alone,
so no mutant of the checker is compiled against this file, and its
kill-rate is unmeasured until that tool lists a checker's pins beside the
spec's.  The one measurement so far is the hand-run pins-only mutation in
the deep-review record of the PR that landed this file: the checker
mutated with the spec pins and the four lemmas stubbed out, so that only
the `rfl` pins here could answer.  Every mutant died but one, which
compared the return on its low 32 bits and lived because every pin then
spelled its return as `errno_ret` or a small literal;
`check_getcwd_return_is_the_full_word` is its pin.

The positive shape is an `iff` over every answer, which fixes what is
accepted and what is refused in one statement; the concrete pins after it
are the cases a reader would otherwise have to derive from it.  `Model`
has no `DecidableEq`, so a concrete checker answer is closed by `rfl`, not
`decide`; the two `iff`s go through the checker's own soundness and
completeness and the spec pins, which is the one place this file leans on
the proofs it exists to complement, and it says so where it does.

The evidence lines cite the kernel and not the probe, for the reason
`Checks/Cases/Checks/Sys/Prelude.lean`'s header gives: the probe's verdict
is about the Rocq checker, and this file is about the Lean one.  Where a
probe case states the same fact of the Rocq side, the docstring names it
— and names the size it is stated at, because the probe's `range` mode
issues the size-0 call first and a `--mutate getcwd:…` without an
occurrence hits that first call, so most of its cases are about size 0. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.DPath

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.DPath
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath (getcwd_errnos)

/-- The input the spec-level facts below are instantiated at: a7 = 17,
`buf` and `size` zero in a0 and a1, the remaining argument registers zero,
and a process whose memory maps nothing.  `check_getcwd` never reads an
input — it takes the `size` word the arm will hand it — and the spec
lemmas' `i` is symbolic and carries any memory, so which input is
immaterial; this one is the shape `Checks/Cases/Fs/DPath.lean`'s
`sysno_17` pins use. -/
def getcwd_in : SyscallInput :=
  SyscallInput.mkInput 17 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! ## What the checker accepts in the band -/

/-- `size = 0`, every answer at once: the checker says `CheckOk` exactly
on a bare return of one of the four errnos the body produces before line
441 on Linux — lines 419, 426, 438 and 440 — and then hands back the
model it was given and no event.  Through `check_getcwd_sound_ok`,
`check_getcwd_complete_ok` and the spec's `getcwd_size0_iff`, whose
docstring says where another supported implementation answers otherwise.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size0_ok_iff (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_getcwd 0 eff m = CheckOk m' evs ↔
      (m' = m ∧ evs = [] ∧
        (eff = mkEffect (errno_ret ENOMEM) [] [] ∨ eff = mkEffect (errno_ret ENOENT) [] []
          ∨ eff = mkEffect (errno_ret ENAMETOOLONG) [] []
          ∨ eff = mkEffect (errno_ret ERANGE) [] [])) := by
  constructor
  · intro h
    have hs := (getcwd_size0_iff getcwd_in m (Ok eff m' evs)).mp
      (check_getcwd_sound_ok 0 eff m m' evs getcwd_in h)
    rcases hs with (h | h | h) | h <;>
      (injection h with heff hm hevs; subst heff hm hevs;
       simp only [and_true, true_or, or_true])
  · rintro ⟨rfl, rfl, h⟩
    refine check_getcwd_complete_ok 0 eff _ _ [] getcwd_in
      ((getcwd_size0_iff getcwd_in _ (Ok eff _ [])).mpr ?_)
    rcases h with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true]

/-- `size = 1`: the same set, for the reason the spec pin gives — one byte
holds the NUL and never the "/" charged on top of it, so line 439 holds
for every working directory.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size1_ok_iff (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_getcwd 1 eff m = CheckOk m' evs ↔
      (m' = m ∧ evs = [] ∧
        (eff = mkEffect (errno_ret ENOMEM) [] [] ∨ eff = mkEffect (errno_ret ENOENT) [] []
          ∨ eff = mkEffect (errno_ret ENAMETOOLONG) [] []
          ∨ eff = mkEffect (errno_ret ERANGE) [] [])) := by
  constructor
  · intro h
    have hs := (getcwd_size1_iff getcwd_in m (Ok eff m' evs)).mp
      (check_getcwd_sound_ok 1 eff m m' evs getcwd_in h)
    rcases hs with (h | h | h) | h <;>
      (injection h with heff hm hevs; subst heff hm hevs;
       simp only [and_true, true_or, or_true])
  · rintro ⟨rfl, rfl, h⟩
    refine check_getcwd_complete_ok 1 eff _ _ [] getcwd_in
      ((getcwd_size1_iff getcwd_in _ (Ok eff _ [])).mpr ?_)
    rcases h with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true]

/-- `getcwd(buf, 0)` answering `-ERANGE` (line 440) is accepted, on the
model as given and with no event: the checker's own computation, with
nothing symbolic in the effect.  The probe's `conform -- range` case
states the same of the Rocq checker, at both sizes.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size0_erange_accepted (m : Model) :
    check_getcwd 0 (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m [] := rfl

/-- Each injected errno is accepted at `size = 1`: `-ENOMEM` from line
419, `-ENOENT` from line 426, `-ENAMETOOLONG` from line 438, all decided
before the size is looked at.  The probe's three `conform --mutate
getcwd:ret=-E…` cases state the same of the Rocq checker at size 0, the
call its mutations default to; size 1 is pinned here because it is the
edge of the band and the probe never injects an errno there.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size1_injected_accepted (m : Model) :
    check_getcwd 1 (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m []
      ∧ check_getcwd 1 (mkEffect (errno_ret ENOENT) [] []) m = CheckOk m []
      ∧ check_getcwd 1 (mkEffect (errno_ret ENAMETOOLONG) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl, rfl⟩

/-! ## What the checker refuses in the band

Each is one concrete answer a lying kernel could give at `size ≤ 1` that
the body of `SYSCALL_DEFINE2(getcwd)` cannot produce on Linux, and the
verdict is `CheckReject` — not the decline, which would let the lie
through as "unknown".  "On Linux" is load-bearing for two of them: the
`-EFAULT` pins refuse an answer qemu-user, a supported implementation,
really gives, and say so where they do.  Every concrete pin is the
checker's computation, closed by `rfl`. -/

/-- `-EFAULT` is refused at size 0: line 441's `copy_to_user` sits behind
line 439, and nothing before it can fault on Linux.  The probe's `reject
--mutate getcwd:ret=-EFAULT` case states the same of the Rocq checker, at
this size.  This is Linux's answer proved certain where another supported
implementation gives a different one: qemu-user checks `buf` before any
size test and answers `-EFAULT` at size 0 on an address above
`reserved_va` under `-R` — shape 2 of
`bugs/getcwd-erange-band-admits-linux-alone.md`, with the QEMU citation
on the spec pin `getcwd_size0_efault_rejected` — so a run under qemu-user
at that shape is refused, not declined.  The checker follows the spec,
which follows Rocq; the entry records the cost and what would move it.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size0_efault_rejected (m : Model) :
    check_getcwd 0 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := rfl

/-- …and at size 1, for the same reason and with the same cost: the
copy at line 441 is never reached on Linux, and qemu-user answers
`-EFAULT` here on a buffer that is not guest memory — shape 1 of the same
entry.  The probe never states this at size 1; its only size-1 mutation
is `getcwd#2:ret=0`.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size1_efault_rejected (m : Model) :
    check_getcwd 1 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := rfl

/-- `-EINVAL` is refused: `SYSCALL_DEFINE2(getcwd)` (lines 412-448) has
no `-EINVAL` arm at all — the one POSIX documents for a zero size is
glibc's, decided before the syscall is issued.  The file's one `-EINVAL`,
`d_absolute_path`'s at line 235, is on no path getcwd calls, so on this
call the errno is spelled only by errno-base.h.  The probe's `reject
--mutate getcwd:ret=-EINVAL` case states the same of the Rocq checker.
kernel: fs/d_path.c:getcwd; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem check_getcwd_size0_einval_rejected (m : Model) :
    check_getcwd 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject := rfl

/-- `-EACCES` is refused: there is no permission check in the body.
Between the allocation (`__getname`, line 416) and the copy out (line
441) it reads the caller's own `root` and `pwd` out of `current->fs`
through `get_fs_root_and_pwd_rcu` (line 422), tests `d_unlinked` (line
424) and walks the dcache in `prepend_path` (line 432); none of these,
nor the allocator or the copy around them, consults a permission bit or
an LSM hook, so nothing on the path can answer for access.  The probe's
`reject --mutate getcwd:ret=-EACCES` case states the same of the Rocq
checker at size 0.
kernel: fs/d_path.c:getcwd; include/uapi/asm-generic/errno-base.h:EACCES@v6.18.46 -/
theorem check_getcwd_size1_eacces_rejected (m : Model) :
    check_getcwd 1 (mkEffect (errno_ret EACCES) [] []) m = CheckReject := rfl

/-- A success return is refused at both sizes, whatever its value: line
444 is reached only when line 439 is false, and `len ≥ 2` for every
working directory, so `len > size` holds at 0 and at 1.  Five concrete
values.  0 at each size — `len` counts the NUL (line 431) and is never
0, and 0 is what an acceptor that forgot to compare would most plausibly
let through.  2 at each size, the shortest `len` there is.  And 4097 at
size 1: the `len` a full buffer yields, `b.len` left at -1 by
`prepend_char` (line 33) or `prepend` (line 69) and subtracted at line
436, which line 437 turns into `-ENAMETOOLONG` before line 439 is
reached, so it is never a success return either.  The probe's `reject
--mutate getcwd:ret=2` and `getcwd:ret=0` cases state the size-0 halves
of the Rocq checker, and its `getcwd#2:ret=0` case the size-1 zero.
kernel: fs/d_path.c:getcwd,prepend_char,prepend@v6.18.46 -/
theorem check_getcwd_success_returns_rejected (m : Model) :
    check_getcwd 0 (mkEffect 0 [] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect 0 [] []) m = CheckReject
      ∧ check_getcwd 0 (mkEffect 2 [] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect 2 [] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect 4097 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `-ERANGE` beside a byte written to `buf` is refused on the write
ledger: line 440 is taken INSTEAD of line 441.  `buf` is symbolic and the
verdict does not depend on it — the `match` refuses the ledger's shape.
The probe's `smuggle-write:a0:1` case states the same of the Rocq
checker, at this size.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_erange_with_write_rejected (buf : word) (m : Model) :
    check_getcwd 0 (SyscallEffect.mkEffectU (errno_ret ERANGE) [(buf, [Z_to_bv 8 0])] [] [] [] []) m
      = CheckReject := rfl

/-- …and beside a zero-fill: the path is built into a kernel page (line
429) and no user byte is touched before line 441.  The probe's
`smuggle-zeros:a0:1` case states the same of the Rocq checker, at this
size.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_erange_with_zeros_rejected (buf : word) (m : Model) :
    check_getcwd 0 (mkEffect (errno_ret ERANGE) [] [(buf, 1)]) m = CheckReject := rfl

/-- …and beside an unmap: the page is a KERNEL page (line 429), freed by
`__putname` (include/linux/fs.h) at line 446; no user mapping is touched.
kernel: fs/d_path.c:getcwd; include/linux/fs.h:__putname@v6.18.46 -/
theorem check_getcwd_erange_with_unmap_rejected (buf : word) (m : Model) :
    check_getcwd 1 (SyscallEffect.mkEffectU (errno_ret ERANGE) [] [] [(buf, 4096)] [] []) m
      = CheckReject := rfl

/-- …and beside a copy-in: `buf` is a destination only, and nothing
between lines 412 and 441 reads user memory.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_erange_with_copyin_rejected (buf : word) (m : Model) :
    check_getcwd 0 (SyscallEffect.mkEffectU (errno_ret ERANGE) [] [] [] [] [(buf, 1)]) m
      = CheckReject := rfl

/-- …and beside a memory copy: the body moves nothing between user
addresses, so the copies ledger is empty on every answer it can give.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_erange_with_copy_rejected (src dst : word) (m : Model) :
    check_getcwd 0 (SyscallEffect.mkEffectU (errno_ret ERANGE) [] [] [] [MemCopy.mkCopy src dst 1] []) m
      = CheckReject := rfl

/-- A ledger entry beside an INJECTED errno is refused too: `-ENOMEM`
returns at line 419 before the page is even taken, and `-ENOENT` (line
426) and `-ENAMETOOLONG` (line 438) are each decided before line 441, so
none of the three writes, zeroes or reads a user byte either.  A checker
that opened the ledgers on the `-ERANGE` arm alone — the shape every
ledger pin above would let through — accepts all three of these.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_injected_with_ledger_rejected (buf : word) (m : Model) :
    check_getcwd 0 (mkEffect (errno_ret ENOMEM) [(buf, [Z_to_bv 8 0])] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect (errno_ret ENOENT) [] [(buf, 1)]) m = CheckReject
      ∧ check_getcwd 1 (SyscallEffect.mkEffectU (errno_ret ENAMETOOLONG) [] [] [] [] [(buf, 1)]) m
          = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The return is compared at all 64 bits.  The body's `int error` (line
414) is widened into the `long` the riscv syscall wrapper returns — `long
ret = __do_sys##name(…)` in `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-97, Linux v6.18.46; riscv
selects `ARCH_HAS_SYSCALL_WRAPPER`, arch/riscv/Kconfig:54) — and stored
whole into a0 by `syscall_handler` (`regs->a0 = fn(regs)`,
arch/riscv/include/asm/syscall.h:112), so a negative errno fills the
register with ones.  Each admitted errno's zero-extended low half —
2^32 - 34, 2^32 - 12, 2^32 - 2, 2^32 - 36 — is a word the kernel never
hands back, and is refused; a checker comparing the low 32 bits of both
sides accepts all four.  This is the one mutant the hand-run mutation of
these pins let live (header).
kernel: fs/d_path.c:getcwd; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getcwd_return_is_the_full_word (m : Model) :
    check_getcwd 0 (mkEffect (Z_to_bv 64 0xFFFFFFDE) [] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect (Z_to_bv 64 0xFFFFFFF4) [] []) m = CheckReject
      ∧ check_getcwd 0 (mkEffect (Z_to_bv 64 0xFFFFFFFE) [] []) m = CheckReject
      ∧ check_getcwd 1 (mkEffect (Z_to_bv 64 0xFFFFFFDC) [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Inside the band the checker never declines: at `size = 1` every
answer is either one of the four the body can give or a lie, and the
model knows which.  Through `check_getcwd_sound_unmodeled` and the spec's
`getcwd_size1_never_unmodeled`.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size1_never_unmodeled (eff : SyscallEffect) (m : Model) :
    check_getcwd 1 eff m ≠ CheckUnmodeled :=
  fun h => getcwd_size1_never_unmodeled getcwd_in m
    (check_getcwd_sound_unmodeled 1 eff m getcwd_in h)

/-- No success at all in the band, whatever the return: the twin of the
spec's `getcwd_size1_no_success` on the checker's side.  Line 444 is
reached only when line 439 is false, and `len ≥ 2 > 1` for every working
directory; the success return is `len`, bounded by `PATH_MAX` at line 437,
so the hypothesis names every value line 444 can hand back, and the four
admitted errnos, all in the top 4095 of the word, lie outside it.  Through
`check_getcwd_sound_ok` and `check_getcwd_size1_never_unmodeled`: the
checker's answer is not `CheckOk` and not `CheckUnmodeled`, so it is
`CheckReject`.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size1_no_success (r : word) (hr : bv_unsigned r ≤ 4096) (m : Model) :
    check_getcwd 1 (mkEffect r [] []) m = CheckReject := by
  cases hc : check_getcwd 1 (mkEffect r [] []) m with
  | CheckOk m' evs =>
    exact absurd (check_getcwd_sound_ok 1 _ m m' evs getcwd_in hc)
      (getcwd_size1_no_success r getcwd_in m m' [] [] [] [] [] evs hr)
  | CheckReject => rfl
  | CheckUnmodeled => exact absurd hc (check_getcwd_size1_never_unmodeled _ m)

/-- The checker never emits an event on an accepted answer: `-ERANGE` is
a bare return, and a `CheckOk` carrying one would let the dispatcher
record a step the kernel did not take.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_erange_answers_no_event (m m' : Model) (e : event) (evs : List event) :
    check_getcwd 0 (mkEffect (errno_ret ERANGE) [] []) m ≠ CheckOk m' (e :: evs) := by
  intro h
  injection h with _ h
  cases h

/-! ## Above the band

`size ≥ 2` is where the working directory decides the answer, and the
model has none: the spec is `unmodeled` there and the checker declines
whatever the trace offers — it neither accepts an answer it cannot check
nor rejects one it cannot refute. -/

/-- `size = 2`: declined for every effect, `-ERANGE` and the working
directory's own length alike.  The probe's `fail-closed
--expect-unmodeled getcwd -- size2` case states the same of the Rocq
checker.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size2_unmodeled (eff : SyscallEffect) (m : Model) :
    check_getcwd 2 eff m = CheckUnmodeled := rfl

/-- `size = PATH_MAX` (4096, include/uapi/linux/limits.h:13): a buffer
every path fits, so the answer is the working directory itself —
declined.
kernel: fs/d_path.c:getcwd; include/uapi/linux/limits.h:PATH_MAX@v6.18.46 -/
theorem check_getcwd_size_path_max_unmodeled (eff : SyscallEffect) (m : Model) :
    check_getcwd 4096 eff m = CheckUnmodeled := rfl

/-- `size` is `unsigned long` (line 412): a register holding -1 is
2^64 - 1, a size every path fits, and the answer is again the working
directory, declined.  A checker that read the size as signed would put
this call in the band and accept `-ERANGE` for it.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size_minus_one_unmodeled (eff : SyscallEffect) (m : Model) :
    check_getcwd (Z_to_bv 64 (-1)) eff m = CheckUnmodeled := rfl

/-- All 64 bits of `size` are read: 2^32, whose low 32 bits are zero, is
declined.  A checker that truncated the `unsigned long` to 32 bits would
read it as 0 and accept `-ERANGE` for a buffer every path fits.  This is
the probe's `reject --mutate getcwd:arg1=1 -- big` case turned around:
there the kernel's own answer to a big buffer is checked against a
register lied down into the band.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_size_high_bits_unmodeled (eff : SyscallEffect) (m : Model) :
    check_getcwd (Z_to_bv 64 0x100000000) eff m = CheckUnmodeled := rfl

/-- Above the band the checker declines, whatever the effect: stated for
every `size` past the band, not one, so the four concrete declines above
are instances and not the whole claim.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_above_band_declines (size : word) (h : 1 < bv_unsigned size)
    (eff : SyscallEffect) (m : Model) :
    check_getcwd size eff m = CheckUnmodeled := by
  simp only [check_getcwd, h, ↓reduceIte]

/-- …and so never rejects there: a `CheckReject` above the band would
call the kernel a liar where the model cannot know what it said.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem check_getcwd_above_band_never_rejects (size : word) (h : 1 < bv_unsigned size)
    (eff : SyscallEffect) (m : Model) :
    check_getcwd size eff m ≠ CheckReject := by
  rw [check_getcwd_above_band_declines size h eff m]
  exact fun hc => nomatch hc

/-! ## The witness -/

/-- In the band the witness is `-ERANGE` on the model as given: the
answer line 440 gives for every working directory at `size ≤ 1`, and the
one the model derives from `size` alone.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_witness_in_band (m : Model) :
    getcwd_witness 0 m = Ok (mkEffect (errno_ret ERANGE) [] []) m []
      ∧ getcwd_witness 1 m = Ok (mkEffect (errno_ret ERANGE) [] []) m [] :=
  ⟨rfl, rfl⟩

/-- Above the band the witness is the decline, the only outcome the spec
admits there — at 2 and `PATH_MAX`, and at the two sizes whose reading
the checker pins above turn on, 2^64 - 1 and 2^32: a witness that read
the size as signed or as 32 bits would exhibit `-ERANGE` at one of them,
an outcome the spec refuses, and `getcwd_witness_ok` would fail
to close.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_witness_above_band (m : Model) :
    getcwd_witness 2 m = Unmodeled ∧ getcwd_witness 4096 m = Unmodeled
      ∧ getcwd_witness (Z_to_bv 64 (-1)) m = Unmodeled
      ∧ getcwd_witness (Z_to_bv 64 0x100000000) m = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The checker accepts its own witness at every size and model: wherever
the witness exhibits an `Ok`, the checker says `CheckOk` to that effect
on that model with those events.  `getcwd_witness_ok` proves the spec
admits the witness; this pins that the checker, run on it, agrees, and
does so without naming the spec: the proof opens none of the four
lemmas, only the two definitions.  It is what makes the arm's
`ca_receptive`, once the registration builds it, a statement about
`check_getcwd` and not only about `getcwd_spec`.
model: `getcwd_witness` fed to `check_getcwd`, no spec named -/
theorem check_getcwd_accepts_its_witness (size : word) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : getcwd_witness size m = Ok e m' evs) : check_getcwd size e m = CheckOk m' evs := by
  unfold getcwd_witness at h
  unfold check_getcwd
  by_cases hs : 1 < bv_unsigned size
  · simp only [hs, ↓reduceIte, reduceCtorEq] at h
  · simp only [hs, ↓reduceIte] at h ⊢
    unfold ret_outcome at h
    injection h with he hm hevs
    subst he hm hevs
    have hno : errno_ret_in getcwd_errnos (errno_ret ERANGE) = false := by decide
    simp only [hno, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl]

-- lean-port sentinel: ticket V-Fs-DPath appends below this line

section V_Fs_DPath

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-DPath — `getcwd` over the real table

WHAT IS STATED HERE.  Rocq states no `check_syscall` example for getcwd:
its checks are the probes `testing/syscall-check/tests/getcwd_spec.c` and
`testing/syscall-check/tests/scenarios/dir_name_unlink.c`, run against the
extracted Rocq checker.  So each pin here states, through the Lean
`check_syscall` over `checked_table` itself, either a call the recorded
corpus replays at the arm — at the buffer address and the size its trace
carries — or a call that separates the arm's reading of its registers
from a wrong one.  Names end in `_over_the_real_table`, K6b's convention
for the pins at which the real table first answers a call.  Every pin
holds at every model: neither the lookup nor the arm reads one.

WHAT A PIN HERE ADDS to its checker-level twin above, where it has one,
is the ARM's claim: that the lookup at 17 finds `arm_getcwd` rather than
the dispatcher's own decline (`lookup_cwd_in`), and that the arm hands the
checker register a1, all 64 bits of it, and no other register
(`size_is_a1_over_the_real_table`,
`registers_after_a1_unread_over_the_real_table`,
`size_is_the_whole_register_over_the_real_table`).

POLARITY: the evidence line is `kernel:` on every pin about the kernel's
answer, `CheckOk`, `CheckReject` and `CheckUnmodeled` alike, and `model:`
on the pin about the table's own contents. -/

/-- A getcwd call: `buf` in a0 and `size` in a1, each the integer taken
modulo 2^64, the remaining argument registers zero, and a process whose
memory maps nothing.  The arm reads no memory, so which memory is
immaterial. -/
def cwd_in (buf size : Int) : SyscallInput :=
  SyscallInput.mkInput 17 [Z_to_bv 64 buf, Z_to_bv 64 size, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The lookup the dispatcher performs on a `cwd_in`, computed once:
`in_sysno` is 17 whatever the two words hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_cwd_in (buf size : Int) :
    lookup_ca checked_table (bv_unsigned (cwd_in buf size).in_sysno) = some arm_getcwd :=
  lookup_ca_checked_table_getcwd

/-! ### The recorded calls, through `check_syscall` -/

/-- The probe's `conform -- range` calls — `getcwd(buf, 0)`,
`getcwd(buf, 1)` and `getcwd(NULL, 0)`, at the address the trace's
buffer has — and `scenarios/dir_name_unlink.c`'s `getcwd(buf, 1)` each
answer `-ERANGE` (fs/d_path.c:439-440, Linux v6.18.46), which is
accepted on the model as given, with no event.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem range_erange_accepted_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m []
    ∧ check_syscall (cwd_in 69632 1) (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m []
    ∧ check_syscall (cwd_in 0 0) (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m []
    ∧ check_syscall (cwd_in 73728 1) (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The probe's three injected errnos at `getcwd(buf, 0)`: `-ENOMEM`
(fs/d_path.c:419), `-ENOENT` (:426) and `-ENAMETOOLONG` (:438), each
decided before the size comparison at :439 (Linux v6.18.46), are
accepted.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem range_injected_accepted_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m []
    ∧ check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ENOENT) [] []) m = CheckOk m []
    ∧ check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ENAMETOOLONG) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl⟩

/-- The probes' return lies in the band are refused: `-EFAULT` at
`getcwd(buf, 0)` and at `getcwd(NULL, 0)` — the `copy_to_user` that
returns it (fs/d_path.c:441-442, Linux v6.18.46) sits behind the
`len > size` test at :439, which holds at both sizes; `-EINVAL` and
`-EACCES`, which the body has no arm for; and the success returns 2 and 0
at size 0 and 0 at size 1, in both probes' buffers — line 444 is reached
only when line 439 is false, and `len` is at least 2 on every path that
reaches line 439, by the argument the spec twin `Sys/Fs/DPath.lean`
carries.
kernel: fs/d_path.c:getcwd; include/uapi/asm-generic/errno-base.h:EINVAL,EACCES@v6.18.46 -/
theorem range_return_lies_rejected_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 0) (mkEffect (errno_ret EFAULT) [] []) m = CheckReject
    ∧ check_syscall (cwd_in 0 0) (mkEffect (errno_ret EFAULT) [] []) m = CheckReject
    ∧ check_syscall (cwd_in 69632 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_syscall (cwd_in 69632 0) (mkEffect (errno_ret EACCES) [] []) m = CheckReject
    ∧ check_syscall (cwd_in 69632 0) (mkEffect 2 [] []) m = CheckReject
    ∧ check_syscall (cwd_in 69632 0) (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (cwd_in 69632 1) (mkEffect 0 [] []) m = CheckReject
    ∧ check_syscall (cwd_in 73728 1) (mkEffect 0 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The probe's ledger lies are refused: `-ERANGE` beside the byte `0x41`
written to `buf`, and beside one byte of `buf` zeroed.  Line 440
(fs/d_path.c, Linux v6.18.46) is taken instead of the `copy_to_user` at
:441, and the path is built in the page `__getname` allocates at :416,
so no user byte is touched.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem range_ledger_lies_rejected_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ERANGE) [(69632, [Z_to_bv 8 0x41])] []) m
      = CheckReject
    ∧ check_syscall (cwd_in 69632 0) (mkEffect (errno_ret ERANGE) [] [(69632, 1)]) m
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- Above the band the arm declines whatever the answer: the probe's
`big` call, `getcwd(buf, 4096)`, whose recorded answer is the success
return 6; `scenarios/dir_name_unlink.c`'s `getcwd(buf, 256)`, the same
answer; and the probe's `size2` call, `getcwd(buf, 2)`, whose recorded
answer is `-ERANGE`.  Which of line 440 and line 444 (fs/d_path.c, Linux
v6.18.46) a size of 2 or more reaches depends on the length of the
working directory, which the model does not carry.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem above_band_declined_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 4096) (mkEffect 6 [] []) m = CheckUnmodeled
    ∧ check_syscall (cwd_in 73728 256) (mkEffect 6 [] []) m = CheckUnmodeled
    ∧ check_syscall (cwd_in 69632 2) (mkEffect (errno_ret ERANGE) [] []) m = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- The probe's `--mutate getcwd:arg1=1 -- big` case: the kernel's own
answer to `getcwd(buf, 4096)`, the success return 6, offered for a call
whose a1 was rewritten to 1.  At size 1 line 439 (fs/d_path.c, Linux
v6.18.46) holds for every working directory, so the success return is a
lie there and is refused, where the same answer at 4096 is declined
(`above_band_declined_over_the_real_table`).
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem big_answer_at_size_one_rejected_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 1) (mkEffect 6 [] []) m = CheckReject := rfl

/-! ### The arm's reading of its registers

`cwd_in` puts zero in every register after a1, and zero is a size inside
the band, so a call whose a1 lies above the band separates the arm from
one that reads its size anywhere else. -/

/-- `getcwd(NULL, 4096)` is declined and `getcwd((char *)4096, 0)` answers
`-ERANGE`: the size is a1, not a0 (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46, hands
`orig_a0` to `buf` and `a1` to `size`).  An arm taking a0 for the size
accepts `-ERANGE` for the first and declines the second; one taking any
register after a1 sees zero there and accepts `-ERANGE` for the first.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/d_path.c:getcwd@v6.18.46 -/
theorem size_is_a1_over_the_real_table (m : Model) :
    check_syscall (cwd_in 0 4096) (mkEffect (errno_ret ERANGE) [] []) m = CheckUnmodeled
    ∧ check_syscall (cwd_in 4096 0) (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m [] :=
  ⟨rfl, rfl⟩

/-- The registers after a1 are not read: `getcwd(buf, 0)` with
2^64 - 1 in a2 and 4096 in a3, a4 and a5 still answers `-ERANGE`.
`SYSCALL_DEFINE2` maps two registers (`__MAP2`,
include/linux/syscalls.h:119, Linux v6.18.46, applied by
`SC_RISCV_REGS_TO_ARGS`), so the others reach no parameter.  An arm
reading its size from any of a2 to a5 sees a size above the band and
declines.
kernel: include/linux/syscalls.h:__MAP2; fs/d_path.c:getcwd@v6.18.46 -/
theorem registers_after_a1_unread_over_the_real_table (m : Model) :
    check_syscall
        (SyscallInput.mkInput 17 [69632, 0, Z_to_bv 64 (-1), 4096, 4096, 4096]
          (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret ERANGE) [] []) m = CheckOk m [] := rfl

/-- `size` is `unsigned long` (fs/d_path.c:412, Linux v6.18.46), the
register's width on riscv64, and `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88) keeps all 64 bits
of a1.  So 2^32 is a size every path fits, and so is 2^64 - 1, and the
arm declines both.  An arm narrowing a1 to 32 bits reads 2^32 as 0, and
one reading it as signed reads 2^64 - 1 as -1; each puts the call in the
band and accepts `-ERANGE`.
kernel: fs/d_path.c:getcwd; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem size_is_the_whole_register_over_the_real_table (m : Model) :
    check_syscall (cwd_in 69632 (2 ^ 32)) (mkEffect (errno_ret ERANGE) [] []) m = CheckUnmodeled
    ∧ check_syscall (cwd_in 69632 (-1)) (mkEffect (errno_ret ERANGE) [] []) m = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 17; `getcwd_witness_in_band` and
`getcwd_witness_above_band` fix `getcwd_witness` at bare words, and this
fixes that the arm hands it the same register the checker gets. -/

/-- In the band the witness exhibits the `-ERANGE` of fs/d_path.c:440
(Linux v6.18.46) on the model as given, with no event; above it, and for
`getcwd(NULL, 4096)` and a size of 2^32, the decline.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem witness_over_the_real_table (m : Model) :
    syscall_spec_witness (cwd_in 69632 0) m = Ok (mkEffect (errno_ret ERANGE) [] []) m []
    ∧ syscall_spec_witness (cwd_in 69632 4096) m = Unmodeled
    ∧ syscall_spec_witness (cwd_in 0 4096) m = Unmodeled
    ∧ syscall_spec_witness (cwd_in 69632 (2 ^ 32)) m = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

end V_Fs_DPath

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.DPath
