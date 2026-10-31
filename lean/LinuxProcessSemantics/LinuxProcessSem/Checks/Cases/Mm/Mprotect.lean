import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Mm.Mprotect — what `mprotect` admits, read off against Linux

Worked examples over `Sys.Mm.Mprotect.mprotect_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Mm/Mprotect.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f)
throughout.

HOW THESE ARE STATED.  As in `Checks/Cases/Mm/Mmap.lean`: the Lean tree has
no executable checker, so a check is stated on the relation itself, as an
`iff` over EVERY outcome `o` wherever the admitted set is finite — which for
`mprotect` is everywhere, since no arm of it chooses a placement.  Each
decision gets that `iff`, closed by `sys_norm`, and a refutation of the
answer a lying kernel would give, closed by `sys_refute`; the `iff` already
excludes the lie, and the refutation is kept because it is the shape a
reader asks for.  The argument gates hold for EVERY model, so their pins
quantify over `m` rather than naming a fixture.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree.  The one exception is
the section headed "Mutants the allowlist excuses", the one before the
dispatcher's, which is not pins: it holds the equivalence arguments the
mutation allowlist rests on, and says so in its own heading. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding, its errno list's, and its post-state builder's, at low priority.
The gates (`mprotect_modeled_b`, `mprotect_grows_conflict_b`,
`mprotect_budget_ok`) are decided, never unfolded, so they are not
registered.  The lines live here rather than in `Tactic.lean`'s register
on purpose: a port PR creates its own files and edits no shared one, so
that ports merge in any order (docs/merge-commutativity.md). -/

attribute [sys_simp low] mprotect_spec.eq_1 mprotect_errnos.eq_1 mprotect_model_next.eq_1

/-! ## The prot words these checks spell out -/

/-- The rw prot word.
kernel: include/uapi/asm-generic/mman-common.h:PROT_READ,PROT_WRITE@v6.18.46 -/
example : PROT_READ + PROT_WRITE = 3 := by decide
/-- rw with the GROWSDOWN modifier.
kernel: include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_READ,PROT_WRITE@v6.18.46 -/
example : PROT_GROWSDOWN + PROT_READ + PROT_WRITE = 16777219 := by decide
/-- rw with the GROWSUP modifier.
kernel: include/uapi/asm-generic/mman-common.h:PROT_GROWSUP,PROT_READ,PROT_WRITE@v6.18.46 -/
example : PROT_GROWSUP + PROT_READ + PROT_WRITE = 33554435 := by decide
/-- rw with both modifiers, the conflict.
kernel: include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP,PROT_READ,PROT_WRITE@v6.18.46 -/
example : PROT_GROWSDOWN + PROT_GROWSUP + PROT_READ + PROT_WRITE = 50331651 := by decide
/-- The one injectable errno.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
example : mprotect_errnos = [ENOMEM] := by decide

/-! ## Fixtures this file adds to the Prelude's

Rocq builds these with `with_vmmaps` over `noaccess_base`; here they are
`fixture` of a literal ledger, the Prelude's normal form. -/

/-- Two live rw pages at 65536 under a 16 KiB budget: the already-rw
no-op's model (Rocq: `with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384)
noaccess_base`). -/
def rw_two_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 16384 0 demo_sp)

/-- One reserved page at 65536 under a ZERO budget: exposing it would
charge a page the budget does not have. -/
def noaccess_zero_backing : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)

/-- Two adjacent one-page mappings: a range covering both is owned but
contained in NEITHER entry. -/
def two_adjacent_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 16384 0 demo_sp)

/-- Two live pages of which only the second is inaccessible: a request
over both is mixed-protection. -/
def mixed_two_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 16384 0 demo_sp)

/-- A two-page MAP_NORESERVE mapping whose second page is a PROT_NONE
guard, with the first page already touched, under a budget of exactly
that one page. -/
def mprotect_lazy_guard : Model :=
  with_vm_backing [(65536, 8192)] [65536]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 4096 0 demo_sp))

/-! ## Gate 1: both grows bits is -EINVAL, for every model

`do_mprotect_pkey` (mm/mprotect.c:867, :876-877, Linux v6.18.46) reads the
two bits before
anything else and rejects the pair, "can't be both".  It does so before the
zero-length return at :881, so `len = 0` does not rescue the call. -/

/-- Both grows bits: -EINVAL before anything else, for every model.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem grows_conflict_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 50331651 i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A zero-length success does not rescue the conflict.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem grows_conflict_zero_length_success_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65536 0 50331651 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The pair is refused before the wrap test too: at `(2^63, 2^63)` with
both grows bits the answer is :876-877's -EINVAL, not :885-886's -ENOMEM.
qemu-user agrees, its `validate_prot_to_pageflags` (linux-user/mmap.c:191-194,
QEMU 11.1.1) running before its range test (:199-201), so this -EINVAL
is inside the intersection.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem grows_conflict_precedes_wrap (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 9223372036854775808 9223372036854775808 50331651 i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- ...so the wrap arm's -ENOMEM is refused on the conflicting pair.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem grows_conflict_wrap_enomem_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 9223372036854775808 9223372036854775808 50331651 i m
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-! ## Either grows bit alone is legal

`do_mprotect_pkey` masks both out of `prot` (:875) and only the PAIR is
-EINVAL (:876-877).  A lone bit goes on to the VMA checks at :909 and
:919 — which sit past the zero-length return at :881, so at `len = 0` a
lone bit is 0 for every model.

LINUX'S ANSWER ALONE.  QEMU's user-mode emulation answers -EINVAL here:
`validate_prot_to_pageflags` (linux-user/mmap.c:121-151, QEMU 11.1.1)
accepts the grows bits only on HPPA (:146-147) and runs before the
zero-length return (:191-197), and the syscall entry's stack hack strips
PROT_GROWSDOWN only for a `start` inside the guest's stack window and
never strips PROT_GROWSUP (linux-user/syscall.c:11203-11216, QEMU 11.1.1).
So the two `_is_zero` pins below prove, and their `_einval_rejected`
twins refuse, an answer a supported implementation really gives at
`start = 65536`: `bugs/mprotect-zero-length-prot-admits-linux-alone.md`
records the residual, and these four are the pins to restate on
`Unmodeled` if the Rocq arm moves to decline. -/

/-- PROT_GROWSDOWN alone at zero length is 0.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN@v6.18.46 -/
theorem growsdown_alone_zero_length_is_zero (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 16777219 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- PROT_GROWSUP alone at zero length is 0.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSUP@v6.18.46 -/
theorem growsup_alone_zero_length_is_zero (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 33554435 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- A lone PROT_GROWSDOWN is not the conflict: -EINVAL refused.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN@v6.18.46 -/
theorem growsdown_alone_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 0 16777219 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A lone PROT_GROWSUP is not the conflict: -EINVAL refused.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSUP@v6.18.46 -/
theorem growsup_alone_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 0 33554435 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A lone grows bit at NONZERO length reaches the VMA checks (:909-915,
:919-924), which the model does not carry: declined, whatever the
model.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN@v6.18.46 -/
theorem growsdown_alone_nonzero_length_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 16777219 i m o ↔ o = Unmodeled := by
  sys_norm

/-! ## Gate 2: a misaligned start is -EINVAL, before the length is read

`if (start & ~PAGE_MASK) return -EINVAL;` (mm/mprotect.c:879-880, Linux
v6.18.46) precedes
`if (!len) return 0;` (:881-882), so a misaligned zero-length call is
-EINVAL, not 0; and it precedes `arch_validate_prot` (:887), so it is
-EINVAL for a `prot` the model would otherwise decline.  `untagged_addr`
(:873) is the identity on the modeled surface (the `mprotect_spec`
docstring), so the test sees the address the program passed. -/

/-- A misaligned start is -EINVAL even at zero length.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_precedes_zero_length (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65537 0 3 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The zero-length 0 does not rescue a misaligned start.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_zero_length_success_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65537 0 3 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and before the prot word: PROT_EXEC at a misaligned start is -EINVAL,
not `Unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_EXEC@v6.18.46 -/
theorem unaligned_precedes_unsupported_prot (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mprotect_spec 65537 4096 4 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ## Gate 3: `len = 0` is 0 for every prot that clears the grows conflict

`if (!len) return 0;` (mm/mprotect.c:881-882, Linux v6.18.46) sits before
`arch_validate_prot` at :887, so the prot word is never validated: nothing
is mapped, nothing is protected.  That is Linux's order; QEMU's user-mode
emulation validates first (`validate_prot_to_pageflags`, called at
linux-user/mmap.c:191-194 ahead of the `len == 0` return at :195-197,
QEMU 11.1.1), so its 0 agrees with Linux only where the LOW 32 bits of
`prot` stay inside PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM — and, for a
word carrying PROT_GROWSDOWN, only where `start` is outside the guest
stack window, inside which the emulation strips that bit and re-aims the
call at the lower stack (linux-user/syscall.c:11208-11213, QEMU 11.1.1),
so even a 0 there is another run; a word without the bit is untouched by
that hack wherever `start` lies.  The words pinned here agree: 1, 4, and
`2^40 + 3`, whose high bits qemu-user's `int` prot drops, all at
`start = 65536`.  The lone grows bits in the
section above do not; see it and the bugs entry it names. -/

/-- PROT_READ alone — the downgrade the model declines at nonzero length —
is 0 at zero length.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_zero_length_is_zero (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 1 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- A zero-length call admits 0 and nothing else.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_zero_length_errno_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 0 1 i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- PROT_EXEC at zero length is 0 too, and so is a prot word with garbage
in its high half (`2^40 + 3`), which `arch_validate_prot`
(include/linux/mman.h:106-109) would reject at :887-888 — a line the call
never reaches.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_EXEC@v6.18.46 -/
theorem exec_zero_length_is_zero (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 4 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- High garbage in `prot` is 0 at zero length: `arch_validate_prot` is never reached.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem high_garbage_zero_length_is_zero (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65536 0 1099511627779 i m o ↔ o = Ok (mkEffect 0 [] []) m [] := by
  sys_norm

/-- The -EINVAL `arch_validate_prot` would give is refused at zero length.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem high_garbage_zero_length_einval_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65536 0 1099511627779 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## Gate 4: a range whose end wraps is -ENOMEM, before the prot is read

`len = PAGE_ALIGN(len); end = start + len; if (end <= start) return
-ENOMEM;` (mm/mprotect.c:883-886, Linux v6.18.46), in `unsigned long`
arithmetic, and
before `arch_validate_prot` at :887. -/

/-- `mprotect(2^63, 2^63, rw)`: `end` wraps to exactly 0.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrapping_end_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 9223372036854775808 9223372036854775808 3 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- A wrapping range admits -ENOMEM and nothing else.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrapping_end_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mprotect_spec 9223372036854775808 9223372036854775808 3 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and it is -ENOMEM for PROT_EXEC as well, which the model would
otherwise decline: the wrap test precedes the prot.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot; include/uapi/asm-generic/mman-common.h:PROT_EXEC@v6.18.46 -/
theorem wrapping_end_precedes_unsupported_prot (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mprotect_spec 9223372036854775808 9223372036854775808 4 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The other way to wrap: a `len` within a page of `2^64` makes
`PAGE_ALIGN(len)` itself wrap to 0, so `end == start` and the test fires
at every aligned `start`.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mm.h:PAGE_ALIGN@v6.18.46 -/
theorem page_align_wrap_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mprotect_spec 65536 (Z_to_bv 64 (-1)) 3 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-! ## The rw exposure of a PROT_NONE range: two resolutions

Inside one live mapping, over a range `vm_noaccess` contains, Linux
produces two answers: -ENOMEM from the `may_expand_vm` test in
`mprotect_fixup` (mm/mprotect.c:801-803, Linux v6.18.46) or its commit
charge (:807-808), or from the `split_vma` map_count test (mm/vma.c:590-591,
Linux v6.18.46) and `__split_vma`'s allocation (mm/vma.c:510-512, Linux
v6.18.46); or 0, with the range now readable and
writable and its fresh anonymous pages reading as zeroes.  The model's
split of the no-access interval is `__split_vma`'s effect on its
intervals. -/

/-- The middle page of a three-page reservation: the success splits the
no-access interval into two remnants and zero-fills exactly that page.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem middle_page_exposure_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 69632 4096 3 i noaccess_three_pages o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []
       ∨ o = Ok (mkEffect 0 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- A success that zero-fills MORE than the page asked for is a lie.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem middle_page_wider_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 69632 4096 3 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(65536, 12288)]) m' evs) := by
  sys_refute

/-- A ONE-BYTE request at the middle page is the whole page's request:
`len = PAGE_ALIGN(len)` (mm/mprotect.c:883) rounds it up before the VMA
is found, so the split, the charge and the zero-fill are the page's, the
same two answers as `middle_page_exposure_iff` with `len` the only
difference.  The one pin here whose `len` is not a page multiple at an
aligned start: every other reaches a gate first.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem middle_page_one_byte_exposure_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 69632 1 3 i noaccess_three_pages o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []
       ∨ o = Ok (mkEffect 0 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- …so a success that zero-fills only the byte asked for is a lie: the
range Linux exposes is the rounded one, not `len`.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem middle_page_one_byte_narrow_zeros_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 69632 1 3 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(69632, 1)]) m' evs) := by
  sys_refute

/-- …and so is a success that leaves the no-access ledger untouched: the
page would read as zeroes to the program and still be inaccessible to
the model.  Refuted in hypothesis form: with `evs` symbolic the goal form
leaves `False → ¬evs = []` (the pass list has no `false_implies`), while
`sys_refute at h` folds the hypothesis to `False`.
kernel: mm/mprotect.c:mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem middle_page_unsplit_ledger_rejected (i : SyscallInput) (evs : List event) :
    ¬ mprotect_spec 69632 4096 3 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages evs) := by
  intro h
  sys_refute at h

/-- The errno preserves the ledger: -ENOMEM from `mprotect_fixup` is
returned before `vma_modify_flags` (:816) has split anything, and a split
that fails leaves the VMA as it was.
kernel: mm/mprotect.c:mprotect_fixup; mm/vma.c:vma_modify_flags@v6.18.46 -/
theorem exposure_errno_preserves_ledger (i : SyscallInput) :
    mprotect_spec 69632 4096 3 i noaccess_three_pages
      (Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []) := by
  sys_norm

/-- An errno outside `mprotect_errnos` is refused: -EINVAL past the four
gates is unreachable (the `mprotect_errnos` docstring walks each -EINVAL of
`do_mprotect_pkey`).
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem exposure_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 69632 4096 3 i noaccess_three_pages
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## The backing budget

Exposing a reserved page consumes backed capacity at the permission
transition, as `mprotect_fixup` charges the commit when a private mapping
turns writable (mm/mprotect.c:804-810, Linux v6.18.46).  The gate sits
INSIDE the success
resolution, so over budget the model MUST answer -ENOMEM rather than
decline. -/

/-- Over budget only the -ENOMEM resolution remains.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem exposure_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 3 i noaccess_zero_backing o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_zero_backing [] := by
  sys_norm

/-- Over budget the success is refused.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem exposure_over_budget_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4096 3 i noaccess_zero_backing
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-! ## MAP_NORESERVE provenance survives the exposure

`mprotect_fixup` takes the commit charge only when `oldflags` lacks
VM_NORESERVE among the flags at mm/mprotect.c:804-805 (Linux v6.18.46), so
a range mapped
MAP_NORESERVE is never charged at the transition; the model keeps its
lazy provenance and the first page's existing first-touch charge, and the
second page is not charged until an instruction accesses it. -/

/-- Exposing the MAP_NORESERVE guard page keeps its lazy provenance and the touched page.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem lazy_guard_exposure_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 69632 4096 3 i mprotect_lazy_guard o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) mprotect_lazy_guard []
       ∨ o = Ok (mkEffect 0 [] [(69632, 4096)])
              (with_vm_backing [(65536, 8192)] [65536]
                (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- The post-state's accounting, read off: the lazy range and the
materialized page are carried across, and the budget used is still the
one touched page.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem lazy_guard_does_not_eagerly_charge :
    m_vm_lazy (mprotect_model_next mprotect_lazy_guard 69632 4096) = [(65536, 8192)]
    ∧ m_vm_materialized (mprotect_model_next mprotect_lazy_guard 69632 4096) = [65536]
    ∧ vm_backing_used (mprotect_model_next mprotect_lazy_guard 69632 4096) = 4096 := by
  decide

/-- A kernel that dropped the lazy provenance at the transition — charging
the guard page eagerly, which is what the exposure of an ORDINARY mapping
does — would report a post-state the model refuses.  The forgery differs
from the admitted post-state in the lazy ledger ALONE: the materialized
page is kept, so the refutation turns on the provenance and nothing
else.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem lazy_guard_eager_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ mprotect_spec 69632 4096 3 i mprotect_lazy_guard
        (Ok (mkEffect 0 [] [(69632, 4096)])
          (with_vm_backing [] [65536]
            (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))) evs) := by
  -- hypothesis form, as `middle_page_unsplit_ledger_rejected`
  intro h
  sys_refute at h

/-! ## Already rw: a no-op that cannot fail

`mprotect_fixup` returns 0 on `newflags == oldflags` (mm/mprotect.c:769-772,
Linux v6.18.46) before `may_expand_vm` (:801), the commit charge (:807) and
`vma_modify_flags` (:816): no split, no map_count test, no accounting.
The equality holds for a strict subrange too, since `newflags` comes from
`prot` and the VMA's flags, not the range (:953-957). -/

/-- A strict subrange of an rw mapping: exactly 0.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem already_rw_subrange_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 3 i rw_two_pages o ↔ o = Ok (mkEffect 0 [] []) rw_two_pages [] := by
  sys_norm

/-- The whole rw mapping: exactly 0.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem already_rw_whole_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 8192 3 i rw_two_pages o ↔ o = Ok (mkEffect 0 [] []) rw_two_pages [] := by
  sys_norm

/-- An already-rw range cannot fail: -ENOMEM refused.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem already_rw_errno_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4096 3 i rw_two_pages (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …and it does not re-zero the pages: Linux leaves the contents alone,
so a success carrying a zero-fill is refused.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem already_rw_rezero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4096 3 i rw_two_pages (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-! ## Ranges the ledger cannot answer for: declined

Linux answers -ENOMEM for a start outside every VMA (`do_mprotect_pkey`,
mm/mprotect.c:905-907, :917-918, Linux v6.18.46), and the model declines
instead: the
ledger is not a complete picture of the address space (the stack has no
entry), so that errno would be a guess.  Nothing rescues a declined shape:
the arm is reached on the argument and the ledger, not on the offered
effect. -/

/-- A range outside every tracked mapping is declined.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unmapped_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 131072 4096 3 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- No offered effect rescues an unmapped range.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unmapped_forged_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 131072 4096 3 i noaccess_three_pages (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The `vm_maps` conjunct: a range `vm_noaccess` holds and `vm_maps` does
not is declined, not exposed.  The fixture is the abstract shape — nothing
mapped at all — where Linux answers -ENOMEM (:905-907); the one REACHABLE
state of this shape is the same-page brk shrink
(`testing/syscall-check/tests/noaccess_vm.c`, `brk-samepage-protect`), where Linux
answers 0 because a break move inside one page changes no VMA
(mm/mmap.c:153-158, Linux v6.18.46) and only the byte-granular ledger has
let go of the page's tail.  The model can name neither answer from its
ledger, so it declines; without the conjunct it would answer 0 over a
range whose last eight bytes it does not own, and a later store there
would fault in the model and not under Linux.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem noaccess_outside_vm_maps_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 3 i noaccess_unowned o ↔ o = Unmodeled := by
  sys_norm

/-- The exposure is refused where `vm_maps` does not own the range.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem noaccess_outside_vm_maps_exposure_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65536 4096 3 i noaccess_unowned
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- A range covered by two adjacent entries is contained in neither
(`map_contains` asks for ONE entry): on Linux the call walks both VMAs
(`for_each_vma_range`, :934) and succeeds; here it is declined.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem spanning_two_entries_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 8192 3 i two_adjacent_pages o ↔ o = Unmodeled := by
  sys_norm

/-- A mixed range — one page rw, one PROT_NONE — is neither wholly
inaccessible nor free of the no-access ledger: declined.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mixed_protection_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 8192 3 i mixed_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- A mixed range admits nothing, a partial zero-fill included.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mixed_protection_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 8192 3 i mixed_two_pages (Ok (mkEffect 0 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-! ## Every other prot at nonzero length: declined

Linux takes each of these on the ordinary path — `do_mprotect_pkey`
computes `newflags` from `prot` (:956-957) and `mprotect_fixup` applies it
— so each is a 0 the model does not give.  The first is the one that
matters: offering the checker the answer the real kernel gives has to
yield `Unmodeled`, not an admission.  A spec that widened
`mprotect_modeled_b` to "a subset of the permissions the range has" would
take that 0 and accept every later store to a page Linux made read-only
(the `Sys/Mm/Mprotect.lean` docstring says why no such page can be
encoded). -/

/-- PROT_READ over live rw pages: Linux answers 0, the model declines.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_downgrade_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 1 i rw_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- Offering the checker the 0 Linux gives yields `Unmodeled`, not an admission.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_downgrade_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4096 1 i rw_two_pages (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The declining arm is reached on the ARGUMENT SHAPE, so no offered
effect rescues it: a zero-fill range is refused for the same reason.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_downgrade_with_zeros_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65536 4096 1 i rw_two_pages (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- PROT_READ over a range still PROT_NONE is declined too: that range IS
in `vm_noaccess`, so the exposure's own gate matches on everything but the
prot word.  A spec that tested containment before the prot would expose
the page and hand a zero-fill to a program that may not write it.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_over_noaccess_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 69632 4096 1 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- PROT_EXEC would make a data page executable, which the machine model
cannot fetch from at all.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_EXEC@v6.18.46 -/
theorem exec_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 4 i rw_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- PROT_NONE over live rw pages would require preserving their contents
behind the transition.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_NONE@v6.18.46 -/
theorem none_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 0 i rw_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- Garbage in the high half of `prot` is a real -EINVAL on Linux at
nonzero length (`arch_validate_prot`, include/linux/mman.h:106-109, at
mm/mprotect.c:887-888), and declined here: the whole 64-bit word is
compared, so no truncation could make it read as rw.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem high_garbage_nonzero_length_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 1099511627779 i rw_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- The garbage word admits no success at nonzero length.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem high_garbage_nonzero_length_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mprotect_spec 65536 4096 1099511627779 i rw_two_pages (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## The budget mark

`mprotect_budget_refused_b` says, from the request and the pre-state
alone, whether the exposure's `choose` is unsatisfiable.  It is exact: it
is true precisely on the call whose `iff` above lost its success
resolution, and false on every gate-declined shape, whatever the
budget. -/

/-- The mark is true exactly where the exposure lost its success resolution.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem budget_mark_fires_over_budget :
    mprotect_budget_refused_b 65536 4096 3 noaccess_zero_backing = true := by decide

/-- Within budget the mark is silent.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_within_budget :
    mprotect_budget_refused_b 69632 4096 3 noaccess_three_pages = false := by decide

/-- The gates ahead of the charge never fire it, even on a spent budget:
zero length, a wrapping end, an unsupported prot, and an already-rw range
under a budget of zero.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_on_gates :
    mprotect_budget_refused_b 65536 0 3 noaccess_zero_backing = false
    ∧ mprotect_budget_refused_b 9223372036854775808 9223372036854775808 3 noaccess_zero_backing = false
    ∧ mprotect_budget_refused_b 65536 4096 1 noaccess_zero_backing = false
    ∧ mprotect_budget_refused_b 65536 4096 3
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 0 0 demo_sp)) = false := by
  decide

/-! ## The gates ahead of the charge, on a budget that is already spent

`budget_mark_silent_on_gates` covers two of the spec's four argument
gates — a zero length and a wrapping end — plus an unsupported prot and
an already-rw range, which are not argument gates at all; neither the
misaligned start nor the grows conflict had a mark pin, since every mark
pin before this section passes prot 3 or 1.  Both get one below.
The two argument gates it does cover are weaker than they look.  `noaccess_zero_backing` is not
over budget: its one page is inaccessible, so the backing is 0 against a
limit of 0, at the limit and inside it.  A mutant that deletes one of
those gates therefore answers `false` anyway — at a zero length because
cutting an empty range out of `vm_noaccess` leaves the backing where it
was, and at the wrapping end because the ledger does not contain the
range the call falls through with.  Either way the mark never reaches the
charge, so the pin cannot tell the gate from the model it is stated on.

The fixtures below separate the two.  Each carries a pre-state whose
backing ALREADY exceeds `vm_limit` (`over_budget_fixtures_exceed_the_limit`
pins all three) and goes on exceeding it however the request is cut out,
so the charge, `!(mprotect_budget_ok …)`, answers `true` wherever a mutant
lets a call reach it: for the first four requests the ledger contains the
range and only a gate stands in the way, and for the last only the
`vm_maps` conjunct does.  Linux reaches the charge on none of them: the
grows conflict is -EINVAL at mm/mprotect.c:876-877 (Linux v6.18.46), the
misaligned start is -EINVAL at :879-880, the zero length returns 0 at :881-882, the
wrapping end is -ENOMEM at :885-886 and a range outside every VMA is
-ENOMEM at :905-907 — or at :917-918 when a VMA begins inside it; the
fixture below reaches :905-907 — (Linux v6.18.46), all of them before
`mprotect_fixup` runs.  Nothing is charged on any of them, so the mark is
false — and would be true on each if the gate above it went, except at
the grows conflict, where `mprotect_modeled_b` refuses the same `prot`
and the mark stays false with or without its gate (the allowlist section
below carries that argument). -/

/-- Three pages live at 65536, the first two of them inaccessible, under a
budget of zero: the one backed page exceeds it already, and it stays
exceeded however the no-access interval is cut. -/
def noaccess_pair_over_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 8192)] 0 0 0 0 demo_sp)

/-- The last page of the address space, inaccessible inside a live
mapping, beside a backed page that exceeds the zero budget.
`mprotect(2^64 - 4096, 4096, rw)` is the page-sized request whose end is
exactly `2^64`, the one aligned start with that end at `len = 4096`:
`end` wraps to 0, so `end <= start` holds with nothing to spare — which is
what fixes the comparison and not just the branch.  No run reaches this
ledger, since no `mmap` grant lands above `TASK_SIZE`
(`__get_unmapped_area` refuses an address above `TASK_SIZE - len`,
mm/mmap.c:857-858, Linux v6.18.46); like `noaccess_unowned` it is a
ledger no grant produces, kept because what it probes is decided before
the ledger is consulted. -/
def noaccess_top_page_over_budget : Model :=
  fixture (VmMaps.mkVmMapsFull []
    [(18446744073709547520, 4096), (131072, 4096)] [(18446744073709547520, 4096)]
    0 0 0 0 demo_sp)

/-- `noaccess_unowned`'s ledger disagreement with a spent budget: a
no-access interval at 65536 that no live mapping owns, and a backed page
elsewhere over the zero budget. -/
def noaccess_unowned_over_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(131072, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)

/-- The premise every silence below rests on, pinned rather than read off
the literals: each of the three ledgers is over its budget BEFORE any
request, so a `false` below is a gate and not a satisfied charge.  Raise
a fixture's limit to a page and this goes red first.
model: `State.vm_backing_within_limit` over three literal ledgers; a fact
about the fixtures, not about Linux -/
theorem over_budget_fixtures_exceed_the_limit :
    vm_backing_within_limit noaccess_pair_over_budget = false
    ∧ vm_backing_within_limit noaccess_top_page_over_budget = false
    ∧ vm_backing_within_limit noaccess_unowned_over_budget = false := by
  decide

/-- Both grows bits is -EINVAL at :876-877, ahead of every other test and
of any charge: the mark is false with the budget spent and the range
inside the no-access interval.  The positive half alone: no mutant of
this gate is refused by the pin, because `mprotect_modeled_b` answers
`false` for the same `prot` and the tail below the gate answers `false`
too (`grows_conflict_excludes_modeled`, and the allowlist entry resting
on it).
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem budget_mark_silent_on_grows_conflict :
    mprotect_budget_refused_b 65536 4096 50331651 noaccess_pair_over_budget = false := by
  decide

/-- A misaligned start is -EINVAL at :879-880, before the length is read
and long before `mprotect_fixup` charges anything: the mark is false with
the budget spent and the range inside the no-access interval.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_on_unaligned_start :
    mprotect_budget_refused_b 65537 1 3 noaccess_pair_over_budget = false := by decide

/-- A zero length returns 0 at :881-882, again before any charge: the mark
is false, though the same model over budget answers `true` for a
page-sized request.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_at_zero_length_over_budget :
    mprotect_budget_refused_b 65536 0 3 noaccess_pair_over_budget = false := by decide

/-- …and that page-sized request on the same model does fire it, so the
zero-length silence above is the gate and not the fixture: the two
requests differ in `len` alone.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem budget_mark_fires_on_the_same_fixture :
    mprotect_budget_refused_b 65536 4096 3 noaccess_pair_over_budget = true := by decide

/-- A one-byte request at the aligned start is rounded up to the page
(`PAGE_ALIGN`, :883) and charged: true on the same model, so the silence
at 65537 above is the alignment gate and not the fixture — those two
requests differ in `addr` alone.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_fires_on_one_byte_request :
    mprotect_budget_refused_b 65536 1 3 noaccess_pair_over_budget = true := by decide

/-- The exposure those marks refuse, on the spec: over budget only the
-ENOMEM resolution remains on this fixture too, so the mark is exact
here as on `noaccess_zero_backing` (`exposure_over_budget_iff`).
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem pair_over_budget_exposure_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4096 3 i noaccess_pair_over_budget o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_pair_over_budget [] := by
  sys_norm

/-- …and the success is refused there.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem pair_over_budget_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4096 3 i noaccess_pair_over_budget
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- An end of exactly `2^64` is -ENOMEM at :885-886 (`end` is 0, so `end <=
start`), before the prot word and before any charge: the mark is false at
the one address where that test holds with nothing to spare.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_on_wrapping_end :
    mprotect_budget_refused_b 18446744073709547520 4096 3 noaccess_top_page_over_budget
      = false := by decide

/-- A range `vm_maps` does not contain is declined, so no charge is
reached and the mark is false — with the budget spent and the range
wholly inside `vm_noaccess`.  The model declines because its ledger
cannot answer for the range, not because it reads the state as outside
every VMA (the `mprotect_spec` docstring: the ledger is thinner than
Linux's picture); what Linux does with a start outside every VMA,
-ENOMEM at :905-907, is why the `vm_maps` conjunct is there at all, and
either way the call never reaches `mprotect_fixup`'s charge.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_outside_vm_maps :
    mprotect_budget_refused_b 65536 4096 3 noaccess_unowned_over_budget = false := by decide

/-- The spec's own answer at that top-of-space range: -ENOMEM from the wrap
gate, not the exposure the ledger would otherwise allow.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem top_page_wrap_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 18446744073709547520 4096 3 i noaccess_top_page_over_budget o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_top_page_over_budget [] := by
  sys_norm

/-- The exposure of that range is refused: `end <= start` is decided at
:885-886, ahead of every VMA lookup.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem top_page_wrap_exposure_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 18446744073709547520 4096 3 i noaccess_top_page_over_budget
        (Ok (mkEffect 0 [] [(18446744073709547520, 4096)]) m' evs) := by
  sys_refute

/-- One page lower the sum is `2^64 - 4096`, `end > start`, and the wrap
gate is silent: the request reaches the ledger, which holds no entry for
`[2^64 - 8192, 2^64 - 4096)`, and is declined — not the -ENOMEM the gate
gives one page up.  Linux answers -ENOMEM here as well, from the VMA
lookup (:905-907: no VMA lies below `end`), which the model does not
read off its thinner ledger; what this pins is the gate's edge from the
side that does not wrap.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem below_top_page_does_not_wrap (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 18446744073709543424 4096 3 i noaccess_top_page_over_budget o ↔
      o = Unmodeled := by
  sys_norm

/-! ## Mutants the allowlist excuses

`tools/lean_mutate.py` rewrites one decision of `Sys/Mm/Mprotect.lean` at a
time and asks whether a theorem above stops elaborating.  Four of its
mutants change no answer on any input, so no pin can refuse them, and
`tools/lean_mutation/allowlist.Mm.Mprotect.json` names each one with the
theorem below that establishes it.

NOTHING IN THIS SECTION IS A PIN.  A pin says what Linux does; these say
that two spellings of the model agree, which is what an allowlist entry
asserts and what its prose cannot be checked for.  Read as evidence about
the kernel each would be the fault PIN-1 exists to catch — a spec
compared with a re-encoding of itself — and PIN-1 cannot see it here,
because it counts `*_spec` names and none of these statements carries
one.  The heading is the only guard, which is why two of them carry a
`kernel:` line: `check_lean_pin_evidence.py`'s MODEL-TWIN rule refuses
`model:` on a statement naming a Bool decision of the Sys twin, and it is
right to — the constants and the bit layout those two rest on are
Linux's.  What is not a kernel claim is the EQUALITY each one draws. -/

/-- What every `check-swap` equivalence turns on: two tests that never both
hold answer alike in either order.  `check-swap` exchanges two consecutive
`if`s of one chain, so this is the whole content of such a mutant.
model: pure logic over two decidable tests; no definition of the model is
read, and none of the kernel is claimed -/
theorem ite_swap_of_disjoint {α : Type _} (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (a b r : α) (h : c1 → ¬ c2) :
    (if c1 then a else if c2 then b else r) = (if c2 then b else if c1 then a else r) := by
  by_cases h1 : c1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (h h1)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : c2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]

/-- `mprotect_spec`'s zero-length gate and its wrap gate never both hold:
at `len = 0` the rounded length is 0 and no address reaches `2^64`.  With
`ite_swap_of_disjoint` that is the whole of the `check-swap` mutant which
exchanges them.
model: arithmetic over `page_round_up_Z` and the 64-bit range of an
address; each gate's own answer is pinned above, by
`read_only_zero_length_is_zero` and `wrapping_end_is_enomem`, and which
of two tests that never both hold fires first is unobservable — which is
what makes the swap equivalent -/
theorem zero_length_never_wraps (addr len : word) (h : w_is0 len = true) :
    ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := by
  have haddr : bv_unsigned addr < two_pow_64 := by
    unfold bv_unsigned two_pow_64
    exact_mod_cast addr.isLt
  have hlen : bv_unsigned len = 0 := by
    have hz : len = Z_to_bv 64 0 := by
      unfold w_is0 bv_eqb at h
      exact eq_of_beq h
    rw [hz]; decide
  intro hc
  rw [hlen, show page_round_up_Z 0 = 0 from by decide] at hc
  omega

/-- Containment in ONE interval and freedom from ALL of them exclude each
other for a nonempty range: the interval that contains it overlaps it.
model: interval arithmetic over `State.map_contains` and
`State.region_free`, which decide nothing about Linux by themselves -/
theorem map_contains_excludes_region_free (maps : List (word × word)) (lo n : word)
    (hn : 0 < bv_unsigned n) : map_contains maps lo n = true → region_free maps lo n = false := by
  induction maps with
  | nil => intro h; simp only [map_contains, List.any_nil] at h; exact absurd h (by decide)
  | cons p r ih =>
    intro h
    simp only [map_contains, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    simp only [region_free, Bool.and_eq_false_iff]
    rcases h with hp | hr
    · left
      simp only [iv_overlap, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]
      omega
    · right
      exact ih (by simp only [map_contains]; exact hr)

/-- Past the zero-length and wrap gates the exposure's range is nonempty:
the rounded length is at least a page and below `2^64`, so the word the
spec builds from it is not 0.
model: arithmetic over `page_round_up_Z` and the 64-bit wrap of `Z_to_bv` -/
theorem exposure_range_nonempty (addr len : word) (hz : w_is0 len = false)
    (hw : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))) :
    0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) := by
  have hge : 0 ≤ bv_unsigned len := by
    unfold bv_unsigned
    exact Int.natCast_nonneg _
  have hne : bv_unsigned len ≠ 0 := by
    intro hc
    have h0 : len.toNat = 0 := by
      unfold bv_unsigned at hc
      omega
    have hzero : len = Z_to_bv 64 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [h0]; decide
    rw [hzero] at hz
    exact absurd hz (by decide)
  have hvpos : 0 < bv_unsigned len := by omega
  have haddr : 0 ≤ bv_unsigned addr := by
    unfold bv_unsigned
    exact Int.natCast_nonneg _
  have hlow : 4096 ≤ page_round_up_Z (bv_unsigned len) := by
    unfold page_round_up_Z page_size
    omega
  have hhigh : page_round_up_Z (bv_unsigned len) < two_pow_64 := by
    unfold two_pow_64 at *
    omega
  have hround : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      = page_round_up_Z (bv_unsigned len) := by
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : Int) ≤ page_round_up_Z (bv_unsigned len)
      by omega)
    have hklt : k < 2 ^ 64 := by
      unfold two_pow_64 at hhigh
      omega
    rw [hk]
    unfold bv_unsigned Z_to_bv
    rw [BitVec.ofInt_natCast]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt]
  rw [hround]
  omega

/-- The exposure branch and the already-rw branch of `mprotect_spec` never
both hold: the exposure asks for a range one `vm_noaccess` interval
contains, the no-op for a range disjoint from all of them, and past the
two gates above the range is nonempty.  With `ite_swap_of_disjoint` that is
the whole of the `check-swap` mutant which exchanges them.
model: `State.map_contains` against `State.region_free`, by the
containment argument of `map_contains_excludes_region_free` -/
theorem exposure_and_already_rw_are_disjoint (vm : VmMaps) (addr len : word)
    (hz : w_is0 len = false)
    (hw : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)))
    (hc : (map_contains vm.vm_noaccess addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains vm.vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
          = true) :
    (map_contains vm.vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      && region_free vm.vm_noaccess addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      = false := by
  have hn := exposure_range_nonempty addr len hz hw
  simp only [Bool.and_eq_true] at hc
  have hfree := map_contains_excludes_region_free vm.vm_noaccess addr _ hn hc.1
  simp only [hfree, Bool.and_false]

/-- Both grows bits at once is not the rw word: PROT_GROWSDOWN and
PROT_GROWSUP are bits 24 and 25 and PROT_READ|PROT_WRITE is 3, so
`mprotect_modeled_b` is false wherever the conflict holds.  That is why
deleting the mark's grows-conflict gate changes no answer: the arms below
it that a conflicting `prot` reaches all answer `false` too.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP,PROT_READ,PROT_WRITE@v6.18.46 -/
theorem grows_conflict_excludes_modeled (prot : word)
    (h : mprotect_grows_conflict_b prot = true) : mprotect_modeled_b prot = false := by
  cases hm : mprotect_modeled_b prot with
  | false => rfl
  | true =>
    exfalso
    unfold mprotect_modeled_b at hm
    have hp : bv_unsigned prot = PROT_READ + PROT_WRITE := eq_of_beq hm
    have hprot : prot = (3 : word) := by
      apply BitVec.eq_of_toNat_eq
      unfold bv_unsigned PROT_READ PROT_WRITE at hp
      have h3 : prot.toNat = 3 := by omega
      rw [h3]; decide
    rw [hprot] at h
    exact absurd h (by decide)

/-- The `branch-else` mutant of the mark's grows-conflict gate, written out
so the theorem below argues about the mutant and not a paraphrase of it:
the tool replaces that `if`'s condition with `False`, which deletes the
arm.

NOTHING CHECKS THAT THIS IS STILL THE MUTANT.  It was byte-for-byte the
tool's rewrite when it was written, and the allowlist entry is sound only
while its tail stays the mark's tail — change `mprotect_budget_refused_b`
below the grows gate without mirroring it here, and this copy quietly
stops being the mutant, the entry's reason becomes false, and no proof,
pin or guard goes red.  No pin can stand in: in the mark itself a
conflicting `prot` is answered by the gate and never by the tail, so only
the mutant observes the tail there.  What would close it is a text check
the way `CLAUDE.md` asks — the mark's body with
`if mprotect_grows_conflict_b prot then false` replaced by
`if False then false` equals this body — and that check does not exist
yet.  Until it does, mirror by hand and say so in the allowlist reason. -/
def budget_refused_grows_gate_dropped (addr len prot : word) (m : Model) : Bool :=
  if False then false
  else if !(bv_unsigned addr % page_size == 0) then false
  else if w_is0 len then false
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then false
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      !(mprotect_budget_ok m addr n)
    else false
  else false

/-- …and where the conflict holds it answers `false`, which is what the
deleted arm answered: `mprotect_modeled_b` is false there
(`grows_conflict_excludes_modeled`) and every other arm of the chain is
`false` outright.  That is the whole content of the equivalence, since
below the deleted arm the two texts are the same text — the half a reader
settles by putting the two bodies side by side, as with the `check-swap`
entries above.

STATED THIS WAY ON PURPOSE.  The equality `… = mprotect_budget_refused_b
…` is the statement one reaches for, and it is a trap: it holds only
while the copy matches the spec, so EVERY later non-equivalent mutant of
`mprotect_budget_refused_b` breaks it too, and `lean_mutate` reports that
mutant as killed by a theorem which says nothing about Linux.  It would
mask a real gap in the mark's pins behind a name that reads like one.
kernel: mm/mprotect.c:do_mprotect_pkey; include/uapi/asm-generic/mman-common.h:PROT_GROWSDOWN,PROT_GROWSUP@v6.18.46 -/
theorem budget_refused_grows_gate_dropped_is_false_on_conflict
    (addr len prot : word) (m : Model) (h : mprotect_grows_conflict_b prot = true) :
    budget_refused_grows_gate_dropped addr len prot m = false := by
  have hm : mprotect_modeled_b prot = false := grows_conflict_excludes_modeled prot h
  unfold budget_refused_grows_gate_dropped
  rw [ite_eq_right_of_eq_false _ _ (eq_false not_false), hm]
  simp only [Bool.false_eq_true, ite_false, ite_self]

/-- The `const-swap` mutant of `mprotect_grows_conflict_b`: exchanging
PROT_GROWSDOWN and PROT_GROWSUP everywhere in that body permutes the two
conjuncts of its one `&&`, and the pair `grows == (PROT_GROWSDOWN|PROT_GROWSUP)`
the kernel tests at :876-877 is symmetric in them too.

STATED ON THE TWO BODIES, NOT ON THE DEF.  The left side is the mutant's
text and the right the spec's, read off side by side as with the
`check-swap` entries.  An equality against `mprotect_grows_conflict_b`
itself was the first draft, and the score cache showed it co-killing both
`guard-drop` mutants of that def — a killer that says nothing about Linux,
standing where `growsup_alone_zero_length_is_zero` and
`growsdown_alone_zero_length_is_zero` are the pins that do.  Naming no
definition, this theorem can kill nothing and needs no `rfl` escape for
the mutated world.
model: `Bool.and_comm` over the two conjuncts; the constants are Linux's
(include/uapi/asm-generic/mman-common.h:17-18, Linux v6.18.46) but the
commutation is not a kernel claim -/
theorem grows_conflict_const_swap_eq (prot : word) :
    (!(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSUP)) == 0)
      && !(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSDOWN)) == 0))
      = (!(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSDOWN)) == 0)
      && !(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSUP)) == 0)) :=
  Bool.and_comm _ _

/-- The `vm_maps` conjunct ahead of the mark is load-bearing: the same-page
brk-shrink shape — `vm_noaccess` holding a page that `vm_maps` owns eight
bytes short of — under a zero budget would be over budget if exposed,
and the mark is false because the arm declines that shape instead — the
silence is the decline's, not Linux's: in the reachable state
(`testing/syscall-check/tests/noaccess_vm.c`, `brk-samepage-protect`)
Linux takes the charge like any exposure of a PROT_NONE page, and what
sends the arm to `Unmodeled` is that `do_mprotect_pkey` answers 0 there
and -ENOMEM (:905-907) on the unmapped shape the ledger cannot tell apart.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem budget_mark_silent_where_vm_maps_does_not_own :
    mprotect_budget_refused_b 65536 4096 3
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 4088)] [(65536, 4096)] 0 0 0 0 demo_sp))
      = false := by
  decide

/-- The spent two-page fixture the next pins share: two live pages at
65536, the first still inaccessible, under a budget of zero, so any
exposure at all is over budget.  The positive half first: an ordinary
aligned one-page call there fires the mark.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem budget_mark_fires_on_the_spent_two_page_fixture :
    mprotect_budget_refused_b 65536 4096 3
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 0 0 demo_sp))
      = true := by
  decide

/-- The wrap gate ahead of the mark is load-bearing: a length whose page
rounding reaches `2^64` rounds to a word of 0, so without the gate the
containment tests would hold on the spent fixture and the mark would fire,
where Linux answers -ENOMEM at :885-886 before the charge.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_silent_on_a_wrapping_length_over_budget :
    mprotect_budget_refused_b 65536 (Z_to_bv 64 (-1)) 3
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 0 0 demo_sp))
      = false := by
  decide

/-- The wrap gate's bound is inclusive: a range ending exactly at `2^64` is
the wrapped `end = 0 <= start` of :885-886 and is refused there, so the
mark stays silent on it even over budget, while the same one-page exposure
one page lower, ending at `2^64 - 4096`, is inside the space and fires.
Both fixtures hold a live, inaccessible page at the top of the word, where
no real trace places one (the `near_ceiling_sum_model` note).
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem budget_mark_wrap_bound_is_inclusive :
    mprotect_budget_refused_b (Z_to_bv 64 (two_pow_64 - 4096)) 4096 3
        (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (two_pow_64 - 4096), 4096)]
          [(Z_to_bv 64 (two_pow_64 - 4096), 4096)] 0 0 0 0 demo_sp))
      = false
    ∧ mprotect_budget_refused_b (Z_to_bv 64 (two_pow_64 - 8192)) 4096 3
        (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)]
          [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] 0 0 0 0 demo_sp))
      = true := by
  decide

/-- The mark rounds the length as the spec does: at `len = 4097` the charge
is two pages, `nrpages` of the `PAGE_ALIGN`ed end (:883, :761), so a budget
of 8191 refuses it, where a mark reading the raw length would see 4097
bytes fit.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/linux/mm.h:PAGE_ALIGN@v6.18.46 -/
theorem budget_mark_charges_the_rounded_length :
    mprotect_budget_refused_b 65536 4097 3
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8191 0 demo_sp))
      = true := by
  decide

/-- The spec's half of the same decision: at `len = 4097` under a budget of
8191 the exposure has lost its success resolution and only the charge's
-ENOMEM (:807-808) remains.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/linux/mm.h:PAGE_ALIGN@v6.18.46 -/
theorem unaligned_len_over_budget_is_enomem_only (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4097 3 i
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8191 0 demo_sp)) o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] [])
            (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8191 0 demo_sp)) [] := by
  sys_norm

/-! ## The length is page-rounded before the range is used

`len = PAGE_ALIGN(len)` (mm/mprotect.c:883, Linux v6.18.46) runs after the
zero-length return and before the range is walked, so a 4097-byte request
covers two pages.  Every other accepting pin in this file passes a
page-multiple `len`, on which rounding is the identity; these are the pins
that tell `page_round_up_Z` from the raw length. -/

/-- 4097 bytes from the start of a three-page reservation expose TWO pages:
the post-state's remnant starts at the third page and the zero-fill is
8192 bytes.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem unaligned_len_rounds_up_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mprotect_spec 65536 4097 3 i noaccess_three_pages o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []
       ∨ o = Ok (mkEffect 0 [] [(65536, 8192)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(73728, 4096)]
                          0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- A spec that used the raw length would expose 4097 bytes and split the
interval mid-page; refused.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_len_raw_exposure_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4097 3 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(65536, 4097)]) m' evs) := by
  sys_refute

/-- ...and one that rounded DOWN would expose one page; refused too.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_len_one_page_exposure_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mprotect_spec 65536 4097 3 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-! ## The dispatcher -/

/-- Syscall 226 reaches `mprotect_spec` with a0..a2 as its three arguments
(a3..a5 are carried as 7 here, and this call's answer does not depend on
them).
kernel: include/uapi/asm-generic/unistd.h:__NR_mprotect; mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem sysno_226_is_mprotect (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 226 [65536, 0, 50331651, 7, 7, 7] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] :=
  grows_conflict_is_einval
    (SyscallInput.mkInput 226 [65536, 0, 50331651, 7, 7, 7] (fun _ => none) (fun _ => none)) m o

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mprotect
